//! The Reed–Solomon code itself: GF(2⁸), a systematic Cauchy generator, and
//! the recovery of erased symbols.
//!
//! **Everything here is pinned to the byte, and that is the point.** "Parity is
//! a pure function of the children" is what makes it deduplicate, verifiable by
//! plain hash, and repairable by anyone without a key — and it is only true if
//! two independent implementations produce identical bytes. Two libraries that
//! both call themselves systematic RS(k+3, k) routinely disagree on the field
//! polynomial, on how the generator matrix is built, and on which axis the
//! symbols run along. So each of those is fixed here and frozen by vectors.
//!
//! - Field GF(2⁸), reducing polynomial **0x11D**, generator **2**.
//! - Generator matrix `[I ; C]`, systematic, with `C` a 3 × k Cauchy matrix:
//!   `C[r][c] = 1 / (x_r ⊕ y_c)`, `x_r = r` for `r ∈ 0..3` and `y_c = 3 + c`
//!   for `c ∈ 0..k`. The two index sets are disjoint for every `k ≤ 12`, every
//!   square submatrix of a Cauchy matrix is invertible, and the `k < 12` case
//!   is literally the first `k` columns — so ONE definition covers every group
//!   size, `k = 1` included.
//! - Layout: byte `i` of every data symbol is one codeword. Parity `p` byte `i`
//!   is `⊕_c C[p][c] · data_c[i]`.

/// The reducing polynomial, x⁸ + x⁴ + x³ + x² + 1.
const POLY: u16 = 0x11D;
/// Parity symbols per group. Three, so a group survives any three losses.
pub const PARITY: usize = 3;
/// The largest group the grouping rule can produce.
pub const MAX_K: usize = 12;

/// `exp[i] = 2^i` and `log[2^i] = i` in GF(2⁸), built once from the polynomial
/// rather than pasted in: a table nobody can check against its own definition
/// is a place for a typo to live for ever.
struct Tables {
    exp: [u8; 512],
    log: [u8; 256],
}

impl Tables {
    const fn new() -> Tables {
        let mut t = Tables {
            exp: [0; 512],
            log: [0; 256],
        };
        let mut x: u16 = 1;
        let mut i = 0;
        while i < 255 {
            t.exp[i] = x as u8;
            t.log[x as usize] = i as u8;
            x <<= 1;
            if x & 0x100 != 0 {
                x ^= POLY;
            }
            i += 1;
        }
        // The second half repeats the first, so a product's exponent needs no
        // modulo: `exp[log a + log b]` is always in range.
        let mut j = 0;
        while j < 255 {
            t.exp[255 + j] = t.exp[j];
            j += 1;
        }
        t
    }
}

static T: Tables = Tables::new();

/// Multiplication in GF(2⁸). Zero is handled before the logarithm, which has
/// no value at zero.
fn mul(a: u8, b: u8) -> u8 {
    if a == 0 || b == 0 {
        return 0;
    }
    T.exp[T.log[a as usize] as usize + T.log[b as usize] as usize]
}

/// Division in GF(2⁸). `b` must not be zero; every call here divides by a
/// Cauchy denominator `x_r ⊕ y_c`, which is non-zero because the index sets are
/// disjoint.
fn div(a: u8, b: u8) -> u8 {
    debug_assert!(b != 0, "division by zero in GF(2^8)");
    if a == 0 {
        return 0;
    }
    let d = T.log[a as usize] as i16 - T.log[b as usize] as i16;
    T.exp[(d.rem_euclid(255)) as usize]
}

/// `C[r][c]` of the Cauchy generator, for a group of `k` data symbols.
///
/// `x_r = r`, `y_c = 3 + c`. `r < 3 ≤ 3 + c`, so the denominator is never zero
/// and the matrix is defined for every `k` — including `k = 1`, where the three
/// parity symbols are three different scalar multiples of the single data
/// symbol.
pub fn coeff(r: usize, c: usize) -> u8 {
    debug_assert!(r < PARITY && c < MAX_K);
    div(1, (r as u8) ^ ((PARITY + c) as u8))
}

/// The three parity symbols of a group.
///
/// Every data symbol must already be the same length — the caller pads them,
/// because padding is where the length prefix lives and that belongs to the
/// block format rather than to the code.
pub fn encode(data: &[Vec<u8>]) -> Result<Vec<Vec<u8>>, RsError> {
    let k = data.len();
    if k == 0 || k > MAX_K {
        return Err(RsError::GroupSize(k));
    }
    let width = data[0].len();
    if data.iter().any(|d| d.len() != width) {
        return Err(RsError::Ragged);
    }
    let mut out = vec![vec![0u8; width]; PARITY];
    for (c, d) in data.iter().enumerate() {
        for (r, p) in out.iter_mut().enumerate() {
            let f = coeff(r, c);
            if f == 0 {
                continue;
            }
            for (o, s) in p.iter_mut().zip(d.iter()) {
                *o ^= mul(f, *s);
            }
        }
    }
    Ok(out)
}

/// Rebuild the missing data symbols from any `k` of the `k + 3` blocks.
///
/// `have[j]` is `Some` for a block that is present: indices `0..k` are the data
/// symbols in group order, `k..k+3` the parity symbols. What comes back is the
/// full data set, so a caller can take whichever symbols it was missing.
pub fn repair(k: usize, have: &[Option<Vec<u8>>]) -> Result<Vec<Vec<u8>>, RsError> {
    if k == 0 || k > MAX_K {
        return Err(RsError::GroupSize(k));
    }
    if have.len() != k + PARITY {
        return Err(RsError::Ragged);
    }
    let width = have
        .iter()
        .flatten()
        .map(|b| b.len())
        .next()
        .ok_or(RsError::NotEnough(0))?;
    if have.iter().flatten().any(|b| b.len() != width) {
        return Err(RsError::Ragged);
    }
    // The first k present blocks, and the rows of [I;C] they stand for.
    let mut rows: Vec<[u8; MAX_K]> = Vec::with_capacity(k);
    let mut vals: Vec<&Vec<u8>> = Vec::with_capacity(k);
    for (j, b) in have.iter().enumerate() {
        if rows.len() == k {
            break;
        }
        let Some(b) = b else { continue };
        let mut row = [0u8; MAX_K];
        if j < k {
            row[j] = 1;
        } else {
            for (c, slot) in row.iter_mut().enumerate().take(k) {
                *slot = coeff(j - k, c);
            }
        }
        rows.push(row);
        vals.push(b);
    }
    if rows.len() < k {
        return Err(RsError::NotEnough(rows.len()));
    }

    // Gauss–Jordan on the k × k matrix, applying the same operations to the
    // symbols. Any k rows of [I;C] are independent — that is the Cauchy
    // property — so a pivot always exists.
    let mut sym: Vec<Vec<u8>> = vals.into_iter().cloned().collect();
    for col in 0..k {
        let p = (col..k)
            .find(|&r| rows[r][col] != 0)
            .ok_or(RsError::Singular)?;
        rows.swap(col, p);
        sym.swap(col, p);
        let inv = div(1, rows[col][col]);
        for v in rows[col].iter_mut().take(k) {
            *v = mul(*v, inv);
        }
        for b in sym[col].iter_mut() {
            *b = mul(*b, inv);
        }
        // The pivot's symbol is lifted out so the other rows can borrow
        // mutably while reading it; it goes back before the next column.
        let pivot_row = rows[col];
        let pivot_sym = core::mem::take(&mut sym[col]);
        for r in 0..k {
            if r == col || rows[r][col] == 0 {
                continue;
            }
            let f = rows[r][col];
            for (c, v) in rows[r].iter_mut().enumerate().take(k) {
                *v ^= mul(f, pivot_row[c]);
            }
            for (o, p) in sym[r].iter_mut().zip(pivot_sym.iter()) {
                *o ^= mul(f, *p);
            }
        }
        sym[col] = pivot_sym;
    }
    Ok(sym)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RsError {
    /// A group of 0, or of more than [`MAX_K`].
    GroupSize(usize),
    /// Symbols of different lengths, or the wrong number of slots.
    Ragged,
    /// Fewer than `k` blocks present.
    NotEnough(usize),
    /// Should be unreachable: any k rows of a Cauchy `[I;C]` are independent.
    Singular,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The field is a field: the tables are inverses of each other, and every
    /// non-zero element has a multiplicative inverse. Built from the polynomial
    /// rather than pasted, so this is what says the polynomial is right.
    #[test]
    fn the_field_tables_are_consistent() {
        for x in 1..=255u8 {
            assert_eq!(
                T.exp[T.log[x as usize] as usize], x,
                "log/exp disagree at {x}"
            );
            assert_eq!(mul(x, div(1, x)), 1, "{x} has no inverse");
        }
        assert_eq!(mul(0, 7), 0);
        assert_eq!(mul(7, 0), 0);
        // 0x11D is what makes 2 a generator: the powers of 2 must visit every
        // non-zero element exactly once before returning to 1.
        let mut seen = [false; 256];
        let mut x = 1u8;
        for _ in 0..255 {
            assert!(
                !seen[x as usize],
                "2 is not a generator under this polynomial"
            );
            seen[x as usize] = true;
            x = mul(x, 2);
        }
        assert_eq!(x, 1);
    }

    /// Systematic: the data symbols are not touched, only three are added.
    /// And the code is a pure function of its input, at every group size.
    #[test]
    fn encoding_is_deterministic_at_every_group_size() {
        for k in 1..=MAX_K {
            // Non-zero: an all-zero data symbol codes to all-zero parity,
            // which is correct and makes the distinctness check below vacuous.
            let data: Vec<Vec<u8>> = (0..k).map(|i| vec![i as u8 + 1; 16]).collect();
            let a = encode(&data).expect("a codeable group");
            let b = encode(&data).expect("a codeable group");
            assert_eq!(a, b, "k = {k}: not deterministic");
            assert_eq!(a.len(), PARITY);
            assert!(a.iter().all(|p| p.len() == 16));
            // k = 1 is the degenerate case worth naming: three DIFFERENT
            // scalar multiples of one symbol, not three copies of it.
            if k == 1 {
                assert!(a[0] != a[1] && a[1] != a[2], "k = 1 parity must differ");
            }
        }
    }

    /// Any three losses, at every group size: the whole point of 3 parity.
    #[test]
    fn any_three_losses_are_repairable_at_every_group_size() {
        for k in 1..=MAX_K {
            let data: Vec<Vec<u8>> = (0..k)
                .map(|i| (0..32u8).map(|b| b.wrapping_mul(i as u8 + 1)).collect())
                .collect();
            let parity = encode(&data).expect("a codeable group");
            let all: Vec<Vec<u8>> = data.iter().chain(parity.iter()).cloned().collect();
            let n = k + PARITY;
            // Every way to lose three of the k + 3.
            for a in 0..n {
                for b in a + 1..n {
                    for c in b + 1..n {
                        let have: Vec<Option<Vec<u8>>> = (0..n)
                            .map(|j| (j != a && j != b && j != c).then(|| all[j].clone()))
                            .collect();
                        let got = repair(k, &have).expect("k of k+3 present");
                        assert_eq!(got, data, "k = {k}: lost {a},{b},{c}");
                    }
                }
            }
        }
    }

    /// Fewer than k blocks cannot be repaired, and says so rather than
    /// returning something plausible.
    #[test]
    fn too_few_blocks_is_refused() {
        let k = 8;
        let data: Vec<Vec<u8>> = (0..k).map(|i| vec![i as u8; 8]).collect();
        let parity = encode(&data).unwrap();
        let all: Vec<Vec<u8>> = data.iter().chain(parity.iter()).cloned().collect();
        // Four losses out of k + 3 = 11 leaves 7 < 8.
        let have: Vec<Option<Vec<u8>>> = (0..k + PARITY)
            .map(|j| (j >= 4).then(|| all[j].clone()))
            .collect();
        assert_eq!(repair(k, &have), Err(RsError::NotEnough(k - 1)));
        assert_eq!(encode(&[]), Err(RsError::GroupSize(0)));
        assert!(matches!(
            encode(&vec![vec![0u8; 4]; MAX_K + 1]),
            Err(RsError::GroupSize(_))
        ));
        assert_eq!(encode(&[vec![0u8; 4], vec![0u8; 5]]), Err(RsError::Ragged));
    }

    /// The Cauchy coefficients, spelled out for the sizes the vectors will
    /// freeze. If the construction or the index sets ever move, this fails
    /// before any vector does and says which cell changed.
    #[test]
    fn the_cauchy_coefficients_are_what_the_rule_says() {
        for r in 0..PARITY {
            for c in 0..MAX_K {
                let want = div(1, (r as u8) ^ ((PARITY + c) as u8));
                assert_eq!(coeff(r, c), want, "C[{r}][{c}]");
                assert_ne!(coeff(r, c), 0, "C[{r}][{c}] must be invertible");
            }
        }
        // x_r and y_c are disjoint for every k <= MAX_K, which is what makes
        // every denominator non-zero.
        for r in 0..PARITY {
            for c in 0..MAX_K {
                assert_ne!(r as u8, (PARITY + c) as u8);
            }
        }
    }
}
