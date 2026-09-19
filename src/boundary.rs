//! Where one node ends and the next begins.
//!
//! The decision is made per entry, *after* the entry is added to the open node:
//!
//! ```text
//! h32 = first 4 bytes (LE) of BLAKE3("PT01-split" ‖ level ‖ key)
//! split after this entry  iff  s_after ≥ MIN_SPLIT
//!                          and  h32 · λ⁴  <  (s_after⁴ − s_before⁴) · 2³²
//! ```
//! where `s` is the open node's [`NodeBuilder::logical_len`](crate::node::NodeBuilder::logical_len)
//! before and after the entry. The hash depends on the key alone, so a value
//! edit never changes *whether an entry can be* a boundary; the size term makes
//! a split ever more likely as the node grows (a Weibull hazard of shape 4),
//! which keeps node sizes tight around the mean instead of geometrically spread.
//!
//! Everything is integer arithmetic in `u128` (both sides stay below 2⁸⁹):
//! boundaries decide hashes, and float rounding is not portable across targets.
//!
//! An entry that would push the open node past the level's hard limit closes the
//! node *before* it instead. That forced split is the only one not decided by
//! content; the hazard makes it vanishingly rare.
//!
//! `LAMBDA`, the limits and the hash domain are format constants: changing any
//! of them changes every root hash. They are pinned by `tests/vectors.txt`.

use crate::node::MAX_NODE;

/// Scale of the split hazard. Mean `logical_len` ≈ 0.906·λ plus about half an entry.
pub const LAMBDA: u64 = 4400;
/// No content-defined split closes a node smaller than this.
pub const MIN_SPLIT: usize = 1024;
/// Hard limit on a leaf's `logical_len`.
pub const MAX_LEAF: usize = MAX_NODE;
/// Hard limit on a branch's `logical_len`. The remaining 4 KiB of the node is
/// reserved for parity cids, which are not part of the boundary measure.
pub const MAX_BRANCH: usize = 12 * 1024;

const DOMAIN: &[u8] = b"PT01-split";
const LAMBDA4: u128 = (LAMBDA as u128).pow(4);

/// Hard limit on `logical_len` for a node at `level`.
pub fn limit(level: u8) -> usize {
    if level == 0 {
        MAX_LEAF
    } else {
        MAX_BRANCH
    }
}

/// The per-entry split hash.
pub fn split_hash(level: u8, key: &[u8]) -> u32 {
    let mut h = blake3::Hasher::new();
    h.update(DOMAIN);
    h.update(&[level]);
    h.update(key);
    let d = h.finalize();
    let b = d.as_bytes();
    u32::from_le_bytes([b[0], b[1], b[2], b[3]])
}

/// Whether a node at `level` closes after the entry with `key`, which grew the
/// node's `logical_len` from `s_before` to `s_after`.
pub fn splits_after(level: u8, key: &[u8], s_before: usize, s_after: usize) -> bool {
    debug_assert!(s_before < s_after && s_after <= MAX_NODE);
    if s_after < MIN_SPLIT {
        return false;
    }
    let p4 = |s: usize| (s as u128).pow(4);
    let lhs = split_hash(level, key) as u128 * LAMBDA4;
    let rhs = (p4(s_after) - p4(s_before)) << 32;
    lhs < rhs
}
