//! Which blocks form a parity group, and what a group's symbols are.
//!
//! A node's children are coded in groups; each group gets three parity blocks
//! ([`crate::rs`]), and the node lists their ids. What this module decides is
//! the **membership** — and it has to decide it the same way for every reader,
//! because `pcount` is verified exactly and a disagreement about grouping is a
//! disagreement about whether a node is valid.
//!
//! **Groups are content-defined on the child's KEY, never on its cid.** A
//! child's cid changes on every write beneath it, so a cid-keyed boundary would
//! appear or disappear on roughly one write in eight per level and regroup two
//! neighbouring groups each time — less stable than counting, in exchange for
//! being more stable on the rare case. The tree's own chunking hashes the key
//! for the same reason.
//!
//! ```text
//! h = first 4 bytes (LE) of BLAKE3("PT01-pgroup" ‖ level ‖ key)
//! close after this member  iff  the group holds ≥ MIN_GROUP  and  h < 2³²/3
//! forced close             iff  the group holds MAX_GROUP
//! ```
//!
//! A final group shorter than `MIN_GROUP` folds into the previous one when the
//! two together are at most `MAX_GROUP`, and otherwise stands alone. **Only the
//! last group can ever be short**, because every earlier one closed on the rule
//! above, so there is at most one fold and it never cascades — which is what
//! makes the reserve arithmetic exact rather than approximate.
//!
//! On a LEAF the members are the referenced values, grouped **by size class
//! first** (§11's padding classes) and content-defined by key within a class.
//! Referenced values run from 1 KiB to 256 KiB with no size-tightness, so
//! grouping them by key alone would pad a mixed group to its largest and write
//! three parity blocks of that size: for private data, where every value in a
//! class is already padded to the class, the waste is instead zero.
//!
//! Inline values are not members of anything: they live in the leaf, and the
//! leaf is a member of its parent's group. The reserve arithmetic depends on
//! that.

use crate::node::{Node, Value, MAX_VALUE};
use crate::rs;

/// Domain for the grouping hash. Distinct from `"PT01-split"` so a key cannot
/// mean one thing to the boundary rule and another to the grouping rule.
const DOMAIN: &[u8] = b"PT01-pgroup";

/// A group closes on the hash only once it holds this many members. Seven, and
/// the number is forced by the reserve rather than chosen: at six, a full leaf
/// of referenced values needs 135 parity ids — 4,320 B — and the reserve is
/// 4,096.
pub const MIN_GROUP: usize = 7;
/// A group closes here whatever the hash says.
pub const MAX_GROUP: usize = rs::MAX_K;
/// Mean group size ≈ 9: after the 7th member, one member in three closes it.
const CLOSE_THRESHOLD: u32 = (u32::MAX / 3) + 1;

/// The size classes for referenced values, in bytes — §11's padding classes.
/// Every Ref value is 1 KiB + 1 .. [`MAX_VALUE`], so these four cover all of
/// them and there is no fifth class and no excluded tail.
pub const CLASSES: [usize; 4] = [4 * 1024, 16 * 1024, 64 * 1024, MAX_VALUE];

/// Which class a referenced value of `len` bytes belongs to.
pub fn class_of(len: usize) -> usize {
    CLASSES
        .iter()
        .position(|&c| len <= c)
        .unwrap_or(CLASSES.len() - 1)
}

/// The grouping hash of one key, held as `prefix ‖ suffix` so a reader checking
/// a whole node never allocates a key.
pub fn group_hash_parts(level: u8, prefix: &[u8], suffix: &[u8]) -> u32 {
    let mut h = blake3::Hasher::new();
    h.update(DOMAIN);
    h.update(&[level]);
    h.update(prefix);
    h.update(suffix);
    let b = h.finalize();
    let b = b.as_bytes();
    u32::from_le_bytes([b[0], b[1], b[2], b[3]])
}

/// Split a run of members, in key order, into groups.
///
/// `hashes` is the grouping hash of each member's key, in order. What comes
/// back is the group sizes, summing to `hashes.len()`.
pub fn group_sizes(hashes: &[u32]) -> Vec<usize> {
    if hashes.is_empty() {
        return Vec::new();
    }
    let mut sizes: Vec<usize> = Vec::new();
    let mut open = 0usize;
    for &h in hashes {
        open += 1;
        if open == MAX_GROUP || (open >= MIN_GROUP && h < CLOSE_THRESHOLD) {
            sizes.push(open);
            open = 0;
        }
    }
    if open > 0 {
        // Only the last group can be short, so this fold happens at most once
        // and cannot cascade.
        match sizes.last_mut() {
            Some(prev) if open < MIN_GROUP && *prev + open <= MAX_GROUP => *prev += open,
            _ => sizes.push(open),
        }
    }
    sizes
}

/// The groups of a node, as counts, in the order their parity ids appear.
///
/// A branch groups its children in key order. A leaf groups its REFERENCED
/// values by class ascending, then by key within the class. A leaf with no
/// referenced values has no groups, and so no parity.
pub fn group_sizes_of(node: &Node<'_>) -> Vec<usize> {
    let level = node.level();
    let prefix = node.prefix();
    if level > 0 {
        let hashes: Vec<u32> = (0..node.len())
            .map(|i| group_hash_parts(level, prefix, node.suffix(i)))
            .collect();
        return group_sizes(&hashes);
    }
    let mut out = Vec::new();
    for class in 0..CLASSES.len() {
        let hashes: Vec<u32> = (0..node.len())
            .filter(|&i| match node.value(i) {
                Value::Ref { len, .. } => class_of(len as usize) == class,
                _ => false,
            })
            .map(|i| group_hash_parts(level, prefix, node.suffix(i)))
            .collect();
        out.extend(group_sizes(&hashes));
    }
    out
}

/// How many parity ids a node must carry: three per group, and a pure function
/// of the entries. This is what `check_node` compares `pcount` against.
pub fn pcount_of(node: &Node<'_>) -> usize {
    rs::PARITY * group_sizes_of(node).len()
}

/// One member's coded symbol: `len:u32 LE ‖ state ‖ zeros`.
///
/// `state` is the member's FULL block state — `kind ‖ body` — so a rebuilt
/// symbol IS the block and verifies against its id by one hash, with nothing
/// inferred from context. The length prefix is what makes the padding
/// reversible: the parent stores a cid and an aggregate, neither of which
/// carries a length, so without it a repairer could not know where the block
/// ends.
pub fn symbol(state: &[u8], width: usize) -> Vec<u8> {
    debug_assert!(state.len() + 4 <= width);
    let mut out = Vec::with_capacity(width);
    out.extend_from_slice(&(state.len() as u32).to_le_bytes());
    out.extend_from_slice(state);
    out.resize(width, 0);
    out
}

/// The width every symbol of a group is padded to: the longest, prefix
/// included.
pub fn group_width(states: &[Vec<u8>]) -> usize {
    4 + states.iter().map(|s| s.len()).max().unwrap_or(0)
}

/// The three parity symbols for one group of member states.
pub fn encode_group(states: &[Vec<u8>]) -> Result<Vec<Vec<u8>>, rs::RsError> {
    let width = group_width(states);
    let data: Vec<Vec<u8>> = states.iter().map(|s| symbol(s, width)).collect();
    rs::encode(&data)
}

/// Recover a member's state from any `k` of the `k + 3` blocks of its group.
///
/// `have` holds the symbols: `0..k` the members in group order, `k..k+3` the
/// parity. What comes back is each member's state, padding stripped by the
/// length its own symbol carries — so the caller can hash it straight against
/// the id it was missing.
pub fn repair_group(k: usize, have: &[Option<Vec<u8>>]) -> Result<Vec<Vec<u8>>, rs::RsError> {
    let symbols = rs::repair(k, have)?;
    symbols
        .into_iter()
        .map(|s| {
            let len = u32::from_le_bytes([s[0], s[1], s[2], s[3]]) as usize;
            if 4 + len > s.len() {
                return Err(rs::RsError::Ragged);
            }
            Ok(s[4..4 + len].to_vec())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hashes(n: usize, closing: &[usize]) -> Vec<u32> {
        (0..n)
            .map(|i| if closing.contains(&i) { 0 } else { u32::MAX })
            .collect()
    }

    /// The close rule: never before MIN_GROUP, always by MAX_GROUP.
    #[test]
    fn a_group_never_closes_early_and_never_runs_past_the_maximum() {
        // A hash that always closes: every group is exactly MIN_GROUP until
        // the tail.
        let all_close: Vec<u32> = vec![0; 30];
        let sizes = group_sizes(&all_close);
        assert!(sizes.iter().all(|&s| (MIN_GROUP..=MAX_GROUP).contains(&s)));
        assert_eq!(sizes.iter().sum::<usize>(), 30);
        assert_eq!(sizes[0], MIN_GROUP, "a group closed before the minimum");

        // A hash that never closes: every group is exactly MAX_GROUP.
        let none: Vec<u32> = vec![u32::MAX; 30];
        let sizes = group_sizes(&none);
        assert_eq!(sizes.iter().sum::<usize>(), 30);
        assert!(sizes[..sizes.len() - 1].iter().all(|&s| s == MAX_GROUP));
    }

    /// Only the last group can be short, so the fold happens at most once and
    /// never cascades. That is what makes the reserve worst case exactly
    /// `⌊n / MIN_GROUP⌋ + 1` per run.
    #[test]
    fn at_most_one_group_is_short_and_the_fold_never_cascades() {
        for n in 1..=60usize {
            for closing in [
                vec![],
                (0..n).step_by(7).collect::<Vec<_>>(),
                (0..n).collect(),
            ] {
                let sizes = group_sizes(&hashes(n, &closing));
                assert_eq!(sizes.iter().sum::<usize>(), n, "n = {n}: members lost");
                assert!(
                    sizes.iter().all(|&s| s <= MAX_GROUP),
                    "n = {n}: a group over the maximum"
                );
                let short = sizes.iter().filter(|&&s| s < MIN_GROUP).count();
                assert!(short <= 1, "n = {n}: {short} short groups");
                if short == 1 {
                    assert!(
                        *sizes.last().expect("non-empty") < MIN_GROUP,
                        "n = {n}: a short group that is not the last"
                    );
                }
            }
        }
    }

    /// The fold: a short tail joins the previous group when it fits, and
    /// stands alone when it does not.
    #[test]
    fn a_short_tail_folds_only_when_it_fits() {
        // 7 then 2: folds to one group of 9.
        let mut h = vec![u32::MAX; 9];
        h[6] = 0;
        assert_eq!(group_sizes(&h), vec![9]);
        // 12 then 2: 14 > MAX_GROUP, so the tail stands alone.
        let mut h = vec![u32::MAX; 14];
        h[11] = 0;
        assert_eq!(group_sizes(&h), vec![12, 2]);
        // A run shorter than MIN_GROUP is one group, with nothing to fold into.
        assert_eq!(group_sizes(&[u32::MAX; 3]), vec![3]);
        assert_eq!(group_sizes(&[]), Vec::<usize>::new());
    }

    /// Every referenced value falls in exactly one class, and the boundaries
    /// are inclusive upper bounds.
    #[test]
    fn the_size_classes_cover_every_referenced_value() {
        assert_eq!(class_of(1025), 0);
        assert_eq!(class_of(4 * 1024), 0, "the boundary is inclusive");
        assert_eq!(class_of(4 * 1024 + 1), 1);
        assert_eq!(class_of(16 * 1024), 1);
        assert_eq!(class_of(64 * 1024), 2);
        assert_eq!(class_of(64 * 1024 + 1), 3);
        assert_eq!(class_of(MAX_VALUE), 3, "the largest value a Ref can hold");
    }

    /// A symbol carries its own length, so padding is reversible without the
    /// parent knowing anything about the child's size.
    #[test]
    fn a_group_round_trips_through_its_parity_at_unequal_lengths() {
        let states: Vec<Vec<u8>> = vec![
            vec![0u8; 1],
            (0..100u8).collect(),
            vec![7u8; 4096],
            vec![9u8; 33],
        ];
        let parity = encode_group(&states).expect("a codeable group");
        let width = group_width(&states);
        assert!(parity.iter().all(|p| p.len() == width));
        let k = states.len();
        let all: Vec<Vec<u8>> = states
            .iter()
            .map(|s| symbol(s, width))
            .chain(parity.iter().cloned())
            .collect();
        // Lose the three largest data symbols; rebuild from the rest.
        let have: Vec<Option<Vec<u8>>> = (0..k + rs::PARITY)
            .map(|j| (!(1..=3).contains(&j)).then(|| all[j].clone()))
            .collect();
        assert_eq!(repair_group(k, &have).expect("repairable"), states);
    }
}
