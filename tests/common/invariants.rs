//! What a tree must look like, checked by walking it.
//!
//! The write gate's main oracle is a from-scratch rebuild: build the same map
//! with `TreeBuilder` and compare roots. That is a strong check and it caught
//! the lost-subtree bug in #22 — but only because it happened to be there. A
//! root comparison says "not the tree a rebuild gives" and nothing about WHAT is
//! wrong, and a test that mutates a tree without a rebuild to compare against
//! has no structural check at all.
//!
//! So this is the second, independent witness: given a root, a store and what
//! the tree is supposed to contain, walk it and decide whether it is a tree.
//!
//! It is deliberately written from `Node::parse` and nothing else. It does not
//! call `load_child`, which makes several of these same checks inside the
//! library — a witness that shares code with the thing it is judging agrees
//! with it by construction. The checks:
//!
//! 1. Every child named by a branch is in the store. A lost subtree is not
//!    "some entries missing" here, it is a dangling id. (Nodes only: a value
//!    kept in its own block is checked by its id and length against the bytes
//!    the reference map holds, because several callers keep node blocks and
//!    value blocks in different places and a walk should work for them too.
//!    That binds the value's ID and LENGTH, not its presence: a leaf cannot
//!    name a different value than the map has, but this walk will not tell you
//!    the block is retrievable. If the store does hold it, it is checked.)
//! 2. The root is a leaf, or has at least two children. A branch with one child
//!    is a level that should have collapsed.
//! 3. Only the LAST branch of a level may have a single child. Anywhere else it
//!    means a split ran where the minimum span forbids one.
//! 4. A child's level is its parent's minus one — the tree is level, not ragged.
//! 5. The first key and the aggregate a parent records for a child are what the
//!    child itself says. Checked at every edge, so a wrong aggregate cannot hide
//!    behind a correct total.
//! 6. A node's own recorded aggregate is what its contents add up to.
//! 7. The entries, read left to right, are exactly the reference map: same keys,
//!    same values, same order, nothing missing and nothing extra.
//!
//! Of these, 7 is what a lost subtree trips, 1 is what a dangling reference
//! trips, and 5 is what a forged or stale aggregate trips. Together they are
//! meant to fail on any damage that leaves a parseable tree behind.

use freenet_prolly::node::{Agg, Node, Value, MAX_INLINE};
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::{block_id, kind, Cid};
use std::collections::BTreeMap;

pub type Map = BTreeMap<Vec<u8>, Vec<u8>>;

/// Walk the tree at `root` and check it against `want`.
///
/// `Err` carries what is wrong and where, not just that something is.
pub fn check_tree(blocks: &MemBlocks, root: &Cid, want: &Map) -> Result<(), String> {
    let mut w = Walk {
        blocks,
        entries: Vec::new(),
        // One entry per level: how many children the last branch seen at that
        // level had, and whether it has been followed by another. Checked in
        // traversal order, which is key order, so "the last one" is the one
        // nothing follows.
        widths: BTreeMap::new(),
    };
    let node = w.node(root, "root")?;
    if !node.is_leaf() && node.len() < 2 {
        return Err(format!(
            "the root is a branch with {} child(ren) — the tree should have lost a level",
            node.len()
        ));
    }
    let agg = w.descend(root, &node, "root")?;

    for (level, seen) in &w.widths {
        if let Some(idx) = seen.thin {
            if idx + 1 < seen.count {
                return Err(format!(
                    "branch {idx} of {} at level {level} has a single child; only a level's last node may have one",
                    seen.count
                ));
            }
        }
    }

    let got = w.entries;
    if got.len() != want.len() {
        return Err(mismatch(&got, want));
    }
    for (i, ((k, seen), (wk, wv))) in got.iter().zip(want).enumerate() {
        if k != wk {
            return Err(mismatch(&got, want));
        }
        match seen {
            Seen::Inline(b) if b != wv => {
                return Err(format!(
                    "entry {i} ({}) holds {} B inline, the map has {} B",
                    String::from_utf8_lossy(k),
                    b.len(),
                    wv.len()
                ))
            }
            Seen::Ref(cid, len) => {
                if *len as usize != wv.len() || *cid != block_id(kind::RAW, wv) {
                    return Err(format!(
                        "entry {i} ({}) references a {len} B value, the map has {} B",
                        String::from_utf8_lossy(k),
                        wv.len()
                    ));
                }
                if wv.len() <= MAX_INLINE {
                    return Err(format!(
                        "entry {i} ({}) is {} B and would fit inline, but is kept in its own block",
                        String::from_utf8_lossy(k),
                        wv.len()
                    ));
                }
            }
            _ => {}
        }
    }
    // The root's aggregate covers the whole tree, so it is also the one number
    // a caller sees without reading anything.
    let total = want.iter().fold(Agg::default(), |a, (k, v)| Agg {
        count: a.count + 1,
        bytes: a.bytes + k.len() as u64 + v.len() as u64,
    });
    if agg != total {
        return Err(format!(
            "root aggregate is {agg:?}, the map adds up to {total:?}"
        ));
    }
    Ok(())
}

/// Where two entry sequences first differ, and by how much — so a failure names
/// the damage rather than leaving the reader to diff two long lists.
fn mismatch(got: &[(Vec<u8>, Seen)], want: &Map) -> String {
    let want: Vec<&Vec<u8>> = want.keys().collect();
    let at = (0..got.len().min(want.len()))
        .find(|&i| &got[i].0 != want[i])
        .unwrap_or(got.len().min(want.len()));
    let show = |k: Option<&Vec<u8>>| match k {
        Some(k) => String::from_utf8_lossy(k).into_owned(),
        None => "<end>".into(),
    };
    format!(
        "the tree holds {} entries, the map has {} — first difference at {at}: tree {}, map {}",
        got.len(),
        want.len(),
        show(got.get(at).map(|(k, _)| k)),
        show(want.get(at).copied()),
    )
}

#[derive(Default)]
struct Level {
    count: usize,
    /// The index of the FIRST branch at this level with a single child. The
    /// first, not the latest: if a middle branch is thin and the level's last
    /// one is too, keeping the latest would report the legal one and miss the
    /// illegal one.
    thin: Option<usize>,
}

/// A value as the LEAF holds it — which of the two shapes, not the bytes. The
/// bytes of a referenced value may live somewhere this walk cannot reach.
enum Seen {
    Inline(Vec<u8>),
    Ref(Cid, u32),
}

struct Walk<'a> {
    blocks: &'a MemBlocks,
    entries: Vec<(Vec<u8>, Seen)>,
    widths: BTreeMap<u8, Level>,
}

impl<'a> Walk<'a> {
    fn node(&self, id: &Cid, whose: &str) -> Result<Node<'a>, String> {
        let b = self
            .blocks
            .get(id)
            .ok_or_else(|| format!("{whose} names {id:?}, which is not in the store"))?;
        Node::parse(b).map_err(|e| format!("{whose} names a block that is not a node: {e:?}"))
    }

    /// Returns what this subtree actually adds up to.
    fn descend(&mut self, id: &Cid, node: &Node<'_>, whose: &str) -> Result<Agg, String> {
        let mut sum = Agg::default();
        if node.is_leaf() {
            for i in 0..node.len() {
                let key = node.key(i);
                let bytes = match node.value(i) {
                    Value::Inline(b) => {
                        if b.len() > MAX_INLINE {
                            return Err(format!(
                                "leaf {id:?} holds {} B inline, over the {MAX_INLINE} B limit",
                                b.len()
                            ));
                        }
                        self.entries.push((key.clone(), Seen::Inline(b.to_vec())));
                        b.len() as u64
                    }
                    Value::Ref { cid, len } => {
                        // If the caller keeps value blocks here too, the block
                        // must be what the leaf says it is. If it does not, the
                        // id itself is checked against the reference map above,
                        // which binds the bytes just as tightly.
                        if let Some(v) = self.blocks.get(&cid) {
                            if v.len() != len as usize || block_id(kind::RAW, v) != cid {
                                return Err(format!(
                                    "leaf {id:?} records a {len} B value for {}, the block is {} B and hashes to {:?}",
                                    String::from_utf8_lossy(&key),
                                    v.len(),
                                    block_id(kind::RAW, v)
                                ));
                            }
                        }
                        self.entries.push((key.clone(), Seen::Ref(cid, len)));
                        len as u64
                    }
                };
                sum = sum
                    .checked_add(Agg {
                        count: 1,
                        bytes: key.len() as u64 + bytes,
                    })
                    .ok_or("aggregate overflow")?;
            }
        } else {
            let lvl = self.widths.entry(node.level()).or_default();
            lvl.count += 1;
            if node.len() == 1 && lvl.thin.is_none() {
                lvl.thin = Some(lvl.count - 1);
            }
            for i in 0..node.len() {
                let (cid, agg) = node.child(i);
                let child = self.node(&cid, &format!("child {i} of {whose} ({id:?})"))?;
                if child.level() + 1 != node.level() {
                    return Err(format!(
                        "child {i} of {whose} is level {}, its parent is level {}",
                        child.level(),
                        node.level()
                    ));
                }
                if child.is_empty() {
                    return Err(format!("child {i} of {whose} is an empty node"));
                }
                let first = child.key(0);
                if first != node.key(i) {
                    return Err(format!(
                        "{whose} records first key {} for child {i}, the child starts at {}",
                        String::from_utf8_lossy(&node.key(i)),
                        String::from_utf8_lossy(&first)
                    ));
                }
                let real = self.descend(&cid, &child, &format!("child {i} of {whose}"))?;
                if real != agg {
                    return Err(format!(
                        "{whose} records {agg:?} for child {i}, it really holds {real:?}"
                    ));
                }
                sum = sum.checked_add(real).ok_or("aggregate overflow")?;
            }
        }
        if node.agg() != sum {
            return Err(format!(
                "{whose} records its own aggregate as {:?}, its contents add up to {sum:?}",
                node.agg()
            ));
        }
        Ok(sum)
    }
}
