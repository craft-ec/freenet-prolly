//! Where blocks come from.
//!
//! Tree operations are pure functions of a root and a [`Blocks`] source. They
//! never wait: an operation that reaches a block the source does not hold stops
//! with [`TreeError::Need`] naming it, the caller fetches it, and runs the same
//! operation again. That fits a caller that works in bounded rounds and cannot
//! block — and re-running is cheap, because the upper levels are the ones
//! already held.

use crate::node::{Node, NodeError};
use crate::Cid;
use std::collections::HashMap;

/// A source of blocks by id. An implementation MUST only return a body whose
/// [`block_id`](crate::block_id) for its kind is `cid` (hash-keyed storage gives
/// this for free). `get` lends bytes that live as long as the source, so a
/// source is a map of blocks already in memory — not a lazy fetcher: what is
/// missing is reported as [`ReadError::Need`], fetched by the caller, added to
/// the map, and the operation is run again.
pub trait Blocks {
    fn get(&self, cid: &Cid) -> Option<&[u8]>;
}

/// So a `&B` is a block source wherever `B` is.
///
/// Without it, anything that WRAPS a block source — the probed source in the
/// tests, a caching layer, a counting one — has to own it, which means cloning
/// a store to hand it to two wrappers. The trait takes `&self` already, so
/// this costs nothing and removes a copy.
impl<B: Blocks + ?Sized> Blocks for &B {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        (**self).get(cid)
    }
}

/// A block source that can also be written to.
///
/// [`apply_into`](crate::apply::apply_into) uses it so that no caller has to
/// write the loop that feeds emitted blocks back into its own store — getting
/// that loop wrong is silent until a read, which makes it exactly the kind of
/// thing a library should do once.
pub trait BlocksMut: Blocks {
    fn insert_block(&mut self, cid: Cid, bytes: &[u8]);
}

/// Fresh blocks first, a base store second.
///
/// A rebuild needs its own output back: a branch's parity members are its
/// CHILDREN, and when a branch closes those children were created moments ago
/// and are not in the caller's store yet — `apply` emits them to a sink and the
/// caller inserts them afterwards. Reading only the store would miss exactly
/// the members the rebuild just made.
///
/// So writes look here first and fall through. `build` with no base store uses
/// an overlay over nothing, where a `Ref` whose bytes were never handed over is
/// a miss — and a miss is refused, never quietly coded as absent.
pub struct Overlay<'a, B: Blocks> {
    fresh: std::collections::BTreeMap<Cid, Vec<u8>>,
    base: Option<&'a B>,
}

impl<'a, B: Blocks> Overlay<'a, B> {
    pub fn new(base: Option<&'a B>) -> Self {
        Overlay {
            fresh: std::collections::BTreeMap::new(),
            base,
        }
    }

    /// Remember a block this call produced or was handed.
    pub fn put(&mut self, cid: Cid, bytes: &[u8]) {
        self.fresh.insert(cid, bytes.to_vec());
    }

    pub fn holds(&self, cid: &Cid) -> bool {
        self.fresh.contains_key(cid)
    }
}

impl<B: Blocks> Blocks for Overlay<'_, B> {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        self.fresh
            .get(cid)
            .map(|v| v.as_slice())
            .or_else(|| self.base.and_then(|b| b.get(cid)))
    }
}

/// Blocks held in memory.
#[derive(Default, Clone)]
pub struct MemBlocks(pub HashMap<Cid, Vec<u8>>);

impl MemBlocks {
    pub fn insert(&mut self, cid: Cid, bytes: &[u8]) {
        self.0.insert(cid, bytes.to_vec());
    }
}

impl BlocksMut for MemBlocks {
    fn insert_block(&mut self, cid: Cid, bytes: &[u8]) {
        self.insert(cid, bytes);
    }
}

impl Blocks for MemBlocks {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        self.0.get(cid).map(Vec::as_slice)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReadError {
    /// These blocks are required and not held. Fetch them and run again.
    Need(Vec<Cid>),
    /// A block does not parse as a node.
    Corrupt(Cid, NodeError),
    /// A child is not what its parent says: wrong level, first key or aggregate.
    Mismatch(Cid),
}

/// Load and parse the node `cid`.
pub fn load<'a>(blocks: &'a impl Blocks, cid: &Cid) -> Result<Node<'a>, ReadError> {
    let bytes = blocks.get(cid).ok_or_else(|| ReadError::Need(vec![*cid]))?;
    Node::parse(bytes).map_err(|e| ReadError::Corrupt(*cid, e))
}

/// The smallest key AFTER child `i` of `parent`: its next sibling's key, else
/// whatever follows the parent itself (`upper`, the caller's own bound).
///
/// `None` only at the right edge of the whole tree.
pub fn child_upper(parent: &Node<'_>, i: usize, upper: Option<&[u8]>) -> Option<Vec<u8>> {
    if i + 1 < parent.len() {
        Some(parent.key(i + 1))
    } else {
        upper.map(<[u8]>::to_vec)
    }
}

/// Load child `i` of `parent` and check it against what the parent records, so
/// that everything reached from a trusted root is itself trusted.
///
/// `upper` is the smallest key after `parent`'s whole subtree — what the
/// caller was itself bounded by, `None` at the root. The child's span must
/// END before its bound (freenet-prolly#52).
///
/// WHY THE BOUND IS INHERITED, not just the next sibling's key. A parent
/// records each child's FIRST key, so without an upper bound a writer can put
/// `z` in the leaf under `a` and `m` in the next one: one root, and a range
/// read says `z` is present while a point read — which descends to the child
/// under `m` — says it is absent. Equivocation without a fork. Checking only
/// against the next sibling refuses that tree and still accepts the same
/// overlap one level up: a leaf under the LAST child of a branch is bounded by
/// the branch's own successor, which only an inherited bound carries. That
/// adjacent-only check was tried, kept the whole suite green, and still
/// accepted the ancestor variant — the tests keep it as the control.
///
/// One comparison suffices: `Node::parse` refuses unsorted keys, so a last
/// key below the bound puts every key below it.
pub fn load_child<'a>(
    blocks: &'a impl Blocks,
    parent: &Node<'_>,
    i: usize,
    upper: Option<&[u8]>,
) -> Result<Node<'a>, ReadError> {
    let (cid, agg) = parent.child(i);
    let child = load(blocks, &cid)?;
    let ok = child.level() + 1 == parent.level()
        && !child.is_empty()
        && child.agg() == agg
        && child.key(0) == parent.key(i)
        && match child_upper(parent, i, upper) {
            Some(end) => child.key(child.len() - 1) < end,
            None => true,
        };
    if ok {
        Ok(child)
    } else {
        Err(ReadError::Mismatch(cid))
    }
}
