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

/// Blocks held in memory.
#[derive(Default, Clone)]
pub struct MemBlocks(pub HashMap<Cid, Vec<u8>>);

impl MemBlocks {
    pub fn insert(&mut self, cid: Cid, bytes: &[u8]) {
        self.0.insert(cid, bytes.to_vec());
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

/// Load child `i` of `parent` and check it against what the parent records, so
/// that everything reached from a trusted root is itself trusted.
pub fn load_child<'a>(
    blocks: &'a impl Blocks,
    parent: &Node<'_>,
    i: usize,
) -> Result<Node<'a>, ReadError> {
    let (cid, agg) = parent.child(i);
    let child = load(blocks, &cid)?;
    let ok = child.level() + 1 == parent.level()
        && !child.is_empty()
        && child.agg() == agg
        && child.key(0) == parent.key(i);
    if ok {
        Ok(child)
    } else {
        Err(ReadError::Mismatch(cid))
    }
}
