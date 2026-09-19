//! Chunk ONE level: entries in, closed nodes out. The from-scratch build and
//! incremental edits both go through this, so they cannot disagree about where
//! a node ends.

use crate::boundary;
use crate::node::{Agg, BuildError, Node, NodeBuilder, Value};
use crate::{block_id, kind, Cid};

/// Decides whether a node closes after an entry: `(level, key, s_before, s_after)`.
pub type SplitRule = fn(u8, &[u8], usize, usize) -> bool;

/// What an entry holds, owned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Body {
    Inline(Vec<u8>),
    Ref { cid: Cid, len: u32 },
    Child { cid: Cid, agg: Agg },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub key: Vec<u8>,
    pub body: Body,
}

impl Entry {
    /// Entry `i` of `node`.
    pub fn of(node: &Node<'_>, i: usize) -> Entry {
        let body = if node.is_leaf() {
            match node.value(i) {
                Value::Inline(b) => Body::Inline(b.to_vec()),
                Value::Ref { cid, len } => Body::Ref { cid, len },
            }
        } else {
            let (cid, agg) = node.child(i);
            Body::Child { cid, agg }
        };
        Entry {
            key: node.key(i),
            body,
        }
    }
}

/// A node that has been closed.
#[derive(Clone, Debug)]
pub struct Closed {
    pub min_key: Vec<u8>,
    pub cid: Cid,
    pub agg: Agg,
    pub bytes: Vec<u8>,
}

impl Closed {
    /// This node as an entry of the level above.
    pub fn as_child(&self) -> Entry {
        Entry {
            key: self.min_key.clone(),
            body: Body::Child {
                cid: self.cid,
                agg: self.agg,
            },
        }
    }
}

pub struct LevelChunker {
    level: u8,
    rule: SplitRule,
    open: NodeBuilder,
}

fn new_node(level: u8) -> NodeBuilder {
    if level == 0 {
        NodeBuilder::leaf()
    } else {
        NodeBuilder::branch(level)
    }
}

impl LevelChunker {
    pub fn new(level: u8, rule: SplitRule) -> Self {
        LevelChunker {
            level,
            rule,
            open: new_node(level),
        }
    }

    /// True when no entry is waiting in an open node: the chunker is in the
    /// state it has at the start of any node.
    pub fn is_clean(&self) -> bool {
        self.open.is_empty()
    }

    /// Add the next entry (keys strictly increasing; the caller has validated
    /// it). Nodes this closes are appended to `out`.
    pub fn push(
        &mut self,
        key: &[u8],
        body: &Body,
        out: &mut Vec<Closed>,
    ) -> Result<(), BuildError> {
        let cost = match body {
            Body::Inline(b) => NodeBuilder::leaf_cost(key, &Value::Inline(b)),
            Body::Ref { cid, len } => NodeBuilder::leaf_cost(
                key,
                &Value::Ref {
                    cid: *cid,
                    len: *len,
                },
            ),
            Body::Child { .. } => NodeBuilder::child_cost(key),
        };
        // The hard limit closes the node BEFORE the entry that would overflow it.
        if self.open.logical_len() + cost > boundary::MAX_LOGICAL {
            self.close(out)?;
        }
        let before = self.open.logical_len();
        match body {
            Body::Inline(b) => self.open.push(key, Value::Inline(b))?,
            Body::Ref { cid, len } => self.open.push(
                key,
                Value::Ref {
                    cid: *cid,
                    len: *len,
                },
            )?,
            Body::Child { cid, agg } => self.open.push_child(key, *cid, *agg)?,
        }
        if (self.rule)(self.level, key, before, self.open.logical_len()) {
            self.close(out)?;
        }
        Ok(())
    }

    /// Close the open node, if it holds anything (end of the level).
    pub fn finish(&mut self, out: &mut Vec<Closed>) -> Result<(), BuildError> {
        if !self.open.is_empty() {
            self.close(out)?;
        }
        Ok(())
    }

    fn close(&mut self, out: &mut Vec<Closed>) -> Result<(), BuildError> {
        let done = std::mem::replace(&mut self.open, new_node(self.level));
        let min_key = done.min_key().unwrap_or_default().to_vec();
        let agg = done.agg();
        let bytes = done.finish()?;
        out.push(Closed {
            min_key,
            cid: block_id(kind::TREE_NODE, &bytes),
            agg,
            bytes,
        });
        Ok(())
    }
}

/// The empty tree: one empty leaf.
pub fn empty_leaf() -> Closed {
    let bytes = NodeBuilder::leaf().finish().expect("an empty leaf encodes");
    Closed {
        min_key: Vec::new(),
        cid: block_id(kind::TREE_NODE, &bytes),
        agg: Agg::default(),
        bytes,
    }
}

// Every entry fits an empty node with room to spare, so the forced close in
// `push` always makes progress.
const _: () = assert!(
    crate::node::HEADER + 6 + 7 + crate::node::MAX_KEY + crate::node::MAX_INLINE
        <= boundary::MAX_LOGICAL
);
