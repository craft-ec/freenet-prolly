//! Build a whole tree from entries in key order, one pass, bottom-up.
//!
//! Every level is chunked by the same rule ([`crate::boundary`]); a node that
//! closes becomes one child entry of the level above. The root is the single
//! node of the first level that produces exactly one node. An empty tree is one
//! empty leaf.

use crate::boundary;
use crate::node::{Agg, BuildError, NodeBuilder, Value};
use crate::{block_id, kind, Cid};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeError {
    Node(BuildError),
    /// More levels than a `u8` can number.
    TooDeep,
    /// An earlier call failed after nodes had been closed; the builder's output
    /// can no longer be the canonical tree, so it refuses to go on.
    Poisoned,
}

impl From<BuildError> for TreeError {
    fn from(e: BuildError) -> Self {
        TreeError::Node(e)
    }
}

/// Decides whether a node closes after an entry: `(level, key, s_before, s_after)`.
pub type SplitRule = fn(u8, &[u8], usize, usize) -> bool;

struct ChildRef {
    min_key: Vec<u8>,
    cid: Cid,
    agg: Agg,
}

struct Level {
    open: NodeBuilder,
    /// The first closed node, held back until a second one proves this level
    /// is not the root.
    first: Option<ChildRef>,
    closed: usize,
}

/// Streaming tree builder. Closed nodes are handed to `sink` as `(cid, bytes)`.
pub struct TreeBuilder<F: FnMut(Cid, &[u8])> {
    levels: Vec<Level>,
    /// Last key pushed: order must hold across node boundaries too.
    last: Option<Vec<u8>>,
    poisoned: bool,
    rule: SplitRule,
    sink: F,
}

impl<F: FnMut(Cid, &[u8])> TreeBuilder<F> {
    pub fn new(sink: F) -> Self {
        Self::with_rule(boundary::splits_after, sink)
    }

    /// A builder with a different split rule. The format uses
    /// [`boundary::splits_after`]; anything else exists for comparison in tests.
    pub fn with_rule(rule: SplitRule, sink: F) -> Self {
        TreeBuilder {
            levels: Vec::new(),
            last: None,
            poisoned: false,
            rule,
            sink,
        }
    }

    /// Add the next entry. Keys must be strictly increasing.
    ///
    /// A refused entry (bad order, key too long, wrong value encoding) leaves the
    /// builder exactly as it was — everything that can refuse an entry is checked
    /// before anything changes, so what a caller tried first never shows in the
    /// root. A failure past that point poisons the builder.
    pub fn push(&mut self, key: &[u8], value: Value<'_>) -> Result<(), TreeError> {
        if self.poisoned {
            return Err(TreeError::Poisoned);
        }
        if self.last.as_deref().is_some_and(|p| p >= key) {
            return Err(BuildError::NotSorted.into());
        }
        NodeBuilder::check_leaf(key, &value)?;
        let cost = NodeBuilder::leaf_cost(key, &value);
        if let Err(e) = self.add(0, key, cost, |b| b.push(key, value)) {
            self.poisoned = true;
            return Err(e);
        }
        self.last = Some(key.to_vec());
        Ok(())
    }

    fn level(&mut self, l: usize) -> Result<&mut Level, TreeError> {
        if l == self.levels.len() {
            let level = u8::try_from(l).map_err(|_| TreeError::TooDeep)?;
            self.levels.push(Level {
                open: new_node(level),
                first: None,
                closed: 0,
            });
        }
        Ok(&mut self.levels[l])
    }

    fn add(
        &mut self,
        l: usize,
        key: &[u8],
        cost: usize,
        put: impl FnOnce(&mut NodeBuilder) -> Result<(), BuildError>,
    ) -> Result<(), TreeError> {
        let limit = boundary::MAX_LOGICAL;
        if self.level(l)?.open.logical_len() + cost > limit {
            self.close(l)?;
        }
        let open = &mut self.levels[l].open;
        let before = open.logical_len();
        put(open)?;
        let after = open.logical_len();
        if (self.rule)(l as u8, key, before, after) {
            self.close(l)?;
        }
        Ok(())
    }

    /// Close level `l`'s open node and pass it up.
    fn close(&mut self, l: usize) -> Result<(), TreeError> {
        let lv = &mut self.levels[l];
        let done = std::mem::replace(&mut lv.open, new_node(l as u8));
        let child = ChildRef {
            min_key: done.min_key().unwrap_or_default().to_vec(),
            agg: done.agg(),
            cid: [0; 32],
        };
        let bytes = done.finish()?;
        let child = ChildRef {
            cid: block_id(kind::TREE_NODE, &bytes),
            ..child
        };
        (self.sink)(child.cid, &bytes);
        lv.closed += 1;
        if lv.closed == 1 {
            lv.first = Some(child);
            return Ok(());
        }
        if let Some(first) = self.levels[l].first.take() {
            self.add_child(l + 1, first)?;
        }
        self.add_child(l + 1, child)
    }

    fn add_child(&mut self, l: usize, c: ChildRef) -> Result<(), TreeError> {
        let cost = NodeBuilder::child_cost(&c.min_key);
        self.add(l, &c.min_key, cost, |b| {
            b.push_child(&c.min_key, c.cid, c.agg)
        })
    }

    /// Close every level and return the root's cid.
    pub fn finish(mut self) -> Result<Cid, TreeError> {
        if self.poisoned {
            return Err(TreeError::Poisoned);
        }
        if self.levels.is_empty() {
            self.level(0)?;
        }
        let mut l = 0;
        loop {
            let lv = &self.levels[l];
            if !lv.open.is_empty() || lv.closed == 0 {
                self.close(l)?;
            }
            let lv = &mut self.levels[l];
            if lv.closed == 1 {
                return Ok(lv.first.take().expect("held back").cid);
            }
            l += 1;
        }
    }
}

fn new_node(level: u8) -> NodeBuilder {
    if level == 0 {
        NodeBuilder::leaf()
    } else {
        NodeBuilder::branch(level)
    }
}

/// Build a tree from entries in key order; returns the root cid.
pub fn build<'a>(
    entries: impl IntoIterator<Item = (&'a [u8], Value<'a>)>,
    sink: impl FnMut(Cid, &[u8]),
) -> Result<Cid, TreeError> {
    let mut t = TreeBuilder::new(sink);
    for (k, v) in entries {
        t.push(k, v)?;
    }
    t.finish()
}

// Every entry fits an empty node with room to spare, so the forced close in
// `add` always makes progress.
const _: () = assert!(
    crate::node::HEADER + 6 + 7 + crate::node::MAX_KEY + crate::node::MAX_INLINE
        <= boundary::MAX_LOGICAL
);
