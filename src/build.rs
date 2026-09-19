//! Build a whole tree from entries in key order, one pass, bottom-up.
//!
//! Every level is chunked by the same rule ([`crate::boundary`]); a node that
//! closes becomes one child entry of the level above. The root is the single
//! node of the lowest level that produces exactly one node. An empty tree is one
//! empty leaf.

use crate::boundary;
use crate::chunk::{empty_leaf, Body, Closed, LevelChunker};
use crate::node::{BuildError, NodeBuilder, Value};
use crate::Cid;

pub use crate::chunk::SplitRule;

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

struct Level {
    chunker: LevelChunker,
    /// The first closed node, held back until a second one proves this level
    /// is not the root.
    first: Option<Closed>,
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
        let body = match value {
            Value::Inline(b) => Body::Inline(b.to_vec()),
            Value::Ref { cid, len } => Body::Ref { cid, len },
        };
        // Defensive: nothing below can fail for a validated entry (TooDeep and
        // aggregate overflow are out of reach), but if it ever did, nodes may
        // already have been emitted.
        if let Err(e) = self.add(0, key, &body) {
            self.poisoned = true;
            return Err(e);
        }
        self.last = Some(key.to_vec());
        Ok(())
    }

    fn add(&mut self, l: usize, key: &[u8], body: &Body) -> Result<(), TreeError> {
        if l == self.levels.len() {
            let level = u8::try_from(l).map_err(|_| TreeError::TooDeep)?;
            self.levels.push(Level {
                chunker: LevelChunker::new(level, self.rule),
                first: None,
                closed: 0,
            });
        }
        let mut done = Vec::new();
        self.levels[l].chunker.push(key, body, &mut done)?;
        self.closed(l, done)
    }

    /// Pass the nodes level `l` just closed to the sink and to the level above.
    fn closed(&mut self, l: usize, done: Vec<Closed>) -> Result<(), TreeError> {
        for node in done {
            (self.sink)(node.cid, &node.bytes);
            let lv = &mut self.levels[l];
            lv.closed += 1;
            if lv.closed == 1 {
                lv.first = Some(node);
                continue;
            }
            if let Some(first) = lv.first.take() {
                let e = first.as_child();
                self.add(l + 1, &e.key, &e.body)?;
            }
            let e = node.as_child();
            self.add(l + 1, &e.key, &e.body)?;
        }
        Ok(())
    }

    /// Close every level and return the root's cid.
    pub fn finish(mut self) -> Result<Cid, TreeError> {
        if self.poisoned {
            return Err(TreeError::Poisoned);
        }
        if self.levels.is_empty() {
            let leaf = empty_leaf();
            (self.sink)(leaf.cid, &leaf.bytes);
            return Ok(leaf.cid);
        }
        let mut l = 0;
        loop {
            let mut done = Vec::new();
            self.levels[l].chunker.finish(&mut done)?;
            self.closed(l, done)?;
            let lv = &mut self.levels[l];
            if lv.closed == 1 {
                return Ok(lv.first.take().expect("held back").cid);
            }
            l += 1;
        }
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
