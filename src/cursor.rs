//! A position in one LEVEL of a tree: the path from the root down to a node at
//! the floor level, with moves to the neighbouring nodes of that level.
//!
//! A move either completes or fails leaving the cursor where it was, so after a
//! [`ReadError::Need`] the caller supplies the block and simply repeats it.

use crate::node::{Agg, Node};
use crate::store::{load, load_child, Blocks, ReadError};
use crate::Cid;

struct Step<'a> {
    id: Cid,
    node: Node<'a>,
    /// Which child the path takes below this node (unused at the floor).
    taken: usize,
}

pub struct LevelCursor<'a, B: Blocks> {
    blocks: &'a B,
    floor: u8,
    path: Vec<Step<'a>>,
}

/// Which child of a branch can hold `key`: the last whose key is ≤ `key`.
pub(crate) fn child_for(node: &Node<'_>, key: &[u8]) -> usize {
    match node.search(key) {
        Ok(i) => i,
        Err(0) => 0,
        Err(i) => i - 1,
    }
}

impl<'a, B: Blocks> LevelCursor<'a, B> {
    /// A cursor on the floor-level node that can hold `key`. `None` if the tree
    /// is not that tall.
    pub fn seek(
        blocks: &'a B,
        root: &Cid,
        floor: u8,
        key: &[u8],
    ) -> Result<Option<Self>, ReadError> {
        let node = load(blocks, root)?;
        if node.level() < floor {
            return Ok(None);
        }
        let mut c = LevelCursor {
            blocks,
            floor,
            path: vec![Step {
                id: *root,
                node,
                taken: 0,
            }],
        };
        c.descend(|n| child_for(n, key))?;
        Ok(Some(c))
    }

    /// Extend the path down to the floor, choosing a child at each branch.
    fn descend(&mut self, pick: impl Fn(&Node<'a>) -> usize) -> Result<(), ReadError> {
        let keep = self.path.len();
        let r = (|| {
            while self.path.last().expect("non-empty").node.level() > self.floor {
                let top = self.path.last_mut().expect("non-empty");
                top.taken = pick(&top.node);
                let (id, _) = top.node.child(top.taken);
                let node = load_child(self.blocks, &top.node, top.taken)?;
                self.path.push(Step { id, node, taken: 0 });
            }
            Ok(())
        })();
        if r.is_err() {
            self.path.truncate(keep);
        }
        r
    }

    pub fn node(&self) -> &Node<'a> {
        &self.path.last().expect("non-empty").node
    }
    pub fn id(&self) -> Cid {
        self.path.last().expect("non-empty").id
    }

    /// The deepest ancestor whose path can move one child to the right (`+1`)
    /// or left (`-1`).
    fn turn(&self, right: bool) -> Option<usize> {
        let above = &self.path[..self.path.len() - 1];
        above.iter().rposition(|s| {
            if right {
                s.taken + 1 < s.node.len()
            } else {
                s.taken > 0
            }
        })
    }

    /// Smallest key of the next node on this level, if there is one. Read from
    /// an ancestor: a branch key is its subtree's smallest key.
    pub fn next_min_key(&self) -> Option<Vec<u8>> {
        self.turn(true).map(|d| {
            let s = &self.path[d];
            s.node.key(s.taken + 1)
        })
    }

    pub fn is_first(&self) -> bool {
        self.turn(false).is_none()
    }

    fn step(&mut self, right: bool) -> Result<bool, ReadError> {
        let Some(d) = self.turn(right) else {
            return Ok(false);
        };
        let saved: Vec<usize> = self.path.iter().map(|s| s.taken).collect();
        let tail: Vec<Step<'a>> = self.path.drain(d + 1..).collect();
        let s = &mut self.path[d];
        s.taken = if right { s.taken + 1 } else { s.taken - 1 };
        // `descend` sets `taken` on the node it starts from, so start one below.
        let r = (|| {
            let top = &self.path[d];
            let (id, _) = top.node.child(top.taken);
            let node = load_child(self.blocks, &top.node, top.taken)?;
            self.path.push(Step { id, node, taken: 0 });
            self.descend(|n| if right { 0 } else { n.len() - 1 })
        })();
        if let Err(e) = r {
            self.path.truncate(d + 1);
            self.path.extend(tail);
            for (s, t) in self.path.iter_mut().zip(saved) {
                s.taken = t;
            }
            return Err(e);
        }
        Ok(true)
    }

    /// Move to the next node on this level. `false` at the end of the level.
    pub fn advance(&mut self) -> Result<bool, ReadError> {
        self.step(true)
    }

    /// Move to the previous node on this level. `false` at the start.
    pub fn retreat(&mut self) -> Result<bool, ReadError> {
        self.step(false)
    }

    /// Id and recorded aggregate of the previous node on this level, without
    /// loading it (only the branches above it).
    pub fn prev_info(&self) -> Result<Option<(Cid, Agg)>, ReadError> {
        let Some(d) = self.turn(false) else {
            return Ok(None);
        };
        let s = &self.path[d];
        let mut i = s.taken - 1;
        let mut held;
        let mut node = &s.node;
        while node.level() > self.floor + 1 {
            held = load_child(self.blocks, node, i)?;
            node = &held;
            i = node.len() - 1;
        }
        Ok(Some(node.child(i)))
    }

    /// Ids of every node on the path above the floor node, root first.
    pub fn ancestors(&self) -> impl Iterator<Item = Cid> + '_ {
        self.path[..self.path.len() - 1].iter().map(|s| s.id)
    }
}
