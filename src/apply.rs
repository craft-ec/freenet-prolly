//! Change a tree: `apply(root, edits)` gives the tree a from-scratch build of
//! the edited contents would give, touching only the nodes the edits reach.
//!
//! Per level, left to right: restart the chunker at the first entry of the node
//! that holds the next edit (a chunker at the start of any node is in the same
//! state whatever lies to its left), stream old entries merged with the edits,
//! and stop as soon as the chunker closes a node exactly where an old node
//! ended with no edit left for the node that follows — from there on the old
//! nodes are what a rebuild would produce, and are kept by id. The run of nodes
//! that was replaced becomes the edit batch for the level above.
//!
//! Nothing is handed to the sink, and nothing is read that the edits do not
//! reach, until the whole change has succeeded. A refused batch, or one that
//! stops for a missing block, leaves no trace.

use crate::boundary::{self, MAX_LOGICAL};
use crate::chunk::{empty_leaf, Body, Closed, LevelChunker, SplitRule};
use crate::cursor::LevelCursor;
use crate::node::{Agg, BuildError, HEADER, MAX_INLINE, MAX_KEY};
use crate::store::{load, load_child, Blocks, ReadError};
use crate::{block_id, kind, Cid};
use std::collections::{BTreeMap, HashSet};

pub use crate::node::MAX_VALUE;
/// At most this many missing blocks are named at once.
pub const MAX_NEED: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Edit {
    /// Store these bytes under the key. The library decides whether they live
    /// in the leaf or in a block of their own.
    Put(Vec<u8>),
    Delete,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApplyError {
    Read(ReadError),
    /// Keys in a batch must be strictly increasing (so: no key twice).
    NotSorted,
    KeyTooLong,
    ValueTooLong,
    Node(BuildError),
}

impl From<ReadError> for ApplyError {
    fn from(e: ReadError) -> Self {
        ApplyError::Read(e)
    }
}
impl From<BuildError> for ApplyError {
    fn from(e: BuildError) -> Self {
        ApplyError::Node(e)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Applied {
    pub root: Cid,
    /// Tree nodes of the old tree that the new tree no longer uses. (Value
    /// blocks are not listed: another key may hold the same value.)
    pub replaced: Vec<Cid>,
}

/// How to apply. The format is [`Options::default`]; anything else exists so
/// tests can show what each part is for.
#[derive(Clone, Copy)]
pub struct Options {
    pub rule: SplitRule,
    /// Re-chunk the node before an edited first entry when it may have been
    /// closed by the hard limit. Off = the bug this guards against.
    pub recheck_neighbour: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            rule: boundary::splits_after,
            recheck_neighbour: true,
        }
    }
}

type LevelEdits = Vec<(Vec<u8>, Option<Body>)>;

struct LevelResult {
    new: Vec<Closed>,
    /// Old nodes that were streamed: id and smallest key.
    old: Vec<(Cid, Vec<u8>)>,
    /// Every old node of the level was streamed: `new` IS the level.
    whole: bool,
    /// Per edit: did it change anything?
    effective: Vec<bool>,
}

/// From a leaf's recorded aggregate alone: can it have been closed by the hard
/// limit? A forced close needs `logical_len + cost(next entry) > MAX_LOGICAL`,
/// the largest entry costs 13 + MAX_KEY + MAX_INLINE, and a leaf's logical size
/// is at most HEADER + 13·count + bytes (what is stored for a value is never
/// longer than the value).
fn leaf_was_not_forced(agg: Agg) -> bool {
    let bound = (HEADER as u64)
        .saturating_add(agg.count.saturating_mul(13))
        .saturating_add(agg.bytes);
    bound <= (MAX_LOGICAL - (13 + MAX_KEY + MAX_INLINE)) as u64
}

fn rewrite_level<B: Blocks>(
    blocks: &B,
    root: &Cid,
    floor: u8,
    edits: &LevelEdits,
    opts: Options,
) -> Result<LevelResult, ApplyError> {
    let rule = opts.rule;
    let mut res = LevelResult {
        new: Vec::new(),
        old: Vec::new(),
        whole: true,
        effective: vec![false; edits.len()],
    };
    let mut i = 0;
    let mut reached_end = false;
    // Smallest key of the node after the last one streamed.
    let mut resume_at: Option<Vec<u8>> = None;
    while i < edits.len() {
        let Some(mut cur) = LevelCursor::seek(blocks, root, floor, &edits[i].0)? else {
            // A level above the old root: nothing old to merge with.
            let mut chunker = LevelChunker::new(floor, rule);
            for (n, (key, body)) in edits.iter().enumerate() {
                if let Some(body) = body {
                    chunker.push(key, body, &mut res.new)?;
                    res.effective[n] = true;
                }
            }
            chunker.finish(&mut res.new)?;
            return Ok(res);
        };
        // A node closed by the hard limit ended because of the entry AFTER it.
        // If that entry is what this edit changes, the node before must be
        // re-chunked too — unless it is known not to have been force-closed.
        let last_streamed = res.old.last().map(|(id, _)| *id);
        if opts.recheck_neighbour && !cur.node().is_empty() && cur.node().key(0) == edits[i].0 {
            if let Some((prev, agg)) = cur.prev_info()? {
                let safe = Some(prev) == last_streamed || (floor == 0 && leaf_was_not_forced(agg));
                if !safe {
                    cur.retreat()?;
                }
            }
        }
        // Does this run start where the last one stopped (or at the start of
        // the level)? Told from keys already in hand, not by loading anything.
        let first_key = (!cur.node().is_empty()).then(|| cur.node().key(0));
        res.whole &= match &resume_at {
            None => cur.is_first(),
            Some(k) => Some(k) == first_key.as_ref(),
        };

        let mut chunker = LevelChunker::new(floor, rule);
        loop {
            let node = *cur.node();
            let upper = cur.next_min_key();
            res.old.push((
                cur.id(),
                if node.is_empty() {
                    Vec::new()
                } else {
                    node.key(0)
                },
            ));
            let mut j = 0;
            loop {
                let edit = edits
                    .get(i)
                    .filter(|(k, _)| upper.as_ref().is_none_or(|u| k < u));
                let have = (j < node.len()).then(|| crate::chunk::Entry::of(&node, j));
                match (have, edit) {
                    (None, None) => break,
                    (Some(e), Some((k, _))) if e.key < *k => {
                        chunker.push(&e.key, &e.body, &mut res.new)?;
                        j += 1;
                    }
                    (Some(e), None) => {
                        chunker.push(&e.key, &e.body, &mut res.new)?;
                        j += 1;
                    }
                    (have, Some((k, body))) => {
                        let same_key = have.as_ref().is_some_and(|e| e.key == *k);
                        let old_body = have.filter(|_| same_key).map(|e| e.body);
                        res.effective[i] = old_body.as_ref() != body.as_ref();
                        if let Some(body) = body {
                            chunker.push(k, body, &mut res.new)?;
                        }
                        if same_key {
                            j += 1;
                        }
                        i += 1;
                    }
                }
            }
            if upper.is_none() {
                chunker.finish(&mut res.new)?;
                reached_end = true;
                break;
            }
            // Clean here means: the chunker closed a node exactly where this old
            // node ended. What follows is what a rebuild would produce, unless
            // an edit says otherwise — and then the outer loop starts again
            // there. The next node is not loaded just to find that out.
            if chunker.is_clean() {
                resume_at = upper;
                break;
            }
            cur.advance()?;
        }
    }
    res.whole &= reached_end;
    Ok(res)
}

/// Ids of every node of the tree at `root` above `floor`.
fn nodes_above<B: Blocks>(blocks: &B, root: &Cid, floor: u8) -> Result<Vec<Cid>, ReadError> {
    let mut out = Vec::new();
    let mut todo = vec![(*root, load(blocks, root)?)];
    while let Some((id, node)) = todo.pop() {
        if node.level() <= floor {
            continue;
        }
        out.push(id);
        if node.level() > floor + 1 {
            for i in 0..node.len() {
                todo.push((node.child(i).0, load_child(blocks, &node, i)?));
            }
        }
    }
    Ok(out)
}

/// Apply a key-sorted batch of edits to the tree at `root`.
///
/// New blocks go to `sink` only if the whole batch succeeds. An edit that
/// changes nothing (the same value again, a delete of an absent key) costs
/// nothing: same root, nothing emitted.
pub fn apply<B: Blocks>(
    blocks: &B,
    root: &Cid,
    edits: &[(Vec<u8>, Edit)],
    sink: impl FnMut(Cid, &[u8]),
) -> Result<Applied, ApplyError> {
    apply_with(Options::default(), blocks, root, edits, sink)
}

/// [`apply`] with non-default [`Options`]; for comparison in tests.
pub fn apply_with<B: Blocks>(
    opts: Options,
    blocks: &B,
    root: &Cid,
    edits: &[(Vec<u8>, Edit)],
    mut sink: impl FnMut(Cid, &[u8]),
) -> Result<Applied, ApplyError> {
    // 1. Refuse a bad batch before anything is read.
    for (n, (key, edit)) in edits.iter().enumerate() {
        if n > 0 && edits[n - 1].0 >= *key {
            return Err(ApplyError::NotSorted);
        }
        if key.len() > MAX_KEY {
            return Err(ApplyError::KeyTooLong);
        }
        if matches!(edit, Edit::Put(v) if v.len() > MAX_VALUE) {
            return Err(ApplyError::ValueTooLong);
        }
    }
    // 2. The library owns the inline-or-reference decision.
    let mut values: Vec<Option<(Cid, &[u8])>> = Vec::with_capacity(edits.len());
    let mut level: LevelEdits = Vec::with_capacity(edits.len());
    for (key, edit) in edits {
        let (body, block) = match edit {
            Edit::Delete => (None, None),
            Edit::Put(v) if v.len() <= MAX_INLINE => (Some(Body::Inline(v.clone())), None),
            Edit::Put(v) => {
                let cid = block_id(kind::RAW, v);
                let len = v.len() as u32;
                (Some(Body::Ref { cid, len }), Some((cid, v.as_slice())))
            }
        };
        values.push(block);
        level.push((key.clone(), body));
    }
    // 3. Name every missing block the edits already point at, in one go.
    let mut need: Vec<Cid> = Vec::new();
    for (key, _) in edits {
        match LevelCursor::seek(blocks, root, 0, key) {
            Err(ReadError::Need(ids)) => {
                for id in ids {
                    if !need.contains(&id) && need.len() < MAX_NEED {
                        need.push(id);
                    }
                }
            }
            Err(e) => return Err(e.into()),
            Ok(_) => {}
        }
    }
    if !need.is_empty() {
        return Err(ReadError::Need(need).into());
    }

    // 4. Rewrite level by level.
    let mut new_nodes: Vec<Closed> = Vec::new();
    let mut old_ids: Vec<Cid> = Vec::new();
    let mut value_blocks: Vec<(Cid, &[u8])> = Vec::new();
    let mut new_root = *root;
    let mut floor: u8 = 0;
    loop {
        let r = rewrite_level(blocks, root, floor, &level, opts)?;
        if floor == 0 {
            value_blocks = values
                .iter()
                .zip(&r.effective)
                .filter_map(|(v, used)| v.filter(|_| *used))
                .collect();
        }
        old_ids.extend(r.old.iter().map(|(id, _)| *id));
        let mut done = false;
        if r.whole && r.new.len() <= 1 {
            // The lowest level with exactly one node is the root.
            let top = r.new.first().cloned().unwrap_or_else(empty_leaf);
            new_root = top.cid;
            old_ids.extend(nodes_above(blocks, root, floor)?);
            if r.new.is_empty() {
                new_nodes.push(top);
            }
            done = true;
        }
        let was: HashSet<Cid> = r.old.iter().map(|(id, _)| *id).collect();
        let now: HashSet<Cid> = r.new.iter().map(|n| n.cid).collect();
        let mut up: BTreeMap<Vec<u8>, Option<Body>> = BTreeMap::new();
        for (id, min_key) in &r.old {
            if !now.contains(id) {
                up.insert(min_key.clone(), None);
            }
        }
        for n in &r.new {
            if !was.contains(&n.cid) {
                let e = n.as_child();
                up.insert(e.key, Some(e.body));
            }
        }
        new_nodes.extend(r.new);
        if done || up.is_empty() {
            break;
        }
        level = up.into_iter().collect();
        floor = floor.checked_add(1).ok_or(BuildError::Overflow)?;
    }

    // 5. Success: hand over what is new, children before parents.
    let old: HashSet<Cid> = old_ids.iter().copied().collect();
    let mut sent: HashSet<Cid> = HashSet::new();
    for (cid, bytes) in value_blocks {
        if sent.insert(cid) {
            sink(cid, bytes);
        }
    }
    let mut kept: HashSet<Cid> = HashSet::new();
    for n in &new_nodes {
        kept.insert(n.cid);
        if !old.contains(&n.cid) && sent.insert(n.cid) {
            sink(n.cid, &n.bytes);
        }
    }
    let mut replaced: Vec<Cid> = Vec::new();
    for id in old_ids {
        if !kept.contains(&id) && !replaced.contains(&id) {
            replaced.push(id);
        }
    }
    Ok(Applied {
        root: new_root,
        replaced,
    })
}
