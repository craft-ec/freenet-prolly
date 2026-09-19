//! Ordered scan over a key range, forward or reverse.
//!
//! Shaped by the engine that calls it (ARCHITECTURE §12): it runs in rounds of
//! a few network operations and cannot wait. So a scan serves what it can from
//! the blocks in hand, says where to resume **by key**, and names the blocks it
//! is missing so the caller can fetch a whole round's worth at once.
//!
//! Resuming by key, never by a position in a node, is what makes a page survive
//! the tree changing underneath it: the caller may hand the next page a newer
//! root and get that tree's entries from the same key on.

use crate::cursor::Cursor;
use crate::node::{Agg, Node, Value};
use crate::store::{load, Blocks, ReadError};
use crate::Cid;
use std::ops::Bound;

/// Most blocks one page will name. The caller fetches a round at a time, so
/// naming more than it can use only delays the entries it asked for.
pub use crate::apply::MAX_NEED;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RangeError {
    Read(ReadError),
    /// `max_entries` was 0. A page that can never hold an entry is a caller
    /// mistake, not an empty result: returning `Ok` would loop forever.
    NoLimit,
}

impl From<ReadError> for RangeError {
    fn from(e: ReadError) -> Self {
        RangeError::Read(e)
    }
}

/// Knobs that exist so the tests can run a control. The defaults are the
/// format's behaviour; nothing else should change them.
#[derive(Clone, Copy, Debug)]
pub struct Options {
    /// Stop naming blocks once the named aggregates cover the caller's limit.
    /// With this off, a page for twenty entries names blocks for sixty-four.
    pub agg_bound: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { agg_bound: true }
    }
}

/// What to scan. `lo`/`hi` are the range; `after` is where to resume.
#[derive(Clone, Debug)]
pub struct Range {
    pub lo: Bound<Vec<u8>>,
    pub hi: Bound<Vec<u8>>,
    pub reverse: bool,
    /// Resume strictly after this key in scan order: forward, keys greater than
    /// it; reverse, keys less than it. Intersected with `lo`/`hi`, and a key
    /// outside them is not an error — it may have been deleted under a newer
    /// root.
    pub after: Option<Vec<u8>>,
    pub max_entries: usize,
    pub max_bytes: usize,
}

impl Default for Range {
    fn default() -> Self {
        Range {
            lo: Bound::Unbounded,
            hi: Bound::Unbounded,
            reverse: false,
            after: None,
            max_entries: 1024,
            max_bytes: 256 * 1024,
        }
    }
}

impl Range {
    /// Every key starting with `p`, i.e. `[p, successor(p))`.
    ///
    /// The successor increments the last byte below `0xff` and drops the rest;
    /// a prefix that is empty, all `0xff`, or longer than a key can be has no
    /// successor, so the range runs to the end.
    pub fn prefix(p: &[u8]) -> Range {
        Range {
            lo: Bound::Included(p.to_vec()),
            hi: match successor(p) {
                Some(s) => Bound::Excluded(s),
                None => Bound::Unbounded,
            },
            ..Range::default()
        }
    }
}

/// Smallest key that is greater than every key starting with `p`.
fn successor(p: &[u8]) -> Option<Vec<u8>> {
    // A key longer than MAX_KEY cannot exist, so nothing starts with such a
    // prefix — but the range must then be empty, not unbounded, which the
    // caller gets from `lo` being above every key.
    let cut = p.iter().rposition(|b| *b != 0xff)?;
    let mut s = p[..=cut].to_vec();
    s[cut] += 1;
    Some(s)
}

/// One page of a scan. `entries` borrow from `blocks`, so consume a page before
/// inserting newly fetched blocks into the source.
#[derive(Debug)]
pub struct Page<'a> {
    pub entries: Vec<(Vec<u8>, Value<'a>)>,
    /// Resume after this key. It does NOT promise more entries exist: when the
    /// limit lands exactly on the range's last entry, the scan does not read on
    /// to find out, and one extra empty page is the honest cost.
    pub next: Option<Vec<u8>>,
    /// Blocks to fetch, in scan order: the leaf the scan stopped at, plus
    /// further blocks of the range that the held branches can name.
    pub need: Vec<Cid>,
}

impl Page<'_> {
    /// The scan is over: nothing more to serve and nothing to fetch.
    pub fn finished(&self) -> bool {
        self.next.is_none() && self.need.is_empty()
    }
}

/// Does `key` satisfy the low end of the range?
fn above_lo(key: &[u8], lo: &Bound<Vec<u8>>) -> bool {
    match lo {
        Bound::Unbounded => true,
        Bound::Included(k) => key >= k.as_slice(),
        Bound::Excluded(k) => key > k.as_slice(),
    }
}

/// Does `key` satisfy the high end of the range?
fn below_hi(key: &[u8], hi: &Bound<Vec<u8>>) -> bool {
    match hi {
        Bound::Unbounded => true,
        Bound::Included(k) => key <= k.as_slice(),
        Bound::Excluded(k) => key < k.as_slice(),
    }
}

fn in_range(key: &[u8], r: &Range) -> bool {
    above_lo(key, &r.lo) && below_hi(key, &r.hi)
}

/// Where a scan starts, with `after` folded into the bound it tightens.
fn start_bound(r: &Range) -> Bound<Vec<u8>> {
    let bound = if r.reverse { &r.hi } else { &r.lo };
    let Some(a) = &r.after else {
        return bound.clone();
    };
    let inside = if r.reverse {
        below_hi(a, bound)
    } else {
        above_lo(a, bound)
    };
    // An `after` outside the range leaves the bound alone rather than failing:
    // the caller may be resuming into a newer tree where that key is gone.
    if inside {
        Bound::Excluded(a.clone())
    } else {
        bound.clone()
    }
}

/// How many bytes an entry costs the page.
fn entry_bytes(key: &[u8], v: &Value<'_>) -> usize {
    key.len()
        + match v {
            Value::Inline(b) => b.len(),
            Value::Ref { .. } => 32,
        }
}

/// Place a cursor at the first entry of the scan.
fn open<'a, B: Blocks>(blocks: &'a B, root: &Cid, r: &Range) -> Result<Cursor<'a, B>, ReadError> {
    let start = start_bound(r);
    if r.reverse {
        return match &start {
            Bound::Unbounded => Cursor::seek_last(blocks, root),
            Bound::Excluded(k) => Cursor::seek_before(blocks, root, k),
            Bound::Included(k) => {
                let mut c = Cursor::seek(blocks, root, k)?;
                // `seek` lands on the first key ≥ k; for a reverse scan that key
                // is only in range when it equals k.
                if c.peek().map(|(got, _)| got == *k) != Some(true) {
                    c.prev()?;
                }
                Ok(c)
            }
        };
    }
    match &start {
        Bound::Unbounded => Cursor::seek(blocks, root, &[]),
        Bound::Included(k) => Cursor::seek(blocks, root, k),
        Bound::Excluded(k) => {
            let mut c = Cursor::seek(blocks, root, k)?;
            if c.peek().map(|(got, _)| got == *k) == Some(true) {
                c.next()?;
            }
            Ok(c)
        }
    }
}

/// Serve as much of `r` from `blocks` as the limits and the held blocks allow.
///
/// Never skips a hole: the page stops at the first missing leaf, and `need`
/// names it. Values are borrowed from `blocks`.
pub fn range<'a, B: Blocks>(blocks: &'a B, root: &Cid, r: &Range) -> Result<Page<'a>, RangeError> {
    range_with(Options::default(), blocks, root, r)
}

/// [`range`], with the test controls.
pub fn range_with<'a, B: Blocks>(
    opts: Options,
    blocks: &'a B,
    root: &Cid,
    r: &Range,
) -> Result<Page<'a>, RangeError> {
    if r.max_entries == 0 {
        return Err(RangeError::NoLimit);
    }
    let mut page = Page {
        entries: Vec::new(),
        next: None,
        need: Vec::new(),
    };
    // The root itself may be missing; then there is nothing to serve and one
    // block to ask for.
    if blocks.get(root).is_none() {
        page.need.push(*root);
        return Ok(page);
    }

    let mut cur = match open(blocks, root, r) {
        Ok(c) => c,
        Err(ReadError::Need(ids)) => {
            // Nothing served, so name what the held branches can see of the
            // range — not only the one block the descent stopped on.
            page.need = frontier(opts, blocks, root, &rest_from_start(r))?;
            if page.need.is_empty() {
                page.need = ids;
            }
            return Ok(page);
        }
        Err(e) => return Err(e.into()),
    };

    let mut bytes = 0usize;
    // The key to resume after is always the last one actually SERVED. Resuming
    // after an entry the page refused would skip it.
    let mut last_served: Option<Vec<u8>> = None;
    loop {
        let Some((key, value)) = cur.peek() else {
            // Ran off the end of the tree: the scan is complete.
            return Ok(page);
        };
        if !in_range(&key, r) {
            // Past the far end of the range: complete.
            return Ok(page);
        }
        let cost = entry_bytes(&key, &value);
        // Progress: a page always returns one entry if one is available, even
        // when that entry alone is over the byte limit. Otherwise a single large
        // entry would stall the scan forever.
        if !page.entries.is_empty() && bytes + cost > r.max_bytes {
            break;
        }
        bytes += cost;
        page.entries.push((key.clone(), value));
        last_served = Some(key.clone());
        if page.entries.len() >= r.max_entries {
            break;
        }
        // Stepping to the neighbouring leaf costs a block, and the ancestors
        // already say which keys it holds. A scan that has reached the end of
        // its range stops here instead of paying for a leaf it cannot use.
        if at_edge_of_range(&cur, r) {
            return Ok(page);
        }
        // Step. A missing next leaf ends the page with a frontier.
        let moved = if r.reverse { cur.prev() } else { cur.next() };
        match moved {
            Ok(true) => {}
            Ok(false) => return Ok(page), // end of the tree
            Err(ReadError::Need(_)) => {
                page.next = last_served.clone();
                page.need = frontier(opts, blocks, root, &rest_after(r, &key))?;
                return Ok(page);
            }
            Err(e) => return Err(e.into()),
        }
    }
    // The limit stopped us with entries in hand. Resuming from the last key
    // served is correct whether or not anything follows it.
    page.next = last_served;
    Ok(page)
}

/// Is the neighbouring leaf wholly outside the range? Decided from the
/// ancestors, so it never loads it.
fn at_edge_of_range<B: Blocks>(cur: &Cursor<'_, B>, r: &Range) -> bool {
    // Only the last entry of a leaf costs a block to step past. Anywhere else
    // the neighbouring leaf is irrelevant — asking about it here would end the
    // page in the middle of a leaf that still has entries in range.
    let crossing = if r.reverse {
        cur.at_leaf_start()
    } else {
        cur.at_leaf_end()
    };
    if !crossing {
        return false;
    }
    if r.reverse {
        // Everything before this leaf is below its smallest key.
        match (cur.leaf_min_key(), &r.lo) {
            (Some(min), Bound::Included(k) | Bound::Excluded(k)) => min <= *k,
            _ => false,
        }
    } else {
        match (cur.next_min_key(), &r.hi) {
            (Some(min), _) => !below_hi(&min, &r.hi),
            (None, _) => false,
        }
    }
}

/// The part of `r` still to come after `key` in scan order.
fn rest_after(r: &Range, key: &[u8]) -> Range {
    let mut rest = r.clone();
    if r.reverse {
        rest.hi = Bound::Excluded(key.to_vec());
    } else {
        rest.lo = Bound::Excluded(key.to_vec());
    }
    rest.after = None;
    rest
}

/// The part of `r` the scan has not started yet, with `after` folded in.
fn rest_from_start(r: &Range) -> Range {
    let mut rest = r.clone();
    let start = start_bound(r);
    if r.reverse {
        rest.hi = start;
    } else {
        rest.lo = start;
    }
    rest.after = None;
    rest
}

/// Which part of the range a child covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Span {
    /// Wholly inside the range: its aggregate counts exactly.
    Inside,
    /// Straddles an end of the range: its aggregate is an upper bound on what
    /// the scan will take from it.
    Edge,
}

/// The blocks a scan needs to continue past `from`, in scan order.
///
/// Walks the branches that are HELD, names the blocks that are not, and stops
/// once the blocks it has named can already cover the rest of the caller's
/// limit — otherwise "the latest 20 posts" would fetch 64 leaves to serve 20
/// entries. Aggregates make that decidable without reading anything: a child
/// wholly inside the range contributes exactly its `agg`, an edge child at most
/// its `agg`.
///
/// A missing branch is named and not descended: its children are unknowable
/// until it arrives.
fn frontier<B: Blocks>(
    opts: Options,
    blocks: &B,
    root: &Cid,
    rest: &Range,
) -> Result<Vec<Cid>, ReadError> {
    let mut f = Walk {
        out: Vec::new(),
        entries: 0,
        bytes: 0,
        want_entries: rest.max_entries as u64,
        want_bytes: rest.max_bytes as u64,
        covered: false,
        agg_bound: opts.agg_bound,
    };
    let node = load(blocks, root)?;
    walk(blocks, &node, None, rest, &mut f)?;
    Ok(f.out)
}

struct Walk {
    out: Vec<Cid>,
    entries: u64,
    bytes: u64,
    want_entries: u64,
    want_bytes: u64,
    covered: bool,
    agg_bound: bool,
}

impl Walk {
    /// Name a block, and record what it can contribute.
    ///
    /// An `Inside` child contributes exactly its aggregate and an `Edge` child
    /// at most its aggregate, so both are added the same way: the question here
    /// is only whether enough has been named to cover the caller's limit, and
    /// for that an upper bound is the right side to err on — it can end the
    /// frontier early, costing one more round, never a wrong answer. (The span
    /// is still yielded: the range aggregate of #7 needs the exact/bound
    /// distinction, and this walk is the one it will reuse.)
    fn name(&mut self, id: Cid, agg: Agg, _span: Span) {
        if self.out.contains(&id) {
            return;
        }
        self.out.push(id);
        self.entries = self.entries.saturating_add(agg.count);
        self.bytes = self.bytes.saturating_add(agg.bytes);
        // The check comes after the push, so the block that stopped the scan is
        // always named however tight the limit is.
        // EITHER limit ends a page, so either one being covered means the
        // blocks named can already fill it. Requiring both would name a byte
        // budget's worth of leaves to serve twenty entries — the exact waste
        // this bound exists to prevent.
        let enough =
            self.agg_bound && (self.entries >= self.want_entries || self.bytes >= self.want_bytes);
        if self.out.len() >= MAX_NEED || enough {
            self.covered = true;
        }
    }
}

/// Visit the children of `node` that intersect `r`, in scan order.
///
/// `upper` is the smallest key of whatever follows this node — the bound its
/// last child's coverage ends at, which the node itself cannot know. That is
/// what makes `Inside` decidable for a last child.
fn walk<B: Blocks>(
    blocks: &B,
    node: &Node<'_>,
    upper: Option<&[u8]>,
    r: &Range,
    f: &mut Walk,
) -> Result<(), ReadError> {
    if node.is_leaf() {
        return Ok(());
    }
    let n = node.len();
    let order: Vec<usize> = if r.reverse {
        (0..n).rev().collect()
    } else {
        (0..n).collect()
    };
    for i in order {
        if f.covered {
            return Ok(());
        }
        let min = node.key(i);
        // This child covers [min, next), where `next` is the following child's
        // key or, for the last child, whatever bounds this node.
        let next: Option<Vec<u8>> = if i + 1 < n {
            Some(node.key(i + 1))
        } else {
            upper.map(|u| u.to_vec())
        };
        // Every key this child holds is ≥ `min` and < `next`. Both tests below
        // follow from that and nothing else, so neither reads the child.
        //
        // Wholly above the range: its smallest key is already past the top.
        let above = !below_hi(&min, &r.hi);
        // Wholly below it: everything it holds is under `next`, so if `next` is
        // at or below the bottom bound, nothing in it can qualify.
        let below = match (&next, &r.lo) {
            (Some(nx), Bound::Included(k) | Bound::Excluded(k)) => nx <= k,
            _ => false,
        };
        if above || below {
            continue;
        }
        // Wholly within: its smallest key clears the bottom, and everything
        // under `next` clears the top.
        let inside = above_lo(&min, &r.lo)
            && match (&next, &r.hi) {
                (_, Bound::Unbounded) => true,
                (Some(nx), Bound::Included(k) | Bound::Excluded(k)) => nx <= k,
                (None, _) => false,
            };
        let span = if inside { Span::Inside } else { Span::Edge };
        let (id, agg) = node.child(i);
        match blocks.get(&id) {
            None => f.name(id, agg, span),
            Some(_) => {
                // Held: nothing to fetch here, but its children may be missing.
                let child = load(blocks, &id)?;
                if !child.is_leaf() {
                    walk(blocks, &child, next.as_deref(), r, f)?;
                }
            }
        }
    }
    Ok(())
}

/// The bytes of a value that lives in its own block.
///
/// The id binds the block's kind (`BLAKE3(RAW ‖ body)`), so a tree node can
/// never be served as a value: its id would be a different one. The recorded
/// length is checked, because a leaf's `vlen` and the block are two separate
/// statements and a reader that trusted the leaf could be handed either.
pub fn value_bytes<'a>(
    blocks: &'a impl Blocks,
    cid: &Cid,
    len: u32,
) -> Result<&'a [u8], ReadError> {
    let body = blocks.get(cid).ok_or_else(|| ReadError::Need(vec![*cid]))?;
    if body.len() != len as usize {
        return Err(ReadError::Mismatch(*cid));
    }
    Ok(body)
}
