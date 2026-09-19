//! What changed between two trees, without reading the parts that did not.
//!
//! `diff(a, b)` is what sync is: "here is the head I have, here is the head I
//! was just told about — what is different?" Live queries, keepers and the
//! per-device overlay are the same question asked of two roots.
//!
//! # The one shortcut
//!
//! A node's id is the hash of its bytes, so **equal id ⇒ equal subtree**. When
//! both sides stand on a child slot that begins at the same key and carries the
//! same id, everything under it is identical and is skipped whole — in both
//! trees, at whatever level it is found. Content-defined boundaries make the
//! two trees re-align a node or two after each edit, so the shortcut starts
//! firing again immediately.
//!
//! It fires on the ID and on nothing else. Equal aggregates, equal first keys
//! and equal lengths are all things two different subtrees can have.
//!
//! # Compare before descending
//!
//! A child's id and first key live in its PARENT, so the comparison costs
//! nothing: [`SlotCursor`] stands on a slot and loads the child only when the
//! ids disagree. This is the whole cost argument. A diff built on entry-level
//! cursors would have walked a root-to-leaf path in each tree before it could
//! say "both at the start of a node", paying `height` reads per tree for every
//! subtree it then skipped — on a cold tree, network fetches of blocks the diff
//! is about to declare irrelevant.
//!
//! So: `a == b` reads **nothing**. Identical contents reached by different
//! histories are the same case — the trees are history-independent, so equal
//! contents give equal roots.
//!
//! # One merge, not a rule per level
//!
//! At each position the highest level at which both sides have a slot beginning
//! at the current key is compared, and a side descends one level only when that
//! comparison fails, or when its slot begins before the other side's position
//! and must be opened to reach it. Lower levels are reached by the same loop —
//! two differing level-2 nodes very often share their first level-1 child, and
//! that is found without a special case. Different heights need no special case
//! either: levels are absolute, and equal ids imply equal levels.
//!
//! # Paging
//!
//! A page is the contiguous run of differences the limits allow, and [`Resume`]
//! says where to carry on — carrying **both roots**, because a diff whose roots
//! moved underneath it cannot give a coherent answer. `Range::after` is
//! refused for the same reason: it cannot carry them, so there is one resume
//! mechanism rather than two that can disagree.
//!
//! Resuming is by KEY, so each page re-opens the path down to where it carries
//! on. That is what lets a resume survive anything but the roots moving, and it
//! is what a small page costs. Measured, 189 changes over 6,000 entries
//! (`small_pages_cost_reads_and_repeat_new_blocks`):
//!
//! | page | pages | distinct blocks | lookups | `new_blocks` repeats |
//! |---|---|---|---|---|
//! | 1 | 190 | 339 | 1,473 | 567 |
//! | 7 | 28 | 339 | 501 | 81 |
//! | 100 | 2 | 339 | 345 | 3 |
//! | unlimited | 1 | 339 | 339 | 0 |
//!
//! The SET of blocks touched does not change — 339 at every size. What changes
//! is how often each is asked for: paging one change at a time asks four times
//! as often. A caller with a cache in front of the store pays little of that;
//! one without pays all of it. So page a diff at whatever size the consumer
//! needs, but do not page a bulk sync at 1.
//!
//! # What is believed, and what is not
//!
//! Values are compared by `(id, len)` for a referenced value and by bytes for
//! an inline one, and a referenced value is NEVER fetched to compare it: one
//! encoding per value ([`Value::for_bytes`](crate::node::Value::for_bytes))
//! means equal bytes have equal ids, and different bytes cannot share one.
//! Aggregates are not consulted at all here.

use crate::cursor::{Slot, SlotCursor};
use crate::node::Value;
use crate::range::{in_range, Range, MAX_NEED};
use crate::store::{Blocks, ReadError};
use crate::Cid;
use std::collections::HashSet;
use std::ops::Bound;

/// One difference, in key order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Change<'a> {
    Added {
        key: Vec<u8>,
        new: Value<'a>,
    },
    Removed {
        key: Vec<u8>,
        old: Value<'a>,
    },
    Changed {
        key: Vec<u8>,
        old: Value<'a>,
        new: Value<'a>,
    },
}

impl Change<'_> {
    pub fn key(&self) -> &[u8] {
        match self {
            Change::Added { key, .. }
            | Change::Removed { key, .. }
            | Change::Changed { key, .. } => key,
        }
    }
}

/// Where to carry on, and between WHICH two trees.
///
/// Both roots travel with the key. Unlike a range scan, a diff cannot survive
/// its roots changing underneath it: pages up to here would describe `a → b`
/// and pages after it `a' → b'`, and applying the concatenation to `a` gives
/// neither — silently. So a resume against different roots is refused rather
/// than answered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resume {
    pub a: Cid,
    pub b: Cid,
    /// Carry on strictly after this key.
    pub after: Vec<u8>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct DiffPage<'a> {
    pub changes: Vec<Change<'a>>,
    /// `None` when the diff is complete for the range.
    pub next: Option<Resume>,
    /// Blocks of EITHER tree that are missing, in scan order, capped at
    /// [`MAX_NEED`]. Named from the two parents at the position that stopped:
    /// the children whose ids are absent from the other side's child-id set,
    /// which is precisely "on a differing path".
    pub need: Vec<Cid>,
    /// The `b`-side nodes this page had to open — the ones for which no
    /// equal-id counterpart was found on the `a` side.
    ///
    /// Within one page each block appears **once**. Across pages it can appear
    /// again: resuming re-opens the path to where it carries on, and the nodes
    /// on that path are named by each page that walks them. So a caller
    /// collecting this across a paged diff must dedupe — the UNION over the
    /// pages is exact (it is `nodes(b) ∖ nodes(a)` at every page size), the
    /// concatenation is not. The smaller the page the more repeats: 567 of them
    /// at one change per page, 0 in a single page, for the same 169 blocks.
    ///
    /// What a keeper told "the head moved from `a` to `b`" must fetch, and no
    /// more. Defined by comparison, never by "we happened to descend it": under
    /// the rule above, the only reason to open a `b`-side node is that its slot
    /// did not match, so the two coincide — and the gate asserts the exact set
    /// `nodes(b) ∖ nodes(a)` rather than anything looser.
    pub new_blocks: Vec<Cid>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiffError {
    Read(ReadError),
    /// A resume token from a different pair of roots.
    RootsChanged,
    /// A range instruction a diff has no answer for.
    Unsupported(&'static str),
}

impl From<ReadError> for DiffError {
    fn from(e: ReadError) -> Self {
        DiffError::Read(e)
    }
}

/// The changes from `a` to `b` within `r`, in key order.
pub fn diff<'a, B: Blocks>(
    blocks: &'a B,
    a: &Cid,
    b: &Cid,
    r: &Range,
    resume: Option<&Resume>,
) -> Result<DiffPage<'a>, DiffError> {
    if r.reverse {
        return Err(DiffError::Unsupported("reverse"));
    }
    if r.after.is_some() {
        // ONE resume mechanism. `Range::after` cannot carry the roots, and a
        // diff that resumes against a different pair of roots answers a
        // question nobody asked (see [`Resume`]) — so the two cannot sit side
        // by side, and the one that can be made safe wins. A caller who wants
        // to start partway through sets `lo`, which is a bound on the range
        // rather than a claim about where a previous page stopped.
        return Err(DiffError::Unsupported(
            "after — use the Resume token, or lo",
        ));
    }
    let mut r = r.clone();
    if let Some(res) = resume {
        if res.a != *a || res.b != *b {
            return Err(DiffError::RootsChanged);
        }
        // Carrying on is a tighter lower bound, so it goes through the same
        // window test as the range itself rather than a second mechanism.
        if !matches!(&r.lo, Bound::Included(k) | Bound::Excluded(k) if k > &res.after) {
            r.lo = Bound::Excluded(res.after.clone());
        }
    }
    let empty = DiffPage {
        changes: Vec::new(),
        next: None,
        need: Vec::new(),
        new_blocks: Vec::new(),
    };
    // Equal roots: nothing is read, not even the roots. The cheapest and by far
    // the most common answer a sync gets.
    if a == b {
        return Ok(empty);
    }

    let mut s: State<'a, '_> = State {
        r: &r,
        changes: Vec::new(),
        need: Vec::new(),
        new_blocks: Vec::new(),
        bytes: 0,
        // ECHOED, not started fresh. A page that stops on a missing block
        // before deciding any key would otherwise report `next: None`, which
        // also means "finished" — and the natural caller loop (`resume =
        // page.next`) would restart from the top and re-deliver every change it
        // had already been given, silently, and only when paging a cold store.
        // With the token echoed the rule is uniform: always take `next`;
        // finished is `next == None` AND `need` empty.
        last: resume.map(|r| r.after.clone()),
        stopped: false,
    };
    let ca = open(blocks, a, &mut s);
    let cb = open(blocks, b, &mut s);
    let (mut ca, mut cb) = match (ca, cb) {
        (Ok(x), Ok(y)) => (x, y),
        (Err(e), _) | (_, Err(e)) => return Err(e.into()),
    };
    // `b`'s root is NOT named here. With the cursor standing on the root as a
    // slot, the root is reported by the same rule as every other node: if the
    // comparison against `a` fails, entering it is a `descend` that names it.
    // Naming it up front was wrong twice over — it listed the root a second
    // time in the ordinary case, and it claimed a new block in the case where
    // `b`'s root is a node `a` already has (b = one leaf of a, the collapse
    // shape), where the right answer is that nothing is new.
    match run(&mut s, &mut ca, &mut cb) {
        Ok(()) => {}
        Err(ReadError::Need(ids)) => {
            s.stopped = true;
            for id in ids {
                push_need(&mut s.need, id);
            }
            name_siblings(blocks, &mut s, &ca, &cb);
        }
        Err(e) => return Err(e.into()),
    }
    let next = (s.stopped)
        .then(|| s.last.clone())
        .flatten()
        .map(|after| Resume {
            a: *a,
            b: *b,
            after,
        });
    Ok(DiffPage {
        changes: s.changes,
        next,
        need: s.need,
        new_blocks: s.new_blocks,
    })
}

fn open<'a, B: Blocks>(
    blocks: &'a B,
    root: &Cid,
    s: &mut State<'_, '_>,
) -> Result<Option<SlotCursor<'a, B>>, ReadError> {
    match SlotCursor::open(blocks, root) {
        Err(ReadError::Need(ids)) => {
            s.stopped = true;
            for id in ids {
                push_need(&mut s.need, id);
            }
            Ok(None)
        }
        other => other,
    }
}

struct State<'a, 'r> {
    r: &'r Range,
    changes: Vec<Change<'a>>,
    need: Vec<Cid>,
    new_blocks: Vec<Cid>,
    bytes: u64,
    last: Option<Vec<u8>>,
    stopped: bool,
}

fn push_need(need: &mut Vec<Cid>, id: Cid) {
    if need.len() < MAX_NEED && !need.contains(&id) {
        need.push(id);
    }
}

/// Where a slot's span sits relative to the range.
enum Window {
    /// Entirely below the bottom bound — nothing in it can qualify.
    Below,
    /// Its first key is already past the top — this side is finished.
    Above,
    Overlap,
}

fn window<B: Blocks>(c: &SlotCursor<'_, B>, r: &Range) -> Window {
    let key = c.key();
    if !crate::range::below_hi(&key, &r.hi) {
        return Window::Above;
    }
    // Keys in this slot are in [key, end). If `end` is at or below the bottom
    // bound, every one of them is under it.
    if let (Some(end), Bound::Included(lo) | Bound::Excluded(lo)) = (c.end_key(), &r.lo) {
        if end <= *lo {
            return Window::Below;
        }
    }
    // A root has no key after it, so the test above cannot dismiss one — and a
    // side that cannot dismiss ground the other side has already left behind
    // gets DRAINED over it, which opens blocks for position rather than for
    // difference. Where the root is a leaf its own last entry settles it.
    if let (Some(last), Bound::Included(lo) | Bound::Excluded(lo)) = (c.last_key_if_known(), &r.lo)
    {
        if last < *lo || (last == *lo && matches!(&r.lo, Bound::Excluded(_))) {
            return Window::Below;
        }
    }
    Window::Overlap
}

/// One side of the merge, named so the two halves of every rule read the same.
enum Side {
    A,
    B,
}

/// The merge. Every read it makes is a comparison that failed or a position
/// that had to be reached.
fn run<'a, B: Blocks>(
    s: &mut State<'a, '_>,
    ca: &mut Option<SlotCursor<'a, B>>,
    cb: &mut Option<SlotCursor<'a, B>>,
) -> Result<(), ReadError> {
    loop {
        if s.full() {
            s.stopped = true;
            return Ok(());
        }
        // Drop what the range excludes before anything is compared: a subtree
        // outside the range is not read, and one past the top ends this side.
        for c in [&mut *ca, &mut *cb] {
            while let Some(cur) = c.as_mut() {
                if cur.finished() {
                    break;
                }
                match window(cur, s.r) {
                    Window::Below => cur.advance(),
                    Window::Above => {
                        while !cur.finished() {
                            cur.advance();
                        }
                    }
                    Window::Overlap => break,
                }
            }
        }
        let a_live = ca.as_ref().is_some_and(|c| !c.finished());
        let b_live = cb.as_ref().is_some_and(|c| !c.finished());
        match (a_live, b_live) {
            (false, false) => return Ok(()),
            (true, false) => drain(s, ca.as_mut().expect("live"), Side::A)?,
            (false, true) => drain(s, cb.as_mut().expect("live"), Side::B)?,
            (true, true) => {
                let a = ca.as_mut().expect("live");
                let b = cb.as_mut().expect("live");
                let (ka, kb) = (a.key(), b.key());
                match ka.cmp(&kb) {
                    std::cmp::Ordering::Less => drain(s, a, Side::A)?,
                    std::cmp::Ordering::Greater => drain(s, b, Side::B)?,
                    std::cmp::Ordering::Equal => step_together(s, a, b)?,
                }
            }
        }
    }
}

/// Both sides begin at the same key. This is where the shortcut lives.
fn step_together<'a, B: Blocks>(
    s: &mut State<'a, '_>,
    a: &mut SlotCursor<'a, B>,
    b: &mut SlotCursor<'a, B>,
) -> Result<(), ReadError> {
    match (a.slot(), b.slot()) {
        (Slot::Sub { level: la, id: ia }, Slot::Sub { level: lb, id: ib }) if la == lb => {
            if ia == ib {
                // THE shortcut. Nothing under here differs, in either tree, and
                // neither child is read. Equal ids and nothing else: two
                // different subtrees can share an aggregate, a first key or a
                // length.
                a.advance();
                b.advance();
            } else {
                a.descend()?;
                let id = b.descend()?;
                s.push_new(id);
            }
        }
        // Different depths cannot be equal (equal ids imply equal levels), so
        // the deeper-reaching side is opened until they meet.
        (Slot::Sub { level: la, .. }, Slot::Sub { level: lb, .. }) => {
            if la > lb {
                a.descend()?;
            } else {
                let id = b.descend()?;
                s.push_new(id);
            }
        }
        (Slot::Sub { .. }, Slot::Entry(_)) => {
            a.descend()?;
        }
        (Slot::Entry(_), Slot::Sub { .. }) => {
            let id = b.descend()?;
            s.push_new(id);
        }
        (Slot::Entry(old), Slot::Entry(new)) => {
            let key = a.key();
            if old != new && in_range(&key, s.r) {
                s.emit(Change::Changed {
                    key: key.clone(),
                    old,
                    new,
                });
            } else {
                s.seen(&key);
            }
            a.advance();
            b.advance();
        }
    }
    Ok(())
}

/// This side holds keys the other side has already passed (or the other side is
/// finished), so everything here is an addition or a removal. An entry is
/// reported; a subtree is opened, because its entries have to be reported one
/// by one — that cost is the size of the change, not of the tree.
fn drain<'a, B: Blocks>(
    s: &mut State<'a, '_>,
    c: &mut SlotCursor<'a, B>,
    side: Side,
) -> Result<(), ReadError> {
    match c.slot() {
        Slot::Entry(v) => {
            let key = c.key();
            if in_range(&key, s.r) {
                s.emit(match side {
                    Side::A => Change::Removed {
                        key: key.clone(),
                        old: v,
                    },
                    Side::B => Change::Added {
                        key: key.clone(),
                        new: v,
                    },
                });
            } else {
                s.seen(&key);
            }
            c.advance();
        }
        Slot::Sub { .. } => {
            let id = c.descend()?;
            if matches!(side, Side::B) {
                s.push_new(id);
            }
        }
    }
    Ok(())
}

impl<'a> State<'a, '_> {
    fn full(&self) -> bool {
        (self.r.max_entries > 0 && self.changes.len() >= self.r.max_entries)
            || (self.r.max_bytes > 0 && self.bytes >= self.r.max_bytes as u64)
    }

    /// A key that has been decided — whether or not it produced a change. The
    /// resume point is the last key DECIDED, so a page never re-offers ground
    /// it has already covered and never skips a key it declined to report.
    fn seen(&mut self, key: &[u8]) {
        self.last = Some(key.to_vec());
    }

    /// A `b`-side block with no counterpart in `a`.
    ///
    /// No de-duplication: a descent moves forward, so within one page a node is
    /// entered at most once. A set here would only hide a bug — and hide it
    /// from the test that asserts this list has no repeats.
    fn push_new(&mut self, id: Cid) {
        self.new_blocks.push(id);
    }

    fn emit(&mut self, c: Change<'a>) {
        self.bytes += c.key().len() as u64 + c.weight();
        let key = c.key().to_vec();
        self.seen(&key);
        self.changes.push(c);
    }
}

impl Change<'_> {
    /// What this change counts against a byte limit: what the PAGE carries.
    ///
    /// A referenced value is 32 bytes of id here, not its referenced length —
    /// the page holds the reference, and nothing fetches the bytes. Charging
    /// the real length would put one `Changed` between two 200 KiB files over a
    /// 256 KiB page on its own, so exactly the domains that reference their
    /// values would get one change per page, each page re-walking from the
    /// roots. Shared with `range` so the two accountings cannot drift.
    fn weight(&self) -> u64 {
        let of = |v: &Value<'_>| crate::range::entry_bytes(&[], v) as u64;
        match self {
            Change::Added { new, .. } => of(new),
            Change::Removed { old, .. } => of(old),
            Change::Changed { old, new, .. } => of(old) + of(new),
        }
    }
}

/// Fill `need` with the blocks of BOTH trees that the position which stopped
/// can already name.
///
/// Two things make this harder than it looks, and both come from the shape a
/// real sync has — one side held, the other being fetched:
///
/// 1. **The two cursors can be at different DEPTHS.** `step_together` descends
///    `a` first; if `a` is the held tree that succeeds, and then `b`'s descend
///    fails for a missing block, so at the stop `a` stands one level deeper
///    than `b`. Child-id sets taken from two different levels are disjoint
///    whatever the trees contain, so comparing them names every remaining
///    sibling on both sides — hundreds of blocks, most already held, crowding
///    the real ones out of a capped round. So the comparison is made at the
///    level the two sides share, and if there is no such level nothing is
///    named beyond the block that stopped.
/// 2. **`need` means MISSING.** A block already in the store is not named,
///    whatever the comparison says about it.
fn name_siblings<'a, B: Blocks>(
    blocks: &B,
    s: &mut State<'a, '_>,
    ca: &Option<SlotCursor<'a, B>>,
    cb: &Option<SlotCursor<'a, B>>,
) {
    let (Some(a), Some(b)) = (ca.as_ref(), cb.as_ref()) else {
        return;
    };
    if a.finished() || b.finished() {
        return;
    }
    // The shallower of the two parents: the deeper side has an ancestor there,
    // the shallower side has nothing loaded below it.
    let level = a.parent().0.level().max(b.parent().0.level());
    let (Some((an, ai)), Some((bn, bi))) = (a.node_at_level(level), b.node_at_level(level)) else {
        return;
    };
    if an.is_leaf() || bn.is_leaf() {
        return;
    }
    let ids = |n: &crate::node::Node<'_>| -> HashSet<Cid> {
        (0..n.len()).map(|i| n.child(i).0).collect()
    };
    let (a_ids, b_ids) = (ids(an), ids(bn));
    // Scan order from where each side stands, and only over the span the two
    // parents share: beyond it there is nothing to have differed from.
    let hi = an.key(an.len() - 1).max(bn.key(bn.len() - 1));
    for (n, from, other) in [(an, ai, &b_ids), (bn, bi, &a_ids)] {
        for i in from..n.len() {
            let k = n.key(i);
            if k > hi || !crate::range::below_hi(&k, &s.r.hi) {
                continue;
            }
            let (id, _) = n.child(i);
            if !other.contains(&id) && blocks.get(&id).is_none() {
                push_need(&mut s.need, id);
            }
        }
    }
}
