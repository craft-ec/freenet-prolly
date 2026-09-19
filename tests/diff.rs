//! What changed between two trees: the answer, and what it cost to get it.

#[path = "common/dataset.rs"]
mod common;
#[path = "common/invariants.rs"]
mod invariants;
use common::{dataset, rng};

use freenet_prolly::apply::{apply_into, Edit};
use freenet_prolly::build::init;
use freenet_prolly::diff::{diff, Change, DiffError, DiffPage, Resume};
use freenet_prolly::node::{Node, Value, MAX_INLINE};
use freenet_prolly::range::Range;
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::{block_id, kind, Cid};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};
use std::ops::Bound;

type Map = BTreeMap<Vec<u8>, Vec<u8>>;

fn value_of(v: &[u8]) -> Value<'_> {
    if v.len() <= MAX_INLINE {
        Value::Inline(v)
    } else {
        Value::Ref {
            cid: block_id(kind::RAW, v),
            len: v.len() as u32,
        }
    }
}

/// Build `m` into `blocks` and return its root, checking on the way out that
/// what was built is a tree.
fn build(blocks: &mut MemBlocks, m: &Map) -> Cid {
    let root = init(blocks);
    let edits: Vec<(Vec<u8>, Edit)> = m
        .iter()
        .map(|(k, v)| (k.clone(), Edit::Put(v.clone())))
        .collect();
    let root = apply_into(blocks, &root, &edits).unwrap().root;
    invariants::check_tree(blocks, &root, m).unwrap();
    root
}

/// A change with its values as bytes, which is what two stores can be
/// compared on when the values live in different places.
type Owned = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);

/// The oracle: what two maps differ by, in key order.
fn reference<'m>(a: &'m Map, b: &'m Map, r: &Range) -> Vec<Change<'m>> {
    let mut keys: Vec<&Vec<u8>> = a.keys().chain(b.keys()).collect();
    keys.sort();
    keys.dedup();
    keys.into_iter()
        .filter(|k| in_range(k, r))
        .filter_map(|k| match (a.get(k), b.get(k)) {
            (Some(x), Some(y)) if x == y => None,
            (Some(x), Some(y)) => Some(Change::Changed {
                key: k.clone(),
                old: value_of(x),
                new: value_of(y),
            }),
            (Some(x), None) => Some(Change::Removed {
                key: k.clone(),
                old: value_of(x),
            }),
            (None, Some(y)) => Some(Change::Added {
                key: k.clone(),
                new: value_of(y),
            }),
            (None, None) => unreachable!(),
        })
        .collect()
}

fn in_range(k: &[u8], r: &Range) -> bool {
    let lo = match &r.lo {
        Bound::Unbounded => true,
        Bound::Included(x) => k >= x.as_slice(),
        Bound::Excluded(x) => k > x.as_slice(),
    };
    let hi = match &r.hi {
        Bound::Unbounded => true,
        Bound::Included(x) => k <= x.as_slice(),
        Bound::Excluded(x) => k < x.as_slice(),
    };
    lo && hi
}

struct Counting<'a> {
    inner: &'a MemBlocks,
    reads: RefCell<HashSet<Cid>>,
    calls: RefCell<usize>,
}
impl Blocks for Counting<'_> {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        self.reads.borrow_mut().insert(*cid);
        *self.calls.borrow_mut() += 1;
        self.inner.get(cid)
    }
}
fn counting(inner: &MemBlocks) -> Counting<'_> {
    Counting {
        inner,
        reads: RefCell::default(),
        calls: RefCell::default(),
    }
}

/// Every page of the diff, concatenated. `limit` of 0 means one page.
fn all_pages<'a, B: Blocks>(
    blocks: &'a B,
    a: &Cid,
    b: &Cid,
    r: &Range,
) -> Result<(Vec<Change<'a>>, Vec<Cid>, usize), DiffError> {
    let mut out = Vec::new();
    let mut new_blocks = Vec::new();
    let mut resume: Option<Resume> = None;
    let mut pages = 0;
    loop {
        let p: DiffPage<'a> = diff(blocks, a, b, r, resume.as_ref())?;
        pages += 1;
        assert!(pages < 10_000, "diff does not terminate");
        assert!(p.need.is_empty(), "a warm store must never need a block");
        out.extend(p.changes);
        new_blocks.extend(p.new_blocks);
        match p.next {
            Some(n) => resume = Some(n),
            None => break,
        }
    }
    Ok((out, new_blocks, pages))
}

/// Every node reachable from `root`, walked independently of the diff.
fn nodes(store: &MemBlocks, root: Cid, out: &mut HashSet<Cid>) {
    if !out.insert(root) {
        return;
    }
    let n = Node::parse(&store.0[&root]).unwrap();
    if !n.is_leaf() {
        for i in 0..n.len() {
            nodes(store, n.child(i).0, out);
        }
    }
}

/// `b` = `a` with `edits` applied, both in one store (which is what a real
/// pair of heads looks like: the unchanged blocks are shared).
struct Pair {
    blocks: MemBlocks,
    a: Cid,
    b: Cid,
    ma: Map,
    mb: Map,
}

fn pair(m: Map, edits: Vec<(Vec<u8>, Edit)>) -> Pair {
    let mut blocks = MemBlocks::default();
    let a = build(&mut blocks, &m);
    let mut mb = m.clone();
    for (k, e) in &edits {
        match e {
            Edit::Put(v) => mb.insert(k.clone(), v.clone()),
            Edit::Delete => mb.remove(k),
        };
    }
    let b = apply_into(&mut blocks, &a, &edits).unwrap().root;
    invariants::check_tree(&blocks, &b, &mb).unwrap();
    Pair {
        blocks,
        a,
        b,
        ma: m,
        mb,
    }
}

impl Pair {
    fn check(&self, r: &Range) -> (Vec<Cid>, usize) {
        let c = counting(&self.blocks);
        let (got, new_blocks, _) = all_pages(&c, &self.a, &self.b, r).unwrap();
        assert_eq!(got, reference(&self.ma, &self.mb, r), "changes");
        let reads = c.reads.borrow().len();
        (new_blocks, reads)
    }
}

/// The keys real callers write: every one above the last.
fn appended(from: usize, n: usize) -> Vec<(Vec<u8>, Edit)> {
    (from..from + n)
        .map(|i| {
            (
                format!("k/{i:08}").into_bytes(),
                Edit::Put(vec![(i % 251) as u8; 120]),
            )
        })
        .collect()
}

fn ordered_map(n: usize) -> Map {
    (0..n)
        .map(|i| (format!("k/{i:08}").into_bytes(), vec![(i % 251) as u8; 120]))
        .collect()
}

// ---------------------------------------------------------------------------
// Structured workloads first: appends, prepends and both ends are what callers
// actually do, and a random generator produces none of them.
// ---------------------------------------------------------------------------

#[test]
fn appends_prepends_and_both_ends_match_the_reference() {
    for (what, base, edits) in [
        ("append 1", ordered_map(5_000), appended(5_000, 1)),
        ("append 10", ordered_map(5_000), appended(5_000, 10)),
        ("append 1000", ordered_map(5_000), appended(5_000, 1000)),
        (
            "prepend 10",
            ordered_map(5_000),
            (0..10)
                .map(|i| (format!("a/{i:08}").into_bytes(), Edit::Put(vec![7u8; 90])))
                .collect(),
        ),
        ("both ends", ordered_map(5_000), {
            let mut v: Vec<(Vec<u8>, Edit)> = (0..5)
                .map(|i| (format!("a/{i:08}").into_bytes(), Edit::Put(vec![1u8; 80])))
                .collect();
            v.extend(appended(5_000, 5));
            v
        }),
        ("delete a run", ordered_map(5_000), {
            (100..140)
                .map(|i| (format!("k/{i:08}").into_bytes(), Edit::Delete))
                .collect()
        }),
        ("change in place", ordered_map(5_000), {
            (0..20)
                .map(|i| {
                    (
                        format!("k/{:08}", i * 100).into_bytes(),
                        Edit::Put(vec![9u8; 121]),
                    )
                })
                .collect()
        }),
    ] {
        let p = pair(base, edits);
        let (_, reads) = p.check(&Range::default());
        // The cost claim, in its strongest form: EVERY block the diff read is
        // one the two trees do not share. A shared block is byte-identical, so
        // reading one means a subtree was entered that a comparison had already
        // settled — which is what "compare before descending" forbids.
        let (mut na, mut nb) = (HashSet::new(), HashSet::new());
        nodes(&p.blocks, p.a, &mut na);
        nodes(&p.blocks, p.b, &mut nb);
        let differing: HashSet<Cid> = na.symmetric_difference(&nb).copied().collect();
        let c = counting(&p.blocks);
        let _ = all_pages(&c, &p.a, &p.b, &Range::default()).unwrap();
        let read: HashSet<Cid> = c.reads.borrow().iter().copied().collect();
        let shared: Vec<&Cid> = read.difference(&differing).collect();
        assert!(
            shared.is_empty(),
            "{what}: read {} block(s) the two trees SHARE — a settled subtree was entered",
            shared.len()
        );
        println!(
            "  {what:16}: {reads} nodes read, {} blocks differ",
            differing.len()
        );
    }
}

#[test]
fn random_pairs_match_the_reference() {
    let mut r = rng(4);
    let base: Map = dataset(41, 20_000).into_iter().collect();
    for k in [0usize, 1, 10, 1000] {
        for clustered in [false, true] {
            let keys: Vec<Vec<u8>> = base.keys().cloned().collect();
            let start = r() as usize % keys.len();
            let mut edits: BTreeMap<Vec<u8>, Edit> = BTreeMap::new();
            for i in 0..k {
                let idx = if clustered {
                    (start + i) % keys.len()
                } else {
                    r() as usize % keys.len()
                };
                edits.insert(
                    keys[idx].clone(),
                    if r().is_multiple_of(3) {
                        Edit::Delete
                    } else {
                        Edit::Put(vec![(r() % 251) as u8; 1 + (r() as usize % 300)])
                    },
                );
            }
            let p = pair(base.clone(), edits.into_iter().collect());
            p.check(&Range::default());
        }
    }
}

/// `new_blocks` must be EXACTLY the b-side nodes that are not in `a` — the set
/// a keeper told "the head moved" has to fetch, and no more.
///
/// The argument it rests on: if node N is in `a`, then N's first key is a node
/// start in `a` at N's level, and every a-side ancestor of N has a slot
/// boundary there. The merge opens the a side only as far as it needs to
/// process keys below that point, so it arrives with both sides holding a slot
/// at N's level, the ids match, and N is skipped. So a node the diff had to
/// open cannot be one that exists in `a` — and this asserts the exact set
/// rather than a superset, so if that laziness is ever lost the test says so.
#[test]
fn new_blocks_is_exactly_what_b_has_and_a_does_not() {
    let mut checked = 0;
    for (what, base, edits) in [
        ("append 1", ordered_map(5_000), appended(5_000, 1)),
        ("append 1000", ordered_map(5_000), appended(5_000, 1000)),
        (
            "prepend",
            ordered_map(5_000),
            (0..7)
                .map(|i| (format!("a/{i:08}").into_bytes(), Edit::Put(vec![3u8; 70])))
                .collect(),
        ),
        (
            "scattered",
            ordered_map(5_000),
            (0..25)
                .map(|i| {
                    (
                        format!("k/{:08}", i * 173).into_bytes(),
                        Edit::Put(vec![5u8; 200]),
                    )
                })
                .collect(),
        ),
        (
            "deletes",
            ordered_map(5_000),
            (200..260)
                .map(|i| (format!("k/{i:08}").into_bytes(), Edit::Delete))
                .collect(),
        ),
    ] {
        let p = pair(base, edits);
        let (got, _) = p.check(&Range::default());
        let (mut na, mut nb) = (HashSet::new(), HashSet::new());
        nodes(&p.blocks, p.a, &mut na);
        nodes(&p.blocks, p.b, &mut nb);
        let want: HashSet<Cid> = nb.difference(&na).copied().collect();
        let got: HashSet<Cid> = got.into_iter().collect();
        assert_eq!(
            got,
            want,
            "{what}: new_blocks must be nodes(b) ∖ nodes(a) exactly \
             ({} named, {} really new)",
            got.len(),
            want.len()
        );
        assert!(
            !want.is_empty(),
            "{what}: the case must have new nodes at all"
        );
        println!(
            "  {what:12}: {} new of {} b-side nodes",
            want.len(),
            nb.len()
        );
        checked += 1;
    }
    assert_eq!(checked, 5);
}

/// The cheapest answer a sync can get, and the most common one.
#[test]
fn equal_roots_read_nothing() {
    let p = pair(ordered_map(3_000), appended(3_000, 5));
    let c = counting(&p.blocks);
    let page = diff(&c, &p.b, &p.b, &Range::default(), None).unwrap();
    assert_eq!(page.changes, []);
    assert_eq!(page.next, None);
    assert!(page.new_blocks.is_empty());
    assert_eq!(*c.calls.borrow(), 0, "not even the roots are loaded");

    // Identical contents reached by different histories is the SAME case: the
    // trees are history-independent, so equal contents give equal roots. It is
    // zero reads, not "one per tree".
    let mut other = MemBlocks::default();
    let same = build(&mut other, &p.mb);
    assert_eq!(same, p.b, "same contents, same root, whatever the history");
    let c = counting(&p.blocks);
    assert_eq!(
        diff(&c, &same, &p.b, &Range::default(), None)
            .unwrap()
            .changes,
        []
    );
    assert_eq!(*c.calls.borrow(), 0);
}

/// Reading the diff the other way round gives the same answer with the two
/// one-sided kinds swapped. `new_blocks` is excluded: it is b-side by
/// definition and cannot be symmetric.
#[test]
fn the_diff_is_symmetric_except_for_new_blocks() {
    let p = pair(ordered_map(4_000), {
        let mut v = appended(4_000, 20);
        v.extend((10..30).map(|i| (format!("k/{i:08}").into_bytes(), Edit::Delete)));
        v.extend((50..60).map(|i| (format!("k/{i:08}").into_bytes(), Edit::Put(vec![2u8; 300]))));
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v
    });
    let (fwd, _, _) = all_pages(&p.blocks, &p.a, &p.b, &Range::default()).unwrap();
    let (back, _, _) = all_pages(&p.blocks, &p.b, &p.a, &Range::default()).unwrap();
    let flipped: Vec<Change<'_>> = back
        .into_iter()
        .map(|c| match c {
            Change::Added { key, new } => Change::Removed { key, old: new },
            Change::Removed { key, old } => Change::Added { key, new: old },
            Change::Changed { key, old, new } => Change::Changed {
                key,
                old: new,
                new: old,
            },
        })
        .collect();
    assert_eq!(fwd, flipped);
    assert!(!fwd.is_empty());
}

/// The property the whole thing is for: applying the diff to `a` gives `b`.
#[test]
fn applying_the_diff_to_a_gives_b() {
    let p = pair(ordered_map(4_000), {
        let mut v = appended(4_000, 30);
        v.extend((0..40).map(|i| (format!("k/{:08}", i * 7).into_bytes(), Edit::Delete)));
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v
    });
    let (changes, _, _) = all_pages(&p.blocks, &p.a, &p.b, &Range::default()).unwrap();
    let mut m = p.ma.clone();
    for c in &changes {
        match c {
            Change::Added { key, new } | Change::Changed { key, new, .. } => {
                m.insert(key.clone(), bytes_of(&p.blocks, new));
            }
            Change::Removed { key, .. } => {
                m.remove(key);
            }
        }
    }
    assert_eq!(m, p.mb, "a + diff must be b");
}

fn bytes_of(store: &MemBlocks, v: &Value<'_>) -> Vec<u8> {
    match v {
        Value::Inline(b) => b.to_vec(),
        Value::Ref { cid, .. } => store.get(cid).expect("value block").to_vec(),
    }
}

/// A diff cannot survive its roots moving underneath it, so it refuses rather
/// than answering. The control shows what allowing it would produce.
#[test]
fn a_resume_under_different_roots_is_refused() {
    let p = pair(ordered_map(4_000), appended(4_000, 200));
    let r = Range {
        max_entries: 50,
        ..Range::default()
    };
    let first = diff(&p.blocks, &p.a, &p.b, &r, None).unwrap();
    let token = first.next.clone().expect("more to come");

    // A third tree: `b` plus further edits, as a second sync round would give.
    let mut blocks = p.blocks.clone();
    let b2 = apply_into(&mut blocks, &p.b, &appended(4_300, 50))
        .unwrap()
        .root;
    assert_eq!(
        diff(&blocks, &p.a, &b2, &r, Some(&token)),
        Err(DiffError::RootsChanged)
    );
    assert_eq!(
        diff(&blocks, &p.b, &p.b, &r, Some(&token)),
        Err(DiffError::RootsChanged)
    );
    // The same token against the roots it was issued for still works.
    assert!(diff(&blocks, &p.a, &p.b, &r, Some(&token)).is_ok());

    // THE CONTROL: had it been allowed, the concatenation would describe
    // neither pair. Pages 1..k from a→b, the rest from a→b2, applied to a.
    let mut m = p.ma.clone();
    let mut resume = Some(token);
    let mut rounds = 0;
    for c in &first.changes {
        apply_change(&mut m, c, &blocks);
    }
    while let Some(t) = resume.take() {
        // pretend the refusal did not happen: same token, the NEW b
        let page = diff(&blocks, &p.a, &b2, &r, None).unwrap_or_else(|_| unreachable!());
        let _ = t;
        for c in page.changes.iter().skip(first.changes.len()) {
            apply_change(&mut m, c, &blocks);
        }
        rounds += 1;
        if rounds > 0 {
            break;
        }
    }
    let mut mb2 = p.mb.clone();
    for (k, e) in appended(4_300, 50) {
        if let Edit::Put(v) = e {
            mb2.insert(k, v);
        }
    }
    assert_ne!(m, p.mb, "the spliced result is not b");
    assert_ne!(m, mb2, "and it is not b2 either — it is neither, silently");
}

fn apply_change(m: &mut Map, c: &Change<'_>, store: &MemBlocks) {
    match c {
        Change::Added { key, new } | Change::Changed { key, new, .. } => {
            m.insert(key.clone(), bytes_of(store, new));
        }
        Change::Removed { key, .. } => {
            m.remove(key);
        }
    }
}

/// Trees of different heights, including the shape that lost a subtree in #22:
/// `b` is `a` under a new root level, so ALL of `a` is skipped in one
/// comparison and the rest of `b` is Added.
#[test]
fn trees_of_different_heights() {
    // One leaf against a tall tree.
    let p = pair(ordered_map(3), appended(3, 4_000));
    let reads = {
        let c = counting(&p.blocks);
        let (ch, _, _) = all_pages(&c, &p.a, &p.b, &Range::default()).unwrap();
        assert_eq!(ch.len(), 4_000);
        assert_eq!(ch, reference(&p.ma, &p.mb, &Range::default()));
        let r = c.reads.borrow().len();
        r
    };
    assert_eq!(
        Node::parse(&p.blocks.0[&p.a]).unwrap().level(),
        0,
        "a is a single leaf"
    );
    assert!(
        Node::parse(&p.blocks.0[&p.b]).unwrap().level() >= 2,
        "b is at least three levels"
    );
    println!("single leaf vs height 3: {reads} nodes read for 4000 additions");

    // The #22 shape: everything in `a` survives under a new root in `b`.
    // The #22 shape has to be CONSTRUCTED, not guessed at: append one entry at
    // a time until the root gains a level. A sweep over round sizes misses it,
    // because the boundary is wherever the chunking happens to put it.
    let mut blocks = MemBlocks::default();
    // Start BELOW the only level boundary these trees have: with 120-byte
    // values the root is level 1 up to ~1,000 entries and level 2 from there
    // to past 60,000. A search that starts above it runs forever.
    let mut m = ordered_map(1_000);
    let mut root = build(&mut blocks, &m);
    let level = |b: &MemBlocks, r: &Cid| Node::parse(&b.0[r]).unwrap().level();
    let mut ha = level(&blocks, &root);
    let hb;
    let mut i = 1_000;
    let p = loop {
        assert!(i < 4_000, "the tree never grew a level");
        let edit = appended(i, 1);
        i += 1;
        let next = apply_into(&mut blocks, &root, &edit).unwrap().root;
        let mut mb = m.clone();
        for (k, e) in &edit {
            if let Edit::Put(v) = e {
                mb.insert(k.clone(), v.clone());
            }
        }
        let h = level(&blocks, &next);
        if h == ha + 1 {
            hb = h;
            break Pair {
                blocks,
                a: root,
                b: next,
                ma: m,
                mb,
            };
        }
        ha = h;
        root = next;
        m = mb;
    };
    assert_eq!(hb, ha + 1);
    // `a`'s root is a child of `b`'s root: every block of `a` is in `b`.
    let (mut na, mut nb) = (HashSet::new(), HashSet::new());
    nodes(&p.blocks, p.a, &mut na);
    nodes(&p.blocks, p.b, &mut nb);
    assert!(na.is_subset(&nb), "all of a survives under b's new root");

    let c = counting(&p.blocks);
    let (ch, new_blocks, _) = all_pages(&c, &p.a, &p.b, &Range::default()).unwrap();
    let reads = c.reads.borrow().len();
    assert_eq!(ch, reference(&p.ma, &p.mb, &Range::default()));
    // The whole of `a` is dismissed by ONE comparison: `a`'s root stands as a
    // slot against `b`'s first child, the ids are equal, and neither is
    // entered. So nothing of `a` below its root is ever read.
    let read_ids: HashSet<Cid> = c.reads.borrow().iter().copied().collect();
    let a_only: Vec<Cid> = read_ids.intersection(&na).copied().collect();
    assert_eq!(
        a_only,
        vec![p.a],
        "the only block of `a` that may be read is its root: {} read",
        a_only.len()
    );
    println!(
        "#22 shape (heights {ha} -> {hb}): {reads} nodes read, {} new blocks, \
         {} entries in a",
        new_blocks.len(),
        p.ma.len()
    );
}

/// A range or a prefix restricts what is VISITED; equality still decides what
/// is SKIPPED, including a subtree that straddles a bound.
#[test]
fn a_ranged_diff_matches_the_reference_and_costs_less() {
    let p = pair(ordered_map(20_000), {
        let mut v: Vec<(Vec<u8>, Edit)> = (0..30)
            .map(|i| {
                (
                    format!("k/{:08}", i * 601).into_bytes(),
                    Edit::Put(vec![4u8; 150]),
                )
            })
            .collect();
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v
    });
    let whole = p.check(&Range::default()).1;
    for (what, r) in [
        (
            "a window with no change in it",
            Range {
                lo: Bound::Included(b"k/00003000".to_vec()),
                hi: Bound::Included(b"k/00003100".to_vec()),
                ..Range::default()
            },
        ),
        (
            "a window with changes",
            Range {
                lo: Bound::Included(b"k/00000000".to_vec()),
                hi: Bound::Included(b"k/00002000".to_vec()),
                ..Range::default()
            },
        ),
        ("a prefix", Range::prefix(b"k/0000")),
    ] {
        let (_, reads) = p.check(&r);
        println!("  {what:30}: {reads} nodes read (whole tree: {whole})");
        assert!(
            reads <= whole,
            "{what}: a restricted diff must not cost more than the whole one"
        );
    }
}

/// Start holding only the two roots and feed back exactly what is asked for.
///
/// The independent oracle: every block named must lie on a DIFFERING path,
/// which is checkable without reference to the diff's own reasoning — a block
/// present in both trees is byte-identical, so it would have been skipped. So
/// `need` must never name anything outside the symmetric difference of the two
/// trees' node sets, and never a value block, because values are compared by
/// (id, len) and never fetched.
#[test]
fn a_cold_diff_resumes_and_names_only_differing_paths() {
    for (what, base, edits) in [
        ("append 1000", ordered_map(5_000), appended(5_000, 1000)),
        (
            "scattered 30",
            ordered_map(5_000),
            (0..30)
                .map(|i| {
                    (
                        format!("k/{:08}", i * 149).into_bytes(),
                        Edit::Put(vec![6u8; 180]),
                    )
                })
                .collect(),
        ),
    ] {
        let p = pair(base, edits);
        let (mut na, mut nb) = (HashSet::new(), HashSet::new());
        nodes(&p.blocks, p.a, &mut na);
        nodes(&p.blocks, p.b, &mut nb);
        let differing: HashSet<Cid> = na.symmetric_difference(&nb).copied().collect();

        let mut held = MemBlocks::default();
        held.insert(p.a, &p.blocks.0[&p.a]);
        held.insert(p.b, &p.blocks.0[&p.b]);
        let mut got = Vec::new();
        let mut resume: Option<Resume> = None;
        let (mut rounds, mut fetched) = (0, 0);
        loop {
            // Take everything owned out of the page before the store is
            // touched: a page borrows the blocks it read from.
            let (changes, need, next) = {
                let page = diff(&held, &p.a, &p.b, &Range::default(), resume.as_ref()).unwrap();
                let changes: Vec<_> = page.changes.iter().map(|c| owned(c, &p.blocks)).collect();
                (changes, page.need.clone(), page.next.clone())
            };
            got.extend(changes);
            for id in &need {
                assert!(
                    differing.contains(id),
                    "{what}: named a block that is in BOTH trees, or is not a node"
                );
                held.insert(*id, &p.blocks.0[id]);
                fetched += 1;
            }
            // The protocol: a page can serve changes AND still need blocks.
            // `next` means "carry on after this key" whether or not blocks are
            // missing, so it must always be taken; only a page that served
            // nothing leaves the position where it was.
            match next {
                Some(n) => resume = Some(n),
                None if need.is_empty() => break,
                None => {}
            }
            rounds += 1;
            assert!(rounds < 400, "{what}: did not converge");
        }
        let want: Vec<Owned> = reference(&p.ma, &p.mb, &Range::default())
            .iter()
            .map(|c| owned(c, &p.blocks))
            .collect();
        assert_eq!(
            got.len(),
            want.len(),
            "{what}: cold diff served {} changes, the reference has {}",
            got.len(),
            want.len()
        );
        if let Some(i) = (0..got.len()).find(|&i| got[i] != want[i]) {
            panic!(
                "{what}: first difference at {i}: key {:?} vs {:?}, old {:?} vs {:?}, new {:?} vs {:?}",
                String::from_utf8_lossy(&got[i].0),
                String::from_utf8_lossy(&want[i].0),
                got[i].1.as_ref().map(|v| v.len()),
                want[i].1.as_ref().map(|v| v.len()),
                got[i].2.as_ref().map(|v| v.len()),
                want[i].2.as_ref().map(|v| v.len()),
            );
        }
        println!(
            "  {what:14}: {rounds} rounds, {fetched} blocks fetched, {} differ",
            differing.len()
        );
        assert!(rounds <= differing.len() + 2, "{what}: too many rounds");
    }
}

fn owned(c: &Change<'_>, store: &MemBlocks) -> Owned {
    match c {
        Change::Added { key, new } => (key.clone(), None, Some(bytes_of(store, new))),
        Change::Removed { key, old } => (key.clone(), Some(bytes_of(store, old)), None),
        Change::Changed { key, old, new } => (
            key.clone(),
            Some(bytes_of(store, old)),
            Some(bytes_of(store, new)),
        ),
    }
}

/// Paged at every limit, the concatenation is the same answer.
#[test]
fn any_limit_gives_the_same_diff() {
    let p = pair(ordered_map(8_000), {
        let mut v = appended(8_000, 60);
        v.extend((0..40).map(|i| (format!("k/{:08}", i * 97).into_bytes(), Edit::Delete)));
        v.extend((0..25).map(|i| {
            (
                format!("k/{:08}", 3_000 + i).into_bytes(),
                Edit::Put(vec![8u8; 1500]),
            )
        }));
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v.dedup_by(|x, y| x.0 == y.0);
        v
    });
    let want = reference(&p.ma, &p.mb, &Range::default());
    assert!(want.len() > 100, "the case must need several pages");
    let mut r = rng(21);
    for _ in 0..12 {
        let rng_range = Range {
            max_entries: (r() as usize % 40),
            max_bytes: (r() as usize % 4096),
            ..Range::default()
        };
        let (got, _, pages) = all_pages(&p.blocks, &p.a, &p.b, &rng_range).unwrap();
        assert_eq!(
            got,
            want,
            "limits {:?}",
            (rng_range.max_entries, rng_range.max_bytes)
        );
        assert!(pages >= 1);
    }
    // A limit of one change per page is the extreme, and must still terminate
    // with every change served exactly once.
    let one = Range {
        max_entries: 1,
        ..Range::default()
    };
    let (got, _, pages) = all_pages(&p.blocks, &p.a, &p.b, &one).unwrap();
    assert_eq!(got, want);
    assert_eq!(
        pages,
        want.len() + 1,
        "one change per page, then an empty one"
    );
}

/// `need` is bounded by a block COUNT, not by aggregates: how much is there
/// says nothing about how much of it differs.
#[test]
fn need_is_capped() {
    use freenet_prolly::range::MAX_NEED;
    // One change in each of many different leaves, so a single pair of level-1
    // branches has far more differing children than a round may name.
    let p = pair(ordered_map(20_000), {
        let mut v: Vec<(Vec<u8>, Edit)> = (0..300)
            .map(|i| {
                (
                    format!("k/{:08}", i * 61).into_bytes(),
                    Edit::Put(vec![11u8; 140]),
                )
            })
            .collect();
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v.dedup_by(|x, y| x.0 == y.0);
        v
    });
    let mut held = MemBlocks::default();
    held.insert(p.a, &p.blocks.0[&p.a]);
    held.insert(p.b, &p.blocks.0[&p.b]);
    let mut widest = 0;
    let mut resume: Option<Resume> = None;
    let mut rounds = 0;
    loop {
        let (need, next) = {
            let page = diff(&held, &p.a, &p.b, &Range::default(), resume.as_ref()).unwrap();
            (page.need.clone(), page.next.clone())
        };
        assert!(
            need.len() <= MAX_NEED,
            "a round named {} blocks, the cap is {MAX_NEED}",
            need.len()
        );
        widest = widest.max(need.len());
        for id in &need {
            held.insert(*id, &p.blocks.0[id]);
        }
        match next {
            Some(n) => resume = Some(n),
            None if need.is_empty() => break,
            None => {}
        }
        rounds += 1;
        assert!(rounds < 500);
    }
    println!("need: widest round named {widest} blocks (cap {MAX_NEED})");
    assert!(
        widest > 1,
        "the case must name siblings, not one block at a time"
    );
}

/// What a diff costs against reading both trees, which is the alternative.
///
/// The control is a real full scan through the public range API — what a
/// consumer without a diff would have to write — not a stripped-down loop.
#[test]
fn the_cost_of_a_diff_measured() {
    println!("\n  n        edits |        diff reads   time |   full-scan reads     time");
    for n in [20_000usize, 200_000] {
        for k in [1usize, 10, 1000] {
            let p = pair(ordered_map(n), appended(n, k));
            let want = reference(&p.ma, &p.mb, &Range::default());
            assert_eq!(want.len(), k);

            let c = counting(&p.blocks);
            let t = std::time::Instant::now();
            let (got, _, _) = all_pages(&c, &p.a, &p.b, &Range::default()).unwrap();
            let fast = t.elapsed();
            let fast_reads = c.reads.borrow().len();
            assert_eq!(got.len(), k);

            let c = counting(&p.blocks);
            let t = std::time::Instant::now();
            let slow = scan_both(&c, &p.a, &p.b);
            let slow_time = t.elapsed();
            let slow_reads = c.reads.borrow().len();
            assert_eq!(slow, k, "the control must find the same changes");

            println!(
                "  {n:<7} {k:>5} | {fast_reads:>6} reads {fast:>10?} | {slow_reads:>6} reads {slow_time:>10?} | {:>5}x",
                slow_reads / fast_reads.max(1)
            );
            // A diff is a different SHAPE, not a faster scan: its cost follows
            // the change and the scan's follows the tree. The 1000-edit rows
            // are the honest limit of that — a thousand changes really do touch
            // a lot of leaves, and the gap narrows because the work is real.
            assert!(fast_reads < slow_reads, "a diff must read less than a scan");
            if k == 1 {
                assert!(
                    fast_reads * 50 < slow_reads,
                    "one changed record must cost a path, not a tree"
                );
            }
        }
    }
}

/// The control: read every entry of both trees and merge them. This is what
/// "what changed?" costs without a structural diff.
fn scan_both<B: Blocks>(blocks: &B, a: &Cid, b: &Cid) -> usize {
    let entries = |root: &Cid| -> Vec<(Vec<u8>, Vec<u8>)> {
        let mut out: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
        let mut after: Option<Vec<u8>> = None;
        loop {
            let r = Range {
                after: after.clone(),
                ..Range::default()
            };
            let page = freenet_prolly::range::range(blocks, root, &r).unwrap();
            for (k, v) in &page.entries {
                out.push((
                    k.clone(),
                    match v {
                        Value::Inline(x) => x.to_vec(),
                        Value::Ref { cid, .. } => blocks.get(cid).unwrap().to_vec(),
                    },
                ));
            }
            match page.next {
                Some(n) => after = Some(n),
                None => break,
            }
        }
        out
    };
    let (ea, eb) = (entries(a), entries(b));
    let ma: Map = ea.into_iter().collect();
    let mb: Map = eb.into_iter().collect();
    ma.iter().filter(|(k, v)| mb.get(*k) != Some(v)).count()
        + mb.iter().filter(|(k, _)| !ma.contains_key(*k)).count()
}
