//! The read gate: a scan must equal the reference map for every range, resume
//! by key across a tree that changes under it, never skip a hole, and read only
//! what it needs. `cargo test --test range -- --nocapture` prints the
//! measurements.

#[path = "common/dataset.rs"]
mod common;
use common::{dataset, rng};

use freenet_prolly::apply::{apply, Edit};
use freenet_prolly::build::TreeBuilder;
use freenet_prolly::cursor::Cursor;
use freenet_prolly::node::{Node, Value, MAX_INLINE};
use freenet_prolly::range::{range, range_with, value_bytes, Options, Range, RangeError, MAX_NEED};
use freenet_prolly::store::{Blocks, MemBlocks, ReadError};
use freenet_prolly::{block_id, kind, Cid};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};
use std::ops::Bound;

type Map = BTreeMap<Vec<u8>, Vec<u8>>;
type Pairs = Vec<(Vec<u8>, Vec<u8>)>;

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

/// Build `m` into a tree, keeping the nodes AND the blocks of values too large
/// to inline — a scan must be able to materialise either kind.
fn scratch(m: &Map) -> (Cid, MemBlocks) {
    let mut store = MemBlocks::default();
    let mut t = TreeBuilder::new(|c, b: &[u8]| store.insert(c, b));
    for (k, v) in m {
        t.push(k, value_of(v)).unwrap();
    }
    let root = t.finish().unwrap();
    for v in m.values() {
        if v.len() > MAX_INLINE {
            store.insert(block_id(kind::RAW, v), v);
        }
    }
    (root, store)
}

/// A block source that records every id it was asked for.
struct Counting<'a> {
    inner: &'a MemBlocks,
    reads: RefCell<HashSet<Cid>>,
}
impl Blocks for Counting<'_> {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        self.reads.borrow_mut().insert(*cid);
        self.inner.get(cid)
    }
}
fn counting(inner: &MemBlocks) -> Counting<'_> {
    Counting {
        inner,
        reads: RefCell::default(),
    }
}

/// A value as bytes, wherever it lives.
fn take(blocks: &impl Blocks, v: &Value<'_>) -> Vec<u8> {
    match v {
        Value::Inline(b) => b.to_vec(),
        Value::Ref { cid, len } => value_bytes(blocks, cid, *len).unwrap().to_vec(),
    }
}

/// The oracle. `BTreeMap::range` panics on a backwards or empty-excluded range,
/// which is a legal thing to ASK this library, so those are screened first.
fn reference(m: &Map, r: &Range) -> Pairs {
    let empty = match (&r.lo, &r.hi) {
        (Bound::Unbounded, _) | (_, Bound::Unbounded) => false,
        (Bound::Included(a), Bound::Included(b)) => a > b,
        (Bound::Included(a), Bound::Excluded(b))
        | (Bound::Excluded(a), Bound::Included(b))
        | (Bound::Excluded(a), Bound::Excluded(b)) => a >= b,
    };
    if empty {
        return Vec::new();
    }
    let mut v: Pairs = m
        .range((r.lo.clone(), r.hi.clone()))
        .map(|(k, val)| (k.clone(), val.clone()))
        .collect();
    if r.reverse {
        v.reverse();
    }
    if let Some(a) = &r.after {
        v.retain(|(k, _)| if r.reverse { k < a } else { k > a });
    }
    v
}

/// Page through a warm store until finished; returns the entries and the page
/// count. A warm scan must never name a block.
fn scan(blocks: &impl Blocks, root: &Cid, r: &Range) -> (Pairs, usize) {
    let mut out = Pairs::new();
    let mut req = r.clone();
    let mut pages = 0;
    loop {
        let p = range(blocks, root, &req).expect("warm scan");
        pages += 1;
        assert!(
            p.need.is_empty(),
            "a warm scan asked for blocks: {:?}",
            p.need.len()
        );
        for (k, v) in &p.entries {
            out.push((k.clone(), take(blocks, v)));
        }
        let done = p.finished();
        // `next == None` with blocks still needed means "ask again as you were";
        // only a key moves the cursor on.
        if let Some(k) = p.next.clone() {
            req.after = Some(k);
        }
        drop(p);
        if done {
            break;
        }
        assert!(pages < 100_000, "scan did not terminate");
    }
    (out, pages)
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Compare, and report the first difference rather than two whole vectors —
/// a 20,000-entry mismatch printed in full tells you nothing.
#[track_caller]
fn same(got: &Pairs, want: &Pairs, what: &str) {
    if got == want {
        return;
    }
    let at = got
        .iter()
        .zip(want.iter())
        .position(|(a, b)| a != b)
        .unwrap_or(got.len().min(want.len()));
    let show = |v: &Pairs, i: usize| {
        v.get(i)
            .map(|(k, val)| format!("{} ({} B)", hex(k), val.len()))
            .unwrap_or_else(|| "<end>".into())
    };
    panic!(
        "{what}: got {} entries, want {}; first difference at {at}: got {} want {}",
        got.len(),
        want.len(),
        show(got, at),
        show(want, at)
    );
}

fn all(m: &Map) -> Pairs {
    m.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
}

fn bounds(keys: &[Vec<u8>], r: &mut impl FnMut() -> u64) -> (Bound<Vec<u8>>, Bound<Vec<u8>>) {
    let pick = |r: &mut dyn FnMut() -> u64| -> Bound<Vec<u8>> {
        let k = keys[r() as usize % keys.len()].clone();
        match r() % 5 {
            0 => Bound::Unbounded,
            1 => Bound::Included(k),
            2 => Bound::Excluded(k),
            // between two keys, and outside every key
            3 => {
                let mut b = k;
                b.push(0);
                Bound::Included(b)
            }
            _ => Bound::Excluded(vec![0xff; 3]),
        }
    };
    let (a, b) = (pick(r), pick(r));
    // Keep them in order often enough to exercise non-empty ranges, but not
    // always: a backwards range is a legal question with an empty answer.
    match (&a, &b) {
        (Bound::Included(x) | Bound::Excluded(x), Bound::Included(y) | Bound::Excluded(y))
            if x > y =>
        {
            (b, a)
        }
        _ => (a, b),
    }
}

#[test]
fn random_ranges_match_the_reference_map() {
    let m: Map = dataset(4, 20_000).into_iter().collect();
    let (root, store) = scratch(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let mut r = rng(31);
    let mut checked = 0;
    for _ in 0..400 {
        let (lo, hi) = bounds(&keys, &mut r);
        for reverse in [false, true] {
            let req = Range {
                lo: lo.clone(),
                hi: hi.clone(),
                reverse,
                after: r()
                    .is_multiple_of(3)
                    .then(|| keys[r() as usize % keys.len()].clone()),
                max_entries: 1 + (r() % 400) as usize,
                max_bytes: 1 + (r() % 40_000) as usize,
            };
            let (got, _) = scan(&store, &root, &req);
            same(&got, &reference(&m, &req), &format!("range {req:?}"));
            checked += 1;
        }
    }
    println!("{checked} random ranges matched the reference map");
    assert_eq!(checked, 800);
}

#[test]
fn named_boundary_cases() {
    let m: Map = dataset(5, 4000).into_iter().collect();
    let (root, store) = scratch(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let k = |i: usize| keys[i].clone();
    let mut after_first = k(0);
    after_first.push(0);

    let cases: Vec<(&str, Range)> = vec![
        ("whole tree", Range::default()),
        (
            "single key, included",
            Range {
                lo: Bound::Included(k(100)),
                hi: Bound::Included(k(100)),
                ..Range::default()
            },
        ),
        (
            "single key, excluded both ends",
            Range {
                lo: Bound::Excluded(k(100)),
                hi: Bound::Excluded(k(100)),
                ..Range::default()
            },
        ),
        (
            "empty: lo above hi",
            Range {
                lo: Bound::Included(k(900)),
                hi: Bound::Included(k(100)),
                ..Range::default()
            },
        ),
        (
            "between two keys",
            Range {
                lo: Bound::Included(after_first.clone()),
                hi: Bound::Excluded(k(3)),
                ..Range::default()
            },
        ),
        (
            "below every key",
            Range {
                hi: Bound::Excluded(vec![0]),
                ..Range::default()
            },
        ),
        (
            "above every key",
            Range {
                lo: Bound::Excluded(vec![0xff; 40]),
                ..Range::default()
            },
        ),
        (
            "excluded lo equals a key",
            Range {
                lo: Bound::Excluded(k(500)),
                hi: Bound::Included(k(520)),
                ..Range::default()
            },
        ),
        (
            "excluded hi equals a key",
            Range {
                lo: Bound::Included(k(500)),
                hi: Bound::Excluded(k(520)),
                ..Range::default()
            },
        ),
    ];
    for (what, req) in cases {
        for reverse in [false, true] {
            let req = Range {
                reverse,
                ..req.clone()
            };
            let (got, _) = scan(&store, &root, &req);
            same(
                &got,
                &reference(&m, &req),
                &format!("{what} (reverse {reverse})"),
            );
        }
    }

    // The empty tree and a tree of one leaf.
    for n in [0usize, 1, 3] {
        let m: Map = dataset(6, n).into_iter().collect();
        let (root, store) = scratch(&m);
        for reverse in [false, true] {
            let req = Range {
                reverse,
                ..Range::default()
            };
            let (got, _) = scan(&store, &root, &req);
            same(&got, &reference(&m, &req), &format!("tree of {n}"));
        }
    }
}

/// Leaves of the tree for `m`, in key order, as (first key, last key).
fn leaves(store: &MemBlocks) -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut v: Vec<_> = store
        .0
        .values()
        .filter_map(|b| Node::parse(b).ok())
        .filter(|n| n.is_leaf() && !n.is_empty())
        .map(|n| (n.key(0), n.key(n.len() - 1)))
        .collect();
    v.sort();
    v
}

/// A range whose `lo` falls after the last entry of the leaf that would hold it
/// must step to the next leaf — exactly once, and only then.
#[test]
fn a_range_starting_past_a_leafs_last_entry_reads_one_extra_leaf() {
    let m: Map = dataset(7, 6000).into_iter().collect();
    let (root, store) = scratch(&m);
    let lv = leaves(&store);
    assert!(lv.len() > 20);
    // A key above leaf 5's last entry and below leaf 6's first.
    let mut gap = lv[5].1.clone();
    gap.push(0);
    assert!(gap < lv[6].0 && !m.contains_key(&gap));

    let req = Range {
        lo: Bound::Included(gap),
        hi: Bound::Included(lv[6].1.clone()),
        max_entries: 10_000,
        ..Range::default()
    };
    let c = counting(&store);
    let p = range(&c, &root, &req).unwrap();
    let got: Pairs = p
        .entries
        .iter()
        .map(|(k, v)| (k.clone(), take(&c, v)))
        .collect();
    drop(p);
    same(&got, &reference(&m, &req), "start past a leaf");
    let leaf_reads = c
        .reads
        .borrow()
        .iter()
        .filter(|id| {
            store
                .0
                .get(*id)
                .and_then(|b| Node::parse(b).ok())
                .is_some_and(|n| n.is_leaf())
        })
        .count();
    println!("start-past-leaf: {leaf_reads} leaves read");
    // The leaf that COULD hold the start key, then the one that actually does:
    // one extra read, and no more — the leaf after the range is never touched,
    // because the ancestors already give its smallest key.
    assert_eq!(leaf_reads, 2, "exactly one extra edge read");
}

#[test]
fn a_scan_reads_no_leaf_outside_its_range() {
    let m: Map = dataset(8, 20_000).into_iter().collect();
    let (root, store) = scratch(&m);
    let lv = leaves(&store);
    let (lo, hi) = (lv[10].0.clone(), lv[14].1.clone());
    let req = Range {
        lo: Bound::Included(lo.clone()),
        hi: Bound::Included(hi.clone()),
        max_entries: 1_000_000,
        max_bytes: usize::MAX,
        ..Range::default()
    };
    let c = counting(&store);
    let p = range(&c, &root, &req).unwrap();
    let served = p.entries.len();
    drop(p);
    let read_leaves: Vec<(Vec<u8>, Vec<u8>)> = c
        .reads
        .borrow()
        .iter()
        .filter_map(|id| store.0.get(id).and_then(|b| Node::parse(b).ok()))
        .filter(|n| n.is_leaf())
        .map(|n| (n.key(0), n.key(n.len() - 1)))
        .collect();
    let outside = read_leaves
        .iter()
        .filter(|(a, b)| *b < lo || *a > hi)
        .count();
    println!(
        "in-range scan: {served} entries, {} leaves read, {outside} outside the range",
        read_leaves.len()
    );
    assert_eq!(outside, 0, "read a leaf wholly outside the range");
    assert!(read_leaves.len() <= 5 + 1);

    // Control: a full scan reads every leaf, so the assertion above is about
    // the range and not about scans reading little in general.
    let c = counting(&store);
    let p = range(
        &c,
        &root,
        &Range {
            max_entries: 1_000_000,
            max_bytes: usize::MAX,
            ..Range::default()
        },
    )
    .unwrap();
    drop(p);
    let full = c
        .reads
        .borrow()
        .iter()
        .filter_map(|id| store.0.get(id).and_then(|b| Node::parse(b).ok()))
        .filter(|n| n.is_leaf())
        .count();
    println!("full scan control: {full} leaves read");
    assert_eq!(full, lv.len(), "the control must read every leaf");
}

#[test]
fn paging_and_the_progress_rule() {
    let m: Map = dataset(9, 5000).into_iter().collect();
    let (root, store) = scratch(&m);
    let want = all(&m);
    let mut r = rng(17);
    for _ in 0..30 {
        let req = Range {
            max_entries: 1 + (r() % 50) as usize,
            max_bytes: 1 + (r() % 2000) as usize,
            reverse: r().is_multiple_of(2),
            ..Range::default()
        };
        let (got, pages) = scan(&store, &root, &req);
        let mut expect = want.clone();
        if req.reverse {
            expect.reverse();
        }
        same(&got, &expect, &format!("paging {req:?}"));
        assert!(pages > 1);
    }

    // Progress: one entry larger than the whole byte limit is still served.
    let big = m
        .iter()
        .max_by_key(|(k, v)| k.len() + v.len())
        .map(|(k, _)| k.clone())
        .unwrap();
    let req = Range {
        lo: Bound::Included(big.clone()),
        max_bytes: 1,
        max_entries: 10,
        ..Range::default()
    };
    let p = range(&store, &root, &req).unwrap();
    assert_eq!(p.entries.len(), 1, "a page must make progress");
    assert_eq!(p.entries[0].0, big);
    drop(p);
    // And the whole scan still completes one entry at a time.
    let (got, pages) = scan(&store, &root, &req);
    same(&got, &reference(&m, &req), "one entry per page");
    // One entry per page. The last page either ends the range itself or is
    // followed by one empty page — both are correct, and which one depends on
    // whether the range's end coincides with a leaf's.
    assert!(
        (got.len()..=got.len() + 1).contains(&pages),
        "{pages} pages for {} entries",
        got.len()
    );

    // A limit of zero is a caller mistake, not an empty page.
    assert_eq!(
        range(
            &store,
            &root,
            &Range {
                max_entries: 0,
                ..Range::default()
            }
        )
        .err(),
        Some(RangeError::NoLimit)
    );
}

#[test]
fn prefixes() {
    let mut m: Map = Map::new();
    for k in [
        &b"a"[..],
        b"a\x00",
        b"ab",
        b"a\xff",
        b"a\xff\x00",
        b"a\xff\xff",
        b"a\xff\xff\x00",
        b"b",
        b"b\x00",
        &[0xff],
        &[0xff, 0xff],
    ] {
        m.insert(k.to_vec(), vec![1, 2, 3]);
    }
    let (root, store) = scratch(&m);
    for p in [
        &b"a"[..],
        b"a\xff",
        b"a\xff\xff",
        b"b",
        b"",
        &[0xff],
        &[0xff, 0xff],
        b"zz",
    ] {
        let req = Range::prefix(p);
        let (got, _) = scan(&store, &root, &req);
        let want: Pairs = m
            .iter()
            .filter(|(k, _)| k.starts_with(p))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        same(&got, &want, &format!("prefix {p:?}"));
    }
    // `a\xff` must stop at `b`, not run to the end of the tree.
    assert!(matches!(Range::prefix(b"a\xff").hi, Bound::Excluded(ref h) if h == b"b"));
    // An all-0xff prefix and the empty prefix have no successor.
    assert!(matches!(Range::prefix(b"").hi, Bound::Unbounded));
    assert!(matches!(Range::prefix(&[0xff, 0xff]).hi, Bound::Unbounded));
    // A prefix longer than any key can be: an empty answer, not everything.
    let long = vec![b'a'; 600];
    let (got, _) = scan(&store, &root, &Range::prefix(&long));
    assert!(got.is_empty(), "no key can start with an over-long prefix");
    // A prefix equal to a key includes that key.
    let (got, _) = scan(&store, &root, &Range::prefix(b"ab"));
    assert_eq!(got, vec![(b"ab".to_vec(), vec![1, 2, 3])]);
}

#[test]
fn a_page_resumes_into_a_newer_tree() {
    let mut m: Map = dataset(10, 8000).into_iter().collect();
    let (root_a, mut store) = scratch(&m);
    for reverse in [false, true] {
        let req = Range {
            max_entries: 700,
            reverse,
            ..Range::default()
        };
        let p = range(&store, &root_a, &req).unwrap();
        let first: Pairs = p
            .entries
            .iter()
            .map(|(k, v)| (k.clone(), take(&store, v)))
            .collect();
        let next = p.next.clone();
        drop(p);
        assert!(next.is_some());

        // Change the tree between pages: edits before, inside and after the
        // page already served.
        let mut m2 = m.clone();
        let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
        let batch: Vec<(Vec<u8>, Edit)> = vec![
            (keys[10].clone(), Edit::Delete),
            (keys[900].clone(), Edit::Put(vec![9; 40])),
            (keys[5000].clone(), Edit::Delete),
        ];
        let mut out = Vec::new();
        let root_b = apply(&store, &root_a, &batch, |c, b| out.push((c, b.to_vec())))
            .unwrap()
            .root;
        for (c, b) in &out {
            store.insert(*c, b);
        }
        for (k, e) in &batch {
            match e {
                Edit::Put(v) => m2.insert(k.clone(), v.clone()),
                Edit::Delete => m2.remove(k),
            };
        }

        // Page 2 onwards, on the NEW root, from the same key.
        let rest = Range {
            after: next,
            ..req.clone()
        };
        let (tail, _) = scan(&store, &root_b, &rest);
        same(
            &tail,
            &reference(&m2, &rest),
            &format!("resumed page (reverse {reverse})"),
        );
        // The two halves are exactly the old page plus the new tree from there.
        assert_eq!(first.len(), 700);
        m = dataset(10, 8000).into_iter().collect();
    }
}

/// Start holding only the root; fetch exactly what each page names.
#[test]
fn a_cold_scan_resumes_round_by_round() {
    let m: Map = dataset(11, 20_000).into_iter().collect();
    let (root, full) = scratch(&m);
    let lv = leaves(&full);
    let height = Node::parse(&full.0[&root]).unwrap().level() as usize + 1;
    println!(
        "cold scan: {} entries, {} leaves, height {height}",
        m.len(),
        lv.len()
    );

    for (what, req, first_page_only) in [
        (
            "whole tree",
            Range {
                max_entries: 1_000_000,
                max_bytes: usize::MAX,
                ..Range::default()
            },
            false,
        ),
        (
            "whole tree, pages of 20",
            Range {
                max_entries: 20,
                ..Range::default()
            },
            false,
        ),
        (
            // The real shape of "the latest 20 posts": one page, then stop.
            "latest 20 (first page)",
            Range {
                reverse: true,
                max_entries: 20,
                ..Range::default()
            },
            true,
        ),
    ] {
        let mut held = MemBlocks::default();
        held.insert(root, &full.0[&root]);
        let mut got = Pairs::new();
        let (mut rounds, mut fetched, mut widest, mut pages) = (0usize, 0usize, 0usize, 0usize);
        let mut req = req.clone();
        loop {
            let p = range(&held, &root, &req).unwrap();
            pages += 1;
            for (k, v) in &p.entries {
                // Value blocks are fetched on demand, like any other block.
                let v = match v {
                    Value::Inline(b) => b.to_vec(),
                    Value::Ref { cid, len } => match value_bytes(&held, cid, *len) {
                        Ok(b) => b.to_vec(),
                        Err(ReadError::Need(_)) => full.0[cid].clone(),
                        Err(e) => panic!("{e:?}"),
                    },
                };
                got.push((k.clone(), v));
            }
            let (need, next, done) = (p.need.clone(), p.next.clone(), p.finished());
            drop(p);
            assert!(need.len() <= MAX_NEED, "need is capped at {MAX_NEED}");
            if done {
                break;
            }
            if !need.is_empty() {
                rounds += 1;
                fetched += need.len();
                widest = widest.max(need.len());
                for id in &need {
                    held.insert(*id, &full.0[id]);
                }
            }
            if let Some(k) = next {
                req.after = Some(k);
            }
            if first_page_only && got.len() >= req.max_entries {
                break;
            }
            assert!(pages < 100_000, "cold scan did not terminate");
        }
        let mut want = reference(&m, &req_of(&req));
        if first_page_only {
            want.truncate(got.len());
        }
        same(&got, &want, what);
        println!(
            "  {what:24}: {pages} pages, {rounds} fetch rounds, {fetched} blocks, widest {widest}"
        );
        if first_page_only {
            assert!(
                rounds <= height,
                "{rounds} rounds to serve one page of 20 (height {height})"
            );
            assert!(fetched <= 8, "{fetched} blocks to serve 20 entries");
        }
        if what == "whole tree" {
            let ceiling = lv.len().div_ceil(MAX_NEED) + height;
            assert!(
                rounds <= ceiling,
                "{rounds} rounds > ceil(leaves/{MAX_NEED}) + height = {ceiling}"
            );
        }
    }
}

/// The request as first asked, with `after` cleared — what the reference covers.
fn req_of(r: &Range) -> Range {
    Range {
        after: None,
        ..r.clone()
    }
}

/// A small limit must not drag a whole round of leaves in. This is the reason
/// the frontier is bounded by the aggregates at all.
#[test]
fn a_small_limit_names_few_blocks_and_the_control_names_many() {
    let m: Map = dataset(12, 20_000).into_iter().collect();
    let (root, full) = scratch(&m);

    let named = |opts: Options| -> usize {
        // Hold the root and its descendants down to the leaves, so the branches
        // can name a frontier but no leaf is available.
        let mut held = MemBlocks::default();
        let mut frontier = vec![root];
        while let Some(id) = frontier.pop() {
            let n = Node::parse(&full.0[&id]).unwrap();
            if n.is_leaf() {
                continue;
            }
            held.insert(id, &full.0[&id]);
            for i in 0..n.len() {
                frontier.push(n.child(i).0);
            }
        }
        let req = Range {
            reverse: true,
            max_entries: 20,
            ..Range::default()
        };
        let p = range_with(opts, &held, &root, &req).unwrap();
        let n = p.need.len();
        assert!(
            p.entries.is_empty(),
            "no leaf is held, so nothing is served"
        );
        assert!(n >= 1, "the first missing block is always named");
        n
    };

    let bounded = named(Options::default());
    let unbounded = named(Options { agg_bound: false });
    println!("latest-20 frontier: {bounded} blocks named, control names {unbounded}");
    assert!(
        bounded <= 4,
        "{bounded} blocks to serve 20 entries is not a bound"
    );
    assert_eq!(unbounded, MAX_NEED, "the control must fill the frontier");
    assert!(unbounded > bounded * 4);
}

/// The cursor is public and usable on its own; it must agree with the map.
#[test]
fn the_cursor_walks_the_tree_in_both_directions() {
    let m: Map = dataset(13, 3000).into_iter().collect();
    let (root, store) = scratch(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();

    let mut c = Cursor::seek(&store, &root, &[]).unwrap();
    let mut forward = Vec::new();
    while let Some((k, _)) = c.peek() {
        forward.push(k);
        if !c.next().unwrap() {
            break;
        }
    }
    assert_eq!(forward, keys);

    let mut c = Cursor::seek_last(&store, &root).unwrap();
    let mut back = Vec::new();
    while let Some((k, _)) = c.peek() {
        back.push(k);
        if !c.prev().unwrap() {
            break;
        }
    }
    back.reverse();
    assert_eq!(back, keys);

    // seek / seek_before land where the map says, including between keys and
    // outside both ends.
    let mut r = rng(5);
    for _ in 0..300 {
        let i = r() as usize % keys.len();
        let probe = match r() % 3 {
            0 => keys[i].clone(),
            1 => {
                let mut k = keys[i].clone();
                k.push(0);
                k
            }
            _ => vec![0xff; 3],
        };
        let c = Cursor::seek(&store, &root, &probe).unwrap();
        assert_eq!(
            c.peek().map(|(k, _)| k),
            m.range(probe.clone()..).next().map(|(k, _)| k.clone())
        );
        let c = Cursor::seek_before(&store, &root, &probe).unwrap();
        assert_eq!(
            c.peek().map(|(k, _)| k),
            m.range(..probe.clone()).next_back().map(|(k, _)| k.clone())
        );
    }
}

/// `need` and `next` are things this library ASSERTS to its caller, and a tree
/// is not always honest: a branch can record child aggregates that lie.
/// `load_child` catches a child whose own aggregate disagrees with its parent —
/// but the frontier is named from the PARENT's numbers, before any child is
/// loaded, so inflated aggregates are believed while the frontier is built.
///
/// What must hold anyway: the page never names more than the cap, never names a
/// block outside the range, and the scan still terminates and serves exactly
/// the entries the honest leaves hold.
#[test]
fn a_branch_with_lying_aggregates_cannot_make_a_scan_misbehave() {
    use freenet_prolly::node::{Agg, NodeBuilder};
    let m: Map = dataset(14, 6000).into_iter().collect();
    let (root, full) = scratch(&m);

    // Rebuild the root with every child aggregate set to 1 entry / 1 byte, so
    // the frontier believes each subtree is nearly empty.
    let r = Node::parse(&full.0[&root]).unwrap();
    assert!(!r.is_leaf() && r.len() > 2);
    let mut b = NodeBuilder::branch(r.level());
    for i in 0..r.len() {
        let (cid, _) = r.child(i);
        b.push_child(&r.key(i), cid, Agg { count: 1, bytes: 1 })
            .unwrap();
    }
    let liar = b.finish().unwrap();
    let liar_id = block_id(kind::TREE_NODE, &liar);
    let mut held = MemBlocks::default();
    held.insert(liar_id, &liar);

    let req = Range {
        max_entries: 50,
        ..Range::default()
    };
    let p = range(&held, &liar_id, &req).unwrap();
    println!(
        "lying root: {} entries served, {} blocks named",
        p.entries.len(),
        p.need.len()
    );
    assert!(p.need.len() <= MAX_NEED, "the cap holds whatever agg says");
    assert!(!p.need.is_empty());
    let named: HashSet<Cid> = p.need.iter().copied().collect();
    drop(p);
    // Every named block is a real child of the range, not an invented id.
    let children: HashSet<Cid> = (0..r.len()).map(|i| r.child(i).0).collect();
    assert!(named.is_subset(&children), "named a block outside the tree");

    // Feeding the frontier still converges, and the entries are the honest ones
    // — the aggregates were believed for BUDGETING and never for content.
    let mut got = Pairs::new();
    let mut req = req.clone();
    let mut rounds = 0;
    loop {
        let p = match range(&held, &liar_id, &req) {
            Ok(p) => p,
            // A child whose recorded aggregate disagrees with the child itself
            // is refused by `load_child`; that is the honest outcome here.
            Err(RangeError::Read(ReadError::Mismatch(_))) => {
                println!("lying root: refused by load_child once a child was loaded");
                return;
            }
            Err(e) => panic!("{e:?}"),
        };
        for (k, v) in &p.entries {
            got.push((k.clone(), take(&held, v)));
        }
        let (need, next, done) = (p.need.clone(), p.next.clone(), p.finished());
        drop(p);
        if done {
            break;
        }
        for id in &need {
            held.insert(*id, &full.0[id]);
        }
        if let Some(k) = next {
            req.after = Some(k);
        }
        rounds += 1;
        assert!(rounds < 10_000, "a lying tree made the scan loop");
    }
    same(&got, &all(&m), "served entries must be the honest ones");
}

/// Every node of the tree with the key span it covers, computed by walking the
/// store from the root — an oracle that owes nothing to `range`.
fn spans(store: &MemBlocks, root: &Cid) -> Vec<(Cid, Vec<u8>, Vec<u8>, bool)> {
    fn go(store: &MemBlocks, id: Cid, out: &mut Vec<(Cid, Vec<u8>, Vec<u8>, bool)>) {
        let n = Node::parse(&store.0[&id]).unwrap();
        if n.is_empty() {
            return;
        }
        if n.is_leaf() {
            out.push((id, n.key(0), n.key(n.len() - 1), true));
            return;
        }
        let before = out.len();
        for i in 0..n.len() {
            go(store, n.child(i).0, out);
        }
        // A branch covers whatever its children cover.
        let lo = out[before..].iter().map(|s| s.1.clone()).min().unwrap();
        let hi = out[before..].iter().map(|s| s.2.clone()).max().unwrap();
        out.push((id, lo, hi, false));
    }
    let mut out = Vec::new();
    go(store, *root, &mut out);
    out
}

/// `need` is an assertion this library makes to its caller, and every id in it
/// becomes a network GET. Naming a block the scan can never use is invisible —
/// the entries still come out right — so it is asserted directly: every id ever
/// named must be a node whose key span overlaps the range.
#[test]
fn a_scan_never_names_a_block_outside_its_range() {
    let m: Map = dataset(15, 20_000).into_iter().collect();
    let (root, full) = scratch(&m);
    let lv = leaves(&full);
    let spans = spans(&full, &root);
    assert!(lv.len() > 500 && spans.len() > lv.len());

    let mid = lv.len() / 2;
    let cases: Vec<(&str, Vec<u8>, Vec<u8>)> = vec![
        // inside a single leaf
        ("inside one leaf", lv[mid].0.clone(), lv[mid].1.clone()),
        // spanning three leaves in the middle
        ("three leaves", lv[mid].0.clone(), lv[mid + 2].1.clone()),
        // at each end of the tree
        ("first leaf", lv[0].0.clone(), lv[0].1.clone()),
        (
            "last leaf",
            lv[lv.len() - 1].0.clone(),
            lv[lv.len() - 1].1.clone(),
        ),
    ];
    for (what, lo, hi) in cases {
        for reverse in [false, true] {
            // No limit, so the aggregate bound cannot mask an over-wide frontier.
            let req = Range {
                lo: Bound::Included(lo.clone()),
                hi: Bound::Included(hi.clone()),
                reverse,
                max_entries: 1_000_000,
                max_bytes: usize::MAX,
                ..Range::default()
            };
            let mut held = MemBlocks::default();
            held.insert(root, &full.0[&root]);
            let mut named: HashSet<Cid> = HashSet::new();
            let mut got = Pairs::new();
            let mut req = req;
            let mut pages = 0;
            loop {
                let p = range(&held, &root, &req).unwrap();
                pages += 1;
                for (k, v) in &p.entries {
                    got.push((k.clone(), take(&full, v)));
                }
                let (need, next, done) = (p.need.clone(), p.next.clone(), p.finished());
                drop(p);
                if done {
                    break;
                }
                for id in &need {
                    named.insert(*id);
                    held.insert(*id, &full.0[id]);
                }
                if let Some(k) = next {
                    req.after = Some(k);
                }
                assert!(pages < 10_000, "{what}: did not terminate");
            }
            same(&got, &reference(&m, &req_of(&req)), what);

            // Every named block overlaps the range, by the oracle's spans.
            let outside: Vec<String> = named
                .iter()
                .map(|id| {
                    spans
                        .iter()
                        .find(|(s, ..)| s == id)
                        .unwrap_or_else(|| panic!("{what}: named an id that is not in the tree"))
                })
                .filter(|(_, smin, smax, _)| *smax < lo || *smin > hi)
                .map(|(_, smin, smax, leaf)| {
                    format!(
                        "{}{}..{}",
                        if *leaf { "leaf " } else { "branch " },
                        hex(smin),
                        hex(smax)
                    )
                })
                .collect();
            assert!(
                outside.is_empty(),
                "{what} (reverse {reverse}): named {} blocks outside the range: {:?}",
                outside.len(),
                &outside[..outside.len().min(4)]
            );

            // And no more than the overlapping nodes exist to be fetched.
            let overlapping = spans
                .iter()
                .filter(|(_, smin, smax, _)| !(*smax < lo || *smin > hi))
                .count();
            assert!(
                named.len() <= overlapping,
                "{what}: fetched {} blocks, only {overlapping} overlap the range",
                named.len()
            );
            if !reverse && what == "three leaves" {
                println!(
                    "  {what:16}: {} blocks fetched, {overlapping} overlap the range",
                    named.len()
                );
            }
        }
    }
}

/// `value_bytes` is the other assertion this library makes: it hands back bytes
/// and says they are the value. Nothing tested it.
#[test]
fn value_bytes_checks_what_it_returns() {
    use freenet_prolly::apply::apply;
    // A value too large to inline, written through `apply` and read back out
    // through a scan — the whole path a caller actually takes.
    let mut m: Map = dataset(16, 2000).into_iter().collect();
    let (root, mut store) = scratch(&m);
    let big = vec![0x5au8; 3000];
    let key = m.keys().nth(500).unwrap().clone();
    let mut out = Vec::new();
    let root = apply(
        &store,
        &root,
        &[(key.clone(), Edit::Put(big.clone()))],
        |c, b| out.push((c, b.to_vec())),
    )
    .unwrap()
    .root;
    for (c, b) in &out {
        store.insert(*c, b);
    }
    m.insert(key.clone(), big.clone());

    let req = Range {
        lo: Bound::Included(key.clone()),
        hi: Bound::Included(key.clone()),
        ..Range::default()
    };
    let p = range(&store, &root, &req).unwrap();
    assert_eq!(p.entries.len(), 1);
    let cid = match p.entries[0].1 {
        Value::Ref { cid, len } => {
            assert_eq!(len as usize, big.len());
            cid
        }
        Value::Inline(_) => panic!("a 3000 B value must live in its own block"),
    };
    drop(p);
    assert_eq!(
        value_bytes(&store, &cid, big.len() as u32).unwrap(),
        &big[..]
    );

    // A length that disagrees with the block is refused, both ways.
    for wrong in [big.len() as u32 - 1, big.len() as u32 + 1, 0] {
        assert_eq!(
            value_bytes(&store, &cid, wrong),
            Err(ReadError::Mismatch(cid)),
            "length {wrong} must not be accepted"
        );
    }
    // A block that is not held names exactly itself.
    let absent = block_id(kind::RAW, b"nobody has this");
    assert_eq!(
        value_bytes(&store, &absent, 15),
        Err(ReadError::Need(vec![absent]))
    );

    // And the claim the doc comment makes: a tree node cannot come back as a
    // value, because an id binds the kind. The same bytes have two different
    // ids, and only the RAW one is what a leaf's `Ref` can carry.
    let node_bytes = store.0[&root].clone();
    assert!(Node::parse(&node_bytes).is_ok());
    let as_node = block_id(kind::TREE_NODE, &node_bytes);
    let as_value = block_id(kind::RAW, &node_bytes);
    assert_eq!(as_node, root, "the root is addressed as a tree node");
    assert_ne!(
        as_node, as_value,
        "kind is hashed into the id, so one body has two ids"
    );
    assert!(
        !store.0.contains_key(&as_value),
        "nothing in the store answers to the RAW id of a node"
    );
}
