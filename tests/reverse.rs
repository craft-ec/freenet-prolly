//! Newest-first listings: the direction every feed uses, and the one a scan
//! could silently truncate.
//!
//! A page may end because it hit its limit, ran out of range, ran out of tree,
//! or could not get a block. Only the last of those leaves work undone, and
//! reporting it as "finished" is a lie a reader cannot detect — the whole point
//! of this file is that no store, however incomplete, can produce one.

#[path = "common/dataset.rs"]
mod common;
use common::{dataset, rng};

use freenet_prolly::apply::{apply_into, Edit};
use freenet_prolly::build::init;
use freenet_prolly::node::Node;
use freenet_prolly::range::{range, Range};
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::Cid;
use std::collections::{BTreeMap, HashSet};
use std::ops::Bound;

type Map = BTreeMap<Vec<u8>, Vec<u8>>;

fn build(m: &Map) -> (MemBlocks, Cid) {
    let mut blocks = MemBlocks::default();
    let root = init(&mut blocks);
    let edits: Vec<(Vec<u8>, Edit)> = m
        .iter()
        .map(|(k, v)| (k.clone(), Edit::Put(v.clone())))
        .collect();
    let root = apply_into(&mut blocks, &root, &edits).unwrap().root;
    (blocks, root)
}

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

/// Every key the range holds, in the order the scan should serve them.
fn expected(m: &Map, r: &Range) -> Vec<Vec<u8>> {
    let mut ks: Vec<Vec<u8>> = m
        .keys()
        .filter(|k| {
            let lo = match &r.lo {
                Bound::Unbounded => true,
                Bound::Included(x) => *k >= x,
                Bound::Excluded(x) => *k > x,
            };
            let hi = match &r.hi {
                Bound::Unbounded => true,
                Bound::Included(x) => *k <= x,
                Bound::Excluded(x) => *k < x,
            };
            let after = match (&r.after, r.reverse) {
                (None, _) => true,
                (Some(a), false) => *k > a,
                (Some(a), true) => *k < a,
            };
            lo && hi && after
        })
        .cloned()
        .collect();
    if r.reverse {
        ks.reverse();
    }
    ks
}

/// THE lie: a page that says it is finished while entries remain.
///
/// A store missing one block may legitimately need it, or may not need it at
/// all — what it may never do is serve nothing, name nothing, and report the
/// listing complete.
fn assert_no_false_finish(full: &MemBlocks, root: &Cid, m: &Map, r: &Range, what: &str) {
    let honest = range(full, root, r).unwrap();
    let mut all = HashSet::new();
    nodes(full, *root, &mut all);
    for missing in all.iter().filter(|c| **c != *root) {
        let mut partial = MemBlocks::default();
        for id in &all {
            if id != missing {
                partial.insert(*id, full.get(id).unwrap());
            }
        }
        let got = match range(&partial, root, r) {
            Ok(p) => p,
            Err(_) => continue,
        };
        if got.entries == honest.entries && got.next == honest.next {
            continue; // the block was not needed for this page
        }
        assert!(
            !(got.entries.is_empty() && got.next.is_none() && got.need.is_empty()),
            "{what}: a store missing one block reported the listing FINISHED \
             with {} entries still in range",
            expected(m, r).len()
        );
        // Any other difference must come with something to fetch.
        assert!(
            !got.need.is_empty(),
            "{what}: a different page with nothing to fetch"
        );
    }
}

/// The architect's repro, as a permanent test: reverse, paged, one block held
/// back at a time.
#[test]
fn a_reverse_page_never_reports_finished_with_entries_left() {
    let m: Map = dataset(21, 8_000).into_iter().collect();
    let (blocks, root) = build(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let mut r = rng(5);
    let mut checked = 0;
    for _ in 0..40 {
        let (a, b) = (r() as usize % keys.len(), r() as usize % keys.len());
        let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
        let limit = 1 + (r() as usize % 40);
        let base = Range {
            lo: Bound::Included(keys[lo].clone()),
            hi: Bound::Included(keys[hi].clone()),
            reverse: true,
            max_entries: limit,
            ..Range::default()
        };
        // Page through it, checking every page's resumption point too.
        let mut after: Option<Vec<u8>> = None;
        for _ in 0..6 {
            let req = Range {
                after: after.clone(),
                ..base.clone()
            };
            assert_no_false_finish(&blocks, &root, &m, &req, "reverse paged");
            let page = range(&blocks, &root, &req).unwrap();
            let want = expected(&m, &req);
            let got: Vec<Vec<u8>> = page.entries.iter().map(|(k, _)| k.clone()).collect();
            assert_eq!(got, want[..got.len()].to_vec(), "honest page wrong");
            checked += 1;
            match page.next {
                Some(n) => after = Some(n),
                None => {
                    assert_eq!(got.len(), want.len(), "finished with entries left");
                    break;
                }
            }
        }
    }
    println!("{checked} reverse pages, every one-block omission checked");
}

/// The same hole without `after`: a bound at an ABSENT key above a leaf's last
/// entry, so a reverse seek steps forward into an out-of-range leaf.
#[test]
fn a_reverse_bound_at_an_absent_key_does_not_truncate() {
    let m: Map = dataset(22, 6_000).into_iter().collect();
    let (blocks, root) = build(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let mut checked = 0;
    for i in [1usize, 47, 500, 1_999, 3_000, 5_998] {
        // A key that is absent and sorts just above keys[i].
        let mut above = keys[i].clone();
        above.push(0x00);
        for r in [
            Range {
                hi: Bound::Included(above.clone()),
                reverse: true,
                max_entries: 25,
                ..Range::default()
            },
            Range {
                hi: Bound::Excluded(above.clone()),
                reverse: true,
                max_entries: 25,
                ..Range::default()
            },
        ] {
            assert_no_false_finish(&blocks, &root, &m, &r, "absent reverse bound");
            let page = range(&blocks, &root, &r).unwrap();
            let want = expected(&m, &r);
            let got: Vec<Vec<u8>> = page.entries.iter().map(|(k, _)| k.clone()).collect();
            assert_eq!(got, want[..got.len().min(want.len())].to_vec());
            assert!(!got.is_empty(), "a bound above a real key served nothing");
            checked += 1;
        }
    }
    println!("{checked} reverse scans from absent bounds");
}

/// Forward and reverse must behave the same way; only the order differs.
#[test]
fn forward_and_reverse_have_parity() {
    let m: Map = dataset(23, 5_000).into_iter().collect();
    let (blocks, root) = build(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    for limit in [1usize, 3, 17, 250] {
        for (lo, hi) in [(0usize, 4_999usize), (100, 400), (2_500, 2_501)] {
            let mut fwd: Vec<Vec<u8>> = Vec::new();
            let mut rev: Vec<Vec<u8>> = Vec::new();
            for reverse in [false, true] {
                let base = Range {
                    lo: Bound::Included(keys[lo].clone()),
                    hi: Bound::Included(keys[hi].clone()),
                    reverse,
                    max_entries: limit,
                    ..Range::default()
                };
                let mut after: Option<Vec<u8>> = None;
                let out = if reverse { &mut rev } else { &mut fwd };
                loop {
                    let req = Range {
                        after: after.clone(),
                        ..base.clone()
                    };
                    let page = range(&blocks, &root, &req).unwrap();
                    assert!(page.need.is_empty(), "a full store needs nothing");
                    out.extend(page.entries.iter().map(|(k, _)| k.clone()));
                    match page.next {
                        Some(n) => after = Some(n),
                        None => break,
                    }
                    assert!(out.len() <= 5_000);
                }
            }
            rev.reverse();
            assert_eq!(fwd, rev, "limit {limit}, keys {lo}..{hi}");
            assert_eq!(fwd, keys[lo..=hi].to_vec());
        }
    }
}

/// Page ends forced onto a leaf boundary, in BOTH directions.
///
/// This is where the frontier is empty and the descent still fails: resuming
/// after a leaf's last key sends a forward scan into that leaf — which now
/// holds nothing in range, so the frontier cannot name it — while the entries
/// that remain are all in the NEXT leaf. Reverse is the mirror. Neither may
/// report the listing finished.
#[test]
fn resuming_exactly_on_a_leaf_boundary_never_finishes_early() {
    let m: Map = dataset(24, 8_000).into_iter().collect();
    let (blocks, root) = build(&m);
    let mut all = HashSet::new();
    nodes(&blocks, root, &mut all);

    // Every leaf, in key order, with its first and last key.
    let mut leaves: Vec<(Vec<u8>, Vec<u8>, Cid)> = all
        .iter()
        .filter_map(|id| {
            let n = Node::parse(&blocks.0[id]).unwrap();
            n.is_leaf().then(|| (n.key(0), n.key(n.len() - 1), *id))
        })
        .collect();
    leaves.sort();
    assert!(leaves.len() > 8);

    let mut checked = 0;
    for i in [1usize, 2, leaves.len() / 2, leaves.len() - 2] {
        let (first, last, id) = leaves[i].clone();
        for (what, reverse, after, missing) in [
            // Forward: resume after this leaf's LAST key. The scan descends
            // into this leaf, which now holds nothing in range.
            ("forward past a leaf's last key", false, last.clone(), id),
            // Reverse: resume before this leaf's FIRST key.
            ("reverse past a leaf's first key", true, first.clone(), id),
        ] {
            let r = Range {
                after: Some(after.clone()),
                reverse,
                max_entries: 30,
                ..Range::default()
            };
            let honest = range(&blocks, &root, &r).unwrap();
            assert!(
                !honest.entries.is_empty(),
                "{what}: the case must serve entries"
            );

            let mut partial = MemBlocks::default();
            for b in all.iter().filter(|b| **b != missing) {
                partial.insert(*b, blocks.get(b).unwrap());
            }
            let got = range(&partial, &root, &r).unwrap();
            assert!(
                !(got.entries.is_empty() && got.next.is_none() && got.need.is_empty()),
                "{what}: reported FINISHED while {} entries remained",
                honest.entries.len()
            );
            assert!(
                !got.finished() || got.entries == honest.entries,
                "{what}: claimed to finish with a different page"
            );
            checked += 1;
        }
    }
    println!("{checked} leaf-boundary resumptions, both directions");
}

/// `finished` must be the SCAN's word. A page that could not get a block says
/// so, whatever its `need` looks like.
#[test]
fn a_blocked_page_is_never_finished() {
    use freenet_prolly::range::PageEnd;
    let m: Map = dataset(25, 4_000).into_iter().collect();
    let (blocks, root) = build(&m);
    let mut all = HashSet::new();
    nodes(&blocks, root, &mut all);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();

    let mut blocked = 0;
    for missing in all.iter().filter(|c| **c != root) {
        let mut partial = MemBlocks::default();
        for id in all.iter().filter(|id| *id != missing) {
            partial.insert(*id, blocks.get(id).unwrap());
        }
        for reverse in [false, true] {
            for after in [None, Some(keys[keys.len() / 2].clone())] {
                let r = Range {
                    reverse,
                    after,
                    max_entries: 40,
                    ..Range::default()
                };
                let p = range(&partial, &root, &r).unwrap();
                if p.end == PageEnd::Blocked {
                    assert!(!p.finished(), "a blocked page called itself finished");
                    blocked += 1;
                } else {
                    // It ended by scanning, so what it served is what the full
                    // store serves for the same request.
                    let honest = range(&blocks, &root, &r).unwrap();
                    let a: Vec<Vec<u8>> = p.entries.iter().map(|(k, _)| k.clone()).collect();
                    let b: Vec<Vec<u8>> = honest.entries.iter().map(|(k, _)| k.clone()).collect();
                    assert_eq!(a, b, "a page that ended by scanning served something else");
                }
            }
        }
    }
    assert!(
        blocked > 0,
        "no page was ever blocked; the test proves nothing"
    );
    println!("{blocked} blocked pages, none of them claimed to be finished");
}

/// The same question put to `diff` and `aggregate`: can either report a
/// complete answer while a block it needed was missing?
///
/// Neither has a "nothing to fetch, so we are done" rule — both reach their end
/// by finishing a walk, and a missing block always produces `need`. Asserted
/// rather than read: this is the shape that hid in `range` for two releases.
#[test]
fn neither_diff_nor_aggregate_can_finish_on_a_missing_block() {
    use freenet_prolly::aggregate::{aggregate, aggregate_verified, AggError};
    use freenet_prolly::diff::{diff, DiffError};
    use freenet_prolly::store::ReadError;

    let m: Map = dataset(26, 4_000).into_iter().collect();
    let (mut blocks, root_a) = build(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let root_b = apply_into(
        &mut blocks,
        &root_a,
        &[(keys[2_000].clone(), Edit::Put(vec![0xab; 150]))],
    )
    .unwrap()
    .root;

    let mut all = HashSet::new();
    nodes(&blocks, root_a, &mut all);
    nodes(&blocks, root_b, &mut all);

    let whole = Range::default();
    let truth_count = aggregate(&blocks, &root_a, &whole).unwrap().agg().count;
    let truth_changes = {
        let p = diff(&blocks, &root_a, &root_b, &whole, None).unwrap();
        p.changes.len()
    };
    assert_eq!(truth_changes, 1);

    let (mut agg_blocked, mut diff_blocked) = (0, 0);
    for missing in all.iter() {
        let mut partial = MemBlocks::default();
        for id in all.iter().filter(|id| *id != missing) {
            partial.insert(*id, blocks.get(id).unwrap());
        }
        // aggregate: a missing block is an error, never a smaller count.
        match aggregate(&partial, &root_a, &whole) {
            Ok(c) => assert_eq!(
                c.agg().count,
                truth_count,
                "aggregate answered with a different count while a block was missing"
            ),
            Err(AggError::Read(ReadError::Need(ids))) => {
                assert!(!ids.is_empty(), "Need with nothing to fetch");
                agg_blocked += 1;
            }
            Err(e) => panic!("{e:?}"),
        }
        let _ = aggregate_verified(&partial, &root_a, &whole);

        // diff: a page is finished only when both walks ended.
        match diff(&partial, &root_a, &root_b, &whole, None) {
            Ok(p) => {
                if p.next.is_none() && p.need.is_empty() {
                    assert_eq!(
                        p.changes.len(),
                        truth_changes,
                        "diff called itself finished with a different answer"
                    );
                } else {
                    diff_blocked += 1;
                }
            }
            Err(DiffError::Read(ReadError::Need(ids))) => {
                assert!(!ids.is_empty(), "Need with nothing to fetch");
                diff_blocked += 1;
            }
            Err(e) => panic!("{e:?}"),
        }
    }
    assert!(
        agg_blocked > 0 && diff_blocked > 0,
        "nothing was ever blocked"
    );
    println!(
        "aggregate blocked {agg_blocked} times, diff {diff_blocked}: neither ever \
         reported a complete answer without the blocks for it"
    );
}
