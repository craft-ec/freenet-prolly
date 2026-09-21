//! freenet-prolly#52: a child's keys must END before whatever follows it.
//!
//! A parent records each child's FIRST key and nothing about its last, so a
//! writer can put `z` in the leaf under `a` and `m` in the next one. Every node
//! parses and passes `check_node`, and the root hash commits to all of it — yet
//! one root then gives two authenticated answers: a range read says `z` is
//! present, a point read (which descends to the child under `m`) says it is
//! absent. Equivocation without a fork.
//!
//! The PROVER is the adversary here, so proofs are assembled by hand: what
//! matters is what the VERIFIER accepts. Two trees:
//!
//! * ADJACENT — the overlap is between two siblings;
//! * ANCESTOR — the same overlap one level up, where the leaf's bound comes
//!   from its GRANDPARENT. An adjacent-only check refuses the first and still
//!   accepts this one; `adjacent_only_check_misses_the_ancestor_variant` is
//!   that negative control, executed.

use freenet_prolly::aggregate::aggregate_verified;
use freenet_prolly::node::{Node, NodeBuilder, Value};
use freenet_prolly::proof::*;
use freenet_prolly::range::{range, Range};
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::{block_id, build, kind, read, Cid};
use std::ops::Bound;

fn id(b: &[u8]) -> Cid {
    block_id(kind::TREE_NODE, b)
}
fn leaf(es: &[(&[u8], &[u8])]) -> Vec<u8> {
    let mut n = NodeBuilder::leaf();
    for (k, v) in es {
        n.push(k, Value::Inline(v)).unwrap();
    }
    n.finish().unwrap()
}
fn branch(level: u8, kids: &[(&[u8], &[u8])]) -> Vec<u8> {
    let mut n = NodeBuilder::branch(level);
    for (k, b) in kids {
        n.push_child(k, id(b), Node::parse(b).unwrap().agg()).unwrap();
    }
    n.finish().unwrap()
}
fn all() -> Range {
    Range::default()
}
fn store(nodes: &[&Vec<u8>]) -> MemBlocks {
    let mut b = MemBlocks::default();
    for n in nodes {
        b.insert(id(n), n);
    }
    b
}

/// A malformed tree: its root, its blocks, and a hand-built range proof over
/// all of it — every node, in the order a read takes them.
struct Bad {
    root: Cid,
    blocks: MemBlocks,
    range_proof: Proof,
    /// The path a point read of `z` takes. It never touches the bad leaf.
    z_proof: Proof,
}

/// `[a→{a,z}, m→{m}]`: `z` sits under `a` although `m` follows.
fn adjacent() -> Bad {
    let (l1, l2) = (leaf(&[(b"a", b"1"), (b"z", b"2")]), leaf(&[(b"m", b"3")]));
    let p = branch(1, &[(b"a", &l1), (b"m", &l2)]);
    Bad {
        root: id(&p),
        blocks: store(&[&l1, &l2, &p]),
        range_proof: Proof { nodes: vec![p.clone(), l1, l2.clone()], value: None },
        z_proof: Proof { nodes: vec![p, l2], value: None },
    }
}

/// `[a→[a→{a,z}], m→[m→{m}]]`: the leaf is the LAST child of its parent, so
/// only the grandparent knows that `m` follows it.
fn ancestor() -> Bad {
    let (la, lm) = (leaf(&[(b"a", b"1"), (b"z", b"2")]), leaf(&[(b"m", b"3")]));
    let (pa, pm) = (branch(1, &[(b"a", &la)]), branch(1, &[(b"m", &lm)]));
    let g = branch(2, &[(b"a", &pa), (b"m", &pm)]);
    Bad {
        root: id(&g),
        blocks: store(&[&la, &lm, &pa, &pm, &g]),
        range_proof: Proof {
            nodes: vec![g.clone(), pa, la, pm.clone(), lm.clone()],
            value: None,
        },
        z_proof: Proof { nodes: vec![g, pm, lm], value: None },
    }
}

fn both() -> [(&'static str, Bad); 2] {
    [("adjacent", adjacent()), ("ancestor", ancestor())]
}

/// The same three entries, built honestly — the control every refusal below
/// is paired with, so a refusal cannot be "everything is refused now".
fn honest() -> (Cid, MemBlocks) {
    let mut b = MemBlocks::default();
    let root = build::build(
        [
            (&b"a"[..], Value::Inline(b"1")),
            (b"m", Value::Inline(b"3")),
            (b"z", Value::Inline(b"2")),
        ],
        |c, x| b.insert(c, x),
    )
    .unwrap();
    (root, b)
}

#[test]
fn a_range_proof_over_an_overlap_is_refused() {
    for (name, t) in both() {
        let got = verify_range_bytes(&t.root, &all(), &t.range_proof.encode());
        assert!(
            got.is_err(),
            "{name}: the verifier accepted a range proof showing {:?} — `z` Present under a root whose point proof says Absent",
            got.map(|p| p.entries.len())
        );
    }
    // CONTROL: an honest proof of the same entries is accepted.
    let (root, b) = honest();
    let page = verify_range_bytes(&root, &all(), &prove_range(&b, &root, &all()).unwrap().encode()).unwrap();
    assert_eq!(page.entries.len(), 3, "CONTROL: the honest range proof");
}

#[test]
fn the_prover_cannot_build_one_either() {
    for (name, t) in both() {
        match prove_range(&t.blocks, &t.root, &all()) {
            Err(_) => {}
            Ok(pf) => assert!(
                verify_range_bytes(&t.root, &all(), &pf.encode()).is_err(),
                "{name}: a PROVER-built range proof over the overlap was accepted"
            ),
        }
    }
}

/// Ranges whose read must OPEN the bad leaf. `[n, ..)` is not one: the
/// parent says the leaf under `a` ends at `m`, so a read of `[n, ..)` never
/// opens it — see `a_range_that_never_opens_the_bad_leaf_agrees_with_descent`.
fn touching() -> [Range; 2] {
    [all(), Range { hi: Bound::Excluded(b"m".to_vec()), ..all() }]
}

#[test]
fn the_plain_read_path_refuses_too() {
    for (name, t) in both() {
        for r in touching() {
            assert!(
                range(&t.blocks, &t.root, &r).is_err(),
                "{name}: range::range answered over an overlapping tree for {:?}..{:?}",
                r.lo,
                r.hi
            );
        }
    }
    let (root, b) = honest();
    assert_eq!(range(&b, &root, &all()).unwrap().entries.len(), 3, "CONTROL");
}

/// `Verified` means "independent of the writer's word". A range whose read
/// opens the bad leaf must refuse it, not count it.
#[test]
fn aggregate_verified_refuses_rather_than_answers() {
    for (name, t) in both() {
        for r in touching() {
            let got = aggregate_verified(&t.blocks, &t.root, &r);
            assert!(
                got.is_err(),
                "{name}: aggregate_verified answered {:?} for {:?}..{:?} over an overlapping tree",
                got.map(|v| v.agg().count),
                r.lo,
                r.hi
            );
        }
    }
    let (root, b) = honest();
    let n = Range { lo: Bound::Included(b"n".to_vec()), ..all() };
    assert_eq!(aggregate_verified(&b, &root, &n).unwrap().agg().count, 1, "CONTROL: keys >= n");
}

/// CONSISTENCY, not detection — the same property as the point proof for `z`
/// below. `[n, ..)` never opens the bad leaf, so it cannot refuse it; what it
/// must do is AGREE with every other accepted answer: `z` is not in the map,
/// so there is nothing at or after `n`. Before the fix `aggregate_verified`
/// also said 0 here — that answer was never the defect; the defect was the
/// OTHER answers (a range proof showing `z`) that disagreed with it.
#[test]
fn a_range_that_never_opens_the_bad_leaf_agrees_with_descent() {
    let n = Range { lo: Bound::Included(b"n".to_vec()), ..all() };
    for (name, t) in both() {
        assert_eq!(range(&t.blocks, &t.root, &n).map(|p| p.entries.len()), Ok(0), "{name}: range [n, ..)");
        assert_eq!(aggregate_verified(&t.blocks, &t.root, &n).map(|v| v.agg().count), Ok(0), "{name}: aggregate_verified [n, ..)");
        assert!(
            matches!(verify_bytes(&t.root, b"z", &t.z_proof.encode()), Ok(ProvenOwned::Absent)),
            "{name}: and the point proof agrees"
        );
    }
}

/// Reverse paging used to return `["m","z"] next=z` for ever. It must END —
/// by refusing — within a bound far above what three entries could need.
#[test]
fn paging_terminates_in_both_directions() {
    for (name, t) in both() {
        for reverse in [false, true] {
            let mut r = Range { max_entries: 2, reverse, ..all() };
            let mut pages = 0;
            let ended = loop {
                if pages == 10 {
                    break false;
                }
                pages += 1;
                // Through the proof path, the way a reader of a foreign tree pages.
                let Ok(pf) = prove_range(&t.blocks, &t.root, &r) else { break true };
                let Ok(pg) = verify_range_bytes(&t.root, &r, &pf.encode()) else { break true };
                match pg.next {
                    Some(n) => r.after = Some(n),
                    None => break true,
                }
            };
            assert!(ended, "{name}: paging (reverse={reverse}) did not end in 10 pages of 2 over 3 entries");
        }
    }
    // CONTROL: over the honest tree, paging really runs AND finishes, with every key.
    let (root, b) = honest();
    for reverse in [false, true] {
        let (mut r, mut seen) = (Range { max_entries: 2, reverse, ..all() }, vec![]);
        for _ in 0..10 {
            let pg = verify_range_bytes(&root, &r, &prove_range(&b, &root, &r).unwrap().encode()).unwrap();
            seen.extend(pg.entries.iter().map(|(k, _)| k.clone()));
            match pg.next {
                Some(n) => r.after = Some(n),
                None => break,
            }
        }
        assert_eq!(seen.len(), 3, "CONTROL: honest paging (reverse={reverse}) reached {} of 3", seen.len());
    }
}

/// NOT a detection property, and it must not be made one: `z`'s point path is
/// root → the child under `m`, which never touches the bad leaf. After the fix
/// it still says Absent — correctly, because once every answer that touches
/// the bad leaf is refused, all ACCEPTED answers agree: `z` is not in the map,
/// and nobody can prove it Present.
#[test]
fn the_point_proof_for_z_still_says_absent() {
    for (name, t) in both() {
        let got = verify_bytes(&t.root, b"z", &t.z_proof.encode());
        assert!(
            matches!(got, Ok(ProvenOwned::Absent)),
            "{name}: the point proof for `z` gave {got:?}"
        );
        assert_eq!(read::get(&t.blocks, &t.root, b"z").map(|v| v.is_some()), Ok(false), "{name}: read::get(z)");
        // And `m`, the other side of the same bad parent, still reads.
        assert_eq!(read::get(&t.blocks, &t.root, b"m").map(|v| v.is_some()), Ok(true), "{name}: read::get(m)");
    }
}

/// The spans every node reached from `cid` must respect, as a standalone
/// walk. `inherit`: the bound of a last child is its parent's own bound (the
/// fix); otherwise a last child is unbounded (the adjacent-only check that was
/// tried and was not enough). Returns (nodes checked, violations).
fn spans(b: &MemBlocks, cid: &Cid, upper: Option<Vec<u8>>, inherit: bool) -> (usize, usize) {
    let n = Node::parse(b.get(cid).unwrap()).unwrap();
    let mut bad = usize::from(upper.as_ref().is_some_and(|u| &n.key(n.len() - 1) >= u));
    let mut seen = 1;
    if !n.is_leaf() {
        for i in 0..n.len() {
            let next = if i + 1 < n.len() {
                Some(n.key(i + 1))
            } else if inherit {
                upper.clone()
            } else {
                None
            };
            let (s, v) = spans(b, &n.child(i).0, next, inherit);
            seen += s;
            bad += v;
        }
    }
    (seen, bad)
}

/// THE NEGATIVE CONTROL, executed rather than described: the adjacent-only
/// check finds the adjacent overlap and MISSES the ancestor one. The fix is
/// the inherited bound, and this is why the ancestor variant is required.
#[test]
fn adjacent_only_check_misses_the_ancestor_variant() {
    let (a, g) = (adjacent(), ancestor());
    assert_eq!(spans(&a.blocks, &a.root, None, false).1, 1, "adjacent-only sees the adjacent overlap");
    assert_eq!(
        spans(&g.blocks, &g.root, None, false).1,
        0,
        "adjacent-only MISSES the ancestor overlap — if this is 1, the ancestor fixture no longer tests the inheritance"
    );
    assert_eq!(spans(&a.blocks, &a.root, None, true).1, 1, "inherited sees the adjacent overlap");
    assert_eq!(spans(&g.blocks, &g.root, None, true).1, 1, "inherited sees the ancestor overlap");
}

/// The falsifier for the whole fix: the WRITER never produces an overlap. If
/// this fails, `build` itself makes trees the reader now refuses — a far worse
/// finding than #52.
#[test]
fn an_honest_tree_has_no_overlapping_spans() {
    let mut es: Vec<(Vec<u8>, Vec<u8>)> = (0..50_000u32)
        .map(|i| {
            let k = format!("k/{:07}", i.wrapping_mul(2_654_435_761) % 9_000_000).into_bytes();
            (k, vec![(i % 251) as u8; if i % 4 == 0 { 800 } else { 30 }])
        })
        .collect();
    es.sort();
    es.dedup_by(|a, b| a.0 == b.0);
    let mut b = MemBlocks::default();
    let root = build::build(es.iter().map(|(k, v)| (&k[..], Value::Inline(&v[..]))), |c, x| b.insert(c, x)).unwrap();
    let (seen, bad) = spans(&b, &root, None, true);
    assert!(seen > 1_000, "the tree has {seen} nodes — too small to say anything about the writer");
    assert_eq!(bad, 0, "the writer produced {bad} overlapping spans in {seen} nodes");
    // And the reader agrees: every entry comes back through the checked path.
    assert_eq!(freenet_prolly::aggregate::aggregate_verified(&b, &root, &all()).unwrap().agg().count as usize, es.len());
}
