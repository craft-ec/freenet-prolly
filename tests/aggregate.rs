//! Counting a range from what branches record, and what that number is worth.

#[path = "common/dataset.rs"]
mod common;
use common::{dataset, rng};

use freenet_prolly::aggregate::{aggregate, aggregate_verified, fraud, AggError};
use freenet_prolly::apply::{apply_into, Edit};
use freenet_prolly::build::init;
use freenet_prolly::node::{Agg, Node, NodeBuilder, MAX_INLINE};
use freenet_prolly::range::Range;
use freenet_prolly::store::{Blocks, MemBlocks, ReadError};
use freenet_prolly::{block_id, kind, Cid};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};
use std::ops::Bound;

type Map = BTreeMap<Vec<u8>, Vec<u8>>;

fn build(m: &Map) -> (Cid, MemBlocks) {
    let mut blocks = MemBlocks::default();
    let root = init(&mut blocks);
    let edits: Vec<(Vec<u8>, Edit)> = m
        .iter()
        .map(|(k, v)| (k.clone(), Edit::Put(v.clone())))
        .collect();
    let root = apply_into(&mut blocks, &root, &edits).unwrap().root;
    (root, blocks)
}

/// The oracle. `Agg.bytes` is LOGICAL bytes: the key's full length plus the
/// value's full length, a referenced value counted at its real size.
fn reference(m: &Map, r: &Range) -> Agg {
    let empty = match (&r.lo, &r.hi) {
        (Bound::Unbounded, _) | (_, Bound::Unbounded) => false,
        (Bound::Included(a), Bound::Included(b)) => a > b,
        (Bound::Included(a), Bound::Excluded(b))
        | (Bound::Excluded(a), Bound::Included(b))
        | (Bound::Excluded(a), Bound::Excluded(b)) => a >= b,
    };
    if empty {
        return Agg::default();
    }
    m.range((r.lo.clone(), r.hi.clone()))
        .fold(Agg::default(), |a, (k, v)| Agg {
            count: a.count + 1,
            bytes: a.bytes + k.len() as u64 + v.len() as u64,
        })
}

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
/// Every node the tree actually reaches, walked independently of the code
/// under test. Not "every block that parses as a node": the store also holds
/// the empty root `init` made before the first apply, which is unreachable.
fn reachable(store: &MemBlocks, id: Cid, out: &mut HashSet<Cid>) {
    if !out.insert(id) {
        return;
    }
    let n = Node::parse(&store.0[&id]).unwrap();
    if !n.is_leaf() {
        for i in 0..n.len() {
            reachable(store, n.child(i).0, out);
        }
    }
}

fn counting(inner: &MemBlocks) -> Counting<'_> {
    Counting {
        inner,
        reads: RefCell::default(),
    }
}

/// Values that cross the inline boundary, so `bytes` has to count a referenced
/// value at its real size to match the reference.
fn with_big(mut m: Map, n: usize) -> Map {
    let mut r = rng(5);
    for i in 0..n {
        m.insert(
            format!("z/big/{i:05}").into_bytes(),
            vec![(r() % 251) as u8; MAX_INLINE + 1 + (r() as usize % 3000)],
        );
    }
    m
}

#[test]
fn both_answers_equal_the_reference_for_random_ranges() {
    let m = with_big(dataset(31, 20_000).into_iter().collect(), 60);
    let (root, blocks) = build(&m);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let mut r = rng(9);
    let pick = |r: &mut dyn FnMut() -> u64, keys: &[Vec<u8>]| -> Bound<Vec<u8>> {
        let k = keys[r() as usize % keys.len()].clone();
        match r() % 5 {
            0 => Bound::Unbounded,
            1 => Bound::Included(k),
            2 => Bound::Excluded(k),
            3 => {
                let mut b = k;
                b.push(0);
                Bound::Included(b)
            }
            _ => Bound::Excluded(vec![0xff; 3]),
        }
    };
    let mut checked = 0;
    for _ in 0..300 {
        let (a, b) = (pick(&mut r, &keys), pick(&mut r, &keys));
        let (lo, hi) = match (&a, &b) {
            (Bound::Included(x) | Bound::Excluded(x), Bound::Included(y) | Bound::Excluded(y))
                if x > y =>
            {
                (b, a)
            }
            _ => (a, b),
        };
        let req = Range {
            lo,
            hi,
            ..Range::default()
        };
        let want = reference(&m, &req);
        assert_eq!(
            aggregate(&blocks, &root, &req).unwrap().agg(),
            want,
            "{req:?}"
        );
        assert_eq!(
            aggregate_verified(&blocks, &root, &req).unwrap().agg(),
            want,
            "{req:?}"
        );
        checked += 1;
    }
    // Prefixes, the whole tree, one leaf, and the empty range.
    for p in [&b"d/"[..], b"e/", b"z/big/", b"nothing"] {
        let req = Range::prefix(p);
        assert_eq!(
            aggregate(&blocks, &root, &req).unwrap().agg(),
            reference(&m, &req)
        );
        checked += 1;
    }
    let whole = aggregate(&blocks, &root, &Range::default()).unwrap().agg();
    assert_eq!(whole, reference(&m, &Range::default()));
    assert_eq!(whole.count, m.len() as u64);
    println!("{checked} ranges: claimed and verified both equal the reference");
}

/// The point of the thing: a count over the whole tree touches the two edge
/// paths, not the tree.
#[test]
fn the_fast_path_reads_two_paths_and_the_verified_one_reads_everything() {
    let m: Map = dataset(32, 20_000).into_iter().collect();
    let (root, blocks) = build(&m);
    let height = Node::parse(blocks.get(&root).unwrap()).unwrap().level() as usize + 1;
    let mut all = HashSet::new();
    reachable(&blocks, root, &mut all);
    let nodes = all.len();

    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    for (what, req) in [
        ("whole tree", Range::default()),
        (
            "a middle range",
            Range {
                lo: Bound::Included(keys[3000].clone()),
                hi: Bound::Included(keys[17000].clone()),
                ..Range::default()
            },
        ),
    ] {
        let c = counting(&blocks);
        let got = aggregate(&c, &root, &req).unwrap();
        let reads = c.reads.borrow().len();
        assert_eq!(got.agg(), reference(&m, &req), "{what}");
        println!("  {what:14}: {reads} nodes read (height {height}, tree {nodes} nodes)");
        assert!(
            reads <= 2 * height + 1,
            "{what}: {reads} reads > 2*{height}+1"
        );
    }

    // The control: the verified answer must read the range.
    let c = counting(&blocks);
    let v = aggregate_verified(&c, &root, &Range::default()).unwrap();
    let reads = c.reads.borrow().len();
    assert_eq!(v.agg(), reference(&m, &Range::default()));
    println!("  verified whole : {reads} nodes read");
    assert_eq!(
        c.reads.borrow().iter().copied().collect::<HashSet<_>>(),
        all,
        "verified must read every node of the tree and nothing else"
    );
    assert_eq!(reads, nodes);
}

/// Start with the root only and feed exactly what it asks for.
#[test]
fn a_cold_count_resumes_and_names_only_the_edges() {
    let m: Map = dataset(33, 20_000).into_iter().collect();
    let (root, full) = build(&m);
    let height = Node::parse(full.0.get(&root).unwrap()).unwrap().level() as usize + 1;
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let req = Range {
        lo: Bound::Included(keys[2500].clone()),
        hi: Bound::Included(keys[15000].clone()),
        ..Range::default()
    };

    // An independent oracle for "on an edge path": a node whose key span
    // CONTAINS one of the two bounds. Computed by walking the store, not by
    // asking the code under test.
    fn spans(store: &MemBlocks, id: Cid, out: &mut Vec<(Cid, Vec<u8>, Vec<u8>)>) {
        let n = Node::parse(&store.0[&id]).unwrap();
        if n.is_empty() {
            return;
        }
        if n.is_leaf() {
            out.push((id, n.key(0), n.key(n.len() - 1)));
            return;
        }
        let before = out.len();
        for i in 0..n.len() {
            spans(store, n.child(i).0, out);
        }
        let lo = out[before..].iter().map(|s| s.1.clone()).min().unwrap();
        let hi = out[before..].iter().map(|s| s.2.clone()).max().unwrap();
        out.push((id, lo, hi));
    }
    let mut sp = Vec::new();
    spans(&full, root, &mut sp);
    let (lo, hi) = (keys[2500].clone(), keys[15000].clone());

    let mut held = MemBlocks::default();
    held.insert(root, &full.0[&root]);
    let mut rounds = 0;
    let mut named: HashSet<Cid> = HashSet::new();
    let got = loop {
        match aggregate(&held, &root, &req) {
            Ok(a) => break a,
            Err(AggError::Read(ReadError::Need(ids))) => {
                rounds += 1;
                assert!(rounds < 20, "did not converge");
                for id in ids {
                    named.insert(id);
                    held.insert(id, &full.0[&id]);
                }
            }
            Err(e) => panic!("{e:?}"),
        }
    };
    assert_eq!(got.agg(), reference(&m, &req));
    println!(
        "cold count: {rounds} rounds, {} blocks fetched, height {height}",
        named.len()
    );
    assert!(rounds <= height, "{rounds} rounds > height {height}");
    // Everything fetched sits on one of the two edge paths: its span contains
    // a bound. A node wholly inside the range should never have been opened.
    for id in &named {
        let (_, smin, smax) = sp.iter().find(|(s, ..)| s == id).expect("a real node");
        assert!(
            (*smin <= lo && lo <= *smax) || (*smin <= hi && hi <= *smax),
            "fetched a node that is not on an edge path"
        );
    }
}

/// The documented limit, and the proof that refutes it.
#[test]
fn a_lying_aggregate_is_believed_refused_and_provable() {
    let m: Map = dataset(34, 6000).into_iter().collect();
    let (root, full) = build(&m);
    let truth = reference(&m, &Range::default());

    // Rebuild the root with one child's recorded aggregate inflated.
    let r = Node::parse(full.0.get(&root).unwrap()).unwrap();
    assert!(!r.is_leaf() && r.len() >= 2);
    let mut b = NodeBuilder::branch(r.level());
    let (victim, victim_agg) = r.child(0);
    for i in 0..r.len() {
        let (cid, agg) = r.child(i);
        let agg = if i == 0 {
            Agg {
                count: agg.count + 1_000_000,
                bytes: agg.bytes,
            }
        } else {
            agg
        };
        b.push_child(&r.key(i), cid, agg).unwrap();
    }
    let liar = b.finish().unwrap();
    let liar_id = block_id(kind::TREE_NODE, &liar);
    let mut blocks = full.clone();
    blocks.insert(liar_id, &liar);

    // Claimed believes it. That is the documented limit, asserted as such.
    let claimed = aggregate(&blocks, &liar_id, &Range::default()).unwrap();
    assert_eq!(
        claimed.agg().count,
        truth.count + 1_000_000,
        "the fast path must return the writer's number, wrong or not"
    );

    // Verified refuses it.
    assert_eq!(
        aggregate_verified(&blocks, &liar_id, &Range::default()),
        Err(AggError::Read(ReadError::Mismatch(victim)))
    );

    // And two blocks prove it, with nothing else and nobody trusted.
    let child = full.0.get(&victim).unwrap();
    assert!(
        fraud(&liar, child),
        "the parent and the child refute each other"
    );
    assert_eq!(
        Node::parse(child).unwrap().agg(),
        victim_agg,
        "the child's own header is what the honest parent recorded"
    );

    // Controls: the honest pair is not fraud, and neither is an unrelated pair.
    let honest = full.0.get(&root).unwrap();
    assert!(
        !fraud(honest, child),
        "an honest pair must not read as fraud"
    );
    let stranger = full
        .0
        .iter()
        .find(|(c, b)| **c != victim && Node::parse(b).is_ok_and(|n| n.is_leaf()))
        .map(|(_, b)| b.clone())
        .unwrap();
    assert!(
        !fraud(&liar, &stranger),
        "a block that is not this parent's child"
    );
    assert!(!fraud(b"not a node", child));
}

/// An aggregate answers about a whole range; paging is a different question.
#[test]
fn a_paging_request_is_refused_rather_than_quietly_answered() {
    let m: Map = dataset(35, 500).into_iter().collect();
    let (root, blocks) = build(&m);
    for (what, req) in [
        (
            "reverse",
            Range {
                reverse: true,
                ..Range::default()
            },
        ),
        (
            "after",
            Range {
                after: Some(m.keys().next().unwrap().clone()),
                ..Range::default()
            },
        ),
        (
            "a limit",
            Range {
                max_entries: 10,
                ..Range::default()
            },
        ),
        (
            "a limit",
            Range {
                max_bytes: 10,
                ..Range::default()
            },
        ),
    ] {
        assert_eq!(
            aggregate(&blocks, &root, &req),
            Err(AggError::NotWholeRange(what)),
            "{what} must be refused"
        );
        assert!(aggregate_verified(&blocks, &root, &req).is_err());
    }
    // The defaults mean "no opinion", and a prefix inherits them.
    assert!(aggregate(&blocks, &root, &Range::default()).is_ok());
    assert!(aggregate(&blocks, &root, &Range::prefix(b"d/")).is_ok());
}

/// What a count costs against reading the range, which is why this exists.
#[test]
fn the_cost_of_a_count_measured() {
    for n in [20_000usize, 200_000] {
        let m: Map = dataset(36, n).into_iter().collect();
        let (root, blocks) = build(&m);
        let req = Range::prefix(b"d/");
        let want = reference(&m, &req);

        let c = counting(&blocks);
        let t = std::time::Instant::now();
        let got = aggregate(&c, &root, &req).unwrap();
        let fast = t.elapsed();
        let fast_reads = c.reads.borrow().len();

        let c = counting(&blocks);
        let t = std::time::Instant::now();
        let v = aggregate_verified(&c, &root, &req).unwrap();
        let slow = t.elapsed();
        let slow_reads = c.reads.borrow().len();

        assert_eq!(got.agg(), want);
        assert_eq!(v.agg(), want);
        println!(
            "count of prefix over {n:>7} entries ({} in range): claimed {fast:>10?} / {fast_reads:>5} reads · verified {slow:>10?} / {slow_reads:>5} reads",
            want.count
        );
        assert!(
            fast_reads * 10 < slow_reads,
            "the fast path must be a different shape"
        );
    }
}

/// `fraud` is handed two blocks by a stranger. Nothing a stranger can send may
/// make it panic — a keeper or a client calling it on submitted bytes would go
/// down with it, which turns a fraud PROOF into a way to kill the checker.
#[test]
fn nothing_a_stranger_can_send_makes_the_fraud_check_panic() {
    let m: Map = dataset(37, 4000).into_iter().collect();
    let (root, store) = build(&m);
    let r = Node::parse(store.0.get(&root).unwrap()).unwrap();
    let branch = store.0.get(&root).unwrap().clone();
    let child = store.0.get(&r.child(0).0).unwrap().clone();
    let leaf = store
        .0
        .values()
        .find(|b| Node::parse(b).is_ok_and(|n| n.is_leaf()))
        .unwrap()
        .clone();
    let empty = {
        let mut blocks = MemBlocks::default();
        let e = init(&mut blocks);
        blocks.0.get(&e).unwrap().clone()
    };
    // A branch that is not this child's parent: same shape, different subtree.
    let other: Vec<u8> = (1..r.len())
        .filter_map(|i| store.0.get(&r.child(i).0).cloned())
        .find(|b| Node::parse(b).is_ok_and(|n| !n.is_leaf()))
        .unwrap_or_else(|| branch.clone());

    for (what, p, c) in [
        ("a leaf as the parent", leaf.clone(), leaf.clone()),
        (
            "garbage as the parent",
            b"not a node at all".to_vec(),
            child.clone(),
        ),
        ("garbage as the child", branch.clone(), b"\0\0\0".to_vec()),
        ("the empty string", Vec::new(), Vec::new()),
        ("an empty node", branch.clone(), empty.clone()),
        ("an empty node as the parent", empty.clone(), child.clone()),
        (
            "a block this parent does not name",
            branch.clone(),
            leaf.clone(),
        ),
        ("a child of a different branch", other, child.clone()),
        (
            "the parent as its own child",
            branch.clone(),
            branch.clone(),
        ),
        ("an honest pair", branch.clone(), child.clone()),
    ] {
        assert!(!fraud(&p, &c), "{what} must not read as fraud");
        // And the same bytes the other way round, which nobody promised is a
        // valid pair either.
        assert!(!fraud(&c, &p) || what == "a child of a different branch");
    }
}

/// The same question put to the counting path: a store is not trusted either.
#[test]
fn a_hostile_store_cannot_make_a_count_panic() {
    let m: Map = dataset(38, 4000).into_iter().collect();
    let (root, full) = build(&m);
    let r = Node::parse(full.0.get(&root).unwrap()).unwrap();
    let victim = r.child(0).0;
    let leaf_bytes = full
        .0
        .values()
        .find(|b| Node::parse(b).is_ok_and(|n| n.is_leaf()))
        .unwrap()
        .clone();

    for (what, served) in [
        ("a leaf served where a branch belongs", leaf_bytes),
        ("raw bytes served as a node", b"nonsense".to_vec()),
        ("an empty body", Vec::new()),
    ] {
        let mut blocks = full.clone();
        blocks.insert(victim, &served);
        // A range whose lower edge runs through the tampered child, so the
        // claimed path has to open it rather than believing its aggregate.
        let req = Range {
            // Not the first key: that would put the tampered child WHOLLY
            // inside the range, where the claimed path believes its aggregate
            // and never opens it — correct behaviour, and a vacuous test.
            lo: Bound::Included(m.keys().nth(5).unwrap().clone()),
            hi: Bound::Included(m.keys().nth(3000).unwrap().clone()),
            ..Range::default()
        };
        // Reached as a CHILD, the parent's claim about it is contradicted, so
        // both paths must refuse rather than fold in whatever was served.
        for got in [
            aggregate(&blocks, &root, &req).err(),
            aggregate_verified(&blocks, &root, &req).err(),
        ] {
            assert!(
                matches!(
                    got,
                    Some(AggError::Read(
                        ReadError::Mismatch(_) | ReadError::Corrupt(..)
                    ))
                ),
                "{what}: expected a refusal, got {got:?}"
            );
        }
        // Handed in as a ROOT, nothing claims anything about it, so there is
        // nothing to contradict: a leaf root is a legitimate one-node tree and
        // answering is correct. The requirement here is only that a count over
        // an arbitrary block decides something instead of panicking.
        let _ = aggregate(&blocks, &victim, &Range::default());
        let _ = aggregate_verified(&blocks, &victim, &Range::default());
    }
}
