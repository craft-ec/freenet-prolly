//! The boundary rule: frozen vectors, tree validity, size spread, edit locality.
//! Every property that says "the rule gives X" is paired with a control rule
//! that must NOT give X, so a pass cannot come from the setup.
//!
//! `cargo test --test boundary -- --nocapture` prints the measurements.

#[path = "common/dataset.rs"]
mod common;
use common::{dataset, rng};

use freenet_prolly::boundary::{self, splits_after, MIN_SPLIT};
use freenet_prolly::build::{SplitRule, TreeBuilder};
use freenet_prolly::node::{Agg, Node, NodeBuilder, Value, HEADER, MAX_INLINE};
use freenet_prolly::Cid;
use std::collections::HashMap;

type Entries = Vec<(Vec<u8>, Vec<u8>)>;
type Nodes = HashMap<Cid, Vec<u8>>;

fn build_with(rule: SplitRule, e: &Entries) -> (Cid, Nodes) {
    let mut nodes = Nodes::new();
    let mut t = TreeBuilder::with_rule(rule, |c, b: &[u8]| {
        nodes.insert(c, b.to_vec());
    });
    for (k, v) in e {
        t.push(k, Value::Inline(v)).unwrap();
    }
    let root = t.finish().unwrap();
    (root, nodes)
}
fn build(e: &Entries) -> (Cid, Nodes) {
    build_with(splits_after, e)
}

/// Control: close a node once it reaches 4 KiB. Depends on position, not content.
fn by_size(_: u8, _: &[u8], _: usize, after: usize) -> bool {
    after >= 4096
}
/// Control: content-defined but size-blind (constant hazard, mean ≈ 4 KiB).
fn geometric(level: u8, key: &[u8], before: usize, after: usize) -> bool {
    after >= MIN_SPLIT
        && (boundary::split_hash(level, key) as u64) * 3584 < ((after - before) as u64) << 32
}

/// Walk the tree; returns entries in order, height, and per-level node sizes (logical).
fn walk(root: Cid, nodes: &Nodes) -> (Entries, usize) {
    fn go(
        c: Cid,
        nodes: &Nodes,
        want: Option<u8>,
        last: bool,
        out: &mut Entries,
    ) -> (u8, Agg, Vec<u8>) {
        let n = Node::parse(&nodes[&c]).expect("every node parses");
        if let Some(l) = want {
            assert_eq!(n.level(), l, "child level is parent level - 1");
        }
        if n.is_leaf() {
            for i in 0..n.len() {
                match n.value(i) {
                    Value::Inline(v) => out.push((n.key(i), v.to_vec())),
                    _ => unreachable!(),
                }
            }
        } else {
            // Only the last node of a level may hold a single child; the root never does.
            assert!(
                n.len() >= 2 || (want.is_some() && last),
                "single-child branch that is not the last of its level"
            );
            for i in 0..n.len() {
                let (child, agg) = n.child(i);
                let last = last && i + 1 == n.len();
                let (_, got, min) = go(child, nodes, Some(n.level() - 1), last, out);
                assert_eq!(got, agg, "recorded child aggregate is the child's");
                assert_eq!(min, n.key(i), "branch key is the child's min key");
            }
        }
        let min = if n.is_empty() { vec![] } else { n.key(0) };
        (n.level(), n.agg(), min)
    }
    let mut out = Vec::new();
    let (level, agg, _) = go(root, nodes, None, true, &mut out);
    assert_eq!(agg.count as usize, out.len());
    (out, level as usize + 1)
}

#[test]
fn tree_holds_exactly_the_entries() {
    for n in [0usize, 1, 2, 50, 3000] {
        let e = dataset(7, n);
        let (root, nodes) = build(&e);
        let (got, height) = walk(root, &nodes);
        assert_eq!(got, e);
        if n <= 2 {
            assert_eq!((height, nodes.len()), (1, 1));
        }
        if n == 3000 {
            assert!(height >= 2);
        }
    }
}

#[test]
fn same_entries_same_root_different_entries_different_root() {
    let e = dataset(11, 4000);
    let (a, _) = build(&e);
    let (b, _) = build(&e.clone());
    assert_eq!(a, b);
    let mut f = e.clone();
    f[1234].1[0] ^= 1;
    assert_ne!(build(&f).0, a);
}

#[test]
fn order_is_enforced_across_node_boundaries_and_oversized_values_are_refused() {
    use freenet_prolly::build::TreeError;
    use freenet_prolly::node::BuildError;
    // Fill until a node closes, then push a key smaller than the last one.
    let mut closed = 0;
    let mut t = TreeBuilder::new(|_, _: &[u8]| closed += 1);
    let v = [0u8; 300];
    let mut i = 0u32;
    while {
        t.push(format!("k{i:06}").as_bytes(), Value::Inline(&v))
            .unwrap();
        i += 1;
        i < 200
    } {}
    assert_eq!(
        t.push(b"k000000", Value::Inline(&v)),
        Err(TreeError::Node(BuildError::NotSorted))
    );
    drop(t);
    assert!(
        closed > 5,
        "the run above must have crossed node boundaries"
    );

    let mut t = TreeBuilder::new(|_, _: &[u8]| {});
    assert_eq!(
        t.push(b"big", Value::Inline(&vec![0u8; MAX_INLINE + 1])),
        Err(TreeError::Node(BuildError::ValueTooLong))
    );
    t.push(b"big", Value::Inline(&vec![0u8; MAX_INLINE]))
        .unwrap();
}

/// A push that fails must leave the builder exactly as it was: otherwise the
/// same contents hash two ways depending on what the caller tried first.
#[test]
fn a_rejected_push_does_not_change_the_root() {
    let e = dataset(1, 400);
    let cid = [5u8; 32];
    let long_key = vec![b'k'; 600];
    let run = |noise: bool| {
        let mut t = TreeBuilder::new(|_, _: &[u8]| {});
        let mut rejected = 0;
        for (i, (k, v)) in e.iter().enumerate() {
            if i % 7 != 0 {
                t.push(k, Value::Inline(v)).unwrap();
                continue;
            }
            if noise {
                // (an empty key is only out of order once something was pushed)
                let unsorted: &[u8] = if i == 0 { &long_key } else { b"" };
                let bad = [
                    t.push(k, Value::Inline(&[0u8; 9000])),
                    t.push(k, Value::Ref { cid, len: 10 }),
                    t.push(&long_key, Value::Inline(b"")),
                    t.push(unsorted, Value::Inline(b"")),
                ];
                rejected += bad.iter().filter(|r| r.is_err()).count();
            }
            t.push(k, Value::Ref { cid, len: 9000 }).unwrap();
        }
        (t.finish().unwrap(), rejected)
    };
    let (clean, _) = run(false);
    let (noisy, rejected) = run(true);
    assert_eq!(
        rejected,
        4 * e.len().div_ceil(7),
        "every bad push was refused"
    );
    assert_eq!(clean, noisy, "same contents, different root");
}

fn leaf_sizes(nodes: &Nodes) -> Vec<usize> {
    let mut v: Vec<(Vec<u8>, usize)> = nodes
        .values()
        .filter_map(|b| {
            let n = Node::parse(b).unwrap();
            n.is_leaf().then(|| (n.key(0), b.len()))
        })
        .collect();
    v.sort();
    v.into_iter().map(|(_, s)| s).collect()
}

/// (mean, coefficient of variation, mean over groups of 8 of max/mean-of-all)
fn spread(sizes: &[usize]) -> (f64, f64, f64) {
    let n = sizes.len() as f64;
    let mean = sizes.iter().sum::<usize>() as f64 / n;
    let var = sizes
        .iter()
        .map(|&s| (s as f64 - mean).powi(2))
        .sum::<f64>()
        / n;
    let groups: Vec<f64> = sizes
        .chunks(8)
        .filter(|g| g.len() == 8)
        .map(|g| *g.iter().max().unwrap() as f64)
        .collect();
    let pad = groups.iter().sum::<f64>() / groups.len() as f64 / mean;
    (mean, var.sqrt() / mean, pad)
}

#[test]
fn sizes_are_tight_and_a_size_blind_rule_is_not() {
    let e = dataset(3, 60_000);
    let (_, ours) = build(&e);
    let (_, ctrl) = build_with(geometric, &e);
    let (so, sc) = (leaf_sizes(&ours), leaf_sizes(&ctrl));
    let (m, cv, pad) = spread(&so);
    let (cm, ccv, cpad) = spread(&sc);
    let mut sorted = so.clone();
    sorted.sort();
    let pct = |p: usize| sorted[sorted.len() * p / 100];
    println!("leaves (encoded bytes), {} entries", e.len());
    println!("  rule       nodes   mean    cv   max-of-8/mean");
    println!("  weibull-4  {:5}  {m:5.0}  {cv:.2}  {pad:.2}", so.len());
    println!("  geometric  {:5}  {cm:5.0}  {ccv:.2}  {cpad:.2}", sc.len());
    println!(
        "  weibull-4 percentiles: min {} p1 {} p50 {} p99 {} max {}",
        sorted[0],
        pct(1),
        pct(50),
        pct(99),
        sorted[sorted.len() - 1]
    );
    assert!((3700.0..4500.0).contains(&m), "mean {m}");
    assert!(cv < 0.35 && pad < 1.55, "cv {cv} pad {pad}");
    assert!(
        ccv > 0.6 && cpad > 1.9,
        "control must be loose: cv {ccv} pad {cpad}"
    );
}

/// Nodes of `new` that `old` does not have.
fn fresh(old: &Nodes, new: &Nodes) -> usize {
    new.keys().filter(|c| !old.contains_key(*c)).count()
}

fn stats(mut v: Vec<usize>) -> (f64, usize, usize) {
    v.sort();
    let mean = v.iter().sum::<usize>() as f64 / v.len() as f64;
    (mean, v[v.len() * 99 / 100], v[v.len() - 1])
}

#[derive(Clone, Copy)]
enum Edit {
    Insert,
    Delete,
    SameLen,
    Grow,
}

fn locality(rule: SplitRule, edit: Edit, trials: usize) -> (f64, usize, usize, usize) {
    // PROLLY_TRIALS=2000 for a p99 worth quoting; the default keeps CI quick.
    let trials = std::env::var("PROLLY_TRIALS")
        .ok()
        .and_then(|t| t.parse().ok())
        .unwrap_or(trials);
    let base = dataset(5, 20_000);
    let (root, old) = build_with(rule, &base);
    let (_, height) = walk(root, &old);
    let mut r = rng(99);
    let mut changed = Vec::new();
    for _ in 0..trials {
        let mut e = base.clone();
        let i = (r() % e.len() as u64) as usize;
        match edit {
            Edit::Insert => {
                let mut k = e[i].0.clone();
                k.extend_from_slice(&r().to_be_bytes());
                let v = vec![r() as u8; 60 + (r() % 341) as usize];
                e.insert(i + 1, (k, v));
            }
            Edit::Delete => {
                e.remove(i);
            }
            Edit::SameLen => {
                if e[i].1.is_empty() {
                    continue;
                }
                e[i].1[0] ^= 0xff;
            }
            Edit::Grow => e[i].1.extend_from_slice(&[r() as u8; 120]),
        }
        let (_, new) = build_with(rule, &e);
        changed.push(fresh(&old, &new));
    }
    let (mean, p99, max) = stats(changed);
    (mean, p99, max, height)
}

#[test]
fn one_edit_rewrites_a_few_nodes_and_a_positional_rule_rewrites_the_rest() {
    println!("nodes rewritten by one edit (20k entries), 150 trials each");
    println!("  edit            mean   p99   max   (height)");
    for (name, edit) in [
        ("insert", Edit::Insert),
        ("delete", Edit::Delete),
        ("value, same len", Edit::SameLen),
        ("value, +120 B", Edit::Grow),
    ] {
        let (mean, p99, max, h) = locality(splits_after, edit, 150);
        println!("  {name:15} {mean:5.2}  {p99:4}  {max:4}   ({h})");
        assert!(mean < h as f64 + 1.5, "{name}: mean {mean}");
        // The tail is the re-sync walk: after a shifted boundary each following
        // node re-joins the old chain with probability ≈ ½ (2000 trials: p99 ≤ h + 8; this run is 150, so the bound is loose).
        assert!(p99 <= h + 11, "{name}: p99 {p99}");
        if let Edit::SameLen = edit {
            assert_eq!(max, h, "a same-length value edit rewrites the path only");
        }
    }
    let (mean, _, _, h) = locality(by_size, Edit::Insert, 150);
    println!("  insert, by-size control: mean {mean:.0} (height {h})");
    // A size threshold re-joins the old chain only when two running sums happen
    // to cross 4 KiB at the same entry, so an insert drags a run of leaves along.
    assert!(mean > 12.0, "control must cascade: {mean}");
}

/// A tree whose first leaf is closed by the hard limit, not by content: tiny
/// entries with keys ground so the rule never fires, then one large entry that
/// cannot fit. Pins MAX_LOGICAL, "close before the overflowing entry", and the
/// restart of the rule at s_before = HEADER.
fn forced_split_tree() -> Cid {
    forced_split_tree_into(&mut Nodes::new())
}

fn forced_split_tree_into(keep: &mut Nodes) -> Cid {
    let mut e: Entries = Vec::new();
    let mut s = HEADER;
    let big = vec![7u8; 1000];
    let mut i = 0;
    while s + NodeBuilder::leaf_cost(b"99999", &Value::Inline(&big)) <= boundary::MAX_LOGICAL {
        let key = (0..)
            .map(|j| format!("{i:05}.{j}").into_bytes())
            .find(|k| {
                let c = NodeBuilder::leaf_cost(k, &Value::Inline(b""));
                !splits_after(0, k, s, s + c)
            })
            .unwrap();
        s += NodeBuilder::leaf_cost(&key, &Value::Inline(b""));
        e.push((key, vec![]));
        i += 1;
    }
    let filled = e.len();
    e.push((b"99999".to_vec(), big));
    e.extend(dataset(2, 40).into_iter().map(|(mut k, v)| {
        k.insert(0, b'z');
        (k, v)
    }));
    let (root, nodes) = build(&e);
    let first = nodes
        .values()
        .map(|b| Node::parse(b).unwrap())
        .find(|n| n.is_leaf() && n.key(0) == e[0].0)
        .unwrap();
    assert_eq!(
        first.len(),
        filled,
        "the limit, not content, closed the first leaf"
    );
    assert!(
        s > boundary::MAX_LOGICAL - 1100,
        "and it was nearly full: {s}"
    );
    assert_eq!(walk(root, &nodes).0, e);
    keep.extend(nodes);
    root
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// The format's frozen values. If this fails, every stored tree's hashes changed.
#[test]
fn frozen_vectors() {
    let mut got = String::new();
    for (level, key) in [
        (0u8, &b""[..]),
        (0, b"d/post/1"),
        (1, b"d/post/1"),
        (3, b"e/follows/x"),
    ] {
        got += &format!(
            "hash {level} {} {:08x}\n",
            hex(key),
            boundary::split_hash(level, key)
        );
    }
    for (key, b, a) in [
        (&b"d/post/1"[..], 900usize, 1023usize),
        (b"d/post/1", 900, 1024),
        (b"d/post/1", 4000, 4300),
        (b"d/post/2", 4000, 4300),
        (b"d/post/3", 2000, 2100),
        (b"d/post/4", 6000, 6400),
        (b"d/post/5", 11000, 12288),
    ] {
        got += &format!(
            "split 0 {} {b} {a} {}\n",
            hex(key),
            splits_after(0, key, b, a)
        );
    }
    // MIN_SPLIT: a key whose hash is low enough to split at any size ≥ 1 KiB.
    let low = (0..1_000_000)
        .map(|i| format!("low-{i}"))
        .find(|k| boundary::split_hash(0, k.as_bytes()) < 1 << 20)
        .unwrap();
    for a in [MIN_SPLIT - 1, MIN_SPLIT] {
        let d = splits_after(0, low.as_bytes(), HEADER, a);
        got += &format!("split 0 {} {HEADER} {a} {d}\n", hex(low.as_bytes()));
    }
    // The level is part of the decision: same key and sizes, opposite answers.
    for want0 in [true, false] {
        let k = (0..100_000)
            .map(|i| format!("lvl-{i}"))
            .find(|k| {
                splits_after(0, k.as_bytes(), 4000, 4300) == want0
                    && splits_after(1, k.as_bytes(), 4000, 4300) != want0
            })
            .expect("the level must change the decision for some key");
        for level in [0, 1] {
            let d = splits_after(level, k.as_bytes(), 4000, 4300);
            got += &format!("split {level} {} 4000 4300 {d}\n", hex(k.as_bytes()));
        }
    }
    got += &format!("forced {}\n", hex(&forced_split_tree()));
    // The smallest size at which a fresh node closes after a key, for keys with
    // a high split hash: this is where a one-unit change of LAMBDA shows.
    let mut edges = 0;
    for i in 0.. {
        let key = format!("edge-{i}");
        if boundary::split_hash(0, key.as_bytes()) < 0xE000_0000 {
            continue;
        }
        let at = (HEADER + 1..=boundary::MAX_LOGICAL)
            .find(|&a| splits_after(0, key.as_bytes(), HEADER, a))
            .unwrap();
        got += &format!("edge 0 {} {HEADER} {at}\n", hex(key.as_bytes()));
        edges += 1;
        if edges == 12 {
            break;
        }
    }
    got += &format!(
        "const {} {} {} {} {}\n",
        boundary::LAMBDA,
        MIN_SPLIT,
        boundary::MAX_LOGICAL,
        MAX_INLINE,
        freenet_prolly::node::MAX_VALUE
    );
    for (k, body) in [(0u8, &b""[..]), (0, b"value"), (1, b"value")] {
        let id = freenet_prolly::block_id(k, body);
        got += &format!("id {k} {} {}\n", hex(body), hex(&id));
    }
    for n in [0usize, 1, 5000] {
        got += &format!("root {n} {}\n", hex(&build(&dataset(1, n)).0));
    }
    let want = include_str!("vectors.txt");
    assert_eq!(got, want, "\n--- computed ---\n{got}");
}

/// What a host can hold a single node to.
#[test]
fn every_built_node_passes_the_per_node_split_check_and_a_miscut_node_does_not() {
    use freenet_prolly::boundary::{check_node, BoundaryError, MAX_LOGICAL};
    let e = dataset(3, 60_000);
    let (_, nodes) = build(&e);
    let mut checked = 0;
    for bytes in nodes.values() {
        assert_eq!(check_node(&Node::parse(bytes).unwrap()), Ok(()));
        checked += 1;
    }
    assert!(checked > 3000);
    let (_, forced) = {
        let mut nodes = Nodes::new();
        let root = forced_split_tree_into(&mut nodes);
        (root, nodes)
    };
    for bytes in forced.values() {
        assert_eq!(check_node(&Node::parse(bytes).unwrap()), Ok(()));
    }

    // Control: the same entries cut by a positional rule parse fine, and are refused.
    let (_, miscut) = build_with(by_size, &e);
    let refused = miscut
        .values()
        .filter(|b| {
            matches!(
                check_node(&Node::parse(b).unwrap()),
                Err(BoundaryError::InteriorSplit(_))
            )
        })
        .count();
    println!("positional cut: {refused}/{} nodes refused", miscut.len());
    // A Weibull node would have ended before 4 KiB with probability
    // 1 − exp(−(4096/4400)⁴) ≈ 0.53, so about half the positional nodes hold an
    // entry that should have closed them.
    assert!(
        refused * 10 > miscut.len() * 4,
        "{refused}/{}",
        miscut.len()
    );

    // A node over the limit (the raw builder allows up to MAX_NODE).
    let mut b = NodeBuilder::leaf();
    let mut i = 0u32;
    while b.logical_len() <= MAX_LOGICAL {
        let key = (0..)
            .map(|j| format!("{i:05}.{j}").into_bytes())
            .find(|k| {
                let c = NodeBuilder::leaf_cost(k, &Value::Inline(b""));
                b.logical_len() + c > MAX_LOGICAL
                    || !splits_after(0, k, b.logical_len(), b.logical_len() + c)
            })
            .unwrap();
        b.push(&key, Value::Inline(b"")).unwrap();
        i += 1;
    }
    let bytes = b.finish().unwrap();
    assert_eq!(
        check_node(&Node::parse(&bytes).unwrap()),
        Err(BoundaryError::TooLarge)
    );

    // Cost on the worst case a host can be handed: ~12 KiB of minimum-size entries.
    let mut b = NodeBuilder::leaf();
    let mut i = 0u32;
    loop {
        let base = b.logical_len();
        if base + 13 + 6 > MAX_LOGICAL {
            break;
        }
        let Some(key) = (0..200u32)
            .map(|j| format!("{i:04}{j:02}").into_bytes())
            .find(|k| !splits_after(0, k, base, base + 13 + k.len()))
        else {
            break;
        };
        if base + 13 + key.len() > MAX_LOGICAL {
            break;
        }
        b.push(&key, Value::Inline(b"")).unwrap();
        i += 1;
    }
    let entries = b.len();
    let bytes = b.finish().unwrap();
    let t = std::time::Instant::now();
    for _ in 0..200 {
        let n = Node::parse(&bytes).unwrap();
        check_node(&n).unwrap();
    }
    println!(
        "worst-case node: {entries} entries, {} B; parse + check_node = {:?} each (native, opt-level 2)",
        bytes.len(),
        t.elapsed() / 200
    );
    assert!(entries > 500);
}
