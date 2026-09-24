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
            // The builder codes a referenced value into its leaf's parity, so
            // it must have been handed the bytes. A `Ref` it never saw is
            // refused — which is the point, not an obstacle.
            t.see(cid, &vec![0xab; 9000]);
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
    // The parity rule's constants, on the wire line rather than only in the
    // source: a change to any of them moves a frozen vector, which is what a
    // reviewer sees. `0x11D` is the field polynomial, then the group bounds,
    // the close threshold, and the size classes.
    {
        use freenet_prolly::parity::{CLASSES, CLOSE_THRESHOLD_FOR_VECTORS, MAX_GROUP, MIN_GROUP};
        got += &format!(
            "pconst 11d {MIN_GROUP} {MAX_GROUP} {CLOSE_THRESHOLD_FOR_VECTORS} {}\n",
            CLASSES
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(",")
        );
    }
    for (k, body) in [(0u8, &b""[..]), (0, b"value"), (1, b"value")] {
        let id = freenet_prolly::block_id(k, body);
        got += &format!("id {k} {} {}\n", hex(body), hex(&id));
    }
    for n in [0usize, 1, 5000] {
        got += &format!("root {n} {}\n", hex(&build(&dataset(1, n)).0));
    }
    // Proof vectors: a proof must be the same bytes on every target, and must
    // VERIFY there — `check-wasm.sh` checks both against these lines.
    for n in [1000usize, 5000] {
        let (key, nodes, bytes, hash) = proof_vector(n);
        got += &format!("proof {n} {} {nodes} {bytes} {}\n", hex(&key), hex(&hash));
    }
    for n in [1000usize, 5000] {
        let (nodes, bytes, hash) = range_proof_vector(n);
        got += &format!("rproof {n} {nodes} {bytes} {}\n", hex(&hash));
    }
    // Parity: the code frozen to the byte, its canonical trimmed form, and
    // repair frozen with it.
    // Rows 0-2 on the `parity` line, byte-identical to the three-row code
    // (sdk#321: those lines do not move); the epoch's rows 3.. on `prows`.
    for k in [1usize, 7, 12, 21, 36] {
        let (plen, ids) = parity_vector(k);
        got += &format!(
            "parity {k} {plen} {} {} {}\n",
            hex(&ids[0]),
            hex(&ids[1]),
            hex(&ids[2])
        );
        got += &format!("prows {k} {}\n", ids[3..].iter().map(|i| hex(i)).collect::<Vec<_>>().join(" "));
        got += &format!("prepair {k} {}\n", hex(&parity_repair_digest(k)));
    }
    got += &format!("puneven {}\n", hex(&parity_uneven_digest()));
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

/// Feeding BLAKE3 the node's shared prefix and then an entry's suffix must give
/// the digest of the joined key — that identity is the only reason `check_node`
/// can avoid building a key per entry, so it is asserted rather than assumed.
#[test]
fn the_two_slice_split_hash_is_the_same_hash() {
    use freenet_prolly::boundary::{split_hash, split_hash_parts, splits_after_parts};
    let mut r = rng(4242);
    let mut checked = 0;
    for _ in 0..2000 {
        let len = (r() % 40) as usize;
        let key: Vec<u8> = (0..len).map(|_| r() as u8).collect();
        // Every possible split of this key, including both empty ends.
        for cut in 0..=key.len() {
            let (prefix, suffix) = key.split_at(cut);
            assert_eq!(
                split_hash_parts(0, prefix, suffix),
                split_hash(0, &key),
                "key {key:?} split at {cut}"
            );
            checked += 1;
        }
        // And the decision built on it agrees too, at a size where it can fire.
        let level = r() as u8;
        let cut = (r() as usize) % (key.len() + 1);
        let (prefix, suffix) = key.split_at(cut);
        assert_eq!(
            splits_after_parts(level, prefix, suffix, 4000, 4300),
            splits_after(level, &key, 4000, 4300)
        );
    }
    println!("two-slice split hash: {checked} splits identical to the joined key");
    assert!(checked > 20_000);
}

/// `pcount` is now a pure function of the entries, so a node carrying the wrong
/// amount of parity is refused and one carrying the right amount is not. That
/// closes the one region of an otherwise valid node nothing used to constrain.
#[test]
fn a_node_with_the_wrong_parity_count_is_refused_and_the_right_one_is_not() {
    use freenet_prolly::boundary::{check_node, check_parity, BoundaryError};
    use freenet_prolly::node::Agg;
    let build = |parity: usize| {
        let mut b = NodeBuilder::branch(1);
        for i in 0..4u8 {
            b.push_child(
                &[b'k', i],
                [i; 32],
                Agg {
                    count: 1,
                    bytes: 10,
                },
            )
            .unwrap();
        }
        for i in 0..parity {
            b.push_parity([0x90 + i as u8; 32]).unwrap();
        }
        b.finish().unwrap()
    };
    // Four children is one group, so the node requires exactly PARITY ids.
    let probe = build(freenet_prolly::parity::PARITY);
    let want = freenet_prolly::parity::pcount_of(&Node::parse(&probe).expect("parses"));
    assert_eq!(want, freenet_prolly::parity::PARITY, "four children are one group");

    // The control: the right count is accepted, so the refusals below are about
    // the COUNT and not about parity being rejected wholesale.
    let right = build(want);
    let n = Node::parse(&right).expect("a node with parity is well-formed");
    assert_eq!(n.parity_count(), want);
    assert_eq!(check_parity(&n), Ok(()));
    // `check_node` does not call it yet — see the note there — so the node
    // passes the entry checks whatever its parity says.
    assert_eq!(check_node(&n), Ok(()));

    for parity in [0usize, 1, want - 1, want + 1, 2 * want] {
        let bytes = build(parity);
        // It PARSES — the region's size is all `parse` decides — and the count
        // is settled here, where the entries are known.
        let n = Node::parse(&bytes).expect("a node with parity is well-formed");
        assert_eq!(n.parity_count(), parity);
        assert_eq!(
            check_parity(&n),
            Err(BoundaryError::WrongParityCount(want, parity)),
            "{parity} ids where {want} are required"
        );
    }
}

/// A third shape: one buffer per NODE rather than one key per entry, so BLAKE3
/// still sees the key as a single run of bytes. Measured alongside the other two.
fn check_node_one_buffer(node: &Node<'_>) -> Result<(), ()> {
    use freenet_prolly::boundary::MAX_LOGICAL;
    use freenet_prolly::node::{NodeBuilder as NB, HEADER, MAX_KEY};
    let prefix = node.prefix();
    let mut key = Vec::with_capacity(MAX_KEY);
    let mut s = HEADER;
    for i in 0..node.len() {
        let suffix = node.suffix(i);
        key.clear();
        key.extend_from_slice(prefix);
        key.extend_from_slice(suffix);
        let after = s + if node.is_leaf() {
            NB::leaf_cost_len(key.len(), &node.value(i))
        } else {
            NB::child_cost_len(key.len())
        };
        if after > MAX_LOGICAL {
            return Err(());
        }
        if i + 1 < node.len() && splits_after(node.level(), &key, s, after) {
            return Err(());
        }
        s = after;
    }
    Ok(())
}

/// The old allocating implementation, kept here so the change can be MEASURED
/// against it on the same machine rather than argued about.
fn check_node_allocating(node: &Node<'_>) -> Result<(), ()> {
    use freenet_prolly::boundary::MAX_LOGICAL;
    use freenet_prolly::node::HEADER;
    let mut s = HEADER;
    for i in 0..node.len() {
        let key = node.key(i);
        let after = s + if node.is_leaf() {
            NodeBuilder::leaf_cost(&key, &node.value(i))
        } else {
            NodeBuilder::child_cost(&key)
        };
        if after > MAX_LOGICAL {
            return Err(());
        }
        if i + 1 < node.len() && splits_after(node.level(), &key, s, after) {
            return Err(());
        }
        s = after;
    }
    Ok(())
}

/// What the per-entry work actually costs, split into its parts. Printed with
/// `--nocapture`; the assertions keep the measurement honest about what it
/// measured.
///
/// IGNORED, so it is not in the pass/fail set (freenet-prolly#58): it compares
/// two wall-clock timings ~10 % apart, and under load their spread between
/// repeats (±15 µs) exceeds that margin — measured failing 1 run in 5 at load
/// average 23–28 on main and on #56 alike. Because `cargo test` stops at the
/// first failing binary and this one runs early, a red here also hid every later
/// binary's tests. It is valid only ALONE ON A QUIET MACHINE:
///
/// ```text
/// cargo test --release --test boundary the_cost_of_check_node_measured -- --ignored --nocapture
/// ```
#[test]
#[ignore = "wall-clock measurement: run alone on a quiet machine (see the doc comment)"]
fn the_cost_of_check_node_measured() {
    use freenet_prolly::boundary::{check_node, split_hash_parts, MAX_LOGICAL};
    // The worst case a host can be handed: ~12 KiB of minimum-size entries.
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
    let node = Node::parse(&bytes).unwrap();
    assert!(entries > 500, "{entries} entries is not the worst case");

    let runs = 500;
    let time = |mut f: Box<dyn FnMut()>| {
        for _ in 0..20 {
            f();
        }
        let t = std::time::Instant::now();
        for _ in 0..runs {
            f();
        }
        t.elapsed() / runs
    };

    let parse = time(Box::new(|| {
        Node::parse(std::hint::black_box(&bytes)).unwrap();
    }));
    let old = time(Box::new(|| {
        check_node_allocating(std::hint::black_box(&node)).unwrap();
    }));
    let new = time(Box::new(|| {
        check_node(std::hint::black_box(&node)).unwrap();
    }));
    // How much of it is BLAKE3: the same hashes, nothing else.
    let prefix = node.prefix();
    let hashes = time(Box::new(|| {
        for i in 0..node.len() {
            std::hint::black_box(split_hash_parts(0, prefix, node.suffix(i)));
        }
    }));
    let one_buf = time(Box::new(|| {
        check_node_one_buffer(std::hint::black_box(&node)).unwrap();
    }));
    // And how much is the allocation alone.
    let keys = time(Box::new(|| {
        for i in 0..node.len() {
            std::hint::black_box(node.key(i));
        }
    }));

    println!(
        "worst-case node: {entries} entries, {} B (native, opt-level 2)",
        bytes.len()
    );
    println!("  Node::parse                 {parse:?}");
    println!("  check_node, allocating      {old:?}");
    println!("  check_node, no allocation   {new:?}");
    println!("  check_node, one buffer/node {one_buf:?}");
    println!("  of which BLAKE3 per entry   {hashes:?}");
    println!("  the allocations alone       {keys:?}");
    assert!(new < old, "the change must not be slower natively");
    // The point of the decomposition: hashing, not key handling, is what this
    // costs. If that ever stops being true the premise of #18 has changed.
    assert!(
        hashes > keys * 2,
        "BLAKE3 {hashes:?} should dominate the key handling {keys:?}"
    );
}

/// The frozen proof for `dataset(1, n)`: the median key, its path, and the
/// hash of the encoded proof.
///
/// Duplicated in `wasm-check` on purpose — the two computations meet only in
/// `tests/vectors.txt`, which is what makes the file a check of the TARGET
/// rather than of a shared helper.
fn proof_vector(n: usize) -> (Vec<u8>, usize, usize, [u8; 32]) {
    use freenet_prolly::proof::{prove, verify, Proven};
    use freenet_prolly::store::MemBlocks;
    let e = dataset(1, n);
    let (root, nodes) = build(&e);
    let mut store = MemBlocks::default();
    for (c, b) in &nodes {
        store.insert(*c, b);
    }
    let mut keys: Vec<Vec<u8>> = e.iter().map(|(k, _)| k.clone()).collect();
    keys.sort();
    keys.dedup();
    let key = keys[keys.len() / 2].clone();
    let p = prove(&store, &root, &key).unwrap();
    assert!(matches!(
        verify(&root, &key, &p).unwrap(),
        Proven::Present(_)
    ));
    let bytes = p.encode();
    (
        key,
        p.nodes.len(),
        bytes.len(),
        *blake3::hash(&bytes).as_bytes(),
    )
}

/// The frozen RANGE proof for `dataset(1, n)`: a 32-entry page from the first
/// key, and the hash of its encoded proof. Same duplication rule as
/// [`proof_vector`] — the two computations meet only in `tests/vectors.txt`.
fn range_proof_vector(n: usize) -> (usize, usize, [u8; 32]) {
    use freenet_prolly::proof::{prove_range, verify_range};
    use freenet_prolly::range::Range;
    use freenet_prolly::store::MemBlocks;
    let e = dataset(1, n);
    let (root, nodes) = build(&e);
    let mut store = MemBlocks::default();
    for (c, b) in &nodes {
        store.insert(*c, b);
    }
    let mut keys: Vec<Vec<u8>> = e.iter().map(|(k, _)| k.clone()).collect();
    keys.sort();
    keys.dedup();
    let r = Range {
        lo: std::ops::Bound::Included(keys[0].clone()),
        max_entries: 32,
        ..Range::default()
    };
    let p = prove_range(&store, &root, &r).unwrap();
    let page = verify_range(&root, &r, &p).unwrap();
    assert_eq!(page.entries.len(), 32);
    let bytes = p.encode();
    (p.nodes.len(), bytes.len(), *blake3::hash(&bytes).as_bytes())
}

/// The parity code, frozen to the byte.
///
/// "Parity is a pure function of the children" is what makes it deduplicate,
/// verifiable by plain hash, and repairable by anyone without a key — and it is
/// only true if two implementations produce identical bytes. These vectors are
/// the evidence: computed here and again in `wasm-check`, meeting only in
/// `tests/vectors.txt`, so they check the TARGET rather than a shared helper.
///
/// `k = 1` is the degenerate group (three different scalar multiples of one
/// symbol), `k = 12` the largest the grouping rule can make, and the lengths
/// are deliberately unequal so the padding and the length prefix are exercised
/// rather than skipped.
pub fn parity_vector(k: usize) -> (usize, [Cid; freenet_prolly::parity::PARITY]) {
    use freenet_prolly::parity::encode_group;
    let states = parity_members(k);
    let parity = encode_group(&states).expect("a codeable group");
    let ids: [Cid; freenet_prolly::parity::PARITY] =
        std::array::from_fn(|i| freenet_prolly::block_id(freenet_prolly::kind::PARITY, &parity[i]));
    // The STORED length of the first parity block, which is a function of its
    // own bytes and not of the group's longest member. Frozen so that a change
    // to trimming shows up here rather than only in the ids.
    (parity[0].len(), ids)
}

/// Deterministic members of unequal length, each a plausible block state
/// (`kind ‖ body`).
pub fn parity_members(k: usize) -> Vec<Vec<u8>> {
    (0..k)
        .map(|i| {
            // Lengths 1, 17, 49, 97, … — no two alike, and none a multiple of
            // the others, so a padding bug cannot cancel out.
            let len = 1 + i * i * 8 + i * 8;
            let mut s = Vec::with_capacity(1 + len);
            s.push(if i % 2 == 0 {
                freenet_prolly::kind::RAW
            } else {
                freenet_prolly::kind::TREE_NODE
            });
            s.extend((0..len).map(|b| (b as u8).wrapping_mul(i as u8 + 3)));
            s
        })
        .collect()
}

/// Every way to lose three of the `k + 3`, rebuilt, digested. This is what
/// says a repairer on another target gets the same bytes back — the claim
/// "anyone can repair without a key" rests on it.
/// A repair sweep over a group of UNEQUAL lengths, with the cases that make
/// trimming hard forced rather than hoped for: the longest member dropped, and
/// a parity block among the lost. The k = 1/7/12 vectors use one shape of
/// member each; this is the shape where the width is not recoverable from
/// what survives.
pub fn parity_uneven_digest() -> [u8; 32] {
    use freenet_prolly::parity::{encode_group, repair_group, symbol, MAX_MEMBER_VALUE};
    use freenet_prolly::parity::PARITY;
    // Strictly increasing, so the LAST member is the one that sets the width.
    let states: Vec<Vec<u8>> = (0..6).map(|i| vec![(i as u8) + 1; 1 + i * 37]).collect();
    let k = states.len();
    let parity = encode_group(&states).expect("codeable");
    let all: Vec<Vec<u8>> = states
        .iter()
        .map(|s| symbol(s))
        .chain(parity.iter().cloned())
        .collect();
    let mut h = blake3::Hasher::new();
    // Every loss that includes the longest member, and every one that includes
    // a parity block — the two cases the equal-length vectors cannot reach.
    let mut cases = 0usize;
    let mut parity_lost = 0usize;
    for a in 0..k + PARITY {
        for b in a + 1..k + PARITY {
            let gone = [k - 1, a, b];
            if a == k - 1 || b == k - 1 {
                continue;
            }
            let have: Vec<Option<Vec<u8>>> = (0..k + PARITY)
                .map(|j| (!gone.contains(&j)).then(|| all[j].clone()))
                .collect();
            let got = repair_group(k, &have, MAX_MEMBER_VALUE).expect("k of k+PARITY present");
            assert_eq!(got, states, "uneven: lost {gone:?}");
            for s in &got {
                h.update(s);
            }
            cases += 1;
            if a >= k || b >= k {
                parity_lost += 1;
            }
        }
    }
    assert!(cases > 20, "only {cases} uneven cases");
    assert!(
        parity_lost > 0,
        "no case dropped a parity block: that half of the sweep is untested"
    );
    *h.finalize().as_bytes()
}

pub fn parity_repair_digest(k: usize) -> [u8; 32] {
    use freenet_prolly::parity::{encode_group, repair_group, symbol, MAX_MEMBER_VALUE};
    use freenet_prolly::parity::PARITY;
    let states = parity_members(k);
    let parity = encode_group(&states).expect("a codeable group");
    let all: Vec<Vec<u8>> = states
        .iter()
        .map(|s| symbol(s))
        .chain(parity.iter().cloned())
        .collect();
    let n = k + PARITY;
    let mut h = blake3::Hasher::new();
    let mut cases = 0usize;
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                let have: Vec<Option<Vec<u8>>> = (0..n)
                    .map(|j| (j != a && j != b && j != c).then(|| all[j].clone()))
                    .collect();
                let got = repair_group(k, &have, MAX_MEMBER_VALUE).expect("k of k+PARITY present");
                assert_eq!(got, states, "k = {k}: lost {a},{b},{c}");
                for s in &got {
                    h.update(s);
                }
                cases += 1;
            }
        }
    }
    assert_eq!(
        cases,
        n * (n - 1) * (n - 2) / 6,
        "k = {k}: combinations missed"
    );
    *h.finalize().as_bytes()
}

/// The parity code end to end, without freezing its bytes yet.
///
/// The vectors wait on the canonical form of a parity block, but nothing about
/// determinism or repair does — and a test that only runs when the bytes are
/// frozen would leave the code unexercised in the meantime.
#[test]
fn the_parity_code_is_deterministic_and_repairs() {
    for k in [1usize, 7, 12] {
        let (width, ids) = parity_vector(k);
        assert_eq!(parity_vector(k), (width, ids), "k = {k}: not deterministic");
        assert!(
            ids[0] != ids[1] && ids[1] != ids[2],
            "k = {k}: parity ids repeat"
        );
        let states = parity_members(k);
        // The stored parity length is its own, and never the group's width.
        assert!(
            width <= 4 + states.iter().map(|s| s.len()).max().unwrap(),
            "a parity block longer than the untrimmed width"
        );
        // Every way to lose three, rebuilt and compared — the assertion lives
        // inside the digest helper, which also counts the combinations.
        let _ = parity_repair_digest(k);
    }
    // The members really are of unequal length, or padding is never exercised.
    let states = parity_members(12);
    let mut lens: Vec<usize> = states.iter().map(|s| s.len()).collect();
    let before = lens.len();
    lens.sort_unstable();
    lens.dedup();
    assert_eq!(lens.len(), before, "the members must differ in length");
}

/// What a host can be made to do by a node it is going to refuse.
///
/// `check_node` now pays a grouping hash per member, which is the most
/// expensive thing in it — so a node that fails a cheaper check must be refused
/// before buying any. Counted, because the verdict is "refused" either way and
/// no assertion about it can see the difference.
#[test]
fn a_node_refused_for_anything_cheaper_costs_no_grouping() {
    use freenet_prolly::boundary::{check_node, BoundaryError};
    use freenet_prolly::parity::work;

    // A well-formed branch, for the control: it pays one hash per child.
    let good = {
        let mut b = NodeBuilder::branch(1);
        for i in 0..8u8 {
            b.push_child(
                &[b'k', i],
                [i; 32],
                freenet_prolly::node::Agg {
                    count: 1,
                    bytes: 10,
                },
            )
            .unwrap();
        }
        // Eight children are one group, so PARITY ids.
        for p in 0..freenet_prolly::parity::PARITY as u8 {
            b.push_parity([0x70 + p; 32]).unwrap();
        }
        b.finish().unwrap()
    };
    let n = Node::parse(&good).expect("parses");
    work::reset();
    assert_eq!(check_node(&n), Ok(()));
    assert_eq!(
        work::hashes(),
        8,
        "the control must pay one hash per member"
    );

    // The cheapest refusals of all: a node whose parity count is wrong is
    // refused only AFTER the entry walk, but one that is over the hard limit
    // never reaches the grouping at all.
    let oversized = {
        let mut b = NodeBuilder::branch(1);
        let mut i = 0u32;
        while b.logical_len() < freenet_prolly::boundary::MAX_LOGICAL - 200 {
            b.push_child(
                &[b'k', (i >> 8) as u8, i as u8],
                [i as u8; 32],
                freenet_prolly::node::Agg {
                    count: 1,
                    bytes: 10,
                },
            )
            .unwrap();
            i += 1;
        }
        b.finish().unwrap()
    };
    let n = Node::parse(&oversized).expect("parses");
    work::reset();
    let verdict = check_node(&n);
    if verdict == Ok(()) {
        // It fitted; then it must have paid for every member, which is the
        // honest control for the counter rather than a silent skip.
        assert_eq!(work::hashes(), n.len());
    } else {
        assert!(
            matches!(
                verdict,
                Err(BoundaryError::TooLarge) | Err(BoundaryError::InteriorSplit(_))
            ),
            "unexpected refusal {verdict:?}"
        );
        assert_eq!(work::hashes(), 0, "an entry-level refusal bought grouping");
    }
}
