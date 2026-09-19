//! The write gate: an incremental edit must give exactly the tree a rebuild
//! from scratch gives, emit exactly the nodes that are new, and read only what
//! it touches. `cargo test --test apply -- --nocapture` prints the measurements.

#[path = "common/dataset.rs"]
mod common;
use common::{dataset, rng};

use freenet_prolly::apply::{apply_with, Edit, Options};
use freenet_prolly::boundary::splits_after;
use freenet_prolly::build::{SplitRule, TreeBuilder};
use freenet_prolly::node::{Node, Value, MAX_INLINE};
use freenet_prolly::read::get;
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::{block_id, kind, Cid};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};

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

/// The oracle: build `m` from scratch. Returns the root and the tree's nodes.
fn scratch(rule: SplitRule, m: &Map) -> (Cid, MemBlocks) {
    let mut nodes = MemBlocks::default();
    let mut t = TreeBuilder::with_rule(rule, |c, b: &[u8]| nodes.insert(c, b));
    for (k, v) in m {
        t.push(k, value_of(v)).unwrap();
    }
    (t.finish().unwrap(), nodes)
}

/// A block source that records what was read.
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

fn ids(b: &MemBlocks) -> HashSet<Cid> {
    b.0.keys().copied().collect()
}

#[derive(Default, Debug)]
struct Stats {
    batches: usize,
    edits: usize,
    emitted: usize,
    reads: usize,
    tree_nodes: usize,
    stray_reads: usize,
}

/// One step of the gate. `m` and `store` are advanced to the edited state.
fn step(
    opts: Options,
    m: &mut Map,
    store: &mut MemBlocks,
    root: &mut Cid,
    batch: &[(Vec<u8>, Edit)],
    stats: &mut Stats,
) -> Result<(), String> {
    let rule = opts.rule;
    let (_, old_nodes) = scratch(rule, m);
    let mut noops = 0;
    // Edits that hit the first key of a node: the node before it may have to be
    // re-read (it could have been closed by the hard limit because of that key).
    let first_keys: HashSet<Vec<u8>> = old_nodes
        .0
        .values()
        .map(|b| Node::parse(b).unwrap())
        .filter(|n| !n.is_empty())
        .map(|n| n.key(0))
        .collect();
    let first_key_edits = batch.iter().filter(|(k, _)| first_keys.contains(k)).count();
    for (k, e) in batch {
        let noop = match e {
            Edit::Put(v) => m.get(k) == Some(v),
            Edit::Delete => !m.contains_key(k),
        };
        noops += noop as usize;
        match e {
            Edit::Put(v) => m.insert(k.clone(), v.clone()),
            Edit::Delete => m.remove(k),
        };
    }
    let (want_root, new_nodes) = scratch(rule, m);

    let counting = Counting {
        inner: store,
        reads: RefCell::default(),
    };
    let mut emitted: Vec<(Cid, Vec<u8>)> = Vec::new();
    let applied = apply_with(opts, &counting, root, batch, |c, b| {
        emitted.push((c, b.to_vec()))
    })
    .map_err(|e| format!("apply failed: {e:?}"))?;
    let reads = counting.reads.into_inner();

    if applied.root != want_root {
        return Err("incremental root != from-scratch root".into());
    }
    let (old, new) = (ids(&old_nodes), ids(&new_nodes));
    let emitted_nodes: HashSet<Cid> = emitted
        .iter()
        .filter(|(_, b)| Node::parse(b).is_ok())
        .map(|(c, _)| *c)
        .collect();
    let want_emitted: HashSet<Cid> = new.difference(&old).copied().collect();
    if emitted_nodes != want_emitted {
        return Err(format!(
            "emitted {} nodes, new∖old is {}",
            emitted_nodes.len(),
            want_emitted.len()
        ));
    }
    if emitted.len() != emitted.iter().map(|(c, _)| c).collect::<HashSet<_>>().len() {
        return Err("a block was emitted twice".into());
    }
    if noops == batch.len() && !emitted.is_empty() {
        return Err("a batch that changes nothing emitted a block".into());
    }
    let replaced: HashSet<Cid> = applied.replaced.iter().copied().collect();
    let want_replaced: HashSet<Cid> = old.difference(&new).copied().collect();
    if replaced != want_replaced {
        return Err(format!(
            "replaced {} nodes, old∖new is {}",
            replaced.len(),
            want_replaced.len()
        ));
    }
    // Every value that must live in its own block was emitted, unless it is a no-op.
    for (k, e) in batch {
        if let Edit::Put(v) = e {
            if v.len() > MAX_INLINE && noops == 0 {
                let id = block_id(kind::RAW, v);
                if !emitted.iter().any(|(c, _)| *c == id) && !store.0.contains_key(&id) {
                    return Err(format!("value block for {k:?} never emitted"));
                }
            }
        }
    }
    // Reads: only nodes that were replaced — plus, per no-op edit, its path.
    let stray = reads.difference(&replaced).count();
    let height = Node::parse(&old_nodes.0[root]).unwrap().level() as usize + 1;
    // Above the leaves the neighbour is always re-read when a branch's first
    // child is replaced (no aggregate bound exists there; upper levels are warm).
    let first_child_replaced = old_nodes
        .0
        .values()
        .map(|b| Node::parse(b).unwrap())
        .filter(|n| !n.is_leaf() && replaced.contains(&n.child(0).0))
        .count();
    if stray > (noops + first_key_edits + first_child_replaced) * height {
        let what: Vec<String> = reads
            .difference(&replaced)
            .map(|c| {
                let n = Node::parse(&old_nodes.0[c]).unwrap();
                let touched = batch
                    .iter()
                    .filter(|(k, _)| n.key(0) <= *k && *k <= n.key(n.len() - 1))
                    .count();
                format!(
                    "level {} entries {} edits-in-range {}",
                    n.level(),
                    n.len(),
                    touched
                )
            })
            .collect();
        return Err(format!(
            "{stray} reads outside the replaced nodes ({noops} no-ops, {first_key_edits} first-key edits): {what:?}"
        ));
    }

    for (c, b) in &emitted {
        if block_id(
            if Node::parse(b).is_ok() {
                kind::TREE_NODE
            } else {
                kind::RAW
            },
            b,
        ) != *c
        {
            return Err("an emitted block does not hash to its id".into());
        }
        store.insert(*c, b);
    }
    *root = applied.root;
    stats.batches += 1;
    stats.edits += batch.len();
    stats.emitted += emitted_nodes.len();
    stats.reads += reads.len();
    stats.stray_reads += stray;
    stats.tree_nodes = new.len();
    Ok(())
}

fn random_batch(r: &mut impl FnMut() -> u64, m: &Map, max: usize) -> Vec<(Vec<u8>, Edit)> {
    let n = 1 + (r() as usize % max);
    let keys: Vec<&Vec<u8>> = m.keys().collect();
    let clustered = r().is_multiple_of(2);
    let anchor = if keys.is_empty() {
        0
    } else {
        r() as usize % keys.len()
    };
    let mut out: BTreeMap<Vec<u8>, Edit> = BTreeMap::new();
    for _ in 0..n {
        let existing = (!keys.is_empty()).then(|| {
            let i = if clustered {
                (anchor + (r() as usize % 60)) % keys.len()
            } else {
                r() as usize % keys.len()
            };
            keys[i].clone()
        });
        let fresh = |r: &mut dyn FnMut() -> u64, base: Option<&Vec<u8>>| {
            let mut k = base.cloned().unwrap_or_else(|| b"d/post/".to_vec());
            k.extend_from_slice(&r().to_be_bytes());
            k
        };
        let val = |r: &mut dyn FnMut() -> u64, len: usize| vec![r() as u8; len];
        let (k, e) = match (r() % 10, existing) {
            (0..=2, base) => {
                let len = 40 + (r() % 300) as usize;
                (fresh(r, base.as_ref()), Edit::Put(val(r, len)))
            }
            (3, base) => {
                let len = 1500 + (r() % 3000) as usize;
                (fresh(r, base.as_ref()), Edit::Put(val(r, len)))
            }
            (4, Some(k)) => {
                let len = m[&k].len();
                (k, Edit::Put(val(r, len)))
            }
            (5, Some(k)) => {
                let len = (r() % 900) as usize;
                (k, Edit::Put(val(r, len)))
            }
            (6, Some(k)) => {
                // flip inline <-> reference
                let len = if m[&k].len() > MAX_INLINE { 100 } else { 2000 };
                (k, Edit::Put(val(r, len)))
            }
            (7, Some(k)) => {
                let same = m[&k].clone();
                (k, Edit::Put(same))
            }
            (8, base) => (fresh(r, base.as_ref()), Edit::Delete),
            (_, Some(k)) => (k, Edit::Delete),
            (_, None) => (fresh(r, None), Edit::Put(val(r, 100))),
        };
        out.insert(k, e);
    }
    out.into_iter().collect()
}

fn run(rule: SplitRule, seed: u64, start: usize, batches: usize) -> Result<Stats, String> {
    let mut m: Map = dataset(seed, start).into_iter().collect();
    let (mut root, mut store) = scratch(rule, &m);
    let mut r = rng(seed ^ 0xabcdef);
    let mut stats = Stats::default();
    for _ in 0..batches {
        let batch = random_batch(&mut r, &m, 50);
        let opts = Options {
            rule,
            ..Options::default()
        };
        step(opts, &mut m, &mut store, &mut root, &batch, &mut stats)?;
    }
    // and the tree still answers like the map
    for (k, v) in m.iter().step_by(37) {
        if get(&store, &root, k).map_err(|e| format!("{e:?}"))? != Some(value_of(v)) {
            return Err("get disagrees with the reference map".into());
        }
    }
    Ok(stats)
}

/// Control: a rule that depends on how many entries were pushed before — on the
/// history of the process, not on the contents.
fn history_dependent(_: u8, _: &[u8], _: usize, after: usize) -> bool {
    static PUSHED: AtomicUsize = AtomicUsize::new(0);
    after >= 1024 && PUSHED.fetch_add(1, Ordering::Relaxed).is_multiple_of(29)
}

#[test]
fn random_edit_sequences_match_a_rebuild_and_a_history_dependent_rule_is_caught() {
    let mut total = Stats::default();
    for (seed, start) in [(1u64, 0usize), (2, 30), (3, 3000), (4, 20_000)] {
        let s = run(splits_after, seed, start, 60).unwrap();
        println!(
            "start {start:5}: {} batches, {} edits, tree {} nodes; per batch: {:.1} nodes emitted, {:.1} read; {} reads outside replaced nodes",
            s.batches,
            s.edits,
            s.tree_nodes,
            s.emitted as f64 / s.batches as f64,
            s.reads as f64 / s.batches as f64,
            s.stray_reads
        );
        total.batches += s.batches;
    }
    assert_eq!(total.batches, 240);
    let control = run(history_dependent, 3, 3000, 60);
    println!("history-dependent control: {control:?}");
    assert!(
        control.is_err(),
        "the gate must catch a history-dependent rule"
    );
}

fn put(k: &[u8], v: &[u8]) -> (Vec<u8>, Edit) {
    (k.to_vec(), Edit::Put(v.to_vec()))
}
fn del(k: &[u8]) -> (Vec<u8>, Edit) {
    (k.to_vec(), Edit::Delete)
}

/// Run one batch through the full gate on a tree built from `m`.
fn check(m: &mut Map, batch: Vec<(Vec<u8>, Edit)>) -> Stats {
    try_check(Options::default(), m, batch).unwrap()
}
fn try_check(opts: Options, m: &mut Map, batch: Vec<(Vec<u8>, Edit)>) -> Result<Stats, String> {
    let (mut root, mut store) = scratch(opts.rule, m);
    let mut stats = Stats::default();
    step(opts, m, &mut store, &mut root, &batch, &mut stats)?;
    Ok(stats)
}

/// Leaves of the tree for `m`, in key order, as (first key, last key).
fn leaves(m: &Map) -> Vec<(Vec<u8>, Vec<u8>)> {
    let (_, nodes) = scratch(splits_after, m);
    let mut v: Vec<_> = nodes
        .0
        .values()
        .map(|b| Node::parse(b).unwrap())
        .filter(|n| n.is_leaf() && !n.is_empty())
        .map(|n| (n.key(0), n.key(n.len() - 1)))
        .collect();
    v.sort();
    v
}

#[test]
fn named_edge_cases() {
    let base: Map = dataset(9, 6000).into_iter().collect();
    let lv = leaves(&base);
    assert!(lv.len() > 100);
    let (first5, last5) = (&lv[5], &lv[lv.len() - 1]);

    // delete a node's first key; change its size; insert into the gap before it
    // (on honest data the parent's aggregate proves the leaf before was not
    // force-closed, so touching a first key reads nothing extra at the leaves)
    for batch in [vec![del(&first5.0)], vec![put(&first5.0, &[1; 700])]] {
        let s = check(&mut base.clone(), batch);
        assert_eq!(s.stray_reads, 0, "no read outside the replaced nodes");
    }
    let mut gap = lv[4].1.clone();
    gap.push(0);
    assert!(gap < first5.0 && !base.contains_key(&gap));
    check(&mut base.clone(), vec![put(&gap, &[2; 90])]);

    // delete a whole node; the level's last node; first and last node at once
    let whole = |a: &Vec<u8>, b: &Vec<u8>| -> Vec<(Vec<u8>, Edit)> {
        base.range(a.clone()..=b.clone())
            .map(|(k, _)| del(k))
            .collect()
    };
    check(&mut base.clone(), whole(&first5.0, &first5.1));
    check(&mut base.clone(), whole(&last5.0, &last5.1));
    let mut both = whole(&lv[0].0, &lv[0].1);
    both.extend(whole(&last5.0, &last5.1));
    check(&mut base.clone(), both);

    // append past the end; prepend before the start
    check(&mut base.clone(), vec![put(&[0xff; 20], &[3; 50])]);
    check(&mut base.clone(), vec![put(&[0x00], &[3; 50])]);

    // inline <-> reference, and a no-op batch emits nothing and reads little
    let k = base.keys().nth(3000).unwrap().clone();
    let mut m = base.clone();
    check(&mut m, vec![put(&k, &[4; 5000])]);
    check(&mut m, vec![put(&k, &[4; 10])]);
    let same = base[&k].clone();
    let s = check(
        &mut base.clone(),
        vec![put(&k, &same), del(b"zzz-absent-key")],
    );
    assert_eq!(s.emitted, 0, "a no-op batch emits nothing");
    // ... also when the unchanged value lives in its own block
    let mut m = base.clone();
    check(&mut m, vec![put(&k, &[4; 5000])]);
    check(&mut m, vec![put(&k, &[4; 5000])]);
}

#[test]
fn height_collapses_and_grows_in_one_batch() {
    let base: Map = dataset(10, 9000).into_iter().collect();
    let height = |m: &Map| {
        let (root, nodes) = scratch(splits_after, m);
        Node::parse(&nodes.0[&root]).unwrap().level() + 1
    };
    assert!(height(&base) >= 3);

    // 3 levels -> one leaf
    let mut m = base.clone();
    let batch: Vec<_> = base.keys().skip(5).map(|k| del(k)).collect();
    check(&mut m, batch);
    assert_eq!((m.len(), height(&m)), (5, 1));

    // 3 levels -> empty
    let mut m = base.clone();
    check(&mut m, base.keys().map(|k| del(k)).collect());
    assert!(m.is_empty());

    // empty -> 3 levels, and one leaf -> 3 levels
    let all: Vec<_> = base.iter().map(|(k, v)| put(k, v)).collect();
    let mut m = Map::new();
    check(&mut m, all.clone());
    assert_eq!(height(&m), height(&base));
    let mut m: Map = base
        .iter()
        .take(5)
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    check(&mut m, all);
    assert_eq!(m, base);
}

/// A leaf closed by the hard limit ends because of the entry AFTER it. Editing
/// that entry must re-chunk the leaf before it.
#[test]
fn an_edit_behind_a_force_closed_node_rechunks_it() {
    use freenet_prolly::boundary::MAX_LOGICAL;
    use freenet_prolly::node::{NodeBuilder, HEADER};
    let big = vec![7u8; 1000];
    let mut m = Map::new();
    let mut s = HEADER;
    let mut i = 0;
    while s + NodeBuilder::leaf_cost(b"99999", &Value::Inline(&big)) <= MAX_LOGICAL {
        let key = (0..)
            .map(|j| format!("{i:05}.{j}").into_bytes())
            .find(|k| {
                let c = NodeBuilder::leaf_cost(k, &Value::Inline(b""));
                !splits_after(0, k, s, s + c)
            })
            .unwrap();
        s += NodeBuilder::leaf_cost(&key, &Value::Inline(b""));
        m.insert(key, vec![]);
        i += 1;
    }
    let filled = m.len();
    m.insert(b"99999".to_vec(), big);
    m.extend(dataset(2, 400).into_iter().map(|(mut k, v)| {
        k.insert(0, b'z');
        (k, v)
    }));
    let lv = leaves(&m);
    assert_eq!(
        lv[1].0,
        b"99999".to_vec(),
        "the big entry opens the second leaf"
    );
    assert_eq!(
        m.range(..b"99999".to_vec()).count(),
        filled,
        "and the first leaf was closed by the limit"
    );
    // Shrinking or deleting the entry lets the first leaf take more: a rebuild
    // moves that boundary, so the edit must too. The gate compares them.
    check(&mut m.clone(), vec![put(b"99999", &[1; 3])]);
    check(&mut m.clone(), vec![del(b"99999")]);
    // Control: without the neighbour re-check the same edits give a wrong tree.
    let off = Options {
        recheck_neighbour: false,
        ..Options::default()
    };
    for batch in [vec![put(b"99999", &[1; 3])], vec![del(b"99999")]] {
        let got = try_check(off, &mut m.clone(), batch);
        assert_eq!(
            got.err().as_deref(),
            Some("incremental root != from-scratch root")
        );
    }
}

#[test]
fn a_rejected_batch_leaves_no_trace() {
    use freenet_prolly::apply::{apply, ApplyError, MAX_VALUE};
    let m: Map = dataset(11, 2000).into_iter().collect();
    let (root, store) = scratch(splits_after, &m);
    let k = m.keys().nth(900).unwrap().clone();
    type Batch = Vec<(Vec<u8>, Edit)>;
    let bad: Vec<(Batch, ApplyError)> = vec![
        (
            vec![put(b"b", b"1"), put(b"a", b"2")],
            ApplyError::NotSorted,
        ),
        (
            vec![put(b"a", b"1"), put(b"a", b"2")],
            ApplyError::NotSorted,
        ),
        (
            vec![put(&k, b"x"), put(&[b'z'; 600], b"")],
            ApplyError::KeyTooLong,
        ),
        (
            vec![put(&k, b"x"), put(b"zz", &vec![0; MAX_VALUE + 1])],
            ApplyError::ValueTooLong,
        ),
    ];
    for (batch, want) in bad {
        let counting = Counting {
            inner: &store,
            reads: RefCell::default(),
        };
        let mut emitted = 0;
        let got = apply(&counting, &root, &batch, |_, _| emitted += 1);
        assert_eq!(got, Err(want));
        assert_eq!(emitted, 0);
        assert!(
            counting.reads.borrow().is_empty(),
            "refused before any read"
        );
    }
    // the largest legal value is accepted
    let mut ok = 0;
    apply(&store, &root, &[put(b"zz", &vec![0; MAX_VALUE])], |_, _| {
        ok += 1
    })
    .unwrap();
    assert!(ok >= 2);
}

/// Start holding only what `Need` names, one round at a time.
#[test]
fn a_cold_edit_resumes_round_by_round_and_emits_only_at_the_end() {
    use freenet_prolly::apply::{apply, ApplyError};
    use freenet_prolly::store::ReadError;
    let mut m: Map = dataset(12, 20_000).into_iter().collect();
    let (root, full) = scratch(splits_after, &m);
    let mut r = rng(77);
    println!("cold apply: rounds (one Need per round), 20k entries");
    for size in [1usize, 5, 25] {
        let mut batch = BTreeMap::new();
        while batch.len() < size {
            let k = m.keys().nth(r() as usize % m.len()).unwrap().clone();
            batch.insert(k, Edit::Put(vec![r() as u8; 200]));
        }
        let batch: Vec<_> = batch.into_iter().collect();
        let mut held = MemBlocks::default();
        let (mut rounds, mut fetched, mut widest) = (0, 0, 0);
        let emitted;
        let applied = loop {
            let mut out = Vec::new();
            match apply(&held, &root, &batch, |c, b| out.push((c, b.to_vec()))) {
                Ok(a) => {
                    emitted = out;
                    break a;
                }
                Err(ApplyError::Read(ReadError::Need(ids))) => {
                    assert!(out.is_empty(), "nothing is emitted before success");
                    assert!(!ids.is_empty());
                    rounds += 1;
                    fetched += ids.len();
                    widest = widest.max(ids.len());
                    for id in ids {
                        held.insert(id, &full.0[&id]);
                    }
                }
                Err(e) => panic!("{e:?}"),
            }
        };
        for (k, e) in &batch {
            if let Edit::Put(v) = e {
                m.insert(k.clone(), v.clone());
            }
        }
        assert_eq!(applied.root, scratch(splits_after, &m).0);
        assert!(!emitted.is_empty());
        println!(
            "  batch {size:2}: {rounds} rounds, {fetched} blocks fetched, widest round {widest}"
        );
        assert!(
            fetched < 12 * size + 8,
            "fetched {fetched} for {size} edits"
        );
        m = dataset(12, 20_000).into_iter().collect();
    }
}

/// The issue's own statement: any order of single edits that ends with the same
/// contents ends with the same root.
#[test]
fn any_edit_order_reaches_the_same_root() {
    use freenet_prolly::apply::apply;
    let target: Map = dataset(13, 1500).into_iter().collect();
    let mut roots = Vec::new();
    for seed in [1u64, 2, 3] {
        let mut r = rng(seed);
        let mut order: Vec<&Vec<u8>> = target.keys().collect();
        for i in (1..order.len()).rev() {
            order.swap(i, r() as usize % (i + 1));
        }
        let (mut root, mut store) = scratch(splits_after, &Map::new());
        // insert in this order, with detours: junk keys added and removed again,
        // values first written wrong and then corrected
        for (n, k) in order.iter().enumerate() {
            let mut edits = vec![put(k, if n % 3 == 0 { b"wrong" } else { &target[*k] })];
            if n % 5 == 0 {
                let mut junk = (*k).clone();
                junk.push(b'~');
                edits.push(put(&junk, b"junk"));
            }
            for e in edits {
                let mut out = Vec::new();
                root = apply(&store, &root, &[e], |c, b| out.push((c, b.to_vec())))
                    .unwrap()
                    .root;
                out.iter().for_each(|(c, b)| store.insert(*c, b));
            }
        }
        for (n, k) in order.iter().enumerate() {
            let mut edits = Vec::new();
            if n % 3 == 0 {
                edits.push(put(k, &target[*k]));
            }
            if n % 5 == 0 {
                let mut junk = (*k).clone();
                junk.push(b'~');
                edits.push(del(&junk));
            }
            for e in edits {
                let mut out = Vec::new();
                root = apply(&store, &root, &[e], |c, b| out.push((c, b.to_vec())))
                    .unwrap()
                    .root;
                out.iter().for_each(|(c, b)| store.insert(*c, b));
            }
        }
        roots.push(root);
    }
    assert_eq!(roots[0], scratch(splits_after, &target).0);
    assert!(roots.iter().all(|r| *r == roots[0]));
}
