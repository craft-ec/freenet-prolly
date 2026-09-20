//! The write gate: an incremental edit must give exactly the tree a rebuild
//! from scratch gives, emit exactly the nodes that are new, and read only what
//! it touches. `cargo test --test apply -- --nocapture` prints the measurements.

#[path = "common/dataset.rs"]
mod common;
#[path = "common/invariants.rs"]
mod invariants;
use common::{dataset, rng};
use invariants::check_tree;

use freenet_prolly::apply::{apply_with, Edit, Options};
use freenet_prolly::boundary::splits_after;
use freenet_prolly::build::{SplitRule, TreeBuilder};
use freenet_prolly::node::{Node, Value, MAX_INLINE};
use freenet_prolly::parity::MAX_GROUP;

/// Members a single edit can drag in: one group per level of the path, each up
/// to `MAX_GROUP`. Named rather than inlined so the number has a reason.
fn parity_budget() -> usize {
    5 * MAX_GROUP
}
use freenet_prolly::read::get;
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::{block_id, kind, Cid};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
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

/// The oracle: build `m` from scratch. Returns the root and the tree's blocks.
///
/// It pushes RAW BYTES, so the inline-or-reference choice is made by the
/// library's own `Value::for_bytes` — the same call `apply` makes. An oracle
/// that restated the rule could drift from it, and then this gate would be
/// comparing two implementations of one mistake.
fn scratch(rule: SplitRule, m: &Map) -> (Cid, MemBlocks) {
    let mut nodes = MemBlocks::default();
    let mut t = TreeBuilder::with_rule(rule, |c, b: &[u8]| {
        // Only the NODES: this oracle is about the tree's shape, and everything
        // downstream reads every block here as one.
        if Node::parse(b).is_ok() {
            nodes.insert(c, b);
        }
    });
    for (k, v) in m {
        t.push_bytes(k, v).unwrap();
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

/// Is the from-scratch comparison in force? Off under
/// `PROLLY_NO_REBUILD_COMPARE=1`, which is how the invariant walk is shown to
/// stand on its own: with the rebuild silenced, a write path that loses a
/// subtree must still be caught, by the walk and nothing else.
///
/// It silences EVERY check derived from a rebuild — the root, the emitted set,
/// the replaced set and the read budget — because silencing only the root
/// comparison leaves the emitted-set check to fail first and mask the walk. The
/// point of the control is that the walk is the thing that speaks, so nothing
/// else may be in a position to speak instead.
///
/// # The two checks do not subsume each other
///
/// With the switch on and NOTHING broken, exactly two tests fail:
/// `an_edit_behind_a_force_closed_node_rechunks_it` and
/// `random_edit_sequences_match_a_rebuild_and_a_history_dependent_rule_is_caught`.
/// That is correct, and it is the clearest statement of what each check is for.
/// Both of those tests are negative controls that ASSERT the rebuild comparison
/// catches a broken rule — so silencing it is exactly what they are built to
/// notice.
///
/// The walk proves the result is **a** tree. The rebuild comparison proves it is
/// **the** tree. A history-dependent split rule and a skipped neighbour re-check
/// both produce well-formed, internally consistent trees that are simply not the
/// canonical one for their contents, and the walk accepts every one of them.
/// C2 is the converse: a forged aggregate is carried identically by the
/// incremental tree and the rebuild, so the roots agree and only the walk
/// objects. Neither check is a weaker version of the other, and running this
/// suite with the switch permanently on would be a real loss of coverage rather
/// than a stricter mode.
fn compare_rebuild() -> bool {
    std::env::var_os("PROLLY_NO_REBUILD_COMPARE").is_none()
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

    let rebuild = compare_rebuild();
    if rebuild && applied.root != want_root {
        return Err("incremental root != from-scratch root".into());
    }
    let (old, new) = (ids(&old_nodes), ids(&new_nodes));
    let emitted_nodes: HashSet<Cid> = emitted
        .iter()
        .filter(|(_, b)| Node::parse(b).is_ok())
        .map(|(c, _)| *c)
        .collect();
    let want_emitted: HashSet<Cid> = new.difference(&old).copied().collect();
    if rebuild && emitted_nodes != want_emitted {
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
    if rebuild && replaced != want_replaced {
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
    let height = Node::parse(&old_nodes.0[root]).unwrap().level() as usize + 1;
    // Which node an edit LANDS in, at each level: the last one whose first key
    // is at or below the edit's — the rule the descent itself uses.
    //
    // A node's ENTRIES are not its coverage. A key in the gap after a node's
    // last entry still lands in that node, and re-chunking it can leave it
    // byte-identical: an insert that starts a node of its own leaves everything
    // before it alone. So the node is read, is not "replaced", and is exactly
    // the one the edit went to. Judging that by "does an edit fall between this
    // node's first and last entry" calls a legitimate read a stray one.
    let mut by_level: HashMap<u8, Vec<(Vec<u8>, Cid)>> = HashMap::new();
    for (id, b) in old_nodes.0.iter() {
        let n = Node::parse(b).unwrap();
        if !n.is_empty() {
            by_level.entry(n.level()).or_default().push((n.key(0), *id));
        }
    }
    let mut landed: HashSet<Cid> = HashSet::new();
    for nodes in by_level.values_mut() {
        nodes.sort();
        for (k, _) in batch {
            let i = match nodes.binary_search_by(|(min, _)| min.cmp(k)) {
                Ok(i) => i,
                Err(0) => 0,
                Err(i) => i - 1,
            };
            landed.insert(nodes[i].1);
        }
    }
    // PARITY MEMBERS. Every group a rebuild touches is recoded from its
    // members, so the members of every node the rebuild emitted are legitimate
    // reads — and ONLY those. Stated exactly rather than as "parity reads
    // something": an accidental whole-node read still shows as stray, because a
    // node that is not a member of anything the rebuild emitted is not in here.
    // What a rewrite may read besides nodes: the blocks the nodes NAME.
    //
    // A group's parity is a pure function of its members, so a rewrite gets its
    // ids from one of three places — copied from an old node that already had
    // the group, corrected from that node's three parity blocks and the one
    // member that changed, or coded from the members. The second and third read
    // blocks the old node names; the third reads blocks the new node names.
    //
    // It is stated as "named by a node this rewrite touched" and not as "parity
    // reads something": a node that is a member of nothing involved is still
    // stray, which is the walk-the-whole-tree failure this guards against.
    let mut named: HashSet<Cid> = HashSet::new();
    let mut note = |n: &Node<'_>| {
        for i in 0..n.len() {
            if n.is_leaf() {
                if let freenet_prolly::node::Value::Ref { cid, .. } = n.value(i) {
                    named.insert(cid);
                }
            } else {
                named.insert(n.child(i).0);
            }
        }
        for p in n.parity() {
            named.insert(p);
        }
    };
    for bytes in new_nodes.0.values() {
        note(&Node::parse(bytes).unwrap());
    }
    for c in &replaced {
        if let Some(bytes) = old_nodes.0.get(c) {
            note(&Node::parse(bytes).unwrap());
        }
    }
    let members = named;
    let stray = reads
        .difference(&replaced)
        .filter(|c| !landed.contains(*c))
        .filter(|c| !members.contains(*c))
        .count();
    // Above the leaves the neighbour is always re-read when a branch's first
    // child is replaced (no aggregate bound exists there; upper levels are warm).
    let first_child_replaced = old_nodes
        .0
        .values()
        .map(|b| Node::parse(b).unwrap())
        .filter(|n| !n.is_leaf() && replaced.contains(&n.child(0).0))
        .count();
    if rebuild && stray > (noops + first_key_edits + first_child_replaced) * height {
        let what: Vec<String> = reads
            .difference(&replaced)
            .filter(|c| !landed.contains(*c))
            .filter(|c| !members.contains(*c))
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
    // The second witness. The comparisons above are all against a from-scratch
    // rebuild; this one asks whether what we have is a tree, independently of
    // what a rebuild would have produced. Set PROLLY_NO_REBUILD_COMPARE to turn
    // the rebuild off and leave the walk holding the gate on its own — that is
    // the control, and it has to fail on a broken write path.
    check_tree(store, root, m).map_err(|e| format!("invariant walk: {e}"))?;
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
        // The walk needs every block of the NEW tree: what the rounds fetched,
        // plus what this apply emitted.
        let mut after = full.clone();
        emitted.iter().for_each(|(c, b)| after.insert(*c, b));
        check_tree(&after, &applied.root, &m).unwrap();
        println!(
            "  batch {size:2}: {rounds} rounds, {fetched} blocks fetched, widest round {widest}"
        );
        // A cold edit now also fetches the MEMBERS of every group it touches,
        // because this version recodes each touched group from its members
        // rather than updating the old parity. That is the honest cost of the
        // simple writer: up to MAX_GROUP members per touched group, on each
        // level of the path. The optimisation — delta from the three old
        // parity blocks, which needs none of those reads — is a separate
        // change behind a byte-equality oracle (freenet-prolly#19, PR B), and
        // this bound comes back down with it.
        let per_edit = 12 + parity_budget();
        assert!(
            fetched < per_edit * size + 8 + 4 * MAX_GROUP,
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
        check_tree(&store, &root, &target).unwrap();
        roots.push(root);
    }
    assert_eq!(roots[0], scratch(splits_after, &target).0);
    assert!(roots.iter().all(|r| *r == roots[0]));
}

/// A level can shrink to one node that the batch never touched: everything else
/// is deleted. The survivor itself is then the root — not a branch holding it.
#[test]
fn deleting_everything_but_an_untouched_node_makes_that_node_the_root() {
    let keep_leaf = |n: usize, which: &dyn Fn(usize) -> usize| {
        let base: Map = dataset(3, n).into_iter().collect();
        let lv = leaves(&base);
        let (lo, hi) = lv[which(lv.len())].clone();
        let batch: Vec<_> = base
            .keys()
            .filter(|k| **k < lo || **k > hi)
            .map(|k| del(k))
            .collect();
        let mut m = base.clone();
        let r = try_check(Options::default(), &mut m, batch);
        (lv.len(), r.map(|_| ()))
    };
    let mut failures = 0;
    for (n, name, which) in [
        (200usize, "first", &(|_| 0usize) as &dyn Fn(usize) -> usize),
        (200, "last", &|len| len - 1),
        (6000, "#40", &|_| 40usize),
        (30_000, "#700", &|_| 700usize),
    ] {
        let (leaves, r) = keep_leaf(n, which);
        println!("n={n} leaves={leaves} keep={name}: {r:?}");
        failures += r.is_err() as usize;
    }
    assert_eq!(failures, 0);
    // One level up: keep one whole level-1 subtree of a height-3 tree.
    let base: Map = dataset(3, 30_000).into_iter().collect();
    let (_, nodes) = scratch(splits_after, &base);
    let mut level1: Vec<Vec<u8>> = nodes
        .0
        .values()
        .map(|b| Node::parse(b).unwrap())
        .filter(|n| n.level() == 1)
        .map(|n| n.key(0))
        .collect();
    level1.sort();
    assert!(level1.len() > 8, "the tree has a level above level 1");
    let (lo, hi) = (level1[3].clone(), level1[4].clone());
    let batch: Vec<_> = base
        .keys()
        .filter(|k| **k < lo || **k >= hi)
        .map(|k| del(k))
        .collect();
    let mut m = base.clone();
    try_check(Options::default(), &mut m, batch).unwrap();
    assert!(m.len() > 100);
}

#[derive(Clone, Copy, Debug)]
enum Order {
    /// Every key above the last: an append-only log, a feed, records keyed by
    /// time. This is the pattern the gate never ran, and #22 lived in it.
    Ascending,
    /// Every key below the first.
    Descending,
    /// Ends inward, so both edges of the tree move.
    Alternating,
}

fn ordered_keys(n: usize, order: Order) -> Vec<Vec<u8>> {
    let k = |i: usize| format!("k/{i:08}").into_bytes();
    match order {
        Order::Ascending => (0..n).map(k).collect(),
        Order::Descending => (0..n).rev().map(k).collect(),
        Order::Alternating => (0..n)
            .map(|i| {
                if i % 2 == 0 {
                    k(i / 2)
                } else {
                    k(n - 1 - i / 2)
                }
            })
            .collect(),
    }
}

/// Write `n` entries in `order`, `per_batch` at a time, through the full gate —
/// which compares against a from-scratch build AND checks that exactly the new
/// nodes were emitted. The second part matters here: the fix must not start
/// re-emitting a node that survived unchanged, only reference it.
fn run_ordered(vlen: usize, order: Order, per_batch: usize, n: usize) -> Result<(), String> {
    let mut m = Map::new();
    let (mut root, mut store) = scratch(splits_after, &m);
    let mut stats = Stats::default();
    let keys = ordered_keys(n, order);
    for (b, chunk) in keys.chunks(per_batch).enumerate() {
        let mut batch: Vec<(Vec<u8>, Edit)> = chunk
            .iter()
            .map(|k| (k.clone(), Edit::Put(vec![(b % 251) as u8; vlen])))
            .collect();
        // The gate takes a sorted batch; which ORDER the batches arrive in is
        // what this test varies.
        batch.sort_by(|a, b| a.0.cmp(&b.0));
        step(
            Options::default(),
            &mut m,
            &mut store,
            &mut root,
            &batch,
            &mut stats,
        )
        .map_err(|e| {
            format!(
                "vlen {vlen} {order:?} batch {per_batch} at {}: {e}",
                b * per_batch
            )
        })?;
    }
    Ok(())
}

/// #22: an append that lands in a new node leaves everything before it
/// byte-identical. When that happens at the old ROOT's level, nothing holds the
/// surviving node — the level above does not exist yet — so it has to be passed
/// up along with its new sibling.
#[test]
fn writing_in_key_order_equals_a_rebuild() {
    let mut runs = 0;
    for vlen in [0usize, 150, 900] {
        // Enough entries to cross several splits at every size.
        let n = (20_000 / (vlen + 12) + 30).min(400);
        for order in [Order::Ascending, Order::Descending, Order::Alternating] {
            for per_batch in [1usize, 5] {
                run_ordered(vlen, order, per_batch, n).unwrap();
                runs += 1;
            }
        }
    }
    assert_eq!(runs, 18);
}

/// The same shape one level up: a height-2 tree whose ROOT BRANCH splits while
/// its first branch survives byte-identically.
#[test]
fn an_append_that_splits_a_root_branch_keeps_the_tree() {
    let mut m = Map::new();
    let (mut root, mut store) = scratch(splits_after, &m);
    let mut stats = Stats::default();
    let mut heights = Vec::new();
    for i in 0..4000u32 {
        let batch = vec![(
            format!("k/{i:08}").into_bytes(),
            Edit::Put(vec![(i % 251) as u8; 300]),
        )];
        step(
            Options::default(),
            &mut m,
            &mut store,
            &mut root,
            &batch,
            &mut stats,
        )
        .unwrap_or_else(|e| panic!("append {i}: {e}"));
        let h = Node::parse(&store.0[&root]).unwrap().level() + 1;
        if heights.last() != Some(&h) {
            heights.push(h);
        }
    }
    println!("appending 4000 entries: heights seen {heights:?}");
    assert!(
        heights.contains(&3),
        "the tree must have grown past height 2, so a root BRANCH split: {heights:?}"
    );
    assert_eq!(m.len(), 4000);
}

/// The SDK's real pattern, at a size where it would be noticed: 20k appends one
/// at a time, checked against the oracle as it goes. `step` is O(n) per call, so
/// this drives `apply` directly and rebuilds only at checkpoints.
#[test]
fn twenty_thousand_appends_one_at_a_time() {
    use freenet_prolly::apply::apply;
    let mut m = Map::new();
    let (mut root, mut store) = scratch(splits_after, &m);
    let mut checks = 0;
    for i in 0..20_000u32 {
        let (k, v) = (format!("k/{i:08}").into_bytes(), vec![(i % 251) as u8; 120]);
        let mut out = Vec::new();
        root = apply(
            &store,
            &root,
            &[(k.clone(), Edit::Put(v.clone()))],
            |c, b| out.push((c, b.to_vec())),
        )
        .unwrap()
        .root;
        for (c, b) in &out {
            store.insert(*c, b);
        }
        m.insert(k, v);
        if i % 1000 == 999 || i < 40 {
            assert_eq!(
                root,
                scratch(splits_after, &m).0,
                "diverged at {} entries",
                m.len()
            );
            check_tree(&store, &root, &m).unwrap();
            checks += 1;
        }
    }
    let h = Node::parse(&store.0[&root]).unwrap().level() + 1;
    println!("20k appends: final height {h}, {} checkpoints", checks);
    assert!(h >= 3, "20k entries should be at least three levels deep");
    // And the whole tree still reads back.
    for (k, v) in m.iter().step_by(97) {
        assert_eq!(get(&store, &root, k).unwrap(), Some(value_of(v)));
    }
}

/// **Reuse changes what is READ, never what is WRITTEN.**
///
/// Parity is a pure function of a group's members, so copying an untouched
/// group's ids from the node being replaced and coding that group from its
/// members must give the same three ids. This is the oracle for that: every
/// case below is applied incrementally AND built from scratch, and the two
/// trees are required to be identical block for block — not merely to have the
/// same root, which a shared bug in both paths could satisfy.
///
/// The cases are the ones where the grouping is most likely to move: an update
/// with no membership change, an insert that shifts a group boundary and one
/// that does not, a delete, a value crossing a size class, and a short tail
/// folding and unfolding.
#[test]
fn reuse_gives_the_same_bytes_as_coding_every_group() {
    use freenet_prolly::chunk::source;

    // Values large enough to be stored by REFERENCE, so the leaves carry parity
    // and the leaf grouping (by size class) is exercised, not only the branches.
    let big = |n: usize, b: u8| vec![b; n];
    let mut base: Map = dataset(11, 900).into_iter().collect();
    for (i, (_, v)) in base.iter_mut().enumerate() {
        // A spread across the first two size classes.
        *v = big(if i % 3 == 0 { 1100 } else { 5000 }, i as u8);
    }
    let keys: Vec<Vec<u8>> = base.keys().cloned().collect();
    let mid = keys[keys.len() / 2].clone();
    let mut before_mid = keys[keys.len() / 2 - 1].clone();
    before_mid.push(0);
    let mut fresh = keys[3].clone();
    fresh.push(7);

    // Named so the list reads as what it is: each case is a label and the
    // batch that case applies.
    type Case = (&'static str, Vec<(Vec<u8>, Edit)>);
    let cases: Vec<Case> = vec![
        (
            "an update beneath a child, no membership change",
            vec![put(&mid, &big(5000, 0xaa))],
        ),
        (
            "an insert between two existing keys",
            vec![put(&before_mid, &big(5000, 0xbb))],
        ),
        (
            "another insert, elsewhere",
            vec![put(&fresh, &big(5000, 0xcc))],
        ),
        ("a delete", vec![del(&mid)]),
        (
            "a value crossing a size class",
            vec![put(&keys[1], &big(20_000, 0xdd))],
        ),
        (
            "several edits at once, which moves boundaries",
            keys.iter()
                .step_by(97)
                .map(|k| put(k, &big(1100, 0xee)))
                .collect(),
        ),
    ];

    // Every case runs twice. With the writer's parity blocks in the store a
    // one-member change can be CORRECTED; without them the same change must
    // fall back to a recode. Both passes assert the same bytes, so the fallback
    // is a negative control that actually executes rather than a comment about
    // one.
    for (what, batch) in &cases {
        let mut counts = Vec::new();
        for with_parity in [true, false] {
            let mut m = base.clone();
            let (mut root, mut store) = scratch(splits_after, &m);
            // Values live in the store too: a leaf's parity is over them.
            for (k, v) in &m {
                let _ = k;
                let (val, block) = freenet_prolly::node::Value::for_bytes(v);
                let _ = val;
                if let Some((c, b)) = block {
                    store.insert(c, b);
                }
            }

            // The parity BLOCKS a writer would have put after its own commit. The
            // library lists parity ids and does not emit the bytes, so a writer
            // that did not keep them has nothing to correct — which is the second
            // pass.
            if with_parity {
                let mut parity_blocks: Vec<(Cid, Vec<u8>)> = Vec::new();
                for bytes in store.0.values() {
                    if let Ok(n) = Node::parse(bytes) {
                        if let Some(ps) = freenet_prolly::parity::blocks_of(&n, &store) {
                            parity_blocks.extend(ps);
                        }
                    }
                }
                for (c, b) in parity_blocks {
                    store.insert(c, &b);
                }
            }

            source::reset();
            let applied = freenet_prolly::apply::apply_into(&mut store, &root, batch)
                .unwrap_or_else(|e| panic!("{what}: {e:?}"));
            root = applied.root;
            let (reused, delta, recoded) = (source::reused(), source::delta(), source::recoded());

            for (k, e) in batch {
                match e {
                    Edit::Put(v) => {
                        m.insert(k.clone(), v.clone());
                    }
                    Edit::Delete => {
                        m.remove(k);
                    }
                }
            }
            let (want_root, want_nodes) = scratch(splits_after, &m);
            assert_eq!(root, want_root, "{what}: the root differs from a rebuild");

            // Block for block, not just the root: identical roots with different
            // parity ids is impossible, but identical roots are also what a bug
            // shared by both paths would produce, so the nodes are compared too.
            for (cid, bytes) in &want_nodes.0 {
                let got = store
                    .0
                    .get(cid)
                    .unwrap_or_else(|| panic!("{what}: the rebuild's node {cid:?} is missing"));
                assert_eq!(got, bytes, "{what}: node bytes differ");
            }

            // And reuse must actually have happened, or the equality above is the
            // equality of two recodes and this test is about nothing.
            assert!(
                reused > 0,
                "{what}: no group was reused ({reused} reused, {recoded} recoded)"
            );
            // And the delta path is the point of the first pass; without this the
            // two passes could be the same run twice.
            if with_parity {
                assert!(
                delta > 0,
                "{what}: the old parity was there and no group was corrected ({reused} reused, {delta} delta, {recoded} recoded)"
            );
            } else {
                assert_eq!(
                    delta, 0,
                    "{what}: no old parity block exists, yet a group claimed to correct one"
                );
            }
            let held = if with_parity {
                "parity held"
            } else {
                "no parity  "
            };
            println!("  {held}  {reused:3} reused, {delta:3} delta, {recoded:3} recoded  {what}");
            counts.push((reused, delta, recoded));
        }

        // The two passes must differ in exactly one way: the groups the first
        // CORRECTED are the groups the second RE-CODED. Equal reuse, and equal
        // work overall, is what says the fallback caught precisely the delta
        // path's groups and did not quietly widen or narrow.
        let ((r0, d0, c0), (r1, d1, c1)) = (counts[0], counts[1]);
        assert_eq!(r0, r1, "{what}: reuse should not depend on holding parity");
        assert_eq!(
            d0 + c0,
            d1 + c1,
            "{what}: {d0} corrected + {c0} recoded, but without parity {d1} + {c1}"
        );
    }
}
