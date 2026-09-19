//! The measurements for #8, as the document itself.
//!
//!     cargo run --release --example measure > docs/MEASUREMENTS.md
//!
//! Everything printed is measured here, now, on the tree this commit builds.
//! Where a number could not be obtained the table says "not measured" and why —
//! it is never filled in from somewhere else.

#[path = "../tests/common/dataset.rs"]
mod common;

use common::{dataset, rng};
use freenet_prolly::aggregate::{aggregate, aggregate_verified};
use freenet_prolly::apply::{apply, apply_into, Edit};
use freenet_prolly::build::init;
use freenet_prolly::diff::{diff, DiffError};
use freenet_prolly::node::Node;
use freenet_prolly::range::{range, Range, RangeError};
use freenet_prolly::read::get;
use freenet_prolly::store::{MemBlocks, ReadError};
use freenet_prolly::Cid;
use std::collections::{BTreeMap, HashSet};
use std::time::{Duration, Instant};

type Map = BTreeMap<Vec<u8>, Vec<u8>>;

// ---------------------------------------------------------------------------
// datasets
// ---------------------------------------------------------------------------

/// The realistic shape: records, edges and index terms, keys out of order.
fn realistic(n: usize) -> Map {
    dataset(7, n).into_iter().collect()
}

/// Time-ordered: every key above the last, which is what a log, a feed, a
/// message thread and every record keyed by creation time actually produce.
fn append_only(n: usize) -> Map {
    (0..n)
        .map(|i| {
            (
                format!("r/{:016x}", i).into_bytes(),
                vec![(i % 251) as u8; 150],
            )
        })
        .collect()
}

fn appended_edits(from: usize, count: usize) -> Vec<(Vec<u8>, Edit)> {
    (from..from + count)
        .map(|i| {
            (
                format!("r/{:016x}", i).into_bytes(),
                Edit::Put(vec![(i % 251) as u8; 150]),
            )
        })
        .collect()
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

struct Built {
    blocks: MemBlocks,
    root: Cid,
    map: Map,
    build_time: Duration,
    /// The prefix the count-of-prefix rows use. See [`pick_prefix`].
    prefix: Vec<u8>,
}

/// A prefix that exists IN THIS DATASET and selects a real slice of it.
///
/// Derived rather than written down: `d/` means nothing to time-ordered keys,
/// and a prefix that matches nothing measures nothing — the first version of
/// this table reported 0 rounds for the append-only rows for exactly that
/// reason, and the hand-picked prefix that replaced it matched EVERYTHING at a
/// smaller size. This takes the shortest prefix of a middle key selecting at
/// most a quarter of the entries, so it is a slice at every size.
fn pick_prefix(map: &Map) -> Vec<u8> {
    let key = map.keys().nth(map.len() / 2).unwrap().clone();
    for len in 1..=key.len() {
        let p = &key[..len];
        let n = map.keys().filter(|k| k.starts_with(p)).count();
        if n > 0 && n * 4 <= map.len() {
            return p.to_vec();
        }
    }
    key
}

fn build(map: Map) -> Built {
    let prefix = pick_prefix(&map);
    let mut blocks = MemBlocks::default();
    let root = init(&mut blocks);
    let edits: Vec<(Vec<u8>, Edit)> = map
        .iter()
        .map(|(k, v)| (k.clone(), Edit::Put(v.clone())))
        .collect();
    let t = Instant::now();
    let root = apply_into(&mut blocks, &root, &edits).unwrap().root;
    let build_time = t.elapsed();
    let built = Built {
        blocks,
        root,
        map,
        build_time,
        prefix,
    };
    let n = built
        .map
        .keys()
        .filter(|k| k.starts_with(&built.prefix))
        .count();
    assert!(
        n > 0 && n < built.map.len(),
        "the prefix must select part of the dataset, not none of it and not all          of it: {n} of {}",
        built.map.len()
    );
    built
}

/// Every node reachable from `root`, walked from the store.
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

/// Node ids in key order, per level: the order a scan meets them.
fn by_level(store: &MemBlocks, root: Cid) -> BTreeMap<u8, Vec<Cid>> {
    let mut out: BTreeMap<u8, Vec<Cid>> = BTreeMap::new();
    fn walk(store: &MemBlocks, id: Cid, out: &mut BTreeMap<u8, Vec<Cid>>) {
        let n = Node::parse(&store.0[&id]).unwrap();
        out.entry(n.level()).or_default().push(id);
        if !n.is_leaf() {
            for i in 0..n.len() {
                walk(store, n.child(i).0, out);
            }
        }
    }
    walk(store, root, &mut out);
    out
}

struct Spread {
    n: usize,
    min: usize,
    p1: usize,
    p50: usize,
    p99: usize,
    max: usize,
    cv: f64,
    max8_over_mean: f64,
}

/// `max8_over_mean`: the sizes in key order are cut into consecutive windows of
/// eight; the mean of those windows' maxima, over the overall mean. It says how
/// much bigger than typical the biggest node in a short run tends to be — a
/// reader that fetches eight neighbouring nodes pays that, not the mean.
fn spread(mut sizes: Vec<usize>) -> Spread {
    let in_order = sizes.clone();
    sizes.sort_unstable();
    let n = sizes.len();
    let at = |q: f64| sizes[((n as f64 - 1.0) * q).round() as usize];
    let mean = sizes.iter().sum::<usize>() as f64 / n as f64;
    let var = sizes
        .iter()
        .map(|s| (*s as f64 - mean).powi(2))
        .sum::<f64>()
        / n as f64;
    let windows: Vec<usize> = in_order
        .chunks(8)
        .map(|w| *w.iter().max().unwrap())
        .collect();
    let wmean = windows.iter().sum::<usize>() as f64 / windows.len() as f64;
    Spread {
        n,
        min: sizes[0],
        p1: at(0.01),
        p50: at(0.50),
        p99: at(0.99),
        max: sizes[n - 1],
        cv: var.sqrt() / mean,
        max8_over_mean: wmean / mean,
    }
}

/// A store that starts with only what is held and is fed exactly what an
/// operation says it needs. Returns (rounds, blocks fetched).
fn cold<F>(full: &MemBlocks, seed: &[Cid], mut op: F) -> (usize, usize)
where
    F: FnMut(&MemBlocks) -> Option<Vec<Cid>>,
{
    let mut held = MemBlocks::default();
    for id in seed {
        held.insert(*id, &full.0[id]);
    }
    let (mut rounds, mut fetched) = (0, 0);
    loop {
        match op(&held) {
            None => return (rounds, fetched),
            Some(ids) => {
                if ids.is_empty() {
                    return (rounds, fetched);
                }
                rounds += 1;
                for id in ids {
                    held.insert(id, &full.0[&id]);
                    fetched += 1;
                }
                assert!(rounds < 10_000, "cold loop did not converge");
            }
        }
    }
}

fn need_of_read<T>(r: Result<T, ReadError>) -> Option<Vec<Cid>> {
    match r {
        Err(ReadError::Need(ids)) => Some(ids),
        Err(e) => panic!("{e:?}"),
        Ok(_) => None,
    }
}

// ---------------------------------------------------------------------------
// tables
// ---------------------------------------------------------------------------

fn shape(name: &str, b: &Built) {
    let mut all = HashSet::new();
    nodes(&b.blocks, b.root, &mut all);
    let levels = by_level(&b.blocks, b.root);
    let height = levels.keys().max().unwrap() + 1;

    println!("### {name}, {} entries\n", b.map.len());
    println!(
        "Built in {:?}. Height {height}, {} nodes.\n",
        b.build_time,
        all.len()
    );
    println!("| level | nodes | kind |");
    println!("|---|---|---|");
    for (lvl, ids) in levels.iter().rev() {
        println!(
            "| {lvl} | {} | {} |",
            ids.len(),
            if *lvl == 0 { "leaf" } else { "branch" }
        );
    }
    println!();

    println!("| nodes | count | min | p1 | p50 | p99 | max | cv | max-of-8 / mean |");
    println!("|---|---|---|---|---|---|---|---|---|");
    for (label, want_leaf) in [("leaves", true), ("branches", false)] {
        let sizes: Vec<usize> = levels
            .iter()
            .filter(|(lvl, _)| (**lvl == 0) == want_leaf)
            .flat_map(|(_, ids)| ids.iter())
            .map(|id| b.blocks.0[id].len())
            .collect();
        if sizes.is_empty() {
            println!("| {label} | 0 | — | — | — | — | — | — | — |");
            continue;
        }
        let s = spread(sizes);
        println!(
            "| {label} | {} | {} | {} | {} | {} | {} | {:.3} | {:.2} |",
            s.n, s.min, s.p1, s.p50, s.p99, s.max, s.cv, s.max8_over_mean
        );
    }
    println!();
}

/// Bytes and BLOCKS written per commit. Blocks is the number that becomes PUTs.
fn writes(name: &str, b: &Built) {
    println!("### {name}, {} entries\n", b.map.len());
    println!("| batch | where | blocks written | bytes written | blocks replaced |");
    println!("|---|---|---|---|---|");
    let keys: Vec<Vec<u8>> = b.map.keys().cloned().collect();
    let mut r = rng(3);
    for batch in [1usize, 10, 100] {
        for place in ["append", "scattered"] {
            let edits: Vec<(Vec<u8>, Edit)> = if place == "append" {
                let mut top = keys.last().unwrap().clone();
                top.push(0);
                (0..batch)
                    .map(|i| {
                        let mut k = top.clone();
                        k.extend_from_slice(&(i as u32).to_be_bytes());
                        (k, Edit::Put(vec![9u8; 150]))
                    })
                    .collect()
            } else {
                let mut m: BTreeMap<Vec<u8>, Edit> = BTreeMap::new();
                while m.len() < batch {
                    m.insert(
                        keys[r() as usize % keys.len()].clone(),
                        Edit::Put(vec![0xa5; 150]),
                    );
                }
                m.into_iter().collect()
            };
            let (mut blocks_w, mut bytes_w) = (0usize, 0usize);
            let applied = apply(&b.blocks, &b.root, &edits, |_, bytes| {
                blocks_w += 1;
                bytes_w += bytes.len();
            })
            .unwrap();
            println!(
                "| {batch} | {place} | {blocks_w} | {bytes_w} | {} |",
                applied.replaced.len()
            );
        }
    }
    println!();
}

fn cold_reads(name: &str, b: &Built) {
    let share = b.map.keys().filter(|k| k.starts_with(&b.prefix)).count();
    println!("### {name}, {} entries\n", b.map.len());
    println!(
        "Prefix `{}` selects {share} of {} entries.\n",
        String::from_utf8_lossy(&b.prefix),
        b.map.len()
    );
    println!("| operation | rounds | blocks fetched |");
    println!("|---|---|---|");
    let keys: Vec<Vec<u8>> = b.map.keys().cloned().collect();
    let mid = keys[keys.len() / 2].clone();
    let seed = [b.root];

    let (rounds, blocks) = cold(&b.blocks, &seed, |held| {
        need_of_read(get(held, &b.root, &mid))
    });
    println!("| get (one key) | {rounds} | {blocks} |");

    let latest = Range {
        reverse: true,
        max_entries: 20,
        ..Range::default()
    };
    let (rounds, blocks) = cold(&b.blocks, &seed, |held| {
        match range(held, &b.root, &latest) {
            Ok(p) => (!p.need.is_empty()).then_some(p.need),
            Err(RangeError::Read(ReadError::Need(ids))) => Some(ids),
            Err(e) => panic!("{e:?}"),
        }
    });
    println!("| range, latest 20 | {rounds} | {blocks} |");

    let prefix = Range::prefix(&b.prefix);
    let (rounds, blocks) = cold(&b.blocks, &seed, |held| {
        match aggregate(held, &b.root, &prefix) {
            Ok(_) => None,
            Err(freenet_prolly::aggregate::AggError::Read(ReadError::Need(ids))) => Some(ids),
            Err(e) => panic!("{e:?}"),
        }
    });
    println!("| count of prefix, Claimed | {rounds} | {blocks} |");

    let (rounds, blocks) = cold(&b.blocks, &seed, |held| {
        match aggregate_verified(held, &b.root, &prefix) {
            Ok(_) => None,
            Err(freenet_prolly::aggregate::AggError::Read(ReadError::Need(ids))) => Some(ids),
            Err(e) => panic!("{e:?}"),
        }
    });
    println!("| count of prefix, Verified | {rounds} | {blocks} |");
    println!();
}

fn cold_diffs(name: &str, b: &Built) {
    println!("### {name}, {} entries\n", b.map.len());
    println!("| edits | rounds | blocks fetched | changes |");
    println!("|---|---|---|---|");
    let keys: Vec<Vec<u8>> = b.map.keys().cloned().collect();
    for k in [1usize, 10, 1000] {
        let step = (keys.len() / k).max(1);
        let edits: Vec<(Vec<u8>, Edit)> = (0..k)
            .map(|i| (keys[i * step].clone(), Edit::Put(vec![0x3c; 170])))
            .collect();
        let mut store = b.blocks.clone();
        let b2 = apply_into(&mut store, &b.root, &edits).unwrap().root;
        let seed = [b.root, b2];
        let mut changes = 0;
        let (rounds, blocks) = cold(&store, &seed, |held| {
            let mut resume = None;
            let mut need;
            let mut got = 0;
            loop {
                match diff(held, &b.root, &b2, &Range::default(), resume.as_ref()) {
                    Ok(page) => {
                        got += page.changes.len();
                        need = page.need.clone();
                        match page.next {
                            Some(n) if need.is_empty() => resume = Some(n),
                            _ => break,
                        }
                    }
                    Err(DiffError::Read(ReadError::Need(ids))) => {
                        need = ids;
                        break;
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
            changes = got;
            (!need.is_empty()).then_some(need)
        });
        println!("| {k} | {rounds} | {blocks} | {changes} |");
    }
    println!();
}

/// What a proof costs to send, and what it proves.
fn proofs(name: &str, b: &Built) {
    use freenet_prolly::proof::{prove, prove_aggregate, verify, verify_aggregate, Proven};
    let keys: Vec<Vec<u8>> = b.map.keys().cloned().collect();
    let height = Node::parse(&b.blocks.0[&b.root]).unwrap().level() as usize + 1;
    println!("### {name}, {} entries (height {height})\n", b.map.len());
    println!("| proof of | nodes | bytes |");
    println!("|---|---|---|");

    let mut below = keys[0].clone();
    below.insert(0, 0x00);
    let mut above = keys[keys.len() - 1].clone();
    above.push(0xff);
    let mut between = keys[keys.len() / 2].clone();
    between.push(0x01);
    for (what, key, present) in [
        ("a present key", keys[keys.len() / 2].clone(), true),
        ("absence, below the minimum", below, false),
        ("absence, above the maximum", above, false),
        ("absence, between two keys", between, false),
    ] {
        let p = prove(&b.blocks, &b.root, &key).unwrap();
        let ok = verify(&b.root, &key, &p).unwrap();
        assert_eq!(matches!(ok, Proven::Present(_)), present, "{what}");
        println!("| {what} | {} | {} |", p.nodes.len(), p.bytes());
    }
    for (what, r) in [
        ("count of the whole tree", Range::default()),
        ("count of a prefix", Range::prefix(&b.prefix)),
    ] {
        let p = prove_aggregate(&b.blocks, &b.root, &r).unwrap();
        verify_aggregate(&b.root, &r, &p).unwrap();
        println!("| {what} | {} | {} |", p.nodes.len(), p.bytes());
    }
    println!();
}

/// What N one-at-a-time appends cost, against what the tree ends up needing.
fn amplification(n: usize, appends: usize) {
    let map = append_only(n);
    let mut b = build(map);
    let before = b.blocks.0.len();
    let (mut written, mut bytes) = (0usize, 0usize);
    let mut replaced_ids: HashSet<Cid> = HashSet::new();
    let t = Instant::now();
    for i in 0..appends {
        let edits = appended_edits(n + i, 1);
        let mut out: Vec<(Cid, Vec<u8>)> = Vec::new();
        let applied = apply(&b.blocks, &b.root, &edits, |c, by| {
            out.push((c, by.to_vec()));
        })
        .unwrap();
        written += out.len();
        bytes += out.iter().map(|(_, by)| by.len()).sum::<usize>();
        replaced_ids.extend(applied.replaced.iter().copied());
        for (c, by) in &out {
            b.blocks.insert(*c, by);
        }
        b.root = applied.root;
    }
    let took = t.elapsed();
    let mut live = HashSet::new();
    nodes(&b.blocks, b.root, &mut live);
    let live_bytes: usize = live.iter().map(|id| b.blocks.0[id].len()).sum();
    let store = b.blocks.0.len();
    let store_bytes: usize = b.blocks.0.values().map(|v| v.len()).sum();
    // What a store that dropped every replaced node would be holding. Replaced
    // is a hint, not a delete list — another tree may still use those blocks —
    // so this is the floor, not a recommendation.
    let dropped: usize = b
        .blocks
        .0
        .keys()
        .filter(|id| !replaced_ids.contains(*id))
        .count();
    println!(
        "| {n} | {appends} | {written} | {bytes} | {} | {live_bytes} | {store} | {store_bytes} | {:.1}x | {dropped} | {:.1}x | {took:?} |",
        live.len(),
        store as f64 / live.len() as f64,
        dropped as f64 / live.len() as f64,
    );
    let _ = before;
}

// ---------------------------------------------------------------------------

fn main() {
    let machine = std::process::Command::new("sysctl")
        .args(["-n", "machdep.cpu.brand_string"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".into());
    let commit = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".into());

    println!("# Measurements\n");
    println!("Produced by `cargo run --release --example measure > docs/MEASUREMENTS.md`.\n");
    println!("| | |");
    println!("|---|---|");
    println!("| machine | {machine} |");
    println!("| commit | `{commit}` |");
    println!("| store | in-memory (`MemBlocks`); no disk or network in any figure |");
    println!(
        "| datasets | **realistic**: records, edges and index terms, keys out of order · **append-only**: every key above the last |"
    );
    println!("| runs | block and byte counts are deterministic for a commit and dataset (checked: two runs differ only in timings); times are a single run on an otherwise idle machine |");
    println!("\nEvery number here was measured by this program on this commit. Nothing is estimated; anything that could not be measured says so.\n");

    let sizes: Vec<usize> = std::env::args()
        .skip(1)
        .filter_map(|a| a.parse().ok())
        .collect();
    let sizes = if sizes.is_empty() {
        vec![20_000usize, 200_000, 1_000_000]
    } else {
        sizes
    };

    let mut built: Vec<(String, Built)> = Vec::new();
    for n in &sizes {
        for (label, map) in [
            ("realistic", realistic(*n)),
            ("append-only", append_only(*n)),
        ] {
            built.push((label.to_string(), build(map)));
        }
    }

    println!("## Shape\n");
    println!("Encoded block size in bytes. `cv` is the standard deviation over the mean; `max-of-8 / mean` is the mean of the largest node in each run of eight, over the overall mean.\n");
    for (label, b) in &built {
        shape(label, b);
    }

    println!("## Cost of a commit\n");
    println!("One `apply` per row. **Blocks written** is what becomes PUTs; **replaced** is what the new tree no longer uses.\n");
    for (label, b) in &built {
        writes(label, b);
    }

    println!("## Cold reads\n");
    println!("Starting from the root alone, fed exactly the blocks each operation asks for.\n");
    for (label, b) in &built {
        cold_reads(label, b);
    }

    println!("## Cold diff\n");
    println!(
        "Both roots held, nothing else; `b` is the tree after the edits in the first column.\n"
    );
    for (label, b) in &built {
        cold_diffs(label, b);
    }

    println!("## Proof size\n");
    println!("A proof is the node bodies on the path, so it is the height times a node — and absence below the tree's minimum is ONE node, because the root's own first key settles it. Every proof here was verified before its size was reported.\n");
    for (label, b) in &built {
        proofs(label, b);
    }

    println!("## Block amplification\n");
    println!("Appending one entry at a time. **Store blocks** is everything the store ends up holding, **live nodes** is what the final tree actually reaches, and **if replaced dropped** is what would remain if every node `apply` reported as replaced were removed — a floor, since `replaced` is a hint and another tree may still use those blocks.\n");
    println!("| entries | appends | blocks written | bytes written | live nodes | live bytes | store blocks | store bytes | store / live | if replaced dropped | then / live | time |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|");
    for n in &sizes {
        for appends in [100usize, 1_000, 10_000] {
            amplification(*n, appends);
        }
    }
    println!();
}
