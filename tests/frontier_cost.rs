use freenet_prolly::apply::{apply_into, Edit};
use freenet_prolly::build::init;
use freenet_prolly::node::Node;
use freenet_prolly::range::{frontier_of, Range};
use freenet_prolly::store::MemBlocks;
use std::ops::Bound;

/// What a frontier costs, on the shape where it costs the most: a wide upper
/// tree with long keys, every branch held and no leaf. Printed with
/// `--nocapture`; the assertion is structural, so the test cannot flake on a
/// busy machine — the number is for a person comparing two revisions, which is
/// what it was added for.
#[test]
fn the_cost_of_a_frontier_measured() {
    // Long keys, so building one per child is a real allocation.
    let mut full = MemBlocks::default();
    let root0 = init(&mut full);
    let edits: Vec<(Vec<u8>, Edit)> = (0..40_000u32)
        .map(|i| {
            let mut k = b"d/some/rather/long/key/prefix/shared/by/everything/".to_vec();
            k.extend_from_slice(format!("{i:012}").as_bytes());
            (k, Edit::Put(vec![7u8; 40]))
        })
        .collect();
    let root = apply_into(&mut full, &root0, &edits).unwrap().root;

    // Branches held, no leaves: the frontier walks the whole upper tree.
    let mut held = MemBlocks::default();
    for (id, b) in full.0.iter() {
        if Node::parse(b).is_ok_and(|n| !n.is_leaf()) {
            held.insert(*id, b);
        }
    }
    let r = Range {
        lo: Bound::Unbounded,
        hi: Bound::Unbounded,
        max_entries: usize::MAX,
        max_bytes: usize::MAX,
        ..Range::default()
    };
    for _ in 0..20 {
        let _ = frontier_of(&held, &root, &r).unwrap();
    }
    let t = std::time::Instant::now();
    let runs = 200;
    let mut n = 0;
    for _ in 0..runs {
        n = frontier_of(&held, &root, &r).unwrap().len();
    }
    println!(
        "frontier over {} branches, {} B keys: {:?} each, names {n}",
        held.0.len(),
        50 + 12,
        t.elapsed() / runs
    );
    assert_eq!(n, 64, "the frontier is capped, whatever it costs");
    assert!(held.0.len() > 20, "the walk must cross a real upper tree");
}
