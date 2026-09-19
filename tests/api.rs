//! The surface a consumer actually uses. Each of these exists because the first
//! real consumer (craftworks-sdk#6) had to write it by hand, and the hand-written
//! version is a place to get it wrong quietly.

#[path = "common/dataset.rs"]
mod common;
use common::{dataset, rng};

use freenet_prolly::apply::{apply, apply_into, ApplyError, Edit};
use freenet_prolly::build::{empty_root, init, TreeBuilder};
use freenet_prolly::node::{Node, Value, MAX_INLINE, MAX_KEY, MAX_VALUE};
use freenet_prolly::range::read_value;
use freenet_prolly::read::{get, height};
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::{block_id, kind, Cid};
use std::collections::{BTreeMap, HashSet};

type Map = BTreeMap<Vec<u8>, Vec<u8>>;

/// `dataset` values are all under the inline cap, so a test about referenced
/// values has to add some — otherwise it passes while never touching the path
/// it names.
fn with_big_values(mut m: Map, n: usize) -> Map {
    let mut r = rng(77);
    for i in 0..n {
        m.insert(
            format!("z/big/{i:04}").into_bytes(),
            vec![(r() % 251) as u8; MAX_INLINE + 1 + (r() as usize % 4000)],
        );
    }
    m
}

fn edits(m: &Map) -> Vec<(Vec<u8>, Edit)> {
    m.iter()
        .map(|(k, v)| (k.clone(), Edit::Put(v.clone())))
        .collect()
}

/// `apply_into` must be exactly `apply` plus the loop every consumer writes —
/// same root, same blocks, nothing extra and nothing missing.
#[test]
fn apply_into_is_apply_plus_the_loop_everyone_writes() {
    let m = with_big_values(dataset(21, 4000).into_iter().collect(), 40);
    let batch = edits(&m);

    // By hand, the way a consumer does it today.
    let mut by_hand = MemBlocks::default();
    let root = init(&mut by_hand);
    let mut emitted = Vec::new();
    let a = apply(&by_hand, &root, &batch, |c, b| {
        emitted.push((c, b.to_vec()))
    })
    .unwrap();
    for (c, b) in &emitted {
        by_hand.insert(*c, b);
    }

    // And with the library doing it.
    let mut inside = MemBlocks::default();
    let root2 = init(&mut inside);
    assert_eq!(root, root2, "two empty trees are the same tree");
    let b = apply_into(&mut inside, &root2, &batch).unwrap();

    assert_eq!(a.root, b.root);
    assert_eq!(a.replaced, b.replaced);
    let (x, y): (HashSet<Cid>, HashSet<Cid>) = (
        by_hand.0.keys().copied().collect(),
        inside.0.keys().copied().collect(),
    );
    assert_eq!(x, y, "the stores must hold exactly the same blocks");

    // The tree reads back, including values that live in their own block.
    let mut refs = 0;
    for (k, v) in &m {
        let got = get(&inside, &b.root, k)
            .unwrap()
            .expect("every key is there");
        if matches!(got, Value::Ref { .. }) {
            refs += 1;
        }
        assert_eq!(read_value(&inside, got).unwrap(), v.as_slice());
    }
    assert_eq!(refs, 40, "every big value must be a reference");
}

/// A refused batch writes nothing — the store is untouched, not cleaned up.
#[test]
fn a_refused_batch_leaves_the_store_alone() {
    let m: Map = dataset(22, 500).into_iter().collect();
    let mut blocks = MemBlocks::default();
    let root = init(&mut blocks);
    let applied = apply_into(&mut blocks, &root, &edits(&m)).unwrap();
    let before: HashSet<Cid> = blocks.0.keys().copied().collect();

    for (what, bad) in [
        (
            "key too long",
            vec![(vec![b'k'; MAX_KEY + 1], Edit::Put(b"v".to_vec()))],
        ),
        (
            "value too long",
            vec![(b"k".to_vec(), Edit::Put(vec![0u8; MAX_VALUE + 1]))],
        ),
        (
            "not sorted",
            vec![
                (b"b".to_vec(), Edit::Put(b"1".to_vec())),
                (b"a".to_vec(), Edit::Put(b"2".to_vec())),
            ],
        ),
    ] {
        let e = apply_into(&mut blocks, &applied.root, &bad).unwrap_err();
        assert!(!matches!(e, ApplyError::Read(_)), "{what}: {e:?}");
        assert_eq!(
            blocks.0.keys().copied().collect::<HashSet<Cid>>(),
            before,
            "{what}: the store was written to"
        );
    }
}

/// The inline-or-reference rule, at the boundary the format defines. One
/// function decides it, and this is what it decides.
#[test]
fn for_bytes_is_the_formats_rule() {
    let short = vec![7u8; MAX_INLINE];
    let (v, block) = Value::for_bytes(&short);
    assert_eq!(v, Value::Inline(&short), "at the cap it is inline");
    assert!(block.is_none(), "and there is no block to keep");

    let long = vec![7u8; MAX_INLINE + 1];
    let (v, block) = Value::for_bytes(&long);
    let cid = block_id(kind::RAW, &long);
    assert_eq!(
        v,
        Value::Ref {
            cid,
            len: long.len() as u32
        },
        "one byte over, it is a reference"
    );
    assert_eq!(block, Some((cid, long.as_slice())), "with a block to keep");

    // The empty value is inline, and a value is addressed as RAW — never as a
    // node, so a tree node can never be served as one.
    assert_eq!(Value::for_bytes(b"").0, Value::Inline(b""));
    assert_ne!(cid, block_id(kind::TREE_NODE, &long));
}

/// A tree built from raw bytes is the tree `apply` builds from the same bytes.
/// This is the property that lets a test oracle call the rule instead of
/// restating it.
#[test]
fn push_bytes_builds_what_apply_builds() {
    for n in [1usize, 40, 3000] {
        let m = with_big_values(dataset(23, n).into_iter().collect(), 5);
        let mut built = MemBlocks::default();
        let mut t = TreeBuilder::new(|c, b: &[u8]| built.insert(c, b));
        for (k, v) in &m {
            t.push_bytes(k, v).unwrap();
        }
        let from_scratch = t.finish().unwrap();

        let mut applied = MemBlocks::default();
        let root = init(&mut applied);
        let incrementally = apply_into(&mut applied, &root, &edits(&m)).unwrap().root;
        assert_eq!(from_scratch, incrementally, "{n} entries");

        // push_bytes also hands the value blocks to the sink, so the built store
        // can serve every value on its own.
        for (k, v) in &m {
            let got = get(&built, &from_scratch, k).unwrap().unwrap();
            assert_eq!(
                read_value(&built, got).unwrap(),
                v.as_slice(),
                "{n} entries"
            );
        }
    }
}

/// `read_value` gives the bytes back whichever way the format stored them, and
/// still refuses a block whose length disagrees with the leaf.
#[test]
fn read_value_handles_both_kinds_and_checks_the_length() {
    use freenet_prolly::store::ReadError;
    let mut blocks = MemBlocks::default();
    let short = b"inline".to_vec();
    let long = vec![9u8; MAX_INLINE + 100];
    for v in [&short, &long] {
        if let (_, Some((cid, b))) = Value::for_bytes(v) {
            blocks.insert(cid, b);
        }
    }
    assert_eq!(
        read_value(&blocks, Value::Inline(&short)).unwrap(),
        &short[..]
    );
    let (v, _) = Value::for_bytes(&long);
    assert_eq!(read_value(&blocks, v).unwrap(), &long[..]);

    // A length that disagrees with the block is refused, both ways.
    let cid = block_id(kind::RAW, &long);
    for wrong in [long.len() as u32 - 1, long.len() as u32 + 1] {
        assert_eq!(
            read_value(&blocks, Value::Ref { cid, len: wrong }),
            Err(ReadError::Mismatch(cid))
        );
    }
    // An absent block names exactly itself.
    let absent = block_id(kind::RAW, b"nobody has this");
    assert_eq!(
        read_value(
            &blocks,
            Value::Ref {
                cid: absent,
                len: 15
            }
        ),
        Err(ReadError::Need(vec![absent]))
    );
}

#[test]
fn the_empty_tree_and_the_height_of_a_real_one() {
    let mut blocks = MemBlocks::default();
    let root = init(&mut blocks);
    assert_eq!(root, empty_root(), "init puts the empty tree in");
    assert_eq!(blocks.0.len(), 1, "which is one block");
    assert_eq!(height(&blocks, &root).unwrap(), 1, "one empty leaf");
    assert!(Node::parse(blocks.get(&root).unwrap()).unwrap().is_empty());

    // Two empty trees agree, and a second init changes nothing.
    let mut other = MemBlocks::default();
    assert_eq!(init(&mut other), root);
    assert_eq!(init(&mut blocks), root);
    assert_eq!(blocks.0.len(), 1);

    let mut r = rng(3);
    let mut seen = Vec::new();
    let mut m = Map::new();
    for chunk in 0..6 {
        for _ in 0..1500 {
            m.insert(
                format!("k/{:08}", r() % 100_000).into_bytes(),
                vec![7u8; 100],
            );
        }
        let root = apply_into(&mut blocks, &root.clone(), &edits(&m))
            .unwrap()
            .root;
        let h = height(&blocks, &root).unwrap();
        if seen.last() != Some(&h) {
            seen.push(h);
        }
        assert_eq!(
            h,
            Node::parse(blocks.get(&root).unwrap()).unwrap().level() as usize + 1,
            "chunk {chunk}"
        );
    }
    assert!(
        seen.len() > 1 && seen.contains(&3),
        "the tree grew: {seen:?}"
    );
}

/// The control for `apply_into` existing at all.
///
/// The loop it replaces is the same in every consumer, and the way to get it
/// wrong is to keep the nodes and drop the value blocks — the tree is intact,
/// the roots match, every key is present, and only reading a long value fails.
/// That is silent until someone reads one, which is why the loop belongs in the
/// library. Here the mistake is made deliberately, to show it is one.
#[test]
fn keeping_only_the_nodes_builds_a_tree_that_cannot_serve_its_values() {
    use freenet_prolly::store::ReadError;
    let m = with_big_values(dataset(24, 200).into_iter().collect(), 20);
    let batch = edits(&m);

    let mut lossy = MemBlocks::default();
    let root = init(&mut lossy);
    let mut emitted = Vec::new();
    let applied = apply(&lossy, &root, &batch, |c, b| emitted.push((c, b.to_vec()))).unwrap();
    for (c, b) in &emitted {
        if Node::parse(b).is_ok() {
            lossy.insert(*c, b); // the mistake: nodes only
        }
    }

    // Everything about the TREE is right.
    let mut whole = MemBlocks::default();
    let r2 = init(&mut whole);
    let good = apply_into(&mut whole, &r2, &batch).unwrap();
    assert_eq!(applied.root, good.root, "same tree, same root");
    for k in m.keys() {
        assert!(
            get(&lossy, &applied.root, k).unwrap().is_some(),
            "key present"
        );
    }

    // And the long values cannot be read.
    let mut missing = 0;
    for (k, v) in &m {
        let got = get(&lossy, &applied.root, k).unwrap().unwrap();
        match read_value(&lossy, got) {
            Ok(b) => assert_eq!(b, v.as_slice()),
            Err(ReadError::Need(ids)) => {
                missing += 1;
                assert_eq!(ids.len(), 1);
            }
            Err(e) => panic!("{e:?}"),
        }
    }
    assert_eq!(missing, 20, "exactly the referenced values are unreadable");

    // `apply_into` does not make that mistake.
    for (k, v) in &m {
        let got = get(&whole, &good.root, k).unwrap().unwrap();
        assert_eq!(read_value(&whole, got).unwrap(), v.as_slice());
    }
}
