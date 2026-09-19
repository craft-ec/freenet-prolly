#[path = "common/dataset.rs"]
mod common;
use common::{dataset, rng};

use freenet_prolly::build::build;
use freenet_prolly::node::{Node, Value};
use freenet_prolly::read::get;
use freenet_prolly::store::{MemBlocks, ReadError};
use freenet_prolly::Cid;
use std::collections::BTreeMap;

fn tree(e: &[(Vec<u8>, Vec<u8>)]) -> (Cid, MemBlocks) {
    let mut blocks = MemBlocks::default();
    let root = build(
        e.iter().map(|(k, v)| (k.as_slice(), Value::Inline(v))),
        |c, b| blocks.insert(c, b),
    )
    .unwrap();
    (root, blocks)
}

#[test]
fn get_matches_a_reference_map_for_present_and_absent_keys() {
    for n in [0usize, 1, 40, 8000] {
        let e = dataset(21, n);
        let reference: BTreeMap<_, _> = e.iter().cloned().collect();
        let (root, blocks) = tree(&e);
        let mut probes: Vec<Vec<u8>> = e.iter().map(|(k, _)| k.clone()).collect();
        let mut r = rng(4);
        for (k, _) in &e {
            // neighbours of real keys: shorter, longer, last byte ±1
            let mut a = k.clone();
            a.pop();
            let mut b = k.clone();
            b.push(0);
            let mut c = k.clone();
            *c.last_mut().unwrap() = c.last().unwrap().wrapping_add(1);
            probes.extend([a, b, c]);
        }
        probes.extend([
            vec![],
            vec![0],
            vec![0xff; 40],
            b"d/".to_vec(),
            b"zzz".to_vec(),
        ]);
        probes.extend((0..200).map(|_| r().to_be_bytes().to_vec()));
        let (mut hits, mut misses) = (0, 0);
        for p in &probes {
            let got = get(&blocks, &root, p).unwrap();
            let want = reference.get(p).map(|v| Value::Inline(v));
            assert_eq!(got, want, "key {p:?}");
            if want.is_some() {
                hits += 1
            } else {
                misses += 1
            }
        }
        assert_eq!(hits, e.len());
        assert!(misses >= 200, "absent keys were really probed: {misses}");
    }
}

#[test]
fn a_missing_block_is_named_and_supplying_it_completes_the_read() {
    let e = dataset(22, 8000);
    let (root, full) = tree(&e);
    let key = &e[5000].0;
    let mut held = MemBlocks::default();
    let mut fetched = 0;
    let value = loop {
        match get(&held, &root, key) {
            Ok(v) => break v,
            Err(ReadError::Need(cids)) => {
                assert_eq!(cids.len(), 1);
                held.insert(cids[0], &full.0[&cids[0]]);
                fetched += 1;
            }
            Err(e) => panic!("{e:?}"),
        }
    };
    assert_eq!(value, Some(Value::Inline(&e[5000].1)));
    let height = Node::parse(&full.0[&root]).unwrap().level() as usize + 1;
    assert_eq!(
        fetched, height,
        "a lookup needs exactly one block per level"
    );
    assert!(height >= 3);
}

#[test]
fn a_child_that_contradicts_its_parent_is_refused() {
    // Two valid trees; graft a leaf of B under A's root cid slot by lying about
    // which bytes a cid names. A source that returns wrong bytes must not get a
    // wrong answer accepted.
    let a = dataset(23, 3000);
    let b = dataset(24, 3000);
    let (root, mut blocks) = tree(&a);
    let (_, other) = tree(&b);
    let rootn = Node::parse(&blocks.0[&root]).unwrap();
    assert!(!rootn.is_leaf());
    let (victim, _) = rootn.child(1);
    let level = Node::parse(&blocks.0[&victim]).unwrap().level();
    let imposter = other
        .0
        .values()
        .find(|bytes| Node::parse(bytes).unwrap().level() == level)
        .unwrap()
        .clone();
    let probe = rootn.key(1);
    blocks.0.insert(victim, imposter);
    assert_eq!(
        get(&blocks, &root, &probe),
        Err(ReadError::Mismatch(victim))
    );
}
