//! What a proof asserts, and what it refuses to assert.
//!
//! `Present(v)` and `Absent` are claims a STRANGER'S BYTES are asking the
//! verifier to make, so the hostile cases come first in this file and the happy
//! ones after.

#[path = "common/dataset.rs"]
mod common;
#[path = "common/invariants.rs"]
mod invariants;
use common::{dataset, rng};

use freenet_prolly::apply::{apply_into, Edit};
use freenet_prolly::build::init;
use freenet_prolly::node::{Node, Value, MAX_INLINE};
use freenet_prolly::proof::{
    prove, prove_aggregate, prove_with_value, verify, verify_aggregate, Proof, ProofError, Proven,
};
use freenet_prolly::range::Range;
use freenet_prolly::store::{Blocks, MemBlocks, ReadError};
use freenet_prolly::{block_id, kind, Cid};
use std::collections::BTreeMap;

type Map = BTreeMap<Vec<u8>, Vec<u8>>;

fn build(m: &Map) -> (MemBlocks, Cid) {
    let mut blocks = MemBlocks::default();
    let root = init(&mut blocks);
    let edits: Vec<(Vec<u8>, Edit)> = m
        .iter()
        .map(|(k, v)| (k.clone(), Edit::Put(v.clone())))
        .collect();
    let root = apply_into(&mut blocks, &root, &edits).unwrap().root;
    invariants::check_tree(&blocks, &root, m).unwrap();
    (blocks, root)
}

fn height(blocks: &MemBlocks, root: &Cid) -> usize {
    Node::parse(blocks.get(root).unwrap()).unwrap().level() as usize + 1
}

/// A tree big enough to have a real path, on realistic keys.
fn tree(n: usize) -> (MemBlocks, Cid, Map) {
    let m: Map = dataset(7, n).into_iter().collect();
    let (blocks, root) = build(&m);
    (blocks, root, m)
}

// ---------------------------------------------------------------------------
// What it asserts — the hostile cases
// ---------------------------------------------------------------------------

/// Nothing a stranger can send makes `verify` panic, and nothing makes it say
/// Absent about a key that is there.
#[test]
fn verify_is_total_on_hostile_input() {
    let (blocks, root, m) = tree(20_000);
    let key = m.keys().nth(9_000).unwrap().clone();
    let good = prove(&blocks, &root, &key).unwrap();
    // The control: unmodified, it verifies.
    assert!(matches!(
        verify(&root, &key, &good).unwrap(),
        Proven::Present(_)
    ));

    let other_key = m.keys().nth(3).unwrap().clone();
    let other_proof = prove(&blocks, &root, &other_key).unwrap();

    // A second tree that shares nothing.
    let (blocks2, root2, m2) = {
        let m2: Map = dataset(19, 20_000).into_iter().collect();
        let (b, r) = build(&m2);
        (b, r, m2)
    };
    let foreign = prove(&blocks2, &root2, m2.keys().nth(10).unwrap()).unwrap();

    let mut cases: Vec<(&str, Proof)> = vec![
        ("empty", Proof::default()),
        (
            "garbage in place of a node",
            Proof {
                nodes: vec![b"not a node".to_vec()],
                value: None,
            },
        ),
        (
            "the root alone",
            Proof {
                nodes: good.nodes[..1].to_vec(),
                value: None,
            },
        ),
        (
            "the last node dropped",
            Proof {
                nodes: good.nodes[..good.nodes.len() - 1].to_vec(),
                value: None,
            },
        ),
        (
            "the first node dropped",
            Proof {
                nodes: good.nodes[1..].to_vec(),
                value: None,
            },
        ),
        (
            "the path reversed",
            Proof {
                nodes: good.nodes.iter().rev().cloned().collect(),
                value: None,
            },
        ),
        (
            "a node repeated",
            Proof {
                nodes: {
                    let mut v = good.nodes.clone();
                    v.push(good.nodes[0].clone());
                    v
                },
                value: None,
            },
        ),
        (
            "an extra node appended",
            Proof {
                nodes: {
                    let mut v = good.nodes.clone();
                    v.push(foreign.nodes[0].clone());
                    v
                },
                value: None,
            },
        ),
        (
            "a node swapped for a valid node of another tree",
            Proof {
                nodes: {
                    let mut v = good.nodes.clone();
                    let i = v.len() - 1;
                    v[i] = foreign.nodes[foreign.nodes.len() - 1].clone();
                    v
                },
                value: None,
            },
        ),
        (
            "a node with one byte flipped",
            Proof {
                nodes: {
                    let mut v = good.nodes.clone();
                    let i = v.len() - 1;
                    let at = v[i].len() / 2;
                    v[i][at] ^= 0x01;
                    v
                },
                value: None,
            },
        ),
        (
            // The root is still first, so the root check passes and the ORDER
            // check is the only thing between this and an accepted proof: the
            // same blocks in a different order would be a second encoding of
            // one proof.
            "the middle of the path swapped",
            Proof {
                nodes: {
                    let mut v = good.nodes.clone();
                    let n = v.len();
                    assert!(n >= 4, "the tree must be deep enough to swap a middle");
                    v.swap(1, n - 2);
                    v
                },
                value: None,
            },
        ),
        ("a proof for another key", other_proof.clone()),
        ("a proof from another tree", foreign.clone()),
    ];
    // A value trailer where there is nothing for it to prove: unchecked bytes
    // riding along would mean two byte strings verifying to one answer.
    cases.push((
        "a value trailer on an inline value",
        Proof {
            nodes: good.nodes.clone(),
            value: Some(b"surprise".to_vec()),
        },
    ));
    cases.push((
        "a value trailer on an absence proof",
        Proof {
            nodes: prove(&blocks, &root, b"zzzz/not-a-key").unwrap().nodes,
            value: Some(b"surprise".to_vec()),
        },
    ));

    for (what, p) in &cases {
        match verify(&root, &key, p) {
            Err(_) => {}
            Ok(Proven::Absent) => panic!("{what}: said ABSENT about a key that is present"),
            Ok(Proven::Present(v)) => {
                // The only acceptable Ok is the true value, and no case above
                // should produce it.
                panic!("{what}: said Present({v:?})");
            }
        }
    }

    // And the same inputs against verify_aggregate: also total.
    let r = Range::prefix(b"d/");
    for (what, p) in &cases {
        let _ = verify_aggregate(&root, &r, p).map_err(|_| ()).is_err();
        let _ = what;
    }

    // Decoding a stranger's bytes never panics either.
    let enc = good.encode();
    let mut r = rng(5);
    for _ in 0..500 {
        let mut b = enc.clone();
        let at = r() as usize % b.len();
        b[at] ^= (r() % 255) as u8 + 1;
        let _ = Proof::decode(&b);
    }
    for cut in [0usize, 1, 3, 4, 5, 6, 7, 20, enc.len() - 1] {
        let _ = Proof::decode(&enc[..cut.min(enc.len())]);
    }
    for junk in [&b""[..], b"PP01", b"PP02\0\0", &[0xff; 64]] {
        let _ = Proof::decode(junk);
    }
    println!(
        "{} hostile proofs refused, decode survived 512 corruptions",
        cases.len()
    );
}

/// The one an attacker most wants: make a present key look absent by sending a
/// shorter path. It must be Incomplete, never Absent.
#[test]
fn a_present_key_cannot_be_made_to_look_absent() {
    let (blocks, root, m) = tree(20_000);
    let mut checked = 0;
    for i in [0usize, 1, 7, 5_000, 12_345, 19_999] {
        let key = m.keys().nth(i).unwrap().clone();
        let good = prove(&blocks, &root, &key).unwrap();
        assert!(matches!(
            verify(&root, &key, &good).unwrap(),
            Proven::Present(_)
        ));
        for drop in 1..good.nodes.len() {
            let short = Proof {
                nodes: good.nodes[..good.nodes.len() - drop].to_vec(),
                value: None,
            };
            assert_eq!(
                verify(&root, &key, &short),
                Err(ProofError::Incomplete),
                "dropping {drop} node(s) must be incomplete, not absent"
            );
            checked += 1;
        }
    }
    assert!(checked >= 15);
}

/// A proof is about ONE root. Two trees that share every node but the root are
/// the sharpest case: the path is identical, only the top differs.
#[test]
fn a_proof_for_one_root_fails_for_another() {
    let m: Map = dataset(7, 20_000).into_iter().collect();
    let (mut blocks, root_a) = build(&m);
    // b = a with one entry changed far away from the key we prove.
    let far = m.keys().next().unwrap().clone();
    let root_b = apply_into(&mut blocks, &root_a, &[(far, Edit::Put(vec![1u8; 99]))])
        .unwrap()
        .root;
    assert_ne!(root_a, root_b);

    let key = m.keys().nth(15_000).unwrap().clone();
    let pa = prove(&blocks, &root_a, &key).unwrap();
    let pb = prove(&blocks, &root_b, &key).unwrap();
    // The paths below the root are the same blocks — only the root differs.
    assert_eq!(
        pa.nodes[1..],
        pb.nodes[1..],
        "the case must be the sharp one"
    );
    assert_ne!(pa.nodes[0], pb.nodes[0]);

    assert!(matches!(
        verify(&root_a, &key, &pa).unwrap(),
        Proven::Present(_)
    ));
    assert!(matches!(
        verify(&root_b, &key, &pb).unwrap(),
        Proven::Present(_)
    ));
    assert_eq!(verify(&root_b, &key, &pa), Err(ProofError::WrongRoot));
    assert_eq!(verify(&root_a, &key, &pb), Err(ProofError::WrongRoot));
}

// ---------------------------------------------------------------------------
// What it answers
// ---------------------------------------------------------------------------

#[test]
fn every_key_and_every_kind_of_absence_verifies() {
    for (what, m) in [
        ("appended", {
            (0..8_000)
                .map(|i| (format!("k/{i:08}").into_bytes(), vec![(i % 251) as u8; 130]))
                .collect::<Map>()
        }),
        ("prepended", {
            (0..8_000)
                .map(|i| {
                    (
                        format!("k/{:08}", 8_000 - i).into_bytes(),
                        vec![(i % 251) as u8; 130],
                    )
                })
                .collect::<Map>()
        }),
        ("realistic", dataset(7, 8_000).into_iter().collect::<Map>()),
    ] {
        let (blocks, root) = build(&m);
        let h = height(&blocks, &root);
        let keys: Vec<Vec<u8>> = m.keys().cloned().collect();

        let mut r = rng(11);
        let mut sample: Vec<Vec<u8>> = (0..60)
            .map(|_| keys[r() as usize % keys.len()].clone())
            .collect();
        sample.push(keys[0].clone());
        sample.push(keys[keys.len() - 1].clone());
        for key in &sample {
            let p = prove(&blocks, &root, key).unwrap();
            assert_eq!(
                verify(&root, key, &p).unwrap(),
                Proven::Present(Value::for_bytes(&m[key]).0),
                "{what}: {}",
                String::from_utf8_lossy(key)
            );
            assert_eq!(p.nodes.len(), h, "{what}: a present key costs the height");
            assert!(p.bytes() <= h * 16 * 1024, "{what}: proof too large");
        }

        // Absence, in each of the three shapes it comes in.
        let mut below = keys[0].clone();
        below.insert(0, 0x00);
        let mut above = keys[keys.len() - 1].clone();
        above.push(0xff);
        let mut between = keys[keys.len() / 2].clone();
        between.push(0x01);
        let mut shorter = keys[keys.len() / 2].clone();
        shorter.pop();
        for (kind_, key, want_len) in [
            ("below the minimum", below, 1),
            ("above the maximum", above, h),
            ("between two keys", between, h),
            ("a shorter key", shorter, h),
        ] {
            if m.contains_key(&key) {
                continue;
            }
            let p = prove(&blocks, &root, &key).unwrap();
            assert_eq!(
                verify(&root, &key, &p).unwrap(),
                Proven::Absent,
                "{what}/{kind_}"
            );
            assert_eq!(p.nodes.len(), want_len, "{what}/{kind_}: path length");
        }
        println!(
            "  {what:10}: height {h}, {} keys and 4 absences verified",
            sample.len()
        );
    }
}

/// Absence below the minimum is ONE node, and it is complete. The root's first
/// key is the tree's minimum and it is hashed into the root the reader already
/// trusted, so nothing below the root is needed — a reader that called this
/// truncated would be wrong.
#[test]
fn absence_below_the_minimum_is_a_one_node_proof() {
    let (blocks, root, m) = tree(20_000);
    let h = height(&blocks, &root);
    assert!(
        h >= 3,
        "the tree must be deep enough for this to be a claim"
    );
    let mut key = m.keys().next().unwrap().clone();
    key.insert(0, 0x00);

    let p = prove(&blocks, &root, &key).unwrap();
    assert_eq!(p.nodes.len(), 1, "one node, not {h}");
    assert_eq!(p.nodes[0], blocks.get(&root).unwrap());
    assert_eq!(verify(&root, &key, &p).unwrap(), Proven::Absent);

    // And it is not a shortcut that works for any key: the same one-node proof
    // must NOT answer for a key that is inside the tree's span.
    let inside = m.keys().nth(100).unwrap().clone();
    assert_eq!(verify(&root, &inside, &p), Err(ProofError::Incomplete));
    println!(
        "below-minimum absence: 1 node of a height-{h} tree, {} bytes",
        p.bytes()
    );
}

#[test]
fn a_referenced_value_is_proved_by_id_and_length_or_carried() {
    let mut m: Map = dataset(7, 4_000).into_iter().collect();
    let key = b"z/big/0001".to_vec();
    let big = vec![0x5au8; MAX_INLINE + 4_000];
    m.insert(key.clone(), big.clone());
    let (blocks, root) = build(&m);

    // Without the trailer: the type says the value was named, not carried.
    let p = prove(&blocks, &root, &key).unwrap();
    match verify(&root, &key, &p).unwrap() {
        Proven::Present(Value::Ref { cid, len }) => {
            assert_eq!(len as usize, big.len());
            assert_eq!(cid, block_id(kind::RAW, &big));
        }
        other => panic!("{other:?}"),
    }

    // With it: the bytes come back, checked against the leaf's record.
    let p = prove_with_value(&blocks, &root, &key).unwrap();
    assert_eq!(
        verify(&root, &key, &p).unwrap(),
        Proven::Present(Value::Inline(&big))
    );

    // A swapped trailer is refused, by id and by length.
    for (what, v) in [
        ("different bytes, same length", {
            let mut v = big.clone();
            v[0] ^= 0xff;
            v
        }),
        ("one byte short", big[..big.len() - 1].to_vec()),
        ("empty", Vec::new()),
    ] {
        let bad = Proof {
            nodes: p.nodes.clone(),
            value: Some(v),
        };
        assert_eq!(
            verify(&root, &key, &bad),
            Err(ProofError::BadValue),
            "{what}"
        );
    }
}

#[test]
fn a_proof_survives_the_round_trip_through_bytes() {
    let (blocks, root, m) = tree(20_000);
    for i in [0usize, 5_000, 19_999] {
        let key = m.keys().nth(i).unwrap().clone();
        let p = prove_with_value(&blocks, &root, &key).unwrap();
        let bytes = p.encode();
        assert_eq!(Proof::decode(&bytes).unwrap(), p);
        assert_eq!(
            verify(&root, &key, &Proof::decode(&bytes).unwrap()).unwrap(),
            verify(&root, &key, &p).unwrap()
        );
    }
}

// ---------------------------------------------------------------------------
// aggregate proofs
// ---------------------------------------------------------------------------

#[test]
fn an_aggregate_proof_authenticates_a_claim_and_only_a_claim() {
    let (blocks, root, m) = tree(20_000);
    let h = height(&blocks, &root);

    // The whole tree is ONE node: the count is in the root. Asserted so that a
    // one-node aggregate proof does not read as a truncated one.
    let whole = Range::default();
    let p = prove_aggregate(&blocks, &root, &whole).unwrap();
    assert_eq!(p.nodes.len(), 1, "the whole-tree count is the root's own");
    let got = verify_aggregate(&root, &whole, &p).unwrap();
    assert_eq!(got.agg().count, m.len() as u64);

    // A prefix: the two edge paths, bounded by twice the height.
    let pre = Range::prefix(b"d/");
    let p = prove_aggregate(&blocks, &root, &pre).unwrap();
    assert!(
        p.nodes.len() <= 2 * h,
        "{} nodes for height {h}",
        p.nodes.len()
    );
    let want = m.keys().filter(|k| k.starts_with(b"d/")).count() as u64;
    assert_eq!(verify_aggregate(&root, &pre, &p).unwrap().agg().count, want);
    println!(
        "aggregate proof: whole tree 1 node, prefix {} nodes (height {h})",
        p.nodes.len()
    );

    // Canonical per (root, RANGE): a proof for one range does not answer for
    // another, and is refused rather than answered from the blocks it happens
    // to contain.
    let other = Range::prefix(b"e/");
    assert!(verify_aggregate(&root, &other, &p).is_err());

    // There is no way to get a Verified out of a proof: the function returns
    // Claimed, and that is the whole point — this is a type-level assertion,
    // checked by the compiler, and stated here so the reason is recorded.
    let _: freenet_prolly::aggregate::Claimed = got;
}

// ---------------------------------------------------------------------------
// cold prove
// ---------------------------------------------------------------------------

#[test]
fn proving_from_a_cold_store_costs_the_path() {
    let (full, root, m) = tree(20_000);
    let h = height(&full, &root);
    let key = m.keys().nth(11_111).unwrap().clone();

    let mut held = MemBlocks::default();
    held.insert(root, full.get(&root).unwrap());
    let (mut rounds, mut fetched) = (0, 0);
    let p = loop {
        match prove(&held, &root, &key) {
            Ok(p) => break p,
            Err(ReadError::Need(ids)) => {
                rounds += 1;
                for id in ids {
                    held.insert(id, full.get(&id).unwrap());
                    fetched += 1;
                }
                assert!(rounds < 20);
            }
            Err(e) => panic!("{e:?}"),
        }
    };
    assert!(matches!(
        verify(&root, &key, &p).unwrap(),
        Proven::Present(_)
    ));
    assert_eq!(rounds, h - 1, "one round per level below the root");
    assert_eq!(fetched, h - 1);
    println!("cold prove: {rounds} rounds, {fetched} blocks, height {h}");
}

/// The nodes an aggregate proof must contain, worked out from the SPANS alone:
/// the root, and every node that straddles a bound of the range (a node wholly
/// inside contributes its recorded aggregate and is never opened; one wholly
/// outside is not looked at). Computed from a plain walk of the store, with no
/// reference to how `aggregate` traverses anything.
fn expected_aggregate_nodes(store: &MemBlocks, root: &Cid, r: &Range) -> Vec<Vec<u8>> {
    fn span(store: &MemBlocks, id: &Cid) -> (Vec<u8>, Vec<u8>) {
        let n = Node::parse(&store.0[id]).unwrap();
        if n.is_leaf() {
            return (n.key(0), n.key(n.len() - 1));
        }
        (
            span(store, &n.child(0).0).0,
            span(store, &n.child(n.len() - 1).0).1,
        )
    }
    fn walk(store: &MemBlocks, id: &Cid, r: &Range, out: &mut Vec<Vec<u8>>) {
        out.push(store.0[id].clone());
        let n = Node::parse(&store.0[id]).unwrap();
        if n.is_leaf() {
            return;
        }
        for i in 0..n.len() {
            let child = n.child(i).0;
            let (lo, hi) = span(store, &child);
            let wholly_in = in_r(&lo, r) && in_r(&hi, r);
            let wholly_out = !in_r(&lo, r) && !in_r(&hi, r) && {
                // Entirely on one side of the range.
                let below = match &r.lo {
                    std::ops::Bound::Unbounded => false,
                    std::ops::Bound::Included(k) => hi < *k,
                    std::ops::Bound::Excluded(k) => hi <= *k,
                };
                let above = match &r.hi {
                    std::ops::Bound::Unbounded => false,
                    std::ops::Bound::Included(k) => lo > *k,
                    std::ops::Bound::Excluded(k) => lo >= *k,
                };
                below || above
            };
            if !wholly_in && !wholly_out {
                walk(store, &child, r, out);
            }
        }
    }
    fn in_r(k: &[u8], r: &Range) -> bool {
        let lo = match &r.lo {
            std::ops::Bound::Unbounded => true,
            std::ops::Bound::Included(x) => k >= x.as_slice(),
            std::ops::Bound::Excluded(x) => k > x.as_slice(),
        };
        let hi = match &r.hi {
            std::ops::Bound::Unbounded => true,
            std::ops::Bound::Included(x) => k <= x.as_slice(),
            std::ops::Bound::Excluded(x) => k < x.as_slice(),
        };
        lo && hi
    }
    let mut out = Vec::new();
    walk(store, root, r, &mut out);
    // The format's order, stated here independently of the library: level
    // descending, then first key ascending.
    out.sort_by_key(|b| {
        let n = Node::parse(b).unwrap();
        (std::cmp::Reverse(n.level()), n.key(0))
    });
    out
}

/// An aggregate proof's BYTES are fixed by the format, not by the order
/// `aggregate` happens to walk in.
#[test]
fn an_aggregate_proofs_bytes_are_what_the_format_says() {
    let (blocks, root, m) = tree(20_000);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let mut checked = 0;
    for (what, r) in [
        ("the whole tree", Range::default()),
        ("a prefix", Range::prefix(b"d/")),
        ("another prefix", Range::prefix(b"e/")),
        (
            "a window",
            Range {
                lo: std::ops::Bound::Included(keys[4_000].clone()),
                hi: std::ops::Bound::Included(keys[15_000].clone()),
                ..Range::default()
            },
        ),
        (
            "an open-ended window",
            Range {
                lo: std::ops::Bound::Included(keys[18_000].clone()),
                ..Range::default()
            },
        ),
    ] {
        let p = prove_aggregate(&blocks, &root, &r).unwrap();
        let want = expected_aggregate_nodes(&blocks, &root, &r);
        assert_eq!(p.nodes, want, "{what}: the node list is not the format's");
        verify_aggregate(&root, &r, &p).unwrap();
        checked += 1;
    }
    assert_eq!(checked, 5);

    // And the order rule is enforced, not merely produced: the same blocks in
    // any other order are refused.
    let r = Range::prefix(b"d/");
    let p = prove_aggregate(&blocks, &root, &r).unwrap();
    assert!(
        p.nodes.len() >= 3,
        "the case must have something to reorder"
    );
    let mut swapped = p.clone();
    let n = swapped.nodes.len();
    swapped.nodes.swap(n - 2, n - 1);
    assert_eq!(
        verify_aggregate(&root, &r, &swapped),
        Err(ProofError::OutOfOrder)
    );
}

/// A proof carrying blocks that were never read is refused even though the
/// ANSWER it would give is correct.
///
/// This is the set rule on its own, and reaching it takes care: extra blocks
/// usually trip the shape gate first (too many for the tree's height), and a
/// proof verified for a key it was not built for trips `Incomplete` first. The
/// one-node absence proof against a tall tree clears both — riders fit under
/// the count bound, and the read stops at the root — so nothing but the set
/// rule stands between this and acceptance.
#[test]
fn blocks_that_were_never_read_are_refused_although_the_answer_is_right() {
    let (blocks, root, m) = tree(20_000);
    let h = height(&blocks, &root);
    assert!(h >= 4, "the tree must be tall enough for riders to fit");
    let mut below = m.keys().next().unwrap().clone();
    below.insert(0, 0x00);

    let honest = prove(&blocks, &root, &below).unwrap();
    assert_eq!(honest.nodes.len(), 1);
    assert_eq!(verify(&root, &below, &honest).unwrap(), Proven::Absent);

    // Valid nodes of this very tree, riding along unread.
    let path = prove(&blocks, &root, m.keys().nth(500).unwrap()).unwrap();
    for riders in 1..=3 {
        let mut nodes = honest.nodes.clone();
        nodes.extend(path.nodes[1..=riders].iter().cloned());
        let p = Proof { nodes, value: None };
        assert!(
            p.nodes.len() <= h,
            "the rider proof must clear the shape gate to test the set rule"
        );
        assert_eq!(
            verify(&root, &below, &p),
            Err(ProofError::Extra),
            "{riders} unread block(s) must be refused, right answer or not"
        );
    }
}
