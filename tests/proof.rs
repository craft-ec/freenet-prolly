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

// ---------------------------------------------------------------------------
// range proofs: a listing is COMPLETE
// ---------------------------------------------------------------------------

use freenet_prolly::proof::{prove_range, verify_range, verify_range_bytes, ProvenValue};

fn page_range(lo: &[u8], entries: usize) -> Range {
    Range {
        lo: std::ops::Bound::Included(lo.to_vec()),
        max_entries: entries,
        ..Range::default()
    }
}

/// What a gateway would lie about: a listing with something left out. Every
/// way of omitting must be unprovable.
#[test]
fn an_omitted_entry_makes_a_listing_unprovable() {
    let (blocks, root, m) = tree(20_000);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let r = page_range(&keys[4_000], 200);

    let honest = prove_range(&blocks, &root, &r).unwrap();
    let page = verify_range(&root, &r, &honest).unwrap();
    assert_eq!(page.entries.len(), 200);
    // The control: it says what the tree says.
    let want: Vec<Vec<u8>> = keys[4_000..4_200].to_vec();
    let got: Vec<Vec<u8>> = page.entries.iter().map(|(k, _)| k.clone()).collect();
    assert_eq!(got, want);
    // And the VALUES are the tree's, not only the keys — a listing with the
    // right keys and wrong values would be the same lie in a different place.
    for (k, v) in &page.entries {
        match v {
            ProvenValue::Inline(b) => assert_eq!(b, &m[k]),
            ProvenValue::Ref { cid, len } => {
                assert_eq!(*len as usize, m[k].len());
                assert_eq!(*cid, block_id(kind::RAW, &m[k]));
            }
        }
    }

    // A leaf of ANOTHER tree covering the same span — the substitution a
    // gateway would reach for.
    let (other_blocks, other_root, _) = {
        let mut m2 = m.clone();
        // Same keys, one value changed, so the leaf spans match.
        let k = keys[4_100].clone();
        m2.insert(k, vec![0xee; 140]);
        let (b, rt) = build(&m2);
        (b, rt, ())
    };
    let other = prove_range(&other_blocks, &other_root, &r).unwrap();

    let leaves: Vec<usize> = (0..honest.nodes.len())
        .filter(|i| Node::parse(&honest.nodes[*i]).unwrap().is_leaf())
        .collect();
    assert!(leaves.len() >= 3, "the page must span several leaves");

    for (what, p) in [
        (
            "a leaf dropped from the middle",
            Proof {
                nodes: {
                    let mut v = honest.nodes.clone();
                    v.remove(leaves[leaves.len() / 2]);
                    v
                },
                value: None,
            },
        ),
        (
            "the first leaf dropped — the page starts late",
            Proof {
                nodes: {
                    let mut v = honest.nodes.clone();
                    v.remove(leaves[0]);
                    v
                },
                value: None,
            },
        ),
        (
            "the last leaf dropped — the page stops early",
            Proof {
                nodes: {
                    let mut v = honest.nodes.clone();
                    v.remove(leaves[leaves.len() - 1]);
                    v
                },
                value: None,
            },
        ),
        (
            "a leaf swapped for another tree's leaf over the same span",
            Proof {
                nodes: {
                    let mut v = honest.nodes.clone();
                    let i = leaves[leaves.len() / 2];
                    // A leaf from the other tree, same position in the page.
                    let theirs: Vec<Vec<u8>> = other
                        .nodes
                        .iter()
                        .filter(|b| Node::parse(b).unwrap().is_leaf())
                        .cloned()
                        .collect();
                    v[i] = theirs[leaves.len() / 2].clone();
                    v
                },
                value: None,
            },
        ),
    ] {
        match verify_range(&root, &r, &p) {
            Err(_) => {}
            Ok(page) => panic!(
                "{what}: accepted a listing of {} entries",
                page.entries.len()
            ),
        }
    }

    // An entry removed from a leaf: the leaf's bytes change, so its id changes,
    // and the block is not the one its parent names.
    let i = leaves[1];
    let leaf = Node::parse(&honest.nodes[i]).unwrap();
    let mut rebuilt = freenet_prolly::node::NodeBuilder::leaf();
    for j in 0..leaf.len() {
        if j == 1 {
            continue; // the omission
        }
        rebuilt.push(&leaf.key(j), leaf.value(j)).unwrap();
    }
    let mut nodes = honest.nodes.clone();
    nodes[i] = rebuilt.finish().unwrap();
    assert!(
        verify_range(&root, &r, &Proof { nodes, value: None }).is_err(),
        "an entry dropped from a leaf must be unprovable"
    );
}

/// A proof answers a QUESTION, and every question it answers it answers truly.
///
/// Not "any other question is refused": a page proof's blocks can answer for a
/// slightly larger limit or a slightly later start, because those entries live
/// in leaves the proof already carries and `next` moves with them. Measured: a
/// proof for 100 entries (11 blocks) behaves like this:
///
/// | limit asked | result |
/// |---|---|
/// | 1 | `TooLarge` |
/// | 50, 99 | `Extra` — a smaller page reads fewer blocks, leaving some unread |
/// | 100, 101, 110 | `Ok`, and complete and true for its own span |
/// | 120, 200, 400, 1024 | `NotComplete` — needs leaves the proof does not carry |
///
/// What matters — and what is asserted here — is that no question yields a
/// FALSE answer, and that any question needing blocks the proof does not carry
/// is refused rather than guessed at.
#[test]
fn a_range_proof_is_for_exactly_its_question() {
    let (blocks, root, m) = tree(20_000);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let r = page_range(&keys[1_000], 100);
    let p = prove_range(&blocks, &root, &r).unwrap();
    assert!(verify_range(&root, &r, &p).is_ok());

    // Changing the entry limit: what matters is not that every other limit is
    // REFUSED — some are answerable from the same blocks — but that no limit
    // can extract a FALSE claim. Measured: a proof for 100 entries answers for
    // 100 to 110 (the entries its leaves hold), and every one of those answers
    // is complete and true for its own span, because `next` moves with it.
    let mut answered = 0;
    for limit in [1usize, 50, 99, 100, 101, 110, 120, 200, 400, 1024] {
        let other = Range {
            max_entries: limit,
            ..r.clone()
        };
        match verify_range(&root, &other, &p) {
            Err(_) => {}
            Ok(page) => {
                // Answered — so it must be the truth, entry for entry.
                let want: Vec<Vec<u8>> = keys[1_000..1_000 + page.entries.len()].to_vec();
                let got: Vec<Vec<u8>> = page.entries.iter().map(|(k, _)| k.clone()).collect();
                assert_eq!(got, want, "limit {limit} answered, and answered wrongly");
                assert!(
                    page.entries.len() >= 100,
                    "limit {limit} answered with fewer entries than were proved"
                );
                answered += 1;
            }
        }
    }
    assert!(
        answered >= 2,
        "the band of answerable limits must be exercised"
    );
    // A limit needing blocks the proof does not carry is refused, not guessed.
    assert_eq!(
        verify_range(
            &root,
            &Range {
                max_entries: 400,
                ..r.clone()
            },
            &p
        ),
        Err(ProofError::NotComplete)
    );
    // A smaller limit reads fewer blocks, so the proof carries blocks that were
    // never read — the set rule.
    assert_eq!(
        verify_range(
            &root,
            &Range {
                max_entries: 50,
                ..r.clone()
            },
            &p
        ),
        Err(ProofError::Extra)
    );

    // A different lo behaves the same way, and for the same reason: the entries
    // for a slightly later start are in leaves the proof already carries, so
    // the answer is available AND true. Nothing false can be extracted.
    for shift in [1usize, 2, 5, 50, 500] {
        let moved = page_range(&keys[1_000 + shift], 100);
        if let Ok(page) = verify_range(&root, &moved, &p) {
            let want: Vec<Vec<u8>> =
                keys[1_000 + shift..1_000 + shift + page.entries.len()].to_vec();
            let got: Vec<Vec<u8>> = page.entries.iter().map(|(k, _)| k.clone()).collect();
            assert_eq!(
                got, want,
                "a shifted start was answered, and answered wrongly"
            );
        }
    }

    // A different root.
    let mut b2 = blocks.clone();
    let root2 = apply_into(
        &mut b2,
        &root,
        &[(keys[19_000].clone(), Edit::Put(vec![3u8; 90]))],
    )
    .unwrap()
    .root;
    assert_eq!(verify_range(&root2, &r, &p), Err(ProofError::WrongRoot));

    // An unbounded page cannot be proved at all.
    let unbounded = Range {
        max_entries: 0,
        max_bytes: 0,
        ..Range::default()
    };
    assert!(matches!(
        prove_range(&blocks, &root, &unbounded),
        Err(ProofError::Unsupported(_))
    ));
    // Nor one bounded only by bytes: there is no leaf count to derive.
    let bytes_only = Range {
        max_entries: 0,
        max_bytes: 4096,
        ..Range::default()
    };
    assert!(matches!(
        prove_range(&blocks, &root, &bytes_only),
        Err(ProofError::Unsupported(_))
    ));
}

/// Pages are proved one at a time, and each says nothing about the others.
#[test]
fn a_continuation_page_proves_its_own_span() {
    let (blocks, root, m) = tree(20_000);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let mut at = keys[0].clone();
    let mut seen: Vec<Vec<u8>> = Vec::new();
    let mut pages = 0;
    loop {
        let r = Range {
            after: (pages > 0).then(|| at.clone()),
            lo: std::ops::Bound::Included(keys[0].clone()),
            max_entries: 250,
            ..Range::default()
        };
        let p = prove_range(&blocks, &root, &r).unwrap();
        let page = verify_range(&root, &r, &p).unwrap();
        seen.extend(page.entries.iter().map(|(k, _)| k.clone()));
        pages += 1;
        assert!(pages < 10);
        match page.next {
            Some(n) => at = n,
            None => break,
        }
        if pages == 4 {
            break;
        }
    }
    assert_eq!(seen, keys[..seen.len()].to_vec(), "the pages concatenate");
    assert!(pages >= 4);
    println!(
        "range proof: {pages} pages of 250, {} entries proved",
        seen.len()
    );
}

/// Hostile input, cheaply refused, never a panic — and the wire form refuses
/// before it copies.
#[test]
fn a_hostile_range_proof_is_refused_cheaply() {
    let (blocks, root, m) = tree(20_000);
    let keys: Vec<Vec<u8>> = m.keys().cloned().collect();
    let r = page_range(&keys[500], 50);
    let honest = prove_range(&blocks, &root, &r).unwrap();
    assert!(verify_range(&root, &r, &honest).is_ok());
    let wire = honest.encode();
    assert!(verify_range_bytes(&root, &r, &wire).is_ok());

    // Padding a stranger attached must not be copied before it is refused.
    let mut padded = honest.clone();
    let filler = Node::parse(&honest.nodes[honest.nodes.len() - 1])
        .unwrap()
        .is_leaf();
    assert!(filler);
    for i in 0..5_000 {
        let mut b = freenet_prolly::node::NodeBuilder::leaf();
        b.push(format!("pad/{i:012}").as_bytes(), Value::Inline(&[0u8; 64]))
            .unwrap();
        padded.nodes.push(b.finish().unwrap());
    }
    let big = padded.encode();
    assert!(big.len() > 500_000, "the case must be large: {}", big.len());
    assert!(matches!(
        verify_range_bytes(&root, &r, &big),
        Err(ProofError::TooLarge(_))
    ));

    for junk in [&b""[..], b"PP01", &[0xff; 200]] {
        assert!(verify_range_bytes(&root, &r, junk).is_err());
    }
    let mut rr = rng(3);
    for _ in 0..300 {
        let mut b = wire.clone();
        let at = rr() as usize % b.len();
        b[at] ^= (rr() % 255) as u8 + 1;
        let _ = verify_range_bytes(&root, &r, &b);
    }
    println!(
        "range proof: {} blocks, {} B; 5,000 pad nodes refused from {} B",
        honest.nodes.len(),
        wire.len(),
        big.len()
    );
}
