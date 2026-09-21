//! ARCHITECT: the tests prolly#53 and #54 need, written BEFORE the fix. Every `#[test]` here must be RED on
//! origin/main 59e5e68 except the ones named `control_*`, which must be green before AND after.
use freenet_prolly::build::{build, init};
use freenet_prolly::node::{NodeBuilder, Value};
use freenet_prolly::proof::*;
use freenet_prolly::range::Range;
use freenet_prolly::store::MemBlocks;
use freenet_prolly::{block_id, kind};
use std::ops::Bound;

fn empty() -> (MemBlocks, freenet_prolly::Cid) {
    let mut b = MemBlocks::default();
    let r = init(&mut b);
    (b, r)
}
fn one() -> (MemBlocks, freenet_prolly::Cid) {
    let mut b = MemBlocks::default();
    let r = build([(&b"a"[..], Value::Inline(b"v"))], |c, x| b.insert(c, x)).unwrap();
    (b, r)
}
fn page() -> Range {
    Range {
        max_entries: 10,
        ..Default::default()
    }
}

// ---------------- #53: honest proofs from the EMPTY tree ----------------
#[test]
fn p53_point_absent_in_the_empty_tree_both_doors() {
    let (b, root) = empty();
    let p = prove(&b, &root, b"missing").unwrap();
    assert_eq!(verify(&root, b"missing", &p), Ok(Proven::Absent));
    assert_eq!(
        verify_bytes(&root, b"missing", &p.encode()),
        Ok(ProvenOwned::Absent)
    );
}
#[test]
fn p53_range_over_the_empty_tree_both_doors() {
    let (b, root) = empty();
    let p = prove_range(&b, &root, &page()).unwrap();
    assert_eq!(
        verify_range(&root, &page(), &p).map(|g| (g.entries.len(), g.next)),
        Ok((0, None))
    );
    assert_eq!(
        verify_range_bytes(&root, &page(), &p.encode()).map(|g| (g.entries.len(), g.next)),
        Ok((0, None))
    );
}
#[test]
fn p53_aggregate_over_the_empty_tree() {
    let (b, root) = empty();
    let p = prove_aggregate(&b, &root, &Default::default()).unwrap();
    assert_eq!(
        verify_aggregate(&root, &Default::default(), &p).map(|c| c.agg().count),
        Ok(0)
    );
}
/// The fix must not open the door it is next to: an empty node is acceptable ONLY as the lone root.
#[test]
fn control_53_an_empty_block_riding_along_is_still_refused() {
    let (b, root) = one();
    let (_, e) = empty();
    let mut p = prove(&b, &root, b"a").unwrap();
    let mut eb = MemBlocks::default();
    let er = init(&mut eb);
    assert_eq!(er, e);
    p.nodes.push(
        freenet_prolly::store::Blocks::get(&eb, &er)
            .unwrap()
            .to_vec(),
    );
    assert!(
        verify(&root, b"a", &p).is_err(),
        "an unused empty block was accepted"
    );
}
#[test]
fn control_53_the_empty_root_does_not_prove_another_root() {
    let (b, root) = empty();
    let (_, other) = one();
    let p = prove(&b, &root, b"a").unwrap();
    assert_eq!(verify(&other, b"a", &p), Err(ProofError::WrongRoot));
}
#[test]
fn control_53_nonempty_tree_absent_key_still_verifies() {
    let (b, root) = one();
    let p = prove(&b, &root, b"missing").unwrap();
    assert_eq!(
        verify_bytes(&root, b"missing", &p.encode()),
        Ok(ProvenOwned::Absent)
    );
}
/// Is there a SECOND empty node a writer could use as a root? If `finish` builds an empty branch, say so.
#[test]
fn control_53_can_an_empty_branch_even_exist() {
    let built = NodeBuilder::branch(1).finish();
    println!(
        "NodeBuilder::branch(1).finish() with no children -> {:?}",
        built.as_ref().map(|b| b.len())
    );
    if let Ok(bytes) = built {
        let id = block_id(kind::TREE_NODE, &bytes);
        let p = Proof {
            nodes: vec![bytes],
            value: None,
        };
        println!(
            "  an empty BRANCH as a lone root: verify -> {:?}",
            verify(&id, b"a", &p).map(|_| ())
        );
    }
}

// ---------------- #54: a trailer nothing reads ----------------
fn junk() -> Option<Vec<u8>> {
    Some(b"unauthenticated payload".to_vec())
}
#[test]
fn p54_range_proof_with_a_trailer_is_refused_by_both_doors() {
    let (b, root) = one();
    let mut p = prove_range(&b, &root, &page()).unwrap();
    p.value = junk();
    assert!(
        verify_range(&root, &page(), &p).is_err(),
        "decoded door accepted an unused trailer"
    );
    assert!(
        verify_range_bytes(&root, &page(), &p.encode()).is_err(),
        "wire door accepted an unused trailer"
    );
}
#[test]
fn p54_aggregate_proof_with_a_trailer_is_refused() {
    let (b, root) = one();
    let mut p = prove_aggregate(&b, &root, &Default::default()).unwrap();
    p.value = junk();
    assert!(verify_aggregate(&root, &Default::default(), &p).is_err());
}
#[test]
fn p54_the_two_doors_agree_on_an_empty_query_with_a_trailer() {
    let (_, root) = one();
    let q = Range {
        lo: Bound::Included(b"z".to_vec()),
        hi: Bound::Included(b"a".to_vec()),
        max_entries: 10,
        ..Default::default()
    };
    let p = Proof {
        nodes: vec![],
        value: junk(),
    };
    let (d, w) = (
        verify_range(&root, &q, &p).is_ok(),
        verify_range_bytes(&root, &q, &p.encode()).is_ok(),
    );
    assert_eq!(d, w, "decoded door says {d}, wire door says {w}");
    assert!(!d, "and the answer is REFUSED");
}
#[test]
fn control_54_honest_range_aggregate_and_empty_query_still_verify() {
    let (b, root) = one();
    assert!(verify_range_bytes(
        &root,
        &page(),
        &prove_range(&b, &root, &page()).unwrap().encode()
    )
    .is_ok());
    assert!(verify_aggregate(
        &root,
        &Default::default(),
        &prove_aggregate(&b, &root, &Default::default()).unwrap()
    )
    .is_ok());
    let q = Range {
        lo: Bound::Included(b"z".to_vec()),
        hi: Bound::Included(b"a".to_vec()),
        max_entries: 10,
        ..Default::default()
    };
    let p = Proof {
        nodes: vec![],
        value: None,
    };
    assert!(
        verify_range(&root, &q, &p).is_ok() && verify_range_bytes(&root, &q, &p.encode()).is_ok()
    );
}
#[test]
fn control_54_a_point_proof_with_its_GENUINE_value_trailer_still_verifies() {
    let mut b = MemBlocks::default();
    let start = init(&mut b);
    let root = freenet_prolly::apply::apply_into(
        &mut b,
        &start,
        &[(
            b"a".to_vec(),
            freenet_prolly::apply::Edit::Put(vec![7u8; 5000]),
        )],
    )
    .unwrap()
    .root;
    let p = prove_with_value(&b, &root, b"a").unwrap();
    assert!(p.value.is_some(), "setup: the proof carries the value");
    assert!(matches!(
        verify(&root, b"a", &p),
        Ok(Proven::Present(Value::Inline(_)))
    ));
}
