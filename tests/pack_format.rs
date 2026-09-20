//! Does this crate build the bytes the Block contract defines?
//!
//! A differential, not a self-test: the vectors in `pack_vectors.txt` were
//! produced by `freenet-contracts block::pack::build` before this module
//! existed, and this crate has to reproduce them byte for byte. A test that
//! checked this crate against its own output would pass forever however far the
//! two had drifted — and the drift does not show up in either repository's
//! tests, it shows up as a host refusing a commit in production.

mod common;

use freenet_prolly::pack;

#[test]
fn this_crate_builds_the_bytes_the_contract_defines() {
    let text = include_str!("pack_vectors.txt");
    let want: Vec<(&str, &str)> = text
        .lines()
        .filter_map(|l| l.strip_prefix("VEC "))
        .filter_map(|l| l.split_once(' '))
        .collect();
    // A file that failed to parse and a file with no disagreements read the
    // same from here: a green run over zero vectors is the failure this guards.
    assert!(
        !want.is_empty(),
        "no vectors were read from pack_vectors.txt; this test would pass over nothing"
    );

    let cases = common::cases();
    assert_eq!(
        want.len(),
        cases.len(),
        "{} vectors for {} cases — a case without a vector is untested, and a \
         vector without a case is a line nobody checks",
        want.len(),
        cases.len()
    );

    for ((name, members), (vec_name, vec_hex)) in cases.iter().zip(&want) {
        assert_eq!(
            name, vec_name,
            "the cases and the vectors are in different orders; a vector is only \
             a differential while it names the same members"
        );
        let body = pack::build(members).expect("every case builds");
        assert_eq!(
            &common::hex(&body),
            vec_hex,
            "case {name}: this crate's build does not reproduce the contract's bytes"
        );
    }
}

/// Every vector must also be a pack this crate ACCEPTS, through the other door.
///
/// Building bytes that match and refusing them at the gate is a drift this test
/// would otherwise pass over: the two doors are what the contract and the
/// engine use respectively, and they have to agree on one set of bytes.
#[test]
fn every_vector_parses_back_to_the_members_it_was_built_from() {
    for (name, members) in common::cases() {
        let body = pack::build(&members).expect("builds");
        let got = pack::members(&body).unwrap_or_else(|e| panic!("case {name}: {e:?}"));
        // De-duplicated by id, so the count is the distinct members, not the
        // ones offered.
        let mut want: Vec<_> = members
            .iter()
            .map(|(k, b)| freenet_prolly::block_id(*k, b))
            .collect();
        want.sort();
        want.dedup();
        assert_eq!(
            got.iter().map(|m| m.id).collect::<Vec<_>>(),
            want,
            "case {name}: the members that come back are not the set that went in"
        );
        // And the bytes round-trip: rebuilding from what came out gives the
        // same body.
        let again = pack::build(
            &got.iter()
                .map(|m| (m.kind, m.body.to_vec()))
                .collect::<Vec<_>>(),
        )
        .expect("rebuilds");
        assert_eq!(again, body, "case {name}: the body is not a fixed point");
    }
}
