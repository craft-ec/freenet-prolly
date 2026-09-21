//! freenet-prolly#55: a child at level 255.
//!
//! A level is a `u8` read from a stranger's bytes, and every place that asked
//! "is this child one level below its parent?" computed `child + 1`. At 255
//! that is a PANIC with overflow checks on — inside `verify_bytes` and
//! `fraud`, which exist to take bytes from strangers — and with them off it
//! wraps to 0 and happens to give the right answer, because no branch has
//! level 0. Right by accident is pinned here as right on purpose: every entry
//! point gives the SAME refusal in both profiles.
//!
//! Run it both ways — `cargo test --test level_overflow` (checks on) and
//! `cargo test --release --test level_overflow` (off). The first test says
//! which one it is, so a log shows which profile a green run covered.

use freenet_prolly::aggregate::{aggregate_verified, fraud};
use freenet_prolly::node::{Agg, Node, NodeBuilder, Value};
use freenet_prolly::proof::*;
use freenet_prolly::range::{range, Range, RangeError};
use freenet_prolly::store::{MemBlocks, ReadError};
use freenet_prolly::{block_id, kind, read, Cid};
use std::panic::{catch_unwind, AssertUnwindSafe};

fn id(b: &[u8]) -> Cid {
    block_id(kind::TREE_NODE, b)
}

/// A branch at `level` holding one child, `a` → an arbitrary id.
fn lone_branch(level: u8) -> Vec<u8> {
    let mut n = NodeBuilder::branch(level);
    n.push_child(b"a", [7u8; 32], Agg { count: 1, bytes: 1 })
        .unwrap();
    n.finish().unwrap()
}

/// `parent` (level `p`) naming `child` (level `c`) truthfully in every other
/// respect: its real hash, its first key, its aggregate. Only the level can be
/// wrong.
fn pair(p: u8, c: u8) -> (Vec<u8>, Vec<u8>) {
    let child = if c == 0 {
        let mut n = NodeBuilder::leaf();
        n.push(b"a", Value::Inline(b"1")).unwrap();
        n.finish().unwrap()
    } else {
        lone_branch(c)
    };
    let mut n = NodeBuilder::branch(p);
    n.push_child(b"a", id(&child), Node::parse(&child).unwrap().agg())
        .unwrap();
    (n.finish().unwrap(), child)
}

fn overflow_checks_on() -> bool {
    let x: u8 = std::hint::black_box(255);
    catch_unwind(|| std::hint::black_box(x) + 1).is_err()
}

#[test]
fn which_profile_this_run_covered() {
    // Not an assertion: a record. The gate runs this file in both profiles,
    // and this line is how a log says which one it is looking at.
    println!(
        "level_overflow: overflow checks {}",
        if overflow_checks_on() {
            "ON (debug-like)"
        } else {
            "OFF (release)"
        }
    );
}

/// What every entry point says about one parent/child pair — run under
/// `catch_unwind`, so a panic is a RESULT this test reports, not a crash that
/// hides the other six.
fn answers(parent: &[u8], child: &[u8]) -> Vec<(&'static str, Result<String, String>)> {
    let root = id(parent);
    let mut b = MemBlocks::default();
    b.insert(root, parent);
    b.insert(id(child), child);
    let all = Range::default();
    let path = Proof {
        nodes: vec![parent.to_vec(), child.to_vec()],
        value: None,
    }
    .encode();
    let run = |f: &dyn Fn() -> String| {
        catch_unwind(AssertUnwindSafe(f)).map_err(|p| {
            p.downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| p.downcast_ref::<String>().cloned())
                .unwrap_or_default()
        })
    };
    let is_mismatch = |e: &ReadError| matches!(e, ReadError::Mismatch(_));
    vec![
        (
            "read::get",
            run(&|| {
                format!(
                    "{:?}",
                    read::get(&b, &root, b"a")
                        .map_err(|e| is_mismatch(&e))
                        .map(|v| v.is_some())
                )
            }),
        ),
        ("fraud", run(&|| format!("{}", fraud(parent, child)))),
        (
            "range::range",
            run(&|| {
                format!(
                    "{:?}",
                    range(&b, &root, &all)
                        .map(|p| p.entries.len())
                        .map_err(|e| matches!(e, RangeError::Read(ReadError::Mismatch(_))))
                )
            }),
        ),
        (
            "aggregate_verified",
            run(&|| format!("{}", aggregate_verified(&b, &root, &all).is_err())),
        ),
        (
            "prove",
            run(&|| {
                format!(
                    "{:?}",
                    prove(&b, &root, b"a")
                        .map(|_| ())
                        .map_err(|e| is_mismatch(&e))
                )
            }),
        ),
        (
            "verify_bytes",
            run(&|| format!("{}", verify_bytes(&root, b"a", &path).is_err())),
        ),
        (
            "verify_range_bytes",
            run(&|| format!("{}", verify_range_bytes(&root, &all, &path).is_err())),
        ),
    ]
}

/// THE REPORTED CASE, and the expected answer at every door: a refusal —
/// `Mismatch` where a read reports one, `true` from `fraud` (the pair IS a
/// proof: the parent names a block that contradicts it).
#[test]
fn a_level_255_child_is_refused_at_every_entry_point_without_panicking() {
    let (parent, child) = pair(1, 255);
    let want = [
        ("read::get", "Err(true)"),
        ("fraud", "true"),
        ("range::range", "Err(true)"),
        ("aggregate_verified", "true"),
        ("prove", "Err(true)"),
        ("verify_bytes", "true"),
        ("verify_range_bytes", "true"),
    ];
    let got = answers(&parent, &child);
    assert_eq!(
        got.len(),
        want.len(),
        "an entry point was dropped from the list"
    );
    // Every door judged, THEN one verdict — so a failure lists all of them,
    // not just whichever came first.
    let mut wrong = Vec::new();
    for ((door, got), (name, want)) in got.iter().zip(want) {
        assert_eq!(*door, name);
        match got {
            Err(msg) => wrong.push(format!("{door} PANICKED ({msg})")),
            Ok(ans) if ans != want => wrong.push(format!("{door} answered {ans}, want {want}")),
            Ok(_) => {}
        }
    }
    assert!(
        wrong.is_empty(),
        "on a level-255 child — a stranger's block is a trap:\n  {}",
        wrong.join("\n  ")
    );
}

/// And the mirror, 255 under 255 — `255 + 1` wrapped is 0, not 255, so the
/// old arithmetic refused this too; a checked rewrite must as well.
#[test]
fn every_other_wrong_level_is_refused_too() {
    for (p, c) in [(1u8, 255u8), (255, 255), (255, 253), (2, 0), (1, 1), (3, 1)] {
        let (parent, child) = pair(p, c);
        assert!(
            catch_unwind(|| fraud(&parent, &child)).expect("fraud panicked"),
            "fraud accepted a level-{c} child under a level-{p} parent"
        );
    }
}

/// CONTROL: adjacent levels — including the top of the range, 254 under 255 —
/// are ACCEPTED, so the refusals above are about the level and not about the
/// fixture.
#[test]
fn adjacent_levels_are_accepted_up_to_the_top() {
    for (p, c) in [(1u8, 0u8), (2, 1), (255, 254)] {
        let (parent, child) = pair(p, c);
        assert!(
            !fraud(&parent, &child),
            "fraud refuted an honest level-{c}-under-{p} pair"
        );
    }
    // Through a READ, where the child can actually be reached: a leaf under 1.
    let (parent, child) = pair(1, 0);
    for (door, got) in answers(&parent, &child) {
        let got = got.unwrap_or_else(|m| panic!("{door} panicked on an honest pair: {m}"));
        let ok = matches!(
            (door, got.as_str()),
            ("read::get", "Ok(true)")
                | ("fraud", "false")
                | ("range::range", "Ok(1)")
                | ("aggregate_verified", "false")
                | ("prove", "Ok(())")
                | ("verify_bytes", "false")
                | ("verify_range_bytes", "false")
        );
        assert!(ok, "CONTROL {door}: an honest pair answered {got}");
    }
}
