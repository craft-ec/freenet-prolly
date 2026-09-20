//! The vector cases, in one place, so the emitter and the differential cannot
//! disagree about what "case three" is.
//!
//! A test file per door would mean two lists that drift — which is the whole
//! failure this module was lifted here to end.
//!
//! Under `tests/common/` rather than `tests/cases.rs`: cargo makes a test
//! TARGET of every file directly in `tests/`, so a shared helper module there
//! compiles as an empty test binary of its own.

use freenet_prolly::kind;

/// A member whose bytes are a function of its seed and length, so a case is
/// reproducible from its name in any of the three repositories.
pub fn member(kind: u8, seed: u8, len: usize) -> (u8, Vec<u8>) {
    (
        kind,
        (0..len)
            .map(|i| (i as u8).wrapping_mul(31).wrapping_add(seed))
            .collect(),
    )
}

/// A named set of members: what one vector covers.
pub type Case = (&'static str, Vec<(u8, Vec<u8>)>);

/// The cases, in the order freenet-contracts emitted them — do not reorder:
/// a vector is only a differential while it names the same members.
pub fn cases() -> Vec<Case> {
    let raw = kind::RAW;
    vec![
        // A member may be empty: the length field is what says so, and a
        // zero-length body is still a block with an id.
        ("one-empty", vec![member(raw, 0, 0)]),
        ("one-small", vec![member(raw, 7, 13)]),
        // Offered out of order: build sorts by block id, so the bytes say
        // nothing about the order they arrived in.
        (
            "three-unordered",
            vec![member(raw, 3, 40), member(raw, 1, 9), member(raw, 2, 77)],
        ),
        // The same block twice is one member: a pack is a SET.
        (
            "duplicates",
            vec![member(raw, 5, 20), member(raw, 5, 20), member(raw, 6, 4)],
        ),
        (
            "many",
            (0..12u8)
                .map(|i| member(raw, i, 1 + i as usize * 3))
                .collect(),
        ),
    ]
}

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
