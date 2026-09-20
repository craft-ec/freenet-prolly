//! Emit the vector lines, so `tests/pack_vectors.txt` has a maintained source.
//!
//! It was one person's scratch file in another repository. A frozen vector
//! whose generator exists only in a comment is one nobody can add a case to
//! without re-authoring the whole file by hand, which is how a differential
//! quietly turns into a self-test.
//!
//!   cargo test --test emit_pack_vectors -- --nocapture | grep '^VEC'
//!
//! DIFF the result into the file; never overwrite it. The first five lines were
//! authored by freenet-contracts and this crate has to reproduce them, not
//! replace them.

mod common;

use freenet_prolly::pack;

#[test]
fn emit() {
    for (name, members) in common::cases() {
        let body = pack::build(&members).expect("every case builds");
        println!("VEC {name} {}", common::hex(&body));
    }
}
