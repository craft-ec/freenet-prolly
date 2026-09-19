//! Computes the frozen root vectors on wasm32 so `check-wasm.sh` can compare
//! them with `tests/vectors.txt`: boundaries must not depend on the target.

#[path = "../../tests/common/dataset.rs"]
mod common;

use freenet_prolly::build::build;
use freenet_prolly::Cid;
use freenet_prolly::node::Value;

/// Root cid of `dataset(1, n)`, written to a static buffer; returns its address.
#[no_mangle]
pub extern "C" fn root(n: u32) -> *const u8 {
    static mut OUT: [u8; 32] = [0; 32];
    let e = common::dataset(1, n as usize);
    let r = build(
        e.iter().map(|(k, v)| (k.as_slice(), Value::Inline(v))),
        |_, _| {},
    )
    .unwrap();
    unsafe {
        OUT = r;
        &raw const OUT as *const u8
    }
}

/// The frozen proof for `dataset(1, n)`: the same computation as
/// `tests/boundary.rs::proof_vector`, meeting it only in `tests/vectors.txt`.
///
/// Deliberately not shared code — if the two met in a helper, this would check
/// that the helper is deterministic rather than that the TARGET is.
fn proof_vector(n: u32) -> (freenet_prolly::proof::Proof, Cid, Vec<u8>) {
    use freenet_prolly::store::MemBlocks;
    let e = common::dataset(1, n as usize);
    let mut store = MemBlocks::default();
    let root = build(
        e.iter().map(|(k, v)| (k.as_slice(), Value::Inline(v))),
        |c, b| store.insert(c, b),
    )
    .unwrap();
    let mut keys: Vec<Vec<u8>> = e.iter().map(|(k, _)| k.clone()).collect();
    keys.sort();
    keys.dedup();
    let key = keys[keys.len() / 2].clone();
    let p = freenet_prolly::proof::prove(&store, &root, &key).unwrap();
    (p, root, key)
}

/// BLAKE3 of the encoded proof, into a static buffer; returns its address.
#[no_mangle]
pub extern "C" fn proof_hash(n: u32) -> *const u8 {
    static mut OUT: [u8; 32] = [0; 32];
    let (p, _, _) = proof_vector(n);
    unsafe {
        OUT = *blake3::hash(&p.encode()).as_bytes();
        &raw const OUT as *const u8
    }
}

/// Node count and encoded size, packed into one u64: `(nodes << 32) | bytes`.
#[no_mangle]
pub extern "C" fn proof_shape(n: u32) -> u64 {
    let (p, _, _) = proof_vector(n);
    ((p.nodes.len() as u64) << 32) | p.encode().len() as u64
}

/// 1 if the proof this target built verifies here, against the root and key it
/// was built for, and answers Present. A proof that is the same bytes but does
/// not verify would be a worse failure than one that differs.
#[no_mangle]
pub extern "C" fn proof_verify(n: u32) -> i32 {
    use freenet_prolly::proof::{verify, Proof, Proven};
    let (p, root, key) = proof_vector(n);
    // Through the wire form, so the encoding is exercised too.
    let Ok(decoded) = Proof::decode(&p.encode()) else {
        return 0;
    };
    match verify(&root, &key, &decoded) {
        Ok(Proven::Present(_)) => 1,
        _ => 0,
    }
}
