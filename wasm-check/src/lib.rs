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

/// The frozen RANGE proof for `dataset(1, n)`: a 32-entry page from the first
/// key. Same duplication rule as `proof_vector`.
fn range_proof_vector(n: u32) -> (freenet_prolly::proof::Proof, Cid, freenet_prolly::range::Range) {
    use freenet_prolly::range::Range;
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
    let r = Range {
        lo: core::ops::Bound::Included(keys[0].clone()),
        max_entries: 32,
        ..Range::default()
    };
    let p = freenet_prolly::proof::prove_range(&store, &root, &r).unwrap();
    (p, root, r)
}

#[no_mangle]
pub extern "C" fn range_proof_hash(n: u32) -> *const u8 {
    static mut OUT: [u8; 32] = [0; 32];
    let (p, _, _) = range_proof_vector(n);
    unsafe {
        OUT = *blake3::hash(&p.encode()).as_bytes();
        &raw const OUT as *const u8
    }
}

#[no_mangle]
pub extern "C" fn range_proof_shape(n: u32) -> u64 {
    let (p, _, _) = range_proof_vector(n);
    ((p.nodes.len() as u64) << 32) | p.encode().len() as u64
}

/// 1 if the page this target proved verifies here and holds 32 entries.
#[no_mangle]
pub extern "C" fn range_proof_verify(n: u32) -> i32 {
    use freenet_prolly::proof::{verify_range_bytes, Proof};
    let (p, root, r) = range_proof_vector(n);
    let bytes = p.encode();
    if Proof::decode(&bytes).is_err() {
        return 0;
    }
    match verify_range_bytes(&root, &r, &bytes) {
        Ok(page) if page.entries.len() == 32 => 1,
        _ => 0,
    }
}

/// 1 if the EMPTY final page of a reverse listing verifies here, at the wire
/// door, and if blocks attached to that question are refused.
///
/// The page a light client sees when it finishes reading a feed. It was
/// refused on this path while passing on the other one, so it is checked on
/// the target and through the bytes.
#[no_mangle]
pub extern "C" fn empty_final_page_ok(n: u32) -> i32 {
    use freenet_prolly::proof::{prove_range, verify_range_bytes, Proof};
    use freenet_prolly::range::Range;
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
    // Reverse, resumed at the lower bound: the bounds cannot hold a key.
    let q = Range {
        lo: core::ops::Bound::Included(keys[10].clone()),
        hi: core::ops::Bound::Included(keys[50].clone()),
        reverse: true,
        after: Some(keys[10].clone()),
        max_entries: 8,
        ..Range::default()
    };
    let Ok(p) = prove_range(&store, &root, &q) else {
        return 0;
    };
    if !p.nodes.is_empty() {
        return 0;
    }
    match verify_range_bytes(&root, &q, &p.encode()) {
        Ok(page) if page.entries.is_empty() && page.next.is_none() => {}
        _ => return 0,
    }
    // And a non-empty proof for that question is refused.
    let Ok(real) = prove_range(
        &store,
        &root,
        &Range {
            after: None,
            ..q.clone()
        },
    ) else {
        return 0;
    };
    if verify_range_bytes(&root, &q, &real.encode()).is_ok() {
        return 0;
    }
    // A zero-node proof still cannot answer a question with entries in it.
    let nonempty = Range {
        after: None,
        ..q.clone()
    };
    if verify_range_bytes(&root, &nonempty, &Proof::default().encode()).is_ok() {
        return 0;
    }
    1
}

// ------------------------------------------------------------- parity ------
//
// The parity code, recomputed HERE rather than shared with the native test:
// the two meet only in `tests/vectors.txt`, which is what makes the file a
// check of the target and not of a helper both sides call.

/// Members of unequal length, each a plausible block state (`kind ‖ body`).
/// Deliberately the same construction as the native side — a different one
/// would prove nothing about the target.
fn parity_members(k: usize) -> Vec<Vec<u8>> {
    (0..k)
        .map(|i| {
            let len = 1 + i * i * 8 + i * 8;
            let mut s = Vec::with_capacity(1 + len);
            s.push(if i % 2 == 0 {
                freenet_prolly::kind::RAW
            } else {
                freenet_prolly::kind::TREE_NODE
            });
            s.extend((0..len).map(|b| (b as u8).wrapping_mul(i as u8 + 3)));
            s
        })
        .collect()
}

/// The three parity ids of the frozen group, concatenated: 96 bytes.
#[no_mangle]
pub extern "C" fn parity_ids(k: u32) -> *const u8 {
    use freenet_prolly::parity::encode_group;
    let states = parity_members(k as usize);
    let parity = encode_group(&states).expect("a codeable group");
    static mut OUT: [u8; 96] = [0; 96];
    unsafe {
        for (i, p) in parity.iter().enumerate() {
            let id = freenet_prolly::block_id(freenet_prolly::kind::PARITY, p);
            OUT[i * 32..(i + 1) * 32].copy_from_slice(&id);
        }
        &raw const OUT as *const u8
    }
}

/// The STORED length of the group's first parity block — a function of its own
/// bytes, since parity is trimmed. Never the group's width.
#[no_mangle]
pub extern "C" fn parity_len(k: u32) -> u32 {
    use freenet_prolly::parity::encode_group;
    encode_group(&parity_members(k as usize)).expect("codeable")[0].len() as u32
}

/// Every way to lose three of the `k + 3`, rebuilt, digested — the claim
/// "anyone can repair without a key" has to hold on THIS target too, not only
/// on the one the vectors were generated on.
#[no_mangle]
pub extern "C" fn parity_repair_digest(k: u32) -> *const u8 {
    use freenet_prolly::parity::{encode_group, repair_group, symbol};
    use freenet_prolly::rs::PARITY;
    let k = k as usize;
    let states = parity_members(k);
    let parity = encode_group(&states).expect("a codeable group");
    let all: Vec<Vec<u8>> = states
        .iter()
        .map(|s| symbol(s))
        .chain(parity.iter().cloned())
        .collect();
    let n = k + PARITY;
    let mut h = blake3::Hasher::new();
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                let have: Vec<Option<Vec<u8>>> = (0..n)
                    .map(|j| (j != a && j != b && j != c).then(|| all[j].clone()))
                    .collect();
                let got = repair_group(k, &have).expect("k of k+3 present");
                // If a rebuild differs here, the digest differs and the driver
                // says so — but assert too, so the failure names the case.
                assert!(got == states, "repair differs on wasm32");
                for s in &got {
                    h.update(s);
                }
            }
        }
    }
    static mut OUT: [u8; 32] = [0; 32];
    unsafe {
        OUT = *h.finalize().as_bytes();
        &raw const OUT as *const u8
    }
}
