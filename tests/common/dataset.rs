//! Deterministic reference dataset, shared by the native tests and the wasm32
//! check so both hash exactly the same entries.

pub fn rng(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed | 1;
    move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    }
}

/// `n` entries shaped like a real identity tree — records (~40 B keys, 60–400 B
/// values), edges (~150 B keys, tiny values), index terms — sorted, keys unique.
pub fn dataset(seed: u64, n: usize) -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut r = rng(seed);
    let domains: [&[u8]; 4] = [b"post", b"comment", b"profile", b"inventory-item"];
    let rels: [&[u8]; 3] = [b"follows", b"likes", b"member-of"];
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let kind = r() % 10;
        let mut key = Vec::new();
        let vlen;
        if kind < 6 {
            key.extend_from_slice(b"d/");
            key.extend_from_slice(domains[(r() % 4) as usize]);
            key.push(b'/');
            key.extend_from_slice(&r().to_be_bytes());
            key.extend_from_slice(&r().to_be_bytes());
            vlen = 60 + (r() % 341) as usize;
        } else if kind < 9 {
            key.extend_from_slice(b"e/");
            key.extend_from_slice(rels[(r() % 3) as usize]);
            key.push(b'/');
            for _ in 0..(16 + r() % 6) {
                key.extend_from_slice(&r().to_be_bytes());
            }
            vlen = (r() % 17) as usize;
        } else {
            key.extend_from_slice(b"i/post/title/");
            for _ in 0..(1 + r() % 8) {
                key.extend_from_slice(&r().to_be_bytes());
            }
            vlen = 16;
        }
        let mut val = vec![0u8; vlen];
        for b in val.iter_mut() {
            *b = r() as u8;
        }
        out.push((key, val));
    }
    out.sort();
    out.dedup_by(|a, b| a.0 == b.0);
    out
}
