//! Prolly tree: a sorted `key -> value` map whose shape and root hash are a pure
//! function of its contents. See ARCHITECTURE.md §5. Built in phase 1.

pub mod boundary;
pub mod build;
pub mod node;

/// Content id of a block: BLAKE3-256 of its bytes.
pub type Cid = [u8; 32];

/// The content id of `bytes`.
pub fn cid(bytes: &[u8]) -> Cid {
    *blake3::hash(bytes).as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cid_is_deterministic_and_content_bound() {
        assert_eq!(cid(b"a"), cid(b"a"));
        assert_ne!(cid(b"a"), cid(b"b"));
    }
}
