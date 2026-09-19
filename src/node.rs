//! Tree node format `PT01`: one node is one Block, read in place.
//!
//! ```text
//! header (26 B)
//!   magic   "PT01"      4
//!   level   u8          0 = leaf
//!   flags   u8          reserved, must be 0
//!   count   u16         entries
//!   agg     count:u64 ‖ bytes:u64     this subtree
//!   pcount  u16         parity cids (branch only)
//! offs   [u16; count]   offset of each entry from the start of the node
//! keys4  [u32; count]   first 4 key bytes, big-endian, zero-padded
//! entries, contiguous, in key order
//!   leaf    klen:u16 ‖ vkind:u8 ‖ vlen:u32 ‖ key ‖ val
//!             vkind 0 = inline bytes (vlen = their length)
//!             vkind 1 = reference: val is cid(32); vlen = referenced length
//!   branch  klen:u16 ‖ child:cid(32) ‖ child_agg(16) ‖ key      key = child's min key
//! parity [cid; pcount]
//! ```
//! All integers little-endian except `keys4`, which is big-endian so that integer
//! order equals byte order. Nothing is aligned; every read is `from_le_bytes`.
//!
//! [`Node::parse`] accepts exactly the bytes [`NodeBuilder`] can produce: a node
//! that parses is sorted, tiled with no gaps or trailing bytes, and carries an
//! aggregate equal to the fold of its entries.

use crate::Cid;

pub const MAGIC: &[u8; 4] = b"PT01";
/// Hard cap on an encoded node. The chunker clamps well below this.
pub const MAX_NODE: usize = 16 * 1024;
const HEADER: usize = 26;
const LEAF_FIXED: usize = 2 + 1 + 4;
const BRANCH_FIXED: usize = 2 + 32 + 16;
const REF_LEN: usize = 32;

/// Rolled-up statistics of a subtree. Per-type counts need no extra fields:
/// keys are type-prefixed, so a range aggregate yields them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Agg {
    /// Leaf entries in the subtree.
    pub count: u64,
    /// Logical bytes: key length + value length (referenced length for refs).
    pub bytes: u64,
}

impl Agg {
    /// Overflow-checked sum; `None` on overflow.
    pub fn checked_add(self, o: Agg) -> Option<Agg> {
        Some(Agg {
            count: self.count.checked_add(o.count)?,
            bytes: self.bytes.checked_add(o.bytes)?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value<'a> {
    Inline(&'a [u8]),
    /// A value stored in its own block (or a blob manifest).
    Ref {
        cid: Cid,
        len: u32,
    },
}

impl Value<'_> {
    fn logical_len(&self) -> u64 {
        match self {
            Value::Inline(b) => b.len() as u64,
            Value::Ref { len, .. } => *len as u64,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeError {
    TooShort,
    TooLarge,
    BadMagic,
    BadFlags,
    /// A leaf carries parity, or a field is inconsistent with the level.
    BadShape,
    OffsetOutOfRange,
    /// Entries do not tile the entry region exactly.
    BadTiling,
    BadEntry,
    KeysNotSorted,
    BadKeyPrefix,
    AggMismatch,
    Overflow,
    TrailingBytes,
}

fn u16_at(b: &[u8], i: usize) -> usize {
    u16::from_le_bytes([b[i], b[i + 1]]) as usize
}
fn u32_at(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes([b[i], b[i + 1], b[i + 2], b[i + 3]])
}
fn u64_at(b: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(b[i..i + 8].try_into().unwrap())
}
fn cid_at(b: &[u8], i: usize) -> Cid {
    b[i..i + 32].try_into().unwrap()
}

/// First four key bytes as a big-endian integer, zero-padded.
pub fn key4(key: &[u8]) -> u32 {
    let mut p = [0u8; 4];
    let n = key.len().min(4);
    p[..n].copy_from_slice(&key[..n]);
    u32::from_be_bytes(p)
}

/// A validated, borrowed view of an encoded node.
#[derive(Clone, Copy, Debug)]
pub struct Node<'a> {
    bytes: &'a [u8],
    level: u8,
    count: usize,
    pcount: usize,
    agg: Agg,
}

impl<'a> Node<'a> {
    /// Validate `bytes` completely. Never panics on any input.
    pub fn parse(bytes: &'a [u8]) -> Result<Self, NodeError> {
        if bytes.len() < HEADER {
            return Err(NodeError::TooShort);
        }
        if bytes.len() > MAX_NODE {
            return Err(NodeError::TooLarge);
        }
        if &bytes[..4] != MAGIC {
            return Err(NodeError::BadMagic);
        }
        let level = bytes[4];
        if bytes[5] != 0 {
            return Err(NodeError::BadFlags);
        }
        let count = u16_at(bytes, 6);
        let agg = Agg {
            count: u64_at(bytes, 8),
            bytes: u64_at(bytes, 16),
        };
        let pcount = u16_at(bytes, 24);
        if level == 0 && pcount != 0 {
            return Err(NodeError::BadShape);
        }
        // A branch with no children is meaningless; an empty leaf is the empty tree.
        if level > 0 && count == 0 {
            return Err(NodeError::BadShape);
        }
        let entries_start = HEADER + count * 6;
        let parity_len = pcount * REF_LEN;
        if entries_start + parity_len > bytes.len() {
            return Err(NodeError::TooShort);
        }
        let entries_end = bytes.len() - parity_len;

        let node = Node {
            bytes,
            level,
            count,
            pcount,
            agg,
        };
        let mut cursor = entries_start;
        let mut fold = Agg::default();
        let mut prev_key: Option<&[u8]> = None;
        for i in 0..count {
            let off = u16_at(bytes, HEADER + i * 2);
            // Entries must tile: each starts exactly where the previous ended.
            if off != cursor {
                return Err(if off < entries_start || off >= entries_end {
                    NodeError::OffsetOutOfRange
                } else {
                    NodeError::BadTiling
                });
            }
            let fixed = if level == 0 { LEAF_FIXED } else { BRANCH_FIXED };
            if off + fixed > entries_end {
                return Err(NodeError::BadEntry);
            }
            let klen = u16_at(bytes, off);
            let (key_at, end, entry_agg) = if level == 0 {
                let vkind = bytes[off + 2];
                let vlen = u32_at(bytes, off + 3);
                let stored = match vkind {
                    0 => vlen as usize,
                    1 => REF_LEN,
                    _ => return Err(NodeError::BadEntry),
                };
                let key_at = off + LEAF_FIXED;
                let end = key_at
                    .checked_add(klen)
                    .and_then(|e| e.checked_add(stored))
                    .ok_or(NodeError::Overflow)?;
                (
                    key_at,
                    end,
                    Agg {
                        count: 1,
                        bytes: klen as u64 + vlen as u64,
                    },
                )
            } else {
                let key_at = off + BRANCH_FIXED;
                let child_agg = Agg {
                    count: u64_at(bytes, off + 34),
                    bytes: u64_at(bytes, off + 42),
                };
                (key_at, key_at + klen, child_agg)
            };
            if end > entries_end {
                return Err(NodeError::BadEntry);
            }
            let key = &bytes[key_at..key_at + klen];
            if prev_key.is_some_and(|p| p >= key) {
                return Err(NodeError::KeysNotSorted);
            }
            if u32_at_be(bytes, HEADER + count * 2 + i * 4) != key4(key) {
                return Err(NodeError::BadKeyPrefix);
            }
            fold = fold.checked_add(entry_agg).ok_or(NodeError::Overflow)?;
            prev_key = Some(key);
            cursor = end;
        }
        if cursor != entries_end {
            return Err(NodeError::TrailingBytes);
        }
        if fold != agg {
            return Err(NodeError::AggMismatch);
        }
        Ok(node)
    }

    pub fn level(&self) -> u8 {
        self.level
    }
    pub fn is_leaf(&self) -> bool {
        self.level == 0
    }
    pub fn len(&self) -> usize {
        self.count
    }
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }
    pub fn agg(&self) -> Agg {
        self.agg
    }
    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    fn off(&self, i: usize) -> usize {
        u16_at(self.bytes, HEADER + i * 2)
    }

    pub fn key(&self, i: usize) -> &'a [u8] {
        let off = self.off(i);
        let klen = u16_at(self.bytes, off);
        let at = off
            + if self.level == 0 {
                LEAF_FIXED
            } else {
                BRANCH_FIXED
            };
        &self.bytes[at..at + klen]
    }

    /// Value of leaf entry `i`. Panics if this is a branch or `i` is out of range.
    pub fn value(&self, i: usize) -> Value<'a> {
        assert!(self.is_leaf() && i < self.count);
        let off = self.off(i);
        let klen = u16_at(self.bytes, off);
        let vlen = u32_at(self.bytes, off + 3);
        let at = off + LEAF_FIXED + klen;
        match self.bytes[off + 2] {
            0 => Value::Inline(&self.bytes[at..at + vlen as usize]),
            _ => Value::Ref {
                cid: cid_at(self.bytes, at),
                len: vlen,
            },
        }
    }

    /// Child of branch entry `i`. Panics if this is a leaf or `i` is out of range.
    pub fn child(&self, i: usize) -> (Cid, Agg) {
        assert!(!self.is_leaf() && i < self.count);
        let off = self.off(i);
        (
            cid_at(self.bytes, off + 2),
            Agg {
                count: u64_at(self.bytes, off + 34),
                bytes: u64_at(self.bytes, off + 42),
            },
        )
    }

    pub fn parity(&self) -> impl Iterator<Item = Cid> + 'a {
        let start = self.bytes.len() - self.pcount * REF_LEN;
        let b = self.bytes;
        (0..self.pcount).map(move |i| cid_at(b, start + i * REF_LEN))
    }

    /// Binary search: `Ok(i)` if entry `i` has `key`, else `Err(i)` = insertion
    /// point. Compares the inline 4-byte prefixes first, touching the key bytes
    /// only when the prefixes tie.
    pub fn search(&self, key: &[u8]) -> Result<usize, usize> {
        let want = key4(key);
        let table = HEADER + self.count * 2;
        let (mut lo, mut hi) = (0usize, self.count);
        while lo < hi {
            let mid = (lo + hi) / 2;
            let have = u32_at_be(self.bytes, table + mid * 4);
            let ord = have.cmp(&want).then_with(|| self.key(mid).cmp(key));
            match ord {
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
                std::cmp::Ordering::Equal => return Ok(mid),
            }
        }
        Err(lo)
    }
}

fn u32_at_be(b: &[u8], i: usize) -> u32 {
    u32::from_be_bytes([b[i], b[i + 1], b[i + 2], b[i + 3]])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildError {
    /// Keys must be pushed in strictly increasing order.
    NotSorted,
    KeyTooLong,
    ValueTooLong,
    TooManyEntries,
    NodeTooLarge,
    /// A value was pushed to a branch, or a child to a leaf, or parity to a leaf.
    WrongKind,
    Overflow,
}

/// Builds the canonical encoding of a node. Entries must arrive in key order.
pub struct NodeBuilder {
    level: u8,
    offs: Vec<u16>,
    keys4: Vec<u32>,
    entries: Vec<u8>,
    parity: Vec<Cid>,
    agg: Agg,
    last_key: Option<Vec<u8>>,
}

impl NodeBuilder {
    pub fn leaf() -> Self {
        Self::new(0)
    }
    /// `level` must be ≥ 1.
    pub fn branch(level: u8) -> Self {
        assert!(level >= 1);
        Self::new(level)
    }
    fn new(level: u8) -> Self {
        NodeBuilder {
            level,
            offs: Vec::new(),
            keys4: Vec::new(),
            entries: Vec::new(),
            parity: Vec::new(),
            agg: Agg::default(),
            last_key: None,
        }
    }

    pub fn len(&self) -> usize {
        self.offs.len()
    }
    pub fn is_empty(&self) -> bool {
        self.offs.is_empty()
    }
    /// Encoded size if finished now.
    pub fn encoded_len(&self) -> usize {
        HEADER + self.offs.len() * 6 + self.entries.len() + self.parity.len() * REF_LEN
    }

    fn admit(&mut self, key: &[u8], entry_agg: Agg) -> Result<(), BuildError> {
        if key.len() > u16::MAX as usize {
            return Err(BuildError::KeyTooLong);
        }
        if self.last_key.as_deref().is_some_and(|p| p >= key) {
            return Err(BuildError::NotSorted);
        }
        if self.offs.len() >= u16::MAX as usize {
            return Err(BuildError::TooManyEntries);
        }
        self.agg = self
            .agg
            .checked_add(entry_agg)
            .ok_or(BuildError::Overflow)?;
        // Offsets are relative to the entry region for now; fixed up in finish().
        self.offs.push(self.entries.len() as u16);
        self.keys4.push(key4(key));
        self.last_key = Some(key.to_vec());
        Ok(())
    }

    pub fn push(&mut self, key: &[u8], value: Value<'_>) -> Result<(), BuildError> {
        if self.level != 0 {
            return Err(BuildError::WrongKind);
        }
        let vlen: u32 = match value {
            Value::Inline(b) => b.len().try_into().map_err(|_| BuildError::ValueTooLong)?,
            Value::Ref { len, .. } => len,
        };
        let stored = match value {
            Value::Inline(b) => b.len(),
            Value::Ref { .. } => REF_LEN,
        };
        if self.encoded_len() + 6 + LEAF_FIXED + key.len() + stored > MAX_NODE {
            return Err(BuildError::NodeTooLarge);
        }
        self.admit(
            key,
            Agg {
                count: 1,
                bytes: key.len() as u64 + value.logical_len(),
            },
        )?;
        self.entries
            .extend_from_slice(&(key.len() as u16).to_le_bytes());
        self.entries.push(matches!(value, Value::Ref { .. }) as u8);
        self.entries.extend_from_slice(&vlen.to_le_bytes());
        self.entries.extend_from_slice(key);
        match value {
            Value::Inline(b) => self.entries.extend_from_slice(b),
            Value::Ref { cid, .. } => self.entries.extend_from_slice(&cid),
        }
        Ok(())
    }

    pub fn push_child(
        &mut self,
        min_key: &[u8],
        child: Cid,
        child_agg: Agg,
    ) -> Result<(), BuildError> {
        if self.level == 0 {
            return Err(BuildError::WrongKind);
        }
        if self.encoded_len() + 6 + BRANCH_FIXED + min_key.len() > MAX_NODE {
            return Err(BuildError::NodeTooLarge);
        }
        self.admit(min_key, child_agg)?;
        self.entries
            .extend_from_slice(&(min_key.len() as u16).to_le_bytes());
        self.entries.extend_from_slice(&child);
        self.entries
            .extend_from_slice(&child_agg.count.to_le_bytes());
        self.entries
            .extend_from_slice(&child_agg.bytes.to_le_bytes());
        self.entries.extend_from_slice(min_key);
        Ok(())
    }

    pub fn push_parity(&mut self, cid: Cid) -> Result<(), BuildError> {
        if self.level == 0 {
            return Err(BuildError::WrongKind);
        }
        if self.parity.len() >= u16::MAX as usize || self.encoded_len() + REF_LEN > MAX_NODE {
            return Err(BuildError::NodeTooLarge);
        }
        self.parity.push(cid);
        Ok(())
    }

    pub fn finish(self) -> Result<Vec<u8>, BuildError> {
        if self.level > 0 && self.offs.is_empty() {
            return Err(BuildError::WrongKind);
        }
        let n = self.offs.len();
        let base = HEADER + n * 6;
        let mut out = Vec::with_capacity(self.encoded_len());
        out.extend_from_slice(MAGIC);
        out.push(self.level);
        out.push(0);
        out.extend_from_slice(&(n as u16).to_le_bytes());
        out.extend_from_slice(&self.agg.count.to_le_bytes());
        out.extend_from_slice(&self.agg.bytes.to_le_bytes());
        out.extend_from_slice(&(self.parity.len() as u16).to_le_bytes());
        for o in &self.offs {
            let abs = base + *o as usize;
            out.extend_from_slice(
                &u16::try_from(abs)
                    .map_err(|_| BuildError::NodeTooLarge)?
                    .to_le_bytes(),
            );
        }
        for k in &self.keys4 {
            out.extend_from_slice(&k.to_be_bytes());
        }
        out.extend_from_slice(&self.entries);
        for c in &self.parity {
            out.extend_from_slice(c);
        }
        debug_assert!(out.len() <= MAX_NODE);
        Ok(out)
    }
}
