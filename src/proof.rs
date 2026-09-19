//! Checking one key against a root you trust, without holding the tree.
//!
//! A reader who has a signed head — a root and nothing else — can be handed a
//! proof and decide for itself whether a key is present, what its value is, or
//! that it is absent. No trust in whoever produced the proof: every block in it
//! is checked against the pointer that names it, and the chain of pointers ends
//! at the root the reader already trusted.
//!
//! # A proof is the path, and nothing cleverer
//!
//! A node's id hashes its WHOLE bytes, so nothing smaller than a node can be
//! checked against its parent's pointer. The proof is therefore the node bodies
//! on the root-to-leaf path — five nodes for a million entries.
//!
//! # `verify` is `get`, run over a store that holds only the proof
//!
//! This is the whole design. Build a block source from the proof, keyed the way
//! every block is keyed, and run the library's own reader against it:
//!
//! - a block that is not what its parent says it is cannot be FOUND, because
//!   the store is keyed by `block_id(TREE_NODE, bytes)` and tampering changes
//!   the id;
//! - a child whose level, first key or aggregate disagrees with its parent is
//!   refused by [`load_child`](crate::store::load_child), which the reader
//!   already calls;
//! - a proof missing a node on the path produces `Need`, which is an incomplete
//!   proof, never an answer.
//!
//! So there is no second verifier to drift from the reader. A change to how the
//! tree is read is a change to how proofs are checked, in the same edit.
//!
//! Canonicity is the part `get` cannot supply, and it is enforced here: every
//! block in the proof must have been READ, in the order given, with the root
//! first and no repeats. One proof per (root, key), and anything else is
//! refused rather than quietly accepted.
//!
//! # What a proof CLAIMS
//!
//! Exactly this: **what the library's own `get` returns against this root**.
//! Not "the key is not in any tree" — a statement about one root, and only
//! because that root's bytes commit to everything the answer rests on.
//!
//! A key below the tree's minimum is the clearest case. `get` answers at the
//! root without descending, because the root's recorded first key is already
//! above the key being asked about — so the proof is ONE node, and it is
//! complete. That first key is the writer's commitment like every other field
//! in the node, hashed into the id the reader already trusted, so a one-node
//! proof of absence is as strong as a five-node one. A reader that expected
//! `height` blocks and saw one would be wrong to call it truncated.
//!
//! # What a proof cannot do
//!
//! It authenticates what the writer COMMITTED TO. It cannot upgrade that into
//! agreement with reality: [`verify_aggregate`] returns
//! [`Claimed`](crate::aggregate::Claimed) and there is no way to get a
//! `Verified` out of a proof, because a count over subtrees nobody opened is
//! exactly what a proof cannot check (see [`crate::aggregate`]).

use crate::aggregate::{aggregate, AggError, Claimed};
use crate::node::{Node, Value};
use crate::range::Range;
use crate::read::get;
use crate::store::{Blocks, ReadError};
use crate::{block_id, kind, Cid};
use std::cell::RefCell;

/// The proof format's magic. Bumped if the encoding changes.
pub const MAGIC: &[u8; 4] = b"PP01";

/// The node bodies on the path from a root to one key, root first.
///
/// Optionally the raw bytes of a referenced value, so a proof about a key whose
/// value lives outside the leaf can carry the value too.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Proof {
    /// Root first, exactly the path a read takes.
    pub nodes: Vec<Vec<u8>>,
    /// The bytes behind a `Value::Ref`, if the prover chose to include them.
    pub value: Option<Vec<u8>>,
}

/// What a verified proof says about the key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proven<'a> {
    /// The key is in the tree with this value. A `Ref` means the proof
    /// authenticated the value's id and length but did not carry its bytes —
    /// the type says which, so a caller cannot mistake one for the other.
    Present(Value<'a>),
    /// The key is not in the tree. A statement about THIS root and no other.
    Absent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofError {
    /// Not a proof: wrong magic, truncated, a length that runs off the end.
    Malformed(&'static str),
    /// A block in the proof is not a node.
    NotANode,
    /// The proof does not contain the whole path — the read ran out of blocks.
    /// This is what an absence proof "made" by dropping the last node becomes.
    Incomplete,
    /// A block in the proof was never read: it is not on the path, so the proof
    /// is not the canonical one for this key.
    Extra,
    /// The proof's blocks are not in the order a read visits them, or one is
    /// repeated.
    OutOfOrder,
    /// The first block is not the root being proved against.
    WrongRoot,
    /// A block is not what its parent says it is.
    Mismatch(Cid),
    /// The carried value is not the one the leaf names — or is carried at all
    /// where there is nothing for it to prove, because the leaf holds its value
    /// inline or the key is absent. An unchecked trailer would mean two
    /// different byte strings verifying to the same answer, which is the
    /// canonicity this format is supposed to have.
    BadValue,
    /// The proof is for a different range than the one being verified.
    WrongRange,
}

impl std::fmt::Display for ProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofError::Malformed(w) => write!(f, "not a proof: {w}"),
            ProofError::NotANode => write!(f, "a block in the proof is not a node"),
            ProofError::Incomplete => write!(f, "the proof does not contain the whole path"),
            ProofError::Extra => write!(f, "the proof carries a block that is not on the path"),
            ProofError::OutOfOrder => write!(f, "the proof's blocks are not in read order"),
            ProofError::WrongRoot => write!(f, "the proof does not start at this root"),
            ProofError::Mismatch(_) => write!(f, "a block is not what its parent says it is"),
            ProofError::BadValue => write!(f, "the carried value is not the one the leaf names"),
            ProofError::WrongRange => write!(f, "the proof is for a different range"),
        }
    }
}

impl std::error::Error for ProofError {}

// ---------------------------------------------------------------------------
// encoding
// ---------------------------------------------------------------------------

impl Proof {
    /// `"PP01" ‖ count u16 ‖ (len u32 ‖ bytes)* ‖ value_len u32 ‖ value`.
    ///
    /// `value_len` is `u32::MAX` when no value is carried, so "no value" and
    /// "an empty value" are different encodings rather than the same one.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::from(&MAGIC[..]);
        out.extend_from_slice(&(self.nodes.len() as u16).to_be_bytes());
        for n in &self.nodes {
            out.extend_from_slice(&(n.len() as u32).to_be_bytes());
            out.extend_from_slice(n);
        }
        match &self.value {
            Some(v) => {
                out.extend_from_slice(&(v.len() as u32).to_be_bytes());
                out.extend_from_slice(v);
            }
            None => out.extend_from_slice(&u32::MAX.to_be_bytes()),
        }
        out
    }

    /// Read a proof from bytes a stranger sent. Every length is checked against
    /// what is left before it is used.
    pub fn decode(bytes: &[u8]) -> Result<Proof, ProofError> {
        let mut r = Reader { b: bytes, at: 0 };
        if r.take(4)? != MAGIC {
            return Err(ProofError::Malformed("magic"));
        }
        let count = u16::from_be_bytes(r.take(2)?.try_into().expect("2 bytes"));
        let mut nodes = Vec::new();
        for _ in 0..count {
            let len = u32::from_be_bytes(r.take(4)?.try_into().expect("4 bytes"));
            nodes.push(r.take(len as usize)?.to_vec());
        }
        let vlen = u32::from_be_bytes(r.take(4)?.try_into().expect("4 bytes"));
        let value = if vlen == u32::MAX {
            None
        } else {
            Some(r.take(vlen as usize)?.to_vec())
        };
        if r.at != bytes.len() {
            return Err(ProofError::Malformed("trailing bytes"));
        }
        Ok(Proof { nodes, value })
    }

    /// What this proof costs to send.
    pub fn bytes(&self) -> usize {
        self.encode().len()
    }
}

struct Reader<'a> {
    b: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], ProofError> {
        let end = self
            .at
            .checked_add(n)
            .ok_or(ProofError::Malformed("length"))?;
        if end > self.b.len() {
            return Err(ProofError::Malformed("truncated"));
        }
        let out = &self.b[self.at..end];
        self.at = end;
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// proving
// ---------------------------------------------------------------------------

/// The blocks a read touched, in the order it touched them.
struct Recording<'a, B: Blocks> {
    inner: &'a B,
    read: RefCell<Vec<(Cid, Vec<u8>)>>,
}

impl<B: Blocks> Blocks for Recording<'_, B> {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        let got = self.inner.get(cid);
        if let Some(b) = got {
            let mut r = self.read.borrow_mut();
            if !r.iter().any(|(c, _)| c == cid) {
                r.push((*cid, b.to_vec()));
            }
        }
        got
    }
}

/// A proof that `key` is present with its value, or absent, under `root`.
///
/// The path is whatever the reader actually reads — recorded, not
/// reconstructed, so a proof cannot disagree with the read it is meant to
/// stand for.
pub fn prove<B: Blocks>(blocks: &B, root: &Cid, key: &[u8]) -> Result<Proof, ReadError> {
    let rec = Recording {
        inner: blocks,
        read: RefCell::default(),
    };
    get(&rec, root, key)?;
    let nodes = rec.read.into_inner().into_iter().map(|(_, b)| b).collect();
    Ok(Proof { nodes, value: None })
}

/// The same, carrying the bytes of a referenced value when there is one.
pub fn prove_with_value<B: Blocks>(blocks: &B, root: &Cid, key: &[u8]) -> Result<Proof, ReadError> {
    let mut p = prove(blocks, root, key)?;
    if let Some(Value::Ref { cid, .. }) = get(blocks, root, key)? {
        let bytes = blocks.get(&cid).ok_or(ReadError::Need(vec![cid]))?;
        p.value = Some(bytes.to_vec());
    }
    Ok(p)
}

/// A proof of what `aggregate` answers for `range` under `root`.
///
/// Canonical per (root, range): the blocks the count reads depend on the range,
/// so a proof is about both.
pub fn prove_aggregate<B: Blocks>(
    blocks: &B,
    root: &Cid,
    range: &Range,
) -> Result<Proof, AggError> {
    let rec = Recording {
        inner: blocks,
        read: RefCell::default(),
    };
    aggregate(&rec, root, range)?;
    let nodes = rec.read.into_inner().into_iter().map(|(_, b)| b).collect();
    Ok(Proof { nodes, value: None })
}

// ---------------------------------------------------------------------------
// verifying
// ---------------------------------------------------------------------------

/// A store holding exactly the proof's blocks, keyed the way every block is
/// keyed, recording which ones were asked for.
struct ProofStore<'a> {
    blocks: Vec<(Cid, &'a [u8])>,
    read: RefCell<Vec<Cid>>,
}

impl<'a> ProofStore<'a> {
    fn new(p: &'a Proof) -> Result<Self, ProofError> {
        let mut blocks = Vec::with_capacity(p.nodes.len());
        for n in &p.nodes {
            // Parsed here so a block that is not a node is refused as such,
            // rather than reaching the reader as a missing block.
            Node::parse(n).map_err(|_| ProofError::NotANode)?;
            let id = block_id(kind::TREE_NODE, n);
            if blocks.iter().any(|(c, _)| *c == id) {
                return Err(ProofError::OutOfOrder);
            }
            blocks.push((id, n.as_slice()));
        }
        Ok(ProofStore {
            blocks,
            read: RefCell::default(),
        })
    }

    /// Canonicity: every block was read, in the order given.
    fn check_canonical(&self) -> Result<(), ProofError> {
        let read = self.read.borrow();
        if read.len() != self.blocks.len() {
            return Err(ProofError::Extra);
        }
        for (i, (id, _)) in self.blocks.iter().enumerate() {
            if read[i] != *id {
                return Err(ProofError::OutOfOrder);
            }
        }
        Ok(())
    }
}

impl<'a> Blocks for ProofStore<'a> {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        let found = self.blocks.iter().find(|(c, _)| c == cid).map(|(_, b)| *b);
        if found.is_some() {
            let mut r = self.read.borrow_mut();
            if !r.contains(cid) {
                r.push(*cid);
            }
        }
        found
    }
}

fn read_err(e: ReadError) -> ProofError {
    match e {
        ReadError::Need(_) => ProofError::Incomplete,
        ReadError::Mismatch(c) => ProofError::Mismatch(c),
        ReadError::Corrupt(..) => ProofError::NotANode,
    }
}

/// Decide, from `proof` alone, whether `key` is under `root`.
///
/// Total: every input a stranger can send is an `Err` or an answer, never a
/// panic. An incomplete proof is [`ProofError::Incomplete`] and never
/// [`Proven::Absent`] — dropping the last node of a path does not turn a
/// present key into an absent one.
pub fn verify<'a>(root: &Cid, key: &[u8], proof: &'a Proof) -> Result<Proven<'a>, ProofError> {
    let store = ProofStore::new(proof)?;
    // The root must be the first block: a proof is read from the root down, and
    // a proof that merely CONTAINS the root somewhere is not the canonical one.
    match store.blocks.first() {
        Some((id, _)) if id == root => {}
        _ => return Err(ProofError::WrongRoot),
    }
    let found = get(&store, root, key).map_err(read_err)?;
    store.check_canonical()?;

    // The ANSWER is the reader's; the returned value has to borrow the proof
    // rather than the store that was just dropped, so it is read again from the
    // last block of the path — and the two are compared, so a difference
    // between them is an error rather than a silent divergence.
    let last = proof.nodes.last().ok_or(ProofError::Incomplete)?;
    let node = Node::parse(last).map_err(|_| ProofError::NotANode)?;
    let again = node
        .is_leaf()
        .then(|| node.search(key).ok().map(|i| node.value(i)))
        .flatten();
    if again != found {
        return Err(ProofError::OutOfOrder);
    }

    // A trailer is only meaningful for a value that lives in its own block.
    // Anywhere else it is unchecked bytes riding along, so it is refused.
    if proof.value.is_some() && !matches!(again, Some(Value::Ref { .. })) {
        return Err(ProofError::BadValue);
    }
    Ok(match again {
        None => Proven::Absent,
        Some(Value::Inline(b)) => Proven::Present(Value::Inline(b)),
        Some(Value::Ref { cid, len }) => match &proof.value {
            None => Proven::Present(Value::Ref { cid, len }),
            Some(v) => {
                // The carried bytes must be the value the leaf names — both the
                // id and the length, since the leaf records both.
                if v.len() != len as usize || block_id(kind::RAW, v) != cid {
                    return Err(ProofError::BadValue);
                }
                Proven::Present(Value::Inline(v))
            }
        },
    })
}

/// Decide, from `proof` alone, what `root` claims about `range`.
///
/// Returns [`Claimed`], never `Verified`: **a proof authenticates what the
/// writer committed to, it cannot upgrade a claim.** The count rests on
/// subtrees nobody opened; a proof shows the writer said so, and no proof can
/// show it is true.
pub fn verify_aggregate(root: &Cid, range: &Range, proof: &Proof) -> Result<Claimed, ProofError> {
    let store = ProofStore::new(proof)?;
    match store.blocks.first() {
        Some((id, _)) if id == root => {}
        _ => return Err(ProofError::WrongRoot),
    }
    let got = aggregate(&store, root, range).map_err(|e| match e {
        AggError::Read(r) => read_err(r),
        AggError::NotWholeRange(_) => ProofError::WrongRange,
    })?;
    store.check_canonical()?;
    Ok(got)
}
