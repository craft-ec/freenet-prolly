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
//! Canonicity is the part `get` cannot supply, and it is enforced here: the
//! blocks given are exactly the blocks read, with no repeats, in the format's
//! own order — **level descending, then first key ascending**, which for a path
//! is top down. Stated as a rule rather than as "whatever the reader visited",
//! so that reordering a traversal is not a silent format break and a verifier
//! written from this page in another language agrees with this one.
//!
//! That makes it **one proof per (root, PATH)**, not per (root, key): the key
//! is not in the proof and is not believed if it were. The verifier computes
//! the answer for the key IT asks about, from blocks authenticated against the
//! root IT trusts. So the same bytes are the canonical proof for every key
//! whose read takes that path — a feature, since one proof answers a key and
//! its neighbours.
//!
//! # A proof is bytes from a stranger
//!
//! So the SHAPE is checked before the bytes are: one parse and one hash decide
//! whether the rest is worth touching. The count is a `u16` and nothing in the
//! proof ties it to the tree, so a 65,000-node proof would otherwise be parsed
//! and hashed in full before being refused — a second of work on a phone, from
//! a message anyone can send. The root settles it: its level bounds how many
//! blocks a path against it can need.
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
//! And a writer cannot profit by lying there. A parent key that misstates its
//! child's first key builds a tree `load_child` refuses for every key in that
//! child: the lie buys a consistent "absent" and breaks the writer's own tree
//! to get it.
//!
//! # What is out of scope, and must be named
//!
//! **The chain above the root.** A proof is checked against a root, and is only
//! as fresh as the root it is checked against. Where that root came from —
//! device head Register ← identity entry ← directory ← signed global head — is
//! somebody else's problem and a real one; nothing here says a root is current.
//!
//! **Sealed domains cannot be proven to outsiders at all.** Node bodies are
//! ciphertext there, so a reader who cannot decrypt them cannot check a path,
//! and no proof in this module changes that.
//!
//! # What a proof cannot do
//!
//! It authenticates what the writer COMMITTED TO. It cannot upgrade that into
//! agreement with reality: [`verify_aggregate`] returns
//! [`Claimed`](crate::aggregate::Claimed) and there is no way to get a
//! `Verified` out of a proof, because a count over subtrees nobody opened is
//! exactly what a proof cannot check (see [`crate::aggregate`]).

use crate::aggregate::{aggregate, AggError, Claimed};
use crate::node::{Node, Value, MAX_NODE, MAX_VALUE};
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
    ///
    /// Carrying it or not gives two different CLAIMS, not two spellings of
    /// one: without it the proof says "the value with this id and length",
    /// with it "these bytes". Both are canonical for the claim they make, and
    /// the returned [`Proven`] says which was proved.
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
    /// The proof claims more blocks than a proof against this root could
    /// possibly need, or a block larger than a block can be. Refused before
    /// the work of parsing and hashing them is done — see [`verify`].
    TooLarge(&'static str),
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
            ProofError::TooLarge(w) => write!(f, "the proof is impossibly large: {w}"),
        }
    }
}

impl std::error::Error for ProofError {}

// ---------------------------------------------------------------------------
// encoding
// ---------------------------------------------------------------------------

impl Proof {
    /// `"PP01" ‖ count u16 ‖ (len u32 ‖ bytes)* ‖ value_len u32 ‖ value`,
    /// little-endian like every other length in this crate.
    ///
    /// `value_len` is `u32::MAX` when no value is carried, so "no value" and
    /// "an empty value" are different encodings rather than the same one.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::from(&MAGIC[..]);
        out.extend_from_slice(&(self.nodes.len() as u16).to_le_bytes());
        for n in &self.nodes {
            out.extend_from_slice(&(n.len() as u32).to_le_bytes());
            out.extend_from_slice(n);
        }
        match &self.value {
            Some(v) => {
                out.extend_from_slice(&(v.len() as u32).to_le_bytes());
                out.extend_from_slice(v);
            }
            None => out.extend_from_slice(&u32::MAX.to_le_bytes()),
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
        let count = u16::from_le_bytes(r.take(2)?.try_into().expect("2 bytes"));
        let mut nodes = Vec::new();
        for _ in 0..count {
            let len = u32::from_le_bytes(r.take(4)?.try_into().expect("4 bytes"));
            // A block cannot be larger than a block. Checked before the bytes
            // are copied, so a lying length costs nothing.
            if len as usize > MAX_NODE {
                return Err(ProofError::TooLarge("a node"));
            }
            nodes.push(r.take(len as usize)?.to_vec());
        }
        let vlen = u32::from_le_bytes(r.take(4)?.try_into().expect("4 bytes"));
        let value = if vlen == u32::MAX {
            None
        } else {
            if vlen as usize > MAX_VALUE {
                return Err(ProofError::TooLarge("a value"));
            }
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
    let mut nodes: Vec<Vec<u8>> = rec.read.into_inner().into_iter().map(|(_, b)| b).collect();
    // Recorded, then SORTED into the format's order — so the bytes of a proof
    // do not depend on the order `aggregate` happens to walk in, and a change
    // to that walk leaves every stored proof byte-identical.
    sort_canonical(&mut nodes);
    Ok(Proof { nodes, value: None })
}

/// The format's order: level descending, then first key ascending.
fn sort_canonical(nodes: &mut [Vec<u8>]) {
    nodes.sort_by_key(|b| {
        let n = Node::parse(b).expect("proving from parsed nodes");
        (std::cmp::Reverse(n.level()), n.key(0))
    });
}

// ---------------------------------------------------------------------------
// verifying
// ---------------------------------------------------------------------------

/// Check the proof's SHAPE before any of its bytes are parsed or hashed.
///
/// A proof is bytes from a stranger, and the count is a `u16` nothing ties to
/// the tree — so a 65,000-node proof would otherwise be parsed and hashed in
/// full before being refused, which on the device that matters (a phone, in
/// wasm) is a denial of service dressed as a proof. The root settles it: parse
/// the first node ONLY, check it is the root the reader trusts, read its level,
/// and refuse anything claiming more blocks than a path against that root could
/// possibly need.
fn shape<'a>(proof: &'a Proof, root: &Cid, per_level: usize) -> Result<Node<'a>, ProofError> {
    let first = proof.nodes.first().ok_or(ProofError::Incomplete)?;
    if block_id(kind::TREE_NODE, first) != *root {
        return Err(ProofError::WrongRoot);
    }
    let node = Node::parse(first).map_err(|_| ProofError::NotANode)?;
    let height = node.level() as usize + 1;
    if proof.nodes.len() > per_level * height + 1 {
        return Err(ProofError::TooLarge("more blocks than the tree is tall"));
    }
    Ok(node)
}

/// Blocks parsed and hashed by [`ProofStore::new`]. The cost a hostile proof
/// can impose, counted so a test can assert on it rather than on a clock.
#[cfg(test)]
pub(crate) static HASHED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

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
            #[cfg(test)]
            HASHED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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

    /// Canonicity, in two parts: the SET is exactly what was read, and the
    /// ORDER is the format's, not the traversal's.
    ///
    /// The order rule is stated normatively — **level descending, then first
    /// key ascending** — rather than "whatever the reader happened to visit".
    /// Tying it to a traversal would mean that reordering that walk turns every
    /// stored proof into `OutOfOrder`, with no test calling it a format break,
    /// and that a verifier written from this doc in another language would
    /// disagree with this one. For a key proof the two coincide: a path visits
    /// one node per level, top down.
    fn check_canonical(&self) -> Result<(), ProofError> {
        // Every block given was used: the set rule. `read` only ever records
        // ids that were found here, so this is also "nothing was read twice
        // and nothing is left over" — one check, not two saying the same thing
        // where only one of them could ever fail.
        let read = self.read.borrow();
        if !self.blocks.iter().all(|(id, _)| read.contains(id)) {
            return Err(ProofError::Extra);
        }
        // And the list is in the format's order: the order rule.
        let key_of = |b: &[u8]| -> Option<(u8, Vec<u8>)> {
            let n = Node::parse(b).ok()?;
            (!n.is_empty()).then(|| (n.level(), n.key(0)))
        };
        let mut last: Option<(u8, Vec<u8>)> = None;
        for (_, b) in &self.blocks {
            let k = key_of(b).ok_or(ProofError::NotANode)?;
            if let Some(prev) = &last {
                // Level descending, then first key ascending.
                let ordered = prev.0 > k.0 || (prev.0 == k.0 && prev.1 < k.1);
                if !ordered {
                    return Err(ProofError::OutOfOrder);
                }
            }
            last = Some(k);
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
    // Shape first: one parse and one hash decide whether the rest is worth
    // touching. A key proof is one node per level.
    shape(proof, root, 1)?;
    let store = ProofStore::new(proof)?;
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
    // An aggregate reads at most the two edge paths, so two per level.
    shape(proof, root, 2)?;
    let store = ProofStore::new(proof)?;
    let got = aggregate(&store, root, range).map_err(|e| match e {
        AggError::Read(r) => read_err(r),
        AggError::NotWholeRange(_) => ProofError::WrongRange,
    })?;
    store.check_canonical()?;
    Ok(got)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::apply::{apply_into, Edit};
    use crate::build::init;
    use crate::node::NodeBuilder;
    use crate::store::MemBlocks;
    use std::sync::atomic::Ordering;

    /// Refusing a hostile proof must cost about what an honest one costs.
    ///
    /// Asserted on BLOCKS HASHED, not on a clock: the number is the work an
    /// attacker can impose, and it is the same number on a phone as here.
    /// Before the shape gate, a 65,003-node proof was parsed and hashed in full
    /// — 3.6 MiB and a second of work — before being refused as `Extra`.
    #[test]
    fn a_hostile_proof_is_refused_for_the_price_of_an_honest_one() {
        let mut blocks = MemBlocks::default();
        let root = init(&mut blocks);
        let edits: Vec<(Vec<u8>, Edit)> = (0..20_000u32)
            .map(|i| {
                (
                    format!("k/{i:08}").into_bytes(),
                    Edit::Put(vec![(i % 251) as u8; 120]),
                )
            })
            .collect();
        let root = apply_into(&mut blocks, &root, &edits).unwrap().root;
        let key = b"k/00010000".to_vec();
        let honest = prove(&blocks, &root, &key).unwrap();
        assert!(matches!(
            verify(&root, &key, &honest).unwrap(),
            Proven::Present(_)
        ));

        HASHED.store(0, Ordering::Relaxed);
        let _ = verify(&root, &key, &honest);
        let honest_work = HASHED.load(Ordering::Relaxed);
        assert_eq!(honest_work, honest.nodes.len());

        // The honest path, then thousands of distinct, individually VALID
        // leaves — every one of which must be parsed and hashed before the old
        // code could notice they were not on the path.
        for n in [1_000usize, 10_000, 65_000] {
            let mut nodes = honest.nodes.clone();
            for i in 0..n {
                let mut b = NodeBuilder::leaf();
                b.push(format!("pad/{i:012}").as_bytes(), Value::Inline(&[0u8; 64]))
                    .unwrap();
                nodes.push(b.finish().unwrap());
            }
            let hostile = Proof { nodes, value: None };
            HASHED.store(0, Ordering::Relaxed);
            let got = verify(&root, &key, &hostile);
            let work = HASHED.load(Ordering::Relaxed);
            assert!(got.is_err(), "{n} pad nodes must be refused");
            assert_eq!(
                work, 0,
                "{n} pad nodes cost {work} blocks hashed; the shape gate should \
                 have refused it after the root"
            );
        }
        println!("honest proof: {honest_work} blocks hashed; 65,000 padded nodes: 0");
    }

    /// The same, through the wire form: a lying length must not be believed.
    #[test]
    fn decode_refuses_impossible_lengths_before_copying() {
        let mut b = Vec::from(&MAGIC[..]);
        b.extend_from_slice(&1u16.to_le_bytes());
        b.extend_from_slice(&(u32::MAX - 1).to_le_bytes()); // a node "larger than the world"
        assert_eq!(Proof::decode(&b), Err(ProofError::TooLarge("a node")));

        let mut b = Vec::from(&MAGIC[..]);
        b.extend_from_slice(&0u16.to_le_bytes());
        b.extend_from_slice(&(u32::MAX - 1).to_le_bytes()); // a value the same
        assert_eq!(Proof::decode(&b), Err(ProofError::TooLarge("a value")));
    }
}
