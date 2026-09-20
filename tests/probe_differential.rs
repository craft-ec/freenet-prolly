//! Does recording change the answer?
//!
//! The one question that decides whether a probe may be left switched on
//! everywhere. It is asked the cheap way the architect described: run the work
//! the existing sweeps already do, three ways, and require byte-identical
//! results.
//!
//!   bare       the block source, unwrapped
//!   no-op      wrapped, recording into `NoProbe`
//!   recorder   wrapped, recording into a real ring
//!
//! Three arms rather than two on purpose. Comparing only no-op against
//! recorder would pass if the WRAPPER itself changed the answer, since both
//! arms are wrapped. The bare arm is what excludes that.

#[path = "common/dataset.rs"]
mod dataset_mod;
#[path = "common/probed.rs"]
mod probed_mod;

use dataset_mod::{dataset, rng};
use probed_mod::Probed;

use freenet_prolly::{
    apply::{apply_into, Edit},
    build::init,
    diff::diff,
    node::Value,
    range::{range, Range},
    store::{Blocks, BlocksMut, MemBlocks},
    Cid,
};
use instrument::{vocab::Key, NoProbe, Record, Recorder};

/// What one sweep produced, as bytes a comparison can be exact about.
#[derive(PartialEq, Debug)]
struct Answer {
    root: Cid,
    replaced: usize,
    page_entries: Vec<(Vec<u8>, Vec<u8>)>,
    page_next: Option<Vec<u8>>,
    diff_changes: usize,
    diff_need: Vec<Cid>,
}

/// Build, apply, range and diff — the three entry points the sweeps exercise.
fn sweep<B: BlocksMut>(blocks: &mut B, root: &Cid, edits: &[(Vec<u8>, Edit)]) -> Answer {
    // `apply_into`, not `apply`: applying to an empty root reads blocks it has
    // just emitted, so a source that is not fed them answers `Need` — which is
    // the loop `apply_into` exists to save every consumer from writing.
    let applied = apply_into(blocks, root, edits).expect("apply_into");
    let all = &*blocks;
    let r = Range {
        max_entries: 64,
        ..Range::default()
    };
    let page = range(all, &applied.root, &r).expect("range");
    let d = diff(all, root, &applied.root, &r, None);

    Answer {
        root: applied.root,
        replaced: applied.replaced.len(),
        page_entries: page
            .entries
            .iter()
            // Both shapes, byte for byte: an Inline compared only by length
            // would pass over different bytes of the same size.
            .map(|(k, v)| {
                (
                    k.clone(),
                    match v {
                        Value::Inline(b) => b.to_vec(),
                        Value::Ref { cid, len } => {
                            let mut out = cid.to_vec();
                            out.extend_from_slice(&len.to_le_bytes());
                            out
                        }
                    },
                )
            })
            .collect(),
        page_next: page.next,
        diff_changes: d.as_ref().map(|p| p.changes.len()).unwrap_or(0),
        diff_need: d.map(|p| p.need).unwrap_or_default(),
    }
}

fn edits_from(seed: u64, n: usize) -> Vec<(Vec<u8>, Edit)> {
    dataset(seed, n)
        .into_iter()
        .map(|(k, v)| (k, Edit::Put(v)))
        .collect()
}

#[test]
fn recording_does_not_change_the_answer() {
    let mut seeds = rng(4242);
    let mut compared = 0usize;
    for _ in 0..12 {
        let seed = seeds();
        let n = 40 + (seed as usize % 400);
        let edits = edits_from(seed, n);
        // `init`, not `empty_root`: the empty leaf has to be IN the store, or
        // the first apply answers `Need` for a block nobody put there.
        let mut bare_store = MemBlocks::default();
        let root = init(&mut bare_store);

        // 1. bare
        let bare = sweep(&mut bare_store, &root, &edits);

        // 2. wrapped, recording nowhere
        let noop = NoProbe;
        let mut a_store = Probed::new(MemBlocks::default(), &noop);
        assert_eq!(init(&mut a_store), root);
        let a = sweep(&mut a_store, &root, &edits);

        // 3. wrapped, recording into a real ring
        let rec = Recorder::with_capacity(8192);
        let mut b_store = Probed::new(MemBlocks::default(), &rec);
        assert_eq!(init(&mut b_store), root);
        let b = sweep(&mut b_store, &root, &edits);

        assert_eq!(bare, a, "the WRAPPER changed the answer (seed {seed})");
        assert_eq!(a, b, "RECORDING changed the answer (seed {seed})");

        // And the recording is not empty, or the comparison above is between
        // two arms that both recorded nothing.
        let r = rec.recording();
        assert!(
            r.total(Key::Reads) > 0,
            "seed {seed}: the recorder saw no reads, so this sweep proves nothing"
        );
        compared += 1;
    }
    assert_eq!(compared, 12, "every sweep was compared");
}

/// The read set IS the behavioural trace, so the probe should see exactly the
/// blocks the work asked for — no more, no fewer.
#[test]
fn the_probe_sees_every_read_and_only_the_reads() {
    let edits = edits_from(9, 300);
    let mut all = MemBlocks::default();
    let root = init(&mut all);
    let applied = apply_into(&mut all, &root, &edits).expect("apply_into");

    // Count reads independently of the probe, by wrapping a counter around the
    // same source — so the assertion is a differential and not the probe
    // agreeing with itself.
    struct Counting<'a>(&'a MemBlocks, std::cell::Cell<u64>);
    impl Blocks for Counting<'_> {
        fn get(&self, cid: &Cid) -> Option<&[u8]> {
            self.1.set(self.1.get() + 1);
            self.0.get(cid)
        }
    }

    let rec = Recorder::with_capacity(16384);
    let r = Range {
        max_entries: 1000,
        ..Range::default()
    };
    let counted = Counting(&all, std::cell::Cell::new(0));
    let probed = Probed::new(Counting(&all, std::cell::Cell::new(0)), &rec);

    let p1 = range(&counted, &applied.root, &r);
    let p2 = range(&probed, &applied.root, &r);
    assert_eq!(p1.is_ok(), p2.is_ok());

    let by_probe = rec.recording().total(Key::Reads);
    let by_counter = probed.into_inner().1.get();
    assert_eq!(
        by_probe, by_counter,
        "the probe counted {by_probe} reads where the source saw {by_counter}"
    );
    assert!(by_probe > 0, "a sweep that read nothing proves nothing");
}

/// A miss leaves its request unanswered, which is what makes OUTSTANDING mean
/// something for a block source.
#[test]
fn a_missing_block_leaves_an_outstanding_request() {
    let rec = Recorder::with_capacity(256);
    let empty = MemBlocks::default();
    let probed = Probed::new(empty, &rec);
    let absent: Cid = [9u8; 32];
    assert!(probed.get(&absent).is_none());

    let r = rec.recording();
    assert_eq!(r.outstanding().len(), 1, "the request has no response");
    assert_eq!(r.total(Key::Misses), 1);
    assert_eq!(r.total(Key::Reads), 1);

    // The control: a block that IS there answers, and leaves nothing
    // outstanding — so the assertion above is about the miss.
    let mut held = MemBlocks::default();
    let bytes = b"a block".to_vec();
    let cid = freenet_prolly::block_id(freenet_prolly::kind::RAW, &bytes);
    held.insert(cid, &bytes);
    let rec2 = Recorder::with_capacity(256);
    let p2 = Probed::new(held, &rec2);
    assert!(p2.get(&cid).is_some());
    assert_eq!(rec2.recording().outstanding().len(), 0);
}
