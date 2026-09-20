//! What does recording COST?
//!
//! Measured, not asserted. A threshold here would be a number about this
//! machine on this afternoon, and it would either fail on someone else's
//! laptop or be so loose it says nothing. The run prints its numbers and the
//! person reading them decides.
//!
//!   cargo test --test probe_cost -- --nocapture
//!
//! Two things the architect's review asked for specifically:
//!
//! - **The LOOP is measured, not the call.** A `&dyn Probe` call inside an
//!   innermost loop can cost the inlining of the loop body, which is a larger
//!   effect than the call itself and invisible if you time the call.
//! - **Interleaved**, because a machine that gets busier halfway through would
//!   otherwise hand the second arm all the noise.

#[path = "common/dataset.rs"]
mod dataset_mod;
#[path = "common/probed.rs"]
mod probed_mod;

use std::time::{Duration, Instant};

use dataset_mod::dataset;
use probed_mod::Probed;

use freenet_prolly::{
    apply::{apply_into, Edit},
    build::init,
    range::{range, Range},
    store::{Blocks, MemBlocks},
    Cid,
};
use instrument::{vocab::Key, NoProbe, Record, Recorder};

const ROUNDS: usize = 9;
const ENTRIES: usize = 2_000;

fn edits(n: usize) -> Vec<(Vec<u8>, Edit)> {
    dataset(11, n)
        .into_iter()
        .map(|(k, v)| (k, Edit::Put(v)))
        .collect()
}

/// One unit of work: a full range scan over a built tree.
///
/// The scan is the INNERMOST loop that touches the block source — `get` per
/// node — which is exactly where a dynamic call could cost the loop its
/// inlining. Timing `get` itself would miss that.
fn scan<B: Blocks>(blocks: &B, root: &Cid) -> usize {
    let r = Range {
        max_entries: usize::MAX,
        max_bytes: usize::MAX,
        ..Range::default()
    };
    range(blocks, root, &r).expect("range").entries.len()
}

fn median(mut v: Vec<Duration>) -> Duration {
    v.sort();
    v[v.len() / 2]
}

#[test]
fn what_recording_costs() {
    let mut store = MemBlocks::default();
    let root = init(&mut store);
    let applied = apply_into(&mut store, &root, &edits(ENTRIES)).expect("apply_into");
    let root = applied.root;

    let noop = NoProbe;
    let rec = Recorder::with_capacity(1 << 20);

    let mut bare = Vec::new();
    let mut with_noop = Vec::new();
    let mut with_rec = Vec::new();
    let mut entries = 0usize;

    // Interleaved: one round of each, ROUNDS times.
    for _ in 0..ROUNDS {
        let t = Instant::now();
        entries = scan(&store, &root);
        bare.push(t.elapsed());

        let probed = Probed::new(&store, &noop);
        let t = Instant::now();
        let n = scan(&probed, &root);
        with_noop.push(t.elapsed());
        assert_eq!(n, entries);

        let probed = Probed::new(&store, &rec);
        let t = Instant::now();
        let n = scan(&probed, &root);
        with_rec.push(t.elapsed());
        assert_eq!(n, entries);
    }

    let b = median(bare);
    let np = median(with_noop);
    let rc = median(with_rec);
    let events = rec.recording().offered();
    let reads = rec.recording().total(Key::Reads);

    println!();
    println!("probe cost — a full scan of a {ENTRIES}-entry tree, {entries} entries read");
    println!("  medians over {ROUNDS} interleaved rounds; the LOOP is timed, not the call");
    println!(
        "  {:<28} {:>10.3} ms",
        "bare block source",
        b.as_secs_f64() * 1e3
    );
    println!(
        "  {:<28} {:>10.3} ms   {:+.1} % vs bare",
        "wrapped, NoProbe",
        np.as_secs_f64() * 1e3,
        (np.as_secs_f64() / b.as_secs_f64() - 1.0) * 100.0
    );
    println!(
        "  {:<28} {:>10.3} ms   {:+.1} % vs bare",
        "wrapped, recording",
        rc.as_secs_f64() * 1e3,
        (rc.as_secs_f64() / b.as_secs_f64() - 1.0) * 100.0
    );
    println!(
        "  {} events recorded over {ROUNDS} rounds ({reads} reads), \
         so the per-event cost is about {:.0} ns",
        events,
        if events > 0 {
            (rc.as_secs_f64() - np.as_secs_f64()) * 1e9 * ROUNDS as f64 / events as f64
        } else {
            0.0
        }
    );
    println!("  NOTE: one machine, one afternoon. Nothing here is a threshold.");

    // The only assertions are that the measurement HAPPENED. A cost test that
    // silently measured an empty scan would print small numbers and mean
    // nothing.
    assert!(entries > 0, "the scan read no entries");
    assert!(events > 0, "the recorder saw no events");
    assert!(
        b > Duration::ZERO && rc > Duration::ZERO,
        "the clock did not move"
    );
}
