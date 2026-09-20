//! `Probed<B>`: a block source that says what was asked of it.
//!
//! This is the second tier of the architect's cut — boundary middleware — and
//! it is an unusually strong tier for this crate specifically. A prolly tree is
//! a pure function of `(root, args, blocks)`, so its ENTIRE interaction with
//! the world is the block-access sequence. Wrapping the block source is
//! therefore close to total observability, which is why the existing diff gate
//! can assert "reads == differing-block count, exactly".
//!
//! It lives in `tests/`, not in `src/`. The library must not depend on
//! `instrument` at all — a dependency's identity reaches a contract's wasm hash
//! even when nothing calls it (F37), and the contracts depend on prolly. A
//! `#[cfg(feature = "testing")]` module in `src/` would not be enough either:
//! a feature does not bring a dev-dependency into a normal build, so it would
//! simply fail to compile. `tests/` is the honest home.
//!
//! What it does NOT do is replace the work counters in `proof.rs` and
//! `pack.rs`. Those count BLAKE3 passes and bodies parsed INSIDE a verifier; a
//! block-source wrapper sees which blocks were asked for and nothing of that.
//! The padded-proof and padded-pack gates rest on `work::ids() == 0`, and
//! conflating the two would delete them.

// A shared test helper is compiled into EVERY binary that includes it, and no
// single binary uses all of it — the differential wants `into_inner`, the cost
// test does not. That is the normal shape of a `#[path]`-included module, not
// dead code anyone should delete.
#![allow(dead_code)]

use core::cell::RefCell;

use freenet_prolly::{
    store::{Blocks, BlocksMut},
    Cid,
};
use instrument::{
    label::{Kind, Labels},
    vocab::{Dir, Key, SizeClass},
    Entry, Event, Probe, Site,
};

pub const READ: Site = Site::of("prolly::blocks::get");

pub struct Probed<'p, B: Blocks> {
    inner: B,
    probe: &'p dyn Probe,
    /// Block ids are labelled per recording — `block#3` — never written out.
    /// `RefCell` because `Blocks::get` takes `&self`, as it must.
    labels: RefCell<Labels<Cid>>,
}

impl<'p, B: Blocks> Probed<'p, B> {
    pub fn new(inner: B, probe: &'p dyn Probe) -> Self {
        Probed {
            inner,
            probe,
            labels: RefCell::new(Labels::new()),
        }
    }

    /// The wrapped source back, for a test that wants to go on using it.
    pub fn into_inner(self) -> B {
        self.inner
    }
}

impl<B: Blocks> Blocks for Probed<'_, B> {
    fn get(&self, cid: &Cid) -> Option<&[u8]> {
        // The label, never the id. A prefix of a block id is not anonymous:
        // the population is enumerable by anyone holding the tree.
        let label = self.labels.borrow_mut().label(Kind::Block, cid);
        self.probe.event(Event::Edge {
            site: READ,
            dir: Dir::Request,
            id: label,
        });
        let got = self.inner.get(cid);
        self.probe.event(Event::Counter {
            site: READ,
            entry: Entry {
                key: Key::Reads,
                value: 1,
            },
        });
        match got {
            Some(bytes) => {
                // A response edge is what makes OUTSTANDING a subtraction: a
                // miss leaves the request unanswered, which is exactly what a
                // reader wants to see.
                self.probe.event(Event::Edge {
                    site: READ,
                    dir: Dir::Response,
                    id: label,
                });
                self.probe.event(Event::Counter {
                    site: READ,
                    entry: Entry {
                        key: Key::BytesClass,
                        // The CLASS. A node's exact length is a property of the
                        // keys and values inside it.
                        value: SizeClass::of(bytes.len()) as u64,
                    },
                });
            }
            None => {
                self.probe.event(Event::Counter {
                    site: READ,
                    entry: Entry {
                        key: Key::Misses,
                        value: 1,
                    },
                });
            }
        }
        got
    }
}

/// A probed source is still writable, because `apply_into` needs it to be —
/// that is the entry point a real consumer uses, and instrumenting only the
/// read-only path would instrument the path nobody takes.
///
/// The write is counted, not described: `Counter(Attempts)` is one block fed
/// back in. No label is emitted for it, because the id of a block being
/// WRITTEN is one the caller already holds — a label would add a line to every
/// dump and tell a reader nothing.
impl<B: BlocksMut> BlocksMut for Probed<'_, B> {
    fn insert_block(&mut self, cid: Cid, bytes: &[u8]) {
        self.probe.event(Event::Counter {
            site: READ,
            entry: Entry {
                key: Key::Attempts,
                value: 1,
            },
        });
        self.inner.insert_block(cid, bytes);
    }
}
