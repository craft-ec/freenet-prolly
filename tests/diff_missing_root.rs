//! freenet-prolly#51: a root that is not HELD is not an EMPTY tree.
//!
//! `diff` stops on a missing block and returns a PREFIX: every change up to
//! `next` is final, nothing past the first key it could not establish is
//! emitted, and `next` never advances past it. That was true for every block
//! except a root — a missing root was read as an exhausted side, so the other
//! tree came out wholly `Added` (or `Removed`), `next` ran to the end, and the
//! resume returned nothing.
//!
//! THE ARM THAT CAN SEE IT is the WARM one: the new tree held, only the old
//! root evicted — a subscriber's normal state. With the interior cold as well
//! the drain stops on a missing child before emitting anything, so a cold-store
//! test passes on the broken code. Every arm here is asserted to be a prefix of
//! the fully-held diff after EVERY round, not only at the end.

use freenet_prolly::diff::{diff, Change, Resume};
use freenet_prolly::node::Value;
use freenet_prolly::range::Range;
use freenet_prolly::store::{Blocks, MemBlocks};
use freenet_prolly::{build, Cid};
use std::cell::RefCell;
use std::collections::{HashSet, VecDeque};

/// Records which blocks a diff actually opened.
struct Watch<'a> {
    inner: &'a MemBlocks,
    seen: RefCell<HashSet<Cid>>,
}
impl Blocks for Watch<'_> {
    fn get(&self, c: &Cid) -> Option<&[u8]> {
        let r = self.inner.get(c);
        if r.is_some() {
            self.seen.borrow_mut().insert(*c);
        }
        r
    }
}

fn show(c: &Change) -> String {
    match c {
        Change::Added { key, .. } => format!("+{}", String::from_utf8_lossy(key)),
        Change::Removed { key, .. } => format!("-{}", String::from_utf8_lossy(key)),
        Change::Changed { key, .. } => format!("~{}", String::from_utf8_lossy(key)),
    }
}

fn all() -> Range {
    Range {
        max_entries: usize::MAX,
        max_bytes: usize::MAX,
        ..Default::default()
    }
}

/// Which of the blocks a diff opens stay held at the start.
type Keep<'a> = Box<dyn Fn(&Cid) -> bool + 'a>;

/// Two trees of `n` entries: scattered edits, removals and additions.
struct Pair {
    full: MemBlocks,
    a: Cid,
    b: Cid,
    reference: Vec<String>,
    /// Every block a fully-held diff opens.
    opened: Vec<Cid>,
}

fn pair(n: u32) -> Pair {
    let val = |i: u32, g: u8| {
        vec![g.wrapping_add((i % 251) as u8); if i.is_multiple_of(5) { 700 } else { 24 }]
    };
    let a_e: Vec<(Vec<u8>, Vec<u8>)> = (0..n)
        .map(|i| (format!("k/{i:06}").into_bytes(), val(i, 0)))
        .collect();
    let mut b_e = Vec::new();
    for (i, (k, v)) in a_e.iter().enumerate() {
        let i = i as u32;
        if i % 1000 == 500 {
            continue;
        }
        b_e.push((k.clone(), if i % 333 == 7 { val(i, 9) } else { v.clone() }));
        if i % 1000 == 250 {
            b_e.push((format!("k/{i:06}x").into_bytes(), val(i, 3)));
        }
    }
    let mut full = MemBlocks::default();
    let a = build::build(
        a_e.iter().map(|(k, v)| (&k[..], Value::Inline(&v[..]))),
        |c, x| full.insert(c, x),
    )
    .unwrap();
    let b = build::build(
        b_e.iter().map(|(k, v)| (&k[..], Value::Inline(&v[..]))),
        |c, x| full.insert(c, x),
    )
    .unwrap();
    let w = Watch {
        inner: &full,
        seen: RefCell::default(),
    };
    let page = diff(&w, &a, &b, &all(), None).unwrap();
    assert!(
        page.need.is_empty() && page.next.is_none(),
        "the reference diff must be complete in one page"
    );
    let reference = page.changes.iter().map(show).collect();
    let opened = w.seen.borrow().iter().copied().collect();
    Pair {
        full,
        a,
        b,
        reference,
        opened,
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Policy {
    /// Apply each page, resume from `next` — the contract.
    Prefix,
    /// Throw away any page with `need`, restart from the top.
    Strong,
}

struct Run {
    got: Vec<String>,
    rounds: usize,
    finished: bool,
    /// The first round after which the applied changes were NOT a prefix.
    broke_prefix_at: Option<usize>,
    /// How many times a root was evicted mid-diff.
    roots_lost: usize,
}

/// Page the diff to the end from `held`, fetching `need` from `full` each
/// round; `cap` bounds how many fetched blocks stay held (F33 eviction).
/// `evict_roots`: the roots are evictable like any other block, so a root can
/// go missing BETWEEN pages of one diff.
fn page_through(p: &Pair, held: MemBlocks, cap: usize, policy: Policy) -> Run {
    page_through_evicting(p, held, cap, policy, false)
}

fn page_through_evicting(
    p: &Pair,
    mut held: MemBlocks,
    cap: usize,
    policy: Policy,
    evict_roots: bool,
) -> Run {
    let mut roots_lost = 0;
    let mut fifo = VecDeque::new();
    let (mut got, mut resume, mut rounds): (Vec<String>, Option<Resume>, usize) = (vec![], None, 0);
    let mut broke_prefix_at = None;
    let finished = loop {
        if rounds == 400 {
            break false;
        }
        rounds += 1;
        let page = diff(&held, &p.a, &p.b, &all(), resume.as_ref()).unwrap();
        let ch: Vec<String> = page.changes.iter().map(show).collect();
        let (need, next) = (page.need.clone(), page.next.clone());
        drop(page);
        match policy {
            Policy::Prefix => {
                got.extend(ch);
                let ok = got.len() <= p.reference.len() && got[..] == p.reference[..got.len()];
                if !ok && broke_prefix_at.is_none() {
                    broke_prefix_at = Some(rounds);
                }
                resume = next.clone();
            }
            Policy::Strong => {
                if need.is_empty() {
                    got = ch;
                }
            }
        }
        for c in &need {
            held.insert(*c, p.full.get(c).unwrap());
            if evict_roots || (*c != p.a && *c != p.b) {
                fifo.push_back(*c);
            }
        }
        while fifo.len() > cap {
            let old = fifo.pop_front().unwrap();
            if old == p.a || old == p.b {
                roots_lost += 1;
            }
            held.0.remove(&old);
        }
        // Rule 3 of the contract: finished ⇔ no `next` AND no `need`.
        if need.is_empty() && next.is_none() {
            break true;
        }
    };
    Run {
        got,
        rounds,
        finished,
        broke_prefix_at,
        roots_lost,
    }
}

/// The store a diff starts from: `full` minus the blocks it would open, except
/// those `keep` says to keep.
fn withheld(p: &Pair, keep: impl Fn(&Cid) -> bool) -> MemBlocks {
    let mut held = p.full.clone();
    for c in &p.opened {
        if !keep(c) {
            held.0.remove(c);
        }
    }
    held
}

fn assert_exact(label: &str, p: &Pair, r: &Run) {
    assert!(r.finished, "{label}: never finished in {} rounds", r.rounds);
    assert_eq!(
        r.broke_prefix_at, None,
        "{label}: the applied changes stopped being a prefix of the full diff at round {:?}",
        r.broke_prefix_at
    );
    let first_wrong = r.got.iter().zip(&p.reference).position(|(g, w)| g != w);
    assert!(
        r.got == p.reference,
        "{label}: got {} changes, want {} — first divergence at {first_wrong:?}",
        r.got.len(),
        p.reference.len()
    );
}

/// THE CONTROL THAT CAN SEE #51. Everything held except ONE root.
#[test]
fn warm_tree_with_one_root_missing_pages_to_the_exact_diff() {
    let p = pair(20_000);
    assert!(
        p.reference.len() > 50,
        "the fixture has only {} changes",
        p.reference.len()
    );
    for (label, missing) in [
        ("WARM, A's root missing", p.a),
        ("WARM, B's root missing", p.b),
    ] {
        let held = withheld(&p, |c| *c != missing);
        assert!(
            held.get(&missing).is_none() && held.0.len() + 1 == p.full.0.len(),
            "{label}: fixture withholds exactly the one root"
        );
        let r = page_through(&p, held, usize::MAX, Policy::Prefix);
        assert_exact(label, &p, &r);
    }
}

/// Cold arms, which the broken code ALSO passed — kept because each is a
/// different availability pattern the contract covers, not as evidence for
/// the fix.
#[test]
fn cold_arms_page_to_the_exact_diff() {
    let p = pair(20_000);
    let arms: [(&str, Keep<'_>); 4] = [
        // Interior only: both roots held, every block below them cold.
        (
            "interior only (both roots held)",
            Box::new(|c| *c == p.a || *c == p.b),
        ),
        ("cold, both roots missing", Box::new(|_| false)),
        ("cold, only A's root missing", Box::new(|c| *c == p.b)),
        ("cold, only B's root missing", Box::new(|c| *c == p.a)),
    ];
    for (label, keep) in arms {
        let r = page_through(&p, withheld(&p, keep), usize::MAX, Policy::Prefix);
        assert!(
            r.rounds > 1,
            "{label}: finished in one round — nothing was withheld"
        );
        assert_exact(label, &p, &r);
    }
}

/// Why the contract is PREFIX and not "discard any page with `need`": under
/// eviction the strong policy needs the whole working set co-resident and
/// never gets it. Prefix needs only the current path.
#[test]
fn under_eviction_prefix_completes_where_discard_and_restart_does_not() {
    let p = pair(20_000);
    let start = withheld(&p, |c| *c == p.a || *c == p.b);
    let prefix = page_through(&p, start.clone(), 40, Policy::Prefix);
    assert_exact("eviction, prefix", &p, &prefix);
    let strong = page_through(&p, start, 40, Policy::Strong);
    assert!(
        !strong.finished || strong.got != p.reference,
        "CONTROL: discard-and-restart finished correctly under a 40-block cap in {} rounds — the eviction arm no longer separates the policies",
        strong.rounds
    );
}

/// The issue's own reproduction: `{a:1}` → `{a:2}`, one root held.
#[test]
fn a_missing_root_yields_the_empty_prefix_then_the_change() {
    let mut full = MemBlocks::default();
    let a = build::build([(&b"a"[..], Value::Inline(b"1"))], |c, x| full.insert(c, x)).unwrap();
    let b = build::build([(&b"a"[..], Value::Inline(b"2"))], |c, x| full.insert(c, x)).unwrap();
    for missing in [a, b] {
        let mut held = full.clone();
        held.0.remove(&missing);
        let page = diff(&held, &a, &b, &all(), None).unwrap();
        // Rule 4: a page with `need` is not evidence of change — nor of none.
        assert!(
            page.changes.is_empty(),
            "a missing root reported {:?}",
            page.changes.iter().map(show).collect::<Vec<_>>()
        );
        assert_eq!(
            page.need,
            vec![missing],
            "the missing root is what to fetch"
        );
        let next = page.next.clone();
        drop(page);
        held.insert(missing, full.get(&missing).unwrap());
        let page = diff(&held, &a, &b, &all(), next.as_ref()).unwrap();
        assert_eq!(
            page.changes.iter().map(show).collect::<Vec<_>>(),
            vec!["~a"]
        );
        assert!(
            page.need.is_empty() && page.next.is_none(),
            "finished after the fetch"
        );
    }
}

/// CONTROL: a genuinely EMPTY tree is a held root with nothing in it, and it
/// is NOT a missing one. Diffing to or from it is every key, in one page — so
/// the fix cannot be "treat every root that yields no cursor as not held".
#[test]
fn an_empty_tree_is_not_a_missing_root() {
    let mut full = MemBlocks::default();
    let e = build::build(std::iter::empty::<(&[u8], Value)>(), |c, x| {
        full.insert(c, x)
    })
    .unwrap();
    let t = build::build(
        [
            (&b"a"[..], Value::Inline(b"1")),
            (b"b", Value::Inline(b"2")),
        ],
        |c, x| full.insert(c, x),
    )
    .unwrap();
    let removed = diff(&full, &t, &e, &all(), None).unwrap();
    assert_eq!(
        removed.changes.iter().map(show).collect::<Vec<_>>(),
        vec!["-a", "-b"]
    );
    assert!(removed.need.is_empty() && removed.next.is_none());
    let added = diff(&full, &e, &t, &all(), None).unwrap();
    assert_eq!(
        added.changes.iter().map(show).collect::<Vec<_>>(),
        vec!["+a", "+b"]
    );
    assert!(added.need.is_empty() && added.next.is_none());
}

/// A root evicted BETWEEN pages: the resumed page stops on it before deciding
/// anything, and must hand back the SAME resume token. Answering `next: None`
/// there would read as "start again", and the caller would re-apply every
/// change it already has.
#[test]
fn a_root_lost_mid_diff_keeps_the_resume_position() {
    let p = pair(20_000);
    // Roots start COLD, so they are fetched through `need` and enter the
    // eviction queue like everything else.
    // Cap 60: roots are lost mid-diff (12 times, measured) and it still
    // finishes. At 40, one round's fetch evicts the roots before the next
    // round can use them and it never finishes — safely (still a prefix
    // after every round), but that is a cache too small for the diff, not
    // a page contract, so it is not what this arm is about.
    let start = withheld(&p, |_| false);
    let r = page_through_evicting(&p, start, 60, Policy::Prefix, true);
    println!(
        "roots evicted mid-diff: {} times in {} rounds",
        r.roots_lost, r.rounds
    );
    assert!(
        r.roots_lost > 0,
        "no root was ever evicted — this arm tests nothing"
    );
    assert_exact("roots evictable, cap 60", &p, &r);
}
