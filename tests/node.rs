use freenet_prolly::node::*;

fn rng(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed | 1;
    move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    }
}

fn sample_leaf() -> Vec<u8> {
    let mut b = NodeBuilder::leaf();
    b.push(b"aa", Value::Inline(b"one")).unwrap();
    b.push(
        b"bb",
        Value::Ref {
            cid: [7; 32],
            len: 5000,
        },
    )
    .unwrap();
    b.push(b"bbb-longer-key", Value::Inline(b"")).unwrap();
    b.finish().unwrap()
}

/// Rebuild a parsed node through the builder.
fn reencode(n: &Node) -> Vec<u8> {
    let mut b = if n.is_leaf() {
        NodeBuilder::leaf()
    } else {
        NodeBuilder::branch(n.level())
    };
    for i in 0..n.len() {
        if n.is_leaf() {
            b.push(n.key(i), n.value(i)).unwrap();
        } else {
            let (c, a) = n.child(i);
            b.push_child(n.key(i), c, a).unwrap();
        }
    }
    for p in n.parity() {
        b.push_parity(p).unwrap();
    }
    b.finish().unwrap()
}

#[test]
fn leaf_round_trips() {
    let bytes = sample_leaf();
    let n = Node::parse(&bytes).unwrap();
    assert!(n.is_leaf());
    assert_eq!(n.len(), 3);
    assert_eq!(n.key(0), b"aa");
    assert_eq!(n.value(0), Value::Inline(b"one"));
    assert_eq!(
        n.value(1),
        Value::Ref {
            cid: [7; 32],
            len: 5000
        }
    );
    assert_eq!(n.value(2), Value::Inline(b""));
    // bytes = key + logical value length; a ref counts what it refers to.
    assert_eq!(
        n.agg(),
        Agg {
            count: 3,
            bytes: (2 + 3) + (2 + 5000) + 14
        }
    );
    assert_eq!(reencode(&n), bytes);
}

#[test]
fn branch_round_trips_with_parity() {
    let mut b = NodeBuilder::branch(2);
    b.push_child(
        b"a",
        [1; 32],
        Agg {
            count: 10,
            bytes: 100,
        },
    )
    .unwrap();
    b.push_child(
        b"m",
        [2; 32],
        Agg {
            count: 5,
            bytes: 50,
        },
    )
    .unwrap();
    b.push_parity([9; 32]).unwrap();
    b.push_parity([8; 32]).unwrap();
    let bytes = b.finish().unwrap();
    let n = Node::parse(&bytes).unwrap();
    assert_eq!(n.level(), 2);
    assert_eq!(
        n.child(1),
        (
            [2; 32],
            Agg {
                count: 5,
                bytes: 50
            }
        )
    );
    assert_eq!(
        n.agg(),
        Agg {
            count: 15,
            bytes: 150
        }
    );
    assert_eq!(n.parity().collect::<Vec<_>>(), vec![[9; 32], [8; 32]]);
    assert_eq!(reencode(&n), bytes);
}

#[test]
fn empty_leaf_is_the_empty_tree_but_an_empty_branch_is_nothing() {
    let bytes = NodeBuilder::leaf().finish().unwrap();
    let n = Node::parse(&bytes).unwrap();
    assert!(n.is_empty());
    assert_eq!(n.agg(), Agg::default());
    assert_eq!(NodeBuilder::branch(1).finish(), Err(BuildError::WrongKind));
}

#[test]
fn builder_refuses_disorder_and_wrong_kinds() {
    let mut b = NodeBuilder::leaf();
    b.push(b"b", Value::Inline(b"")).unwrap();
    assert_eq!(b.push(b"a", Value::Inline(b"")), Err(BuildError::NotSorted));
    assert_eq!(b.push(b"b", Value::Inline(b"")), Err(BuildError::NotSorted)); // duplicate
    assert_eq!(
        b.push_child(b"c", [0; 32], Agg::default()),
        Err(BuildError::WrongKind)
    );
    assert_eq!(b.push_parity([0; 32]), Err(BuildError::WrongKind));
    let mut br = NodeBuilder::branch(1);
    assert_eq!(
        br.push(b"a", Value::Inline(b"")),
        Err(BuildError::WrongKind)
    );
}

#[test]
fn builder_refuses_to_exceed_the_node_cap() {
    let mut b = NodeBuilder::leaf();
    let big = vec![0u8; MAX_NODE];
    assert_eq!(
        b.push(b"k", Value::Inline(&big)),
        Err(BuildError::NodeTooLarge)
    );
    // and whatever it does accept always parses
    let mut i = 0u32;
    while b.push(&i.to_be_bytes(), Value::Inline(&[0u8; 100])).is_ok() {
        i += 1;
    }
    let bytes = b.finish().unwrap();
    assert!(bytes.len() <= MAX_NODE);
    Node::parse(&bytes).unwrap();
}

// Header: magic 0..4, level 4, flags 5, count 6..8, agg.count 8..16, agg.bytes 16..24, pcount 24..26
// then offs [u16; n] at 26, keys4 [u32; n] at 26 + 2n.
fn two_key_leaf() -> Vec<u8> {
    let mut b = NodeBuilder::leaf();
    b.push(b"aaaa", Value::Inline(b"x")).unwrap();
    b.push(b"bbbb", Value::Inline(b"y")).unwrap();
    b.finish().unwrap()
}

#[test]
fn each_malformation_is_named() {
    let good = two_key_leaf();
    Node::parse(&good).unwrap();
    let with = |f: &dyn Fn(&mut Vec<u8>)| {
        let mut v = good.clone();
        f(&mut v);
        Node::parse(&v).map(|_| ()).unwrap_err()
    };
    assert_eq!(with(&|v| v[0] = b'X'), NodeError::BadMagic);
    assert_eq!(with(&|v| v[5] = 1), NodeError::BadFlags);
    assert_eq!(with(&|v| v[24] = 1), NodeError::BadShape); // parity on a leaf
    assert_eq!(with(&|v| v[8] = 9), NodeError::AggMismatch);
    assert_eq!(with(&|v| v[16] ^= 1), NodeError::AggMismatch);
    assert_eq!(
        with(&|v| {
            v[26] = 0xFF;
            v[27] = 0xFF;
        }),
        NodeError::OffsetOutOfRange
    );
    assert_eq!(with(&|v| v[28] += 1), NodeError::BadTiling); // second entry's offset
    assert_eq!(with(&|v| v[30] ^= 0xFF), NodeError::BadKeyPrefix); // keys4[0]
    assert_eq!(with(&|v| v.push(0)), NodeError::TrailingBytes);
    assert_eq!(with(&|v| v.truncate(10)), NodeError::TooShort);
    assert_eq!(with(&|v| v.resize(MAX_NODE + 1, 0)), NodeError::TooLarge);
    // value kind 2 does not exist: first entry starts at 26 + 2*6 = 38; vkind at +2
    assert_eq!(with(&|v| v[40] = 2), NodeError::BadEntry);
    // A branch header over leaf entries is not a branch.
    assert!(Node::parse(&{
        let mut v = good.clone();
        v[4] = 1;
        v
    })
    .is_err());
}

#[test]
fn unsorted_keys_are_refused_even_with_consistent_prefixes() {
    // Make key[0] = "cccc" > key[1] = "bbbb", and fix its keys4 so that ONLY the
    // ordering is wrong — otherwise BadKeyPrefix would mask the check under test.
    let mut v = two_key_leaf();
    let key0_at = 38 + 7;
    v[key0_at..key0_at + 4].copy_from_slice(b"cccc");
    v[30..34].copy_from_slice(&key4(b"cccc").to_be_bytes());
    assert_eq!(
        Node::parse(&v).map(|_| ()).unwrap_err(),
        NodeError::KeysNotSorted
    );
    // equal keys are also disorder
    let mut v = two_key_leaf();
    v[key0_at..key0_at + 4].copy_from_slice(b"bbbb");
    v[30..34].copy_from_slice(&key4(b"bbbb").to_be_bytes());
    assert_eq!(
        Node::parse(&v).map(|_| ()).unwrap_err(),
        NodeError::KeysNotSorted
    );
}

#[test]
fn search_agrees_with_a_linear_scan() {
    let mut next = rng(42);
    for round in 0..200 {
        // keys of length 0..8 over a tiny alphabet: many shared 4-byte prefixes,
        // and keys shorter than the prefix.
        let mut keys: Vec<Vec<u8>> = (0..(next() % 60))
            .map(|_| {
                (0..(next() % 9))
                    .map(|_| b'a' + (next() % 3) as u8)
                    .collect()
            })
            .collect();
        keys.sort();
        keys.dedup();
        let mut b = NodeBuilder::leaf();
        for k in &keys {
            b.push(k, Value::Inline(b"v")).unwrap();
        }
        let bytes = b.finish().unwrap();
        let n = Node::parse(&bytes).unwrap();
        for _ in 0..200 {
            let probe: Vec<u8> = (0..(next() % 9))
                .map(|_| b'a' + (next() % 3) as u8)
                .collect();
            assert_eq!(
                n.search(&probe),
                keys.binary_search(&probe),
                "round {round} probe {probe:?}"
            );
        }
    }
}

/// Corrupt valid nodes at random. `parse` must never panic, and anything it
/// accepts must be exactly what the builder would produce — so there is one
/// encoding per logical node, and a parsed node can be trusted without rechecks.
#[test]
fn parse_never_panics_and_accepts_only_canonical_bytes() {
    let mut next = rng(7);
    let mut branch = NodeBuilder::branch(1);
    branch
        .push_child(b"a", [1; 32], Agg { count: 2, bytes: 9 })
        .unwrap();
    branch
        .push_child(
            b"q",
            [2; 32],
            Agg {
                count: 3,
                bytes: 11,
            },
        )
        .unwrap();
    branch.push_parity([5; 32]).unwrap();
    let seeds = [
        sample_leaf(),
        two_key_leaf(),
        branch.finish().unwrap(),
        NodeBuilder::leaf().finish().unwrap(),
    ];
    let (mut accepted, mut rejected) = (0u32, 0u32);
    for i in 0..300_000u32 {
        let mut v = seeds[(next() % seeds.len() as u64) as usize].clone();
        for _ in 0..=(next() % 3) {
            match next() % 4 {
                0 if !v.is_empty() => {
                    let at = (next() % v.len() as u64) as usize;
                    v[at] = next() as u8;
                }
                1 if !v.is_empty() => {
                    let at = (next() % v.len() as u64) as usize;
                    v[at] ^= 1 << (next() % 8);
                }
                2 => {
                    let keep = (next() % (v.len() as u64 + 1)) as usize;
                    v.truncate(keep);
                }
                _ => v.push(next() as u8),
            }
        }
        match Node::parse(&v) {
            Ok(n) => {
                accepted += 1;
                assert_eq!(
                    reencode(&n),
                    v,
                    "iteration {i}: accepted a non-canonical node"
                );
            }
            Err(_) => rejected += 1,
        }
    }
    // Guard against a vacuous run: mutations must actually be rejected, and some
    // harmless ones (e.g. a flipped byte inside a value) must still be accepted.
    assert!(rejected > 100_000, "only {rejected} rejected");
    assert!(accepted > 1_000, "only {accepted} accepted");
}
