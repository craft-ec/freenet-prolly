# Measurements

Produced by `cargo run --release --example measure > docs/MEASUREMENTS.md`.

| | |
|---|---|
| machine | Apple M4 Max |
| commit | `cf292b2` |
| store | in-memory (`MemBlocks`); no disk or network in any figure |
| datasets | **realistic**: records, edges and index terms, keys out of order · **append-only**: every key above the last |
| runs | block and byte counts are deterministic for a commit and dataset (checked: two runs differ only in timings); times are a single run on an otherwise idle machine |

Every number here was measured by this program on this commit. Nothing is estimated; anything that could not be measured says so.

## Shape

Encoded block size in bytes. `cv` is the standard deviation over the mean; `max-of-8 / mean` is the mean of the largest node in each run of eight, over the overall mean.

### realistic, 20000 entries

Built in 11.626208ms. Height 4, 1143 nodes.

| level | nodes | kind |
|---|---|---|
| 3 | 1 | branch |
| 2 | 2 | branch |
| 1 | 34 | branch |
| 0 | 1106 | leaf |

| nodes | count | min | p1 | p50 | p99 | max | cv | max-of-8 / mean |
|---|---|---|---|---|---|---|---|---|
| leaves | 1106 | 270 | 1487 | 3903 | 5920 | 6224 | 0.254 | 1.35 |
| branches | 37 | 342 | 342 | 3782 | 5377 | 5377 | 0.358 | 1.45 |

### append-only, 20000 entries

Built in 8.285083ms. Height 3, 933 nodes.

| level | nodes | kind |
|---|---|---|
| 2 | 1 | branch |
| 1 | 16 | branch |
| 0 | 916 | leaf |

| nodes | count | min | p1 | p50 | p99 | max | cv | max-of-8 / mean |
|---|---|---|---|---|---|---|---|---|
| leaves | 916 | 373 | 1357 | 3674 | 5819 | 6149 | 0.272 | 1.37 |
| branches | 17 | 1002 | 1002 | 3347 | 5412 | 5412 | 0.310 | 1.12 |

### realistic, 200000 entries

Built in 130.864ms. Height 4, 11383 nodes.

| level | nodes | kind |
|---|---|---|
| 3 | 1 | branch |
| 2 | 11 | branch |
| 1 | 320 | branch |
| 0 | 11051 | leaf |

| nodes | count | min | p1 | p50 | p99 | max | cv | max-of-8 / mean |
|---|---|---|---|---|---|---|---|---|
| leaves | 11051 | 590 | 1569 | 3908 | 5935 | 6628 | 0.257 | 1.35 |
| branches | 332 | 945 | 1318 | 3721 | 6076 | 6443 | 0.291 | 1.39 |

### append-only, 200000 entries

Built in 95.662958ms. Height 4, 9261 nodes.

| level | nodes | kind |
|---|---|---|
| 3 | 1 | branch |
| 2 | 4 | branch |
| 1 | 174 | branch |
| 0 | 9082 | leaf |

| nodes | count | min | p1 | p50 | p99 | max | cv | max-of-8 / mean |
|---|---|---|---|---|---|---|---|---|
| leaves | 9082 | 1029 | 1364 | 3674 | 5819 | 6479 | 0.264 | 1.36 |
| branches | 179 | 285 | 456 | 3229 | 4822 | 5412 | 0.311 | 1.38 |

### realistic, 1000000 entries

Built in 654.996666ms. Height 5, 57185 nodes.

| level | nodes | kind |
|---|---|---|
| 4 | 1 | branch |
| 3 | 3 | branch |
| 2 | 59 | branch |
| 1 | 1600 | branch |
| 0 | 55522 | leaf |

| nodes | count | min | p1 | p50 | p99 | max | cv | max-of-8 / mean |
|---|---|---|---|---|---|---|---|---|
| leaves | 55522 | 858 | 1502 | 3892 | 5909 | 6872 | 0.258 | 1.35 |
| branches | 1663 | 498 | 1388 | 3702 | 5720 | 6374 | 0.270 | 1.37 |

### append-only, 1000000 entries

Built in 481.797083ms. Height 4, 46196 nodes.

| level | nodes | kind |
|---|---|---|
| 3 | 1 | branch |
| 2 | 16 | branch |
| 1 | 840 | branch |
| 0 | 45339 | leaf |

| nodes | count | min | p1 | p50 | p99 | max | cv | max-of-8 / mean |
|---|---|---|---|---|---|---|---|---|
| leaves | 45339 | 1029 | 1364 | 3674 | 5687 | 6849 | 0.263 | 1.36 |
| branches | 857 | 869 | 1017 | 3288 | 4940 | 5412 | 0.267 | 1.34 |

## Cost of a commit

One `apply` per row. **Blocks written** is what becomes PUTs; **replaced** is what the new tree no longer uses.

### realistic, 20000 entries

| batch | where | blocks written | bytes written | blocks replaced |
|---|---|---|---|---|
| 1 | append | 4 | 7090 | 4 |
| 1 | scattered | 4 | 10858 | 4 |
| 10 | append | 4 | 9025 | 4 |
| 10 | scattered | 25 | 85111 | 24 |
| 100 | append | 10 | 25279 | 4 |
| 100 | scattered | 144 | 564068 | 143 |

### append-only, 20000 entries

| batch | where | blocks written | bytes written | blocks replaced |
|---|---|---|---|---|
| 1 | append | 3 | 3711 | 3 |
| 1 | scattered | 3 | 8635 | 3 |
| 10 | append | 3 | 5232 | 3 |
| 10 | scattered | 20 | 68051 | 20 |
| 100 | append | 7 | 20483 | 3 |
| 100 | scattered | 113 | 429006 | 113 |

### realistic, 200000 entries

| batch | where | blocks written | bytes written | blocks replaced |
|---|---|---|---|---|
| 1 | append | 4 | 5973 | 4 |
| 1 | scattered | 4 | 15920 | 4 |
| 10 | append | 4 | 7980 | 4 |
| 10 | scattered | 35 | 131615 | 35 |
| 100 | append | 9 | 24066 | 4 |
| 100 | scattered | 208 | 836894 | 207 |

### append-only, 200000 entries

| batch | where | blocks written | bytes written | blocks replaced |
|---|---|---|---|---|
| 1 | append | 4 | 3269 | 4 |
| 1 | scattered | 4 | 10720 | 4 |
| 10 | append | 4 | 4790 | 4 |
| 10 | scattered | 24 | 88267 | 24 |
| 100 | append | 9 | 20130 | 4 |
| 100 | scattered | 180 | 670775 | 180 |

### realistic, 1000000 entries

| batch | where | blocks written | bytes written | blocks replaced |
|---|---|---|---|---|
| 1 | append | 5 | 6542 | 5 |
| 1 | scattered | 7 | 22051 | 7 |
| 10 | append | 5 | 8333 | 5 |
| 10 | scattered | 31 | 124169 | 31 |
| 100 | append | 10 | 24118 | 5 |
| 100 | scattered | 274 | 1078367 | 272 |

### append-only, 1000000 entries

| batch | where | blocks written | bytes written | blocks replaced |
|---|---|---|---|---|
| 1 | append | 4 | 7513 | 4 |
| 1 | scattered | 4 | 11202 | 4 |
| 10 | append | 4 | 9034 | 4 |
| 10 | scattered | 28 | 98638 | 28 |
| 100 | append | 8 | 24300 | 4 |
| 100 | scattered | 206 | 768450 | 206 |

## Cold reads

Starting from the root alone, fed exactly the blocks each operation asks for.

### realistic, 20000 entries

Prefix `d/pr` selects 2982 of 20000 entries.

| operation | rounds | blocks fetched |
|---|---|---|
| get (one key) | 3 | 3 |
| range, latest 20 | 3 | 4 |
| count of prefix, Claimed | 3 | 5 |
| count of prefix, Verified | 6 | 202 |

### append-only, 20000 entries

Prefix `r/0000000000002` selects 4096 of 20000 entries.

| operation | rounds | blocks fetched |
|---|---|---|
| get (one key) | 2 | 2 |
| range, latest 20 | 2 | 3 |
| count of prefix, Claimed | 2 | 4 |
| count of prefix, Verified | 4 | 191 |

### realistic, 200000 entries

Prefix `d/pr` selects 30068 of 200000 entries.

| operation | rounds | blocks fetched |
|---|---|---|
| get (one key) | 3 | 3 |
| range, latest 20 | 3 | 4 |
| count of prefix, Claimed | 3 | 6 |
| count of prefix, Verified | 34 | 2037 |

### append-only, 200000 entries

Prefix `r/0000000000018` selects 4096 of 200000 entries.

| operation | rounds | blocks fetched |
|---|---|---|
| get (one key) | 3 | 3 |
| range, latest 20 | 3 | 4 |
| count of prefix, Claimed | 3 | 5 |
| count of prefix, Verified | 5 | 189 |

### realistic, 1000000 entries

Prefix `d/pr` selects 150132 of 1000000 entries.

| operation | rounds | blocks fetched |
|---|---|---|
| get (one key) | 4 | 4 |
| range, latest 20 | 4 | 5 |
| count of prefix, Claimed | 4 | 7 |
| count of prefix, Verified | 162 | 10213 |

### append-only, 1000000 entries

Prefix `r/000000000007` selects 65536 of 1000000 entries.

| operation | rounds | blocks fetched |
|---|---|---|
| get (one key) | 3 | 3 |
| range, latest 20 | 3 | 4 |
| count of prefix, Claimed | 3 | 6 |
| count of prefix, Verified | 49 | 3015 |

## Cold diff

Both roots held, nothing else; `b` is the tree after the edits in the first column.

### realistic, 20000 entries

| edits | rounds | blocks fetched | changes |
|---|---|---|---|
| 1 | 3 | 6 | 1 |
| 10 | 13 | 46 | 10 |
| 1000 | 68 | 2010 | 1000 |

### append-only, 20000 entries

| edits | rounds | blocks fetched | changes |
|---|---|---|---|
| 1 | 2 | 4 | 1 |
| 10 | 11 | 41 | 10 |
| 1000 | 34 | 1732 | 1000 |

### realistic, 200000 entries

| edits | rounds | blocks fetched | changes |
|---|---|---|---|
| 1 | 3 | 6 | 1 |
| 10 | 18 | 56 | 10 |
| 1000 | 349 | 3845 | 1000 |

### append-only, 200000 entries

| edits | rounds | blocks fetched | changes |
|---|---|---|---|
| 1 | 3 | 6 | 1 |
| 10 | 14 | 46 | 10 |
| 1000 | 183 | 2481 | 1000 |

### realistic, 1000000 entries

| edits | rounds | blocks fetched | changes |
|---|---|---|---|
| 1 | 4 | 8 | 1 |
| 10 | 29 | 192 | 10 |
| 1000 | 1047 | 5449 | 1000 |

### append-only, 1000000 entries

| edits | rounds | blocks fetched | changes |
|---|---|---|---|
| 1 | 3 | 6 | 1 |
| 10 | 21 | 60 | 10 |
| 1000 | 821 | 3665 | 1000 |

## Block amplification

Appending one entry at a time. **Store blocks** is everything the store ends up holding, **live nodes** is what the final tree actually reaches, and **if replaced dropped** is what would remain if every node `apply` reported as replaced were removed — a floor, since `replaced` is a hint and another tree may still use those blocks.

| entries | appends | blocks written | bytes written | live nodes | live bytes | store blocks | store bytes | store / live | if replaced dropped | then / live | time |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 20000 | 100 | 300 | 512800 | 938 | 3414573 | 1234 | 3910387 | 1.3x | 939 | 1.0x | 1.923375ms |
| 20000 | 1000 | 3000 | 5639083 | 978 | 3567362 | 3934 | 9036670 | 4.0x | 979 | 1.0x | 20.786625ms |
| 20000 | 10000 | 30000 | 54844118 | 1383 | 5094749 | 30934 | 58241705 | 22.4x | 1384 | 1.0x | 202.031125ms |
| 200000 | 100 | 400 | 314036 | 9266 | 33987178 | 9662 | 34284216 | 1.0x | 9267 | 1.0x | 1.357917ms |
| 200000 | 1000 | 4000 | 3879605 | 9307 | 34140007 | 13262 | 37849785 | 1.4x | 9308 | 1.0x | 15.467834ms |
| 200000 | 10000 | 40000 | 46656087 | 9722 | 35668552 | 49262 | 80626267 | 5.1x | 9723 | 1.0x | 182.99125ms |
| 1000000 | 100 | 400 | 816012 | 46201 | 169860159 | 46597 | 170659179 | 1.0x | 46202 | 1.0x | 3.032166ms |
| 1000000 | 1000 | 4000 | 9596053 | 46245 | 170013246 | 50197 | 179439220 | 1.1x | 46246 | 1.0x | 34.83575ms |
| 1000000 | 10000 | 40000 | 78022002 | 46667 | 171542481 | 86197 | 247865169 | 1.8x | 46668 | 1.0x | 308.497208ms |

