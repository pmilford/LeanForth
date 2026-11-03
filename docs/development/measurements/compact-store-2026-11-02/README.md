# Compact store prototype: measurements on `Init`, `Std` and all of Mathlib

Measured 2026-11-02 by a Claude Code agent for
[ADR 0016](../../../adr/0016-compact-store.md) (proposed). The prototype in
this folder is measurement code, not a module: it is not loaded by
`src/main.fs`, keeps its state in plain variables and does not follow the
style guide. It uses the real NDJSON reader (`src/import/ndjson.fs`) and the
new `src/lib/u32.fs`. All figures are **measured** on this machine unless
stated otherwise. The runs used the repository at `80b43e4`; after this
work was moved onto `41d83f6` (which had changed `src/lib/bytes.fs` and
`src/lib/json.fs` in between), `verify.sh` on `Init` gave the same three
digests.

## Summary

The prototype reads an export with the Forth reader and stores every name,
level, universe list, literal, expression and declaration in packed 32-bit
records, hash-consed through open-addressing tables (ADR 0016 C1–C4). It
then reports sizes and table statistics, looks up every declaration's name,
walks every declaration with and without a visited cache, and counts the
nodes reachable only from theorem proofs.

| | `Init` | `Std` | all of Mathlib |
| --- | ---: | ---: | ---: |
| Export: bytes / expression nodes | 345.7 MB / 6,099,054 | 562.2 MB / 9,539,642 | 6.26 GB / 105,894,257 |
| Duplicate expressions found | 0 | 0 | 0 |
| Node records (16 B; `letE` takes two) | 6,110,313 | 9,561,212 | 106,136,340 |
| Expression table: slots, load factor | 2²³, 0.727 | 2²⁴, 0.569 | 2²⁸, 0.394 |
| Expression table: occupied slots compared per insertion | 2.56 | 2.23 | 2.61 |
| Bytes per expression: record + table slot | 16 + 5.5 | 16 + 7.0 | 16 + 10.1 |
| Input tier in use, all parts (computed below) | 142.8 MB | 241.4 MB | 2,942 MB |
| Load, `gforth-fast` (table growing from 2¹⁶) | 14.4 s | 22.7 s | 328 s; 383 s in a first run |
| Load, `gforth-fast`, table pre-sized | 12.1 s (2²³) | — | 256 s (2²⁸) |
| Load, `gforth-fast`, no expression table (`1 variant !`) | 8.9 s, against 13.5 s with it in the same session | — | — |
| Load, `gforth` | 32.0 s | 61.4 s | not run |
| The reader alone (`ndjson-count.fs`), `gforth-fast` | 6.3 s; 6.9 s | 10.0 s; 9.6 s ¹ | 103 s ¹ |
| Whole run (`full`), `gforth-fast`: wall, peak RSS | 17.5 s, 228.6 MB | 28.7 s, 367.3 MB | 391.3 s, 4,163.0 MB; first run 443.9 s |
| Whole run (`full`), `gforth`: wall, peak RSS | 38.1 s, 225.3 MB | 71.4 s, 363.8 MB | not run |
| Name lookups by text, every declaration (`gforth-fast`) | 59,349 in 0.032 s | 99,619 in 0.100 s | 729,263 in 0.686 s |
| Name number → declaration, every declaration | 0.6 ms | 1.5 ms | 6.4 ms |
| Walk, dense visited stamps: visits, time | 12,081,281, 1.00 s | 20,027,145, 1.98 s | 226,650,130, 22.4 s |
| Walk, hashed visited set: time (slots compared) | 1.32 s (8.9 M) | 2.54 s (14.6 M) | 26.3 s (169.1 M) |
| Walk without a cache | 764,504,359 visits, 25.0 s | 1,294,593,181 visits with 2 declarations capped at 10⁸, 40.8 s | 11.4×10⁹ visits with 3,913 capped at 10⁶, 364 s |
| Most distinct nodes in one declaration | 27,718 | 79,001 | 95,123 |
| Nodes reachable only from theorem values | 4,997,726 (81.9%) | 7,424,083 (77.8%) | 75,488,059 (71.3%) |
| Largest loose bound-variable range; depth | 144; 324 | 144; 324 | 361; over 1,023 (capped) |

¹ From [NDJSON_READER.md](../../NDJSON_READER.md), measured earlier the
same day; `Init` and `Std` were measured again here (`count-init-std.out`).

Times are from `/usr/bin/time` and the prototype's own clock (`utime`). The
machine ran other agents' test jobs at the same time (load average about
4 on 12 threads), so times vary by about ±20% between runs: two `Init` loads
of the same code took 13.5 s and 15.0 s. User time is within 3% of wall
time for `Init` and `Std` and within 8% for Mathlib (system time for page
faults).

## Verification of the load

1. **Re-emission equals the reader's dump.** `verify.sh` runs the reader's
   field dump (`tests/core/ndjson-dump.fs`, already proven equal to Python's
   `json` module on `Init` and Mathlib) and the prototype's re-emission
   (`dump-file`: every name, level and expression record printed back from
   the packed store, children as export indices) and compares each family's
   lines in index order:

   | Export | Names | Levels | Expressions |
   | --- | --- | --- | --- |
   | `Init` | 295,431 lines, equal (`062a404d…a9028`) | 577, equal (`a37233ac…c491c`) | 6,099,054, equal (`83d1d3ca…b45a016`) |
   | `Std` | 556,077, equal (`c60336f5…fd8f9`) | 929, equal (`35bf430f…f4300`) | 9,539,642, equal (`b76cc599…72de`) |
   | all of Mathlib | 4,241,558, equal (`88e24c54…e45f5`) | 47,805, equal (`a5fad285…a4de3`) | 105,894,257, equal (`144415f8…ba2ea4`) |

   Full SHA-256 values are in `verify-init-std.out` (which also has the
   forced Forth-2012 fallback's run) and `mathlib-verify.out`. The Mathlib
   comparison took 228 s for the reader's dump and 433 s (3.75 GB peak)
   for the re-emission.
2. **Counts per kind** printed by `full` equal the recorded
   [`count.out`](../mathlib-2026-11-02/count.out) for Mathlib (90,514,763
   applications, 8,207,621 lambdas, 5,437,711 Pi types, 1,426,722
   constants, 242,083 `letE`, 38,389 projections, 19,235 and 5,616
   literals, 1,757 sorts, 360 bound variables; 4,241,558 names, 47,805
   levels, 729,263 declarations, 7,013 inductive blocks).
3. **Data words** (loose bound-variable range, "has universe parameters",
   depth capped at 1023) were computed again by `data_check.py` with
   Python's `json` module, following Lean's rules (ADR 0016 fact L3). Sums
   over all expressions agree exactly: `Init` range 59,307,843, depth
   82,186,728, 3,179,536 nodes with universe parameters; `Std` 109,255,068,
   129,987,039 and 5,762,775.
4. **Planted fault.** With the hash-consing comparison changed to ignore a
   node's second child (`ek=` without the `e-b@` test), `verify.sh` on
   `Init` reported the expressions DIFFERENT (`7c000d5d…`) and names and
   levels equal: a merge of distinct terms is caught (`planted-fault.out`,
   run on a scratch copy of the prototype with the fault planted).
5. **The Forth-2012 fallback** of `src/lib/u32.fs`, forced with
   `MAIN=portable.fs` (`u32-native` 0), gave the same three `Init` digests,
   the same statistics, and was slower: load 16.0 s against 14.4 s, dense
   walk 2.58 s against 1.00 s (`init-portable.out`).

## Memory, part by part (bytes in use)

| Part | `Init` | `Std` | Mathlib |
| --- | ---: | ---: | ---: |
| Node records | 97,765,008 | 152,979,392 | 1,698,181,440 |
| Expression table (4 B slots) | 33,554,432 | 67,108,864 | 1,073,741,824 |
| Name records (16 B) | 4,726,912 | 8,897,248 | 67,864,944 |
| Name bytes | 1,395,133 | 2,528,683 | 19,787,897 |
| Name table | 2,097,152 | 4,194,304 | 33,554,432 |
| Levels and level table | 25,632 | 31,264 | 1,027,040 |
| Lists and list table | 51,304 | 94,824 | 3,930,084 |
| Literals: bytes, records, table | 58,163 | 103,868 | 3,693,381 |
| Declarations (32 B) | 1,899,168 | 3,187,808 | 23,336,416 |
| Name → declaration array | 1,181,728 | 2,224,312 | 16,966,236 |
| **Input tier** | **142,754,632** | **241,350,567** | **2,942,083,694** |
| Load-only export-index maps (used) | 25.6 MB | 40.4 MB | 440.7 MB |

The peak RSS of a whole run is larger than the input tier: the load maps,
the arenas' doubling slack (allocated but partly untouched), the dense
visited stamps (4 B per node, 424 MB for Mathlib, made for the walks) and
Gforth itself. With the table pre-sized, a Mathlib load peaked at
3,320.8 MB.

**Against the estimate** in [SCALE_ASSESSMENT.md](../../../project/SCALE_ASSESSMENT.md)
(30 B per node and 3.1 GB, plus 0.3 GB for names, declarations and
literals): measured 26.1 B per node, 2.77 GB for expressions and 0.17 GB for
the rest, 2.94 GB in all, 13% under. The record is 8 B smaller than the
estimate's 24 B (no stored hash; one 32-bit data word); the table is 4 B
larger, because 106 M nodes are 79% of 2²⁷, just past the 3/4 growth
threshold, so the table doubled to 2²⁸ and is 39% full. A table allowed to
fill to 0.8 would be 2²⁷ (0.54 GB) and the input tier 2.4 GB. The
assessment's load estimate of about one minute for Mathlib (from a sketch
that did not validate records) was too low: the reader alone takes 103 s
and the prototype 256–383 s.

## Building nodes and instantiating, in Gforth

Asked for by [the profile of Lean's kernel](../lean-kernel-profile-2026-11-02/README.md),
which found substitution and node building to be the operations to make
fast. `bench.fs` adds a scratch tier to a loaded `Init` (ADR 0016 C3:
scratch nodes after the input's, a scratch table of (node + 1, epoch)
pairs, the input probe only when every child is an input node) and an
`instantiate` with one reusable (node, offset) memo emptied by an epoch
(C4). Results (`bench-init.out`; `gforth-fast`, run while another
measurement ran):

| | Input table 2²³ slots, 73% full | 2²⁴ slots, 36% full |
| --- | ---: | ---: |
| Build app(a, f) for each of the 5,189,376 input applications: input children, mostly new (612 found in the input) | 1,740 ns | 646 ns |
| Build app(previous result, f): a scratch child, so no input probe; always new | 264 ns | 245 ns |
| Build app(f, a) again: found in the input | 612 ns | 351 ns |
| Instantiate each of the 535,415 lambda bodies with a closed term: time per step | 508 ns | 404 ns |
| … time per new node | 904 ns | 718 ns |
| … total | 47.3 s | 37.6 s |

The instantiate run: 172.6 M visits, of which 39.0 M were skipped by the
loose-range test and 40.4 M answered by the memo, leaving 93.1 M steps;
92.0 M builds, of which 47.2 M (51%) skipped the input probe because a
child was a scratch node; of the 44.8 M input probes, 38.7 M (86%) found an
existing input node; 0.95 M builds found a scratch node and 52.3 M made a
new one. Every result passed the sanity check that its loose range is at
most the body's minus one. A missed lookup reads every occupied slot of its
run, each a node record elsewhere in memory, which is why the input
table's fullness matters most for builds whose children are input nodes.

## Walks without a cache, and on Mathlib

A walk without a visited cache visits a shared node once per path. On
`Init` that is 764.5 M visits instead of 12.1 M (63 times, as the
assessment measured); on `Std` two declarations exceed 10⁸ visits each.
On Mathlib the tree size of one declaration is 1.25×10¹⁴ (measured in
[the Mathlib measurements](../mathlib-2026-11-02/README.md)); at the
measured 30 M visits per second that would take about 50 days. Capped at
10⁶ visits per declaration, the walk made 11.4×10⁹ visits in 364 s, with
3,913 declarations capped (the count of declarations whose tree exceeds
10⁶ in that measurement): 50 times the visits of the walk with a cache,
and still under 0.01% of the full trees' 1.3×10¹⁴ visits
(`mathlib-trees.out`).

## Files

- `arena.fs` — heap arenas of 32-bit fields grown by `RESIZE`, byte pools,
  the portable 32-bit hashes (`fmix32`, FNV-1a), and open-addressing tables
  with statistics.
- `compact.fs` — the record layouts of ADR 0016 C1–C2 and hash-consing of
  names, levels, lists, literals and expressions; declarations; the name →
  declaration array.
- `load.fs` — one handler per record kind for `src/import/ndjson.fs`,
  computing each node's data word as Lean does.
- `measure.fs` — statistics, re-emission, walks, name lookups and the
  proof-only count. `main.fs` — the entry words `full`, `dump-file`,
  `trees`. `portable.fs` — `main.fs` with the Forth-2012 fallback forced.
- `bench.fs` — the node-building and instantiate benchmark (loads
  `main.fs`).
- `data_check.py` — the independent data-word computation.
- `run.sh`, `verify.sh`, `count.sh` — the commands below.
- `*.out` — the outputs of the runs in this README, with Gforth's
  redefinition warnings removed: `init-*.out`, `std-*.out`,
  `mathlib-gforth-fast.out` (`full`), `mathlib-trees.out`,
  `trees-init-std.out`, `init-portable.out`, `bench-init.out`,
  `verify-init-std.out`, `data-check.out`, `count-init-std.out`,
  `planted-fault.out`.
  `mathlib-first-run.out`, `mathlib-presized.out` and `mathlib-verify.out`
  came from the same code in the scratch folder before it was copied here;
  the copy adds only the data-word sums, a length guard on name lookups and
  repository-relative paths.

## Commands

Exports: `Init` and `Std` from `leanexport Init` and `leanexport Std` of the
pinned toolchain (SHA-256 `c1b2071a…a59a179` and `bae74d69…a9afcbeb`, as in
[NDJSON_READER.md](../../NDJSON_READER.md)); Mathlib is
`.tools/mathlib/mathlib.ndjson` (`18448e5d…59c6`). Gforth 1.0.0 from
`.tools/gforth/bin`. From the repository root, with `E` the export's path:

```sh
M=docs/development/measurements/compact-store-2026-11-02
bash $M/run.sh gforth-fast 2400 ".native s\" $E\" full bye"     # init/std/mathlib-gforth-fast.out
bash $M/run.sh gforth 2400 ".native s\" $E\" full bye"          # init/std-gforth.out
bash $M/run.sh gforth-fast 2400 "28 etab-log2 ! s\" $E\" phase-load bye"   # pre-sized table
bash $M/run.sh gforth-fast 2400 "max-n s\" $E\" trees bye"      # walk without a cache
MAIN=portable.fs bash $M/run.sh gforth-fast 2400 ".native s\" $E\" full bye"
MAIN=bench.fs bash $M/run.sh gforth-fast 900 "24 etab-log2 ! s\" $E\" bench bye"   # Init only
bash $M/verify.sh "$E" gforth-fast                             # re-emission against the dump
bash $M/count.sh "$E" gforth-fast                              # the reader alone
python3 -I $M/data_check.py "$E"                               # data words, independently
```

`run.sh` caps the address space at 8 GiB (`ulimit -v`), so a run that
would not fit fails its allocation instead of taking the machine's memory.
Every run was started under `timeout -k 5`, with at most two heavy runs at
once; the owner's image-generation process (about 11 GB) was left alone.
