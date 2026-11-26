# A leaner term store and lean walks (design, 2026-11-25)

Status: **designed, not reviewed, no code.** Base: main f0f552fd. Builds on
[KERNEL_SPEED.md](../development/KERNEL_SPEED.md) (sections 0-4, 9, 10), the two landed steps
[KERNEL_VALIDITY_CHECKS.md](KERNEL_VALIDITY_CHECKS.md) and [KERNEL_TERM_READS.md](KERNEL_TERM_READS.md) with
their reviews, and takes in the unreviewed, on-hold group 2 design (its file KERNEL_SPEED_GROUP_2 on branch
`kernel-speed-2-design`). Measurements: [term-store-2026-11-25](../development/measurements/term-store-2026-11-25/README.md).

## Summary for the owner (one page)

**Where the 21 times comes from.** Init's check takes 656.5 s on one thread against 31.0 s for Lean's
checker (measured on main, 2026-11-25). LeanForth does almost the same work as Lean: counted on the decide
slice, an instantiation visits exactly the nodes Lean's `replace` visits (the root plus both children of
every node it rebuilds: 134,665 + 2 x 593,792 = 1,322,249 visits), and every node already carries Lean's
cached summaries (loose bound-variable range, has-free-variable, has-universe-parameter), which the walks
use to skip closed subterms. The split of the 656.5 s (estimates from the profile and the counts):

- **(a) work Lean does not do: 121-140 s (18-21%)**: audits of every term a pass takes (29 s), universe
  substitution's collect, sort and binary search (33-52 s), passes set up on roots that need nothing
  (13 s), a second hash probe per new node (28 s), a hash probe per read of an input constant (18 s);
- **(b) the same work at many more instructions: about 440-480 s (68-73%)**: a real instantiation visit
  costs **862 ns** (timed on the decide slice), where a plain recursive Forth word on the same 16-byte
  node costs **16-24 ns** and C **4-5.5 ns** (micro-benchmark). The cost is in the layers each visit goes
  through (frame admission, fuel, outcome values, validity, identity and input-or-store reads, memo),
  not in Forth itself;
- **(c) memory: about 40-55 s (6-8%)**: cache misses on hash slots and records, the same in Forth and C.

**What Forth itself costs.** Measured on gforth-fast against `gcc -O2` on the same layout: well-written
Forth is **3-4 times slower than C** on pointer work that stays in the cache, **about equal** when memory
misses dominate, and **2.5-3 times slower** on hash-consing at Init's scale. So the floor for LeanForth is
not 21 times Lean but a few times.

**What changes.** The 16-byte node stays (no file or snapshot format changes); the hash tables keep each
entry's hash beside it; an input constant's entry is found by one load instead of a probe; walks test
each child inline and spend a frame only on a node they rebuild; universe substitution becomes the same
memoized walk as instantiation; the audit and the memo use per-node marks instead of hash probes; last,
the hottest read and probe words become Forth macros where measured.

**What it will reach, and what not.** Five slices, each its own group, take Init from 656.5 s to about
**430 s (about 14 times Lean)** (estimate). That is not 3-5 times. 3-5 times needs every kernel pass
(whnf, inference, definitional equality, the caches) at 150-240 ns per unit of fuel instead of 1,000 ns.
**Slice 2 decides it**: it rewrites instantiation in the new style and measures ns per visit on Init. At
200 ns or less the same rewrite of the other passes (three or four more groups) reaches about 3.5-6
times in pure Forth; at 200-400 ns pure Forth stops near 6-9 times and 3-5 needs a few native
primitives; above 400 ns the approach is wrong and we stop.

**Why it is safe.** Verdicts, diagnostics, reports and fuel numbers stay identical: a child kept without a
frame is charged its one unit of fuel at the same moment, with the same exhaustion test. Every
fail-closed check on export data stays (an input leaf without an entry is still refused, by one load).
Nothing is written to files differently; no new dependency; all state stays per context.

**Cost and risk.** About 600-900 Forth lines changed over five groups, 0.8-1.1 M tokens each (under 1.2 M),
about 4.8 M in all (estimate). Risks: the walks are the kernel's core (mitigated: identical fuel and
reports on Init, decide and every pinned-Lean comparison per slice); a cached block address across an
allocation (forbidden by rule, tested by growth faults); peak memory up 1-6% (stored hashes).

**Recommendation.** Do slice 1 (the on-hold group 2 with the leaf column) and slice 2 now, as ordinary
behaviour-preserving refactoring; decide on the rest of the route, and on native code, from slice 2's
measured ns per visit.

## 1. Where the 21 times comes from

Basis: the profile of main after both steps (`.claude/work/init-profile-2026-11-25-after-reads/`, 67,511
samples, inclusive and exclusive shares, measured), times 656.5 s; the counted and timed decide slice
(Appendix A, measured); the micro-benchmarks (section 2, measured). Shares are of the check phase.

| Part | Seconds of 656.5 | Basis |
| --- | ---: | --- |
| (a1) audit of each term a pass takes (`lf-cterm-check`) | 29 | 4.45% inclusive; Lean audits nothing in memory |
| (a2) universe substitution's set, sort and binary search beyond one memoized pass | 33-52 | KERNEL_SPEED candidate 2 (5-8 points); `lf-mls-checks` alone 6.38% (42 s) |
| (a3) passes set up on a root Lean returns at once | 13 | 42.5% of Init's passes (counted 2026-11-24), 46.5% on decide; 2% |
| (a4) the input tier's probe before the store's, for every new node | 28 | `lf-tin-given` 4.33%; it finds 7.4% (62,068 of 833,837 on decide) |
| (a5) an input leaf's fields found by a hash probe | 18 | `lf-tin-leaf` 2.80%; Lean reads a pointer |
| **(a) work Lean does not do** | **121-140** | 18-21% |
| (b) the same visits, cons, lookups at more instructions each | about 440-480 | the rest less (c); per visit below |
| (c) cache misses on slots and records | about 40-55 | `htab@` 4.18% (27 s, the slot load) and record compares (estimate) |

**The visits are Lean's.** On the decide slice (Appendix A) instantiation made 134,665 passes and
1,322,249 visits: 516,370 leaves (247,826 bound variables replaced), 150,022 binary nodes kept because their
data word shows them closed, 62,065 memo hits and 593,792 nodes rebuilt. Visits = passes + 2 x rebuilt,
exactly the count of Lean's `replace_rec_fn`, which calls its function on each child of a node it rebuilds
and returns a closed child at once. 63.7% of the visits are nodes that contain a variable to replace;
the rest are the closed children both checkers must look at. LeanForth already skips closed subterms
as Lean does; the skipping is not where the time goes. The only visits Lean saves are the closed roots
(a3), and Lean's cache is consulted only for shared nodes where LeanForth's memo is asked at every
rebuilt node (771,674 lookups, 8% hits) — but a memo hit saves fuel, so the memo must stay where it is.

**What a visit costs.** `lf-open-pass` took 1.140 s inclusive for the 1,322,249 visits (timed on the decide
slice, load 3.6, timers included): **862 ns a visit**, of which by the counts about 250 ms are new nodes
(lf-term-add, about 420 ns each), about 320 ms the memo, up to 230 ms audits, and about 340 ms (257 ns a
visit) frames, reads, validity and dispatch. The same rebuild as a recursive Forth word on a 16-byte node
with a stored-hash table costs 15.7-24.1 ns a visit, new nodes included, and in C 4.0-5.5 ns
(section 2). Per unit of fuel the whole check costs 1.00 µs (656.5 s / 654,719,715 units); if Lean did the
same units it spends about 47 ns on each. Reads per unit: 7.1 field reads (tag, first, second, data:
18.9 M on decide), 3.1 validity tests, 2.0 identity reads and 6.3 input-record decodes (16.6 M).

So the 21 times is about 1.25 times from (a) and about 16-17 times from (b) with (c): a few times from
Forth against C++ (section 2), the rest from the layering of every operation. The data words, the
summaries and the visit rule are already Lean's; the access protocol is not.

## 2. The floor for portable Forth

Micro-benchmarks (Appendix B; `bench.fs` on Gforth 1.0 `gforth-fast`, `bench.c` with gcc 13.3 `-O2`, three
runs each, load 0.5-2.7): the same 16-byte node (tag, first, second, data) and a hash table whose 8-byte
slot keeps the 32-bit hash beside the index plus one. *cur* uses LeanForth's own read words, *col* one
colon word per field, *raw* the field reads written out in the step (what a macro gives).

| Operation | cur | col | raw | C | raw / C |
| --- | ---: | ---: | ---: | ---: | ---: |
| chase: tag, data and a child per step, 4,096 nodes (in cache) | 12.7-13.7 ns | 7.3-8.7 | 3.8-4.6 | 1.0-1.4 | 3.2-3.8 |
| chase, 4 M nodes (64 MB, a miss a step) | 46-75 | 48-66 | 46-65 | 47-57 | 0.8-1.2 |
| hash-cons app(a, b), 4.2 M calls, 37% found, 2.7 M nodes | 329-410 | – | 179-210 | 61-71 | 2.5-3.2 |
| rebuild (instantiate) a tree, per visit, recursive | (862 real) | – | 15.7-24.1 | 4.0-5.5 | 3.9-4.4 |

The recursive rebuild is the floor of one pass: it has no fuel, no outcome values and no depth-free
stack, which LeanForth needs (fuel is a resource outcome; deep terms must not overflow the return stack:
plan 6.2.0). A lean frame step costs about two to three times a recursive call in Forth (estimate from
the frame words' 15-20 primitives against 6-8), still tens of ns, not hundreds.

**What ratio to Lean each level can reach** (estimate: Lean at about 47 ns a unit of fuel, a C rewrite of
LeanForth's algorithm at about Lean's speed, Forth at the measured raw/C ratios, memory misses unchanged):

- **(i) algorithms and layout, plain colon words**: the col level on the hot paths, about 2 times raw
  in cache: **about 6-9 times Lean** (190-280 s), if every hot pass is rewritten as slice 2 rewrites
  instantiation;
- **(ii) with Forth macros for the read chain, the probe and the frame step** (immediate words built with
  `POSTPONE`, Forth-2012): the raw level, **about 3.5-6 times** (110-185 s);
- **(iii) with native primitives** through Gforth's C interface (`c-function`, libcc) or a small shared
  library: **about 2.5-4 times** (80-125 s). The candidates, each 10-40 lines of C, with the pure-Forth
  words kept as the reference implementation and the fallback the tests compare against: (1) `hash-3`
  with `hash-fmix`; (2) `htab-find` with stored hashes and the record compare inlined for the term
  layout; (3) `lf-term-cons`'s probe-and-append for the store (not the input tier's twin); (4) the closed
  test and read of one child (tag, fields, data in one call); (5) the replace memo's probe; (6) the
  frame step (admit, charge, save). Cost: a C compiler at run time (libcc) or a built library per
  platform; Gforth 0.7.3's C interface differs (it would run the Forth fallback); other Forths have none;
  the C code joins the trusted base only where it decides verdicts (none of the six does: they find,
  hash and read). It is a new runtime dependency: owner's approval and the review gate.

## 3. The new term store

**The node stays 16 bytes** (four 32-bit fields through `u32@`, `u32!`, C7): word 0 is the tag in bits 0-7
and **summary bits 8-15** (bit 8: has an expression metavariable, for the front end's
`lf-instantiate-mvars`, KERNEL_SPEED section 8; 9-15 reserved, 0); first; second; and the data word
unchanged (bits 0-19 loose range, 20 has a universe parameter, 21 has a free variable, 22-31 depth),
which is Lean's `Expr.Data` (Expr.lean 118-160: hash 32, approxDepth 8, four flags, looseBVarRange 20)
without the hash and the metavariable flags. **No hash in the node**: children are hash-consed, so
`hash-3` of (tag, first, second) over child numbers is a structural hash, cheaper than Lean's.
Per store node besides: the 8-byte identity (birth serial, unchanged: handles and rollback need it) and
an 8-byte table slot (32-bit hash, index plus one; today 4 bytes) at a load of at most 3/4.

**The input tier stays read in place** (ADR 0016 C3; the tier's records and data words are the snapshot's
expressions, ADR 0020, so they do not change). What changes is how a read finds an input leaf: the
view's node-to-entry table `lf-tview-nodes` becomes a dense **leaf column**, 4 bytes per input term number
(the entry number plus one, 0 for none: a leaf without an entry stays refused, the binding lesson of the
reads review), written by the importer where it enters a leaf (`lf-tleaf-new`) and borrowed read-only by
workers with the other view tables. Init: 12.2 M input terms; the column is 49 MB where the table it
replaces holds about 30-60 MB (estimate); slice 1 measures the peak first and keeps the probe (with
stored hashes) if the peak grows more than 5%.

**Hash-consing** keeps its order and answers: the input tier is still asked first (so an input node is
given, never a store copy), then the store's table; both tables keep the stored hash, so a probe compares
a record only where the hashes agree, growth moves the stored hash with its entry and never rehashes, and
deletion (Knuth's Algorithm R, used by rollback) moves hashes with entries. The find's empty slot is
reused for the insert (no second probe). The same tables, entries and slots as today: identical sharing,
so identical cache hits and fuel.

**Marks.** The audit's "seen in this check" memo becomes a 4-byte store column stamped with the check's
number (lib/store-columns.fs, which grows columns with the store), and the view's equivalent for input
nodes; a node made after a rollback gets its column cleared when it is made, so it never inherits a mark.
Rollback marks, `store-mark`, generations and identities are unchanged.

**Walks** (a new shared walker in `kernel/mixed-rebuild.fs`, used by instantiate, instantiate_rev,
abstract, shift and, in slice 3, universe substitution): a pass whose root is closed for it returns at
once (charging the root's one unit, as today); a visit reads its node once (tag, first, second, data from
one address); each child is tested inline: a leaf to keep or a closed child is kept without a frame,
charged one unit by `frame-charge` (exhausted when fuel is spent, at the same unit as today); only a child
to rebuild gets a frame; inside a pass whose root and substitution were checked at entry, field reads are
unchecked except the input-leaf entry test (one load). **No address is kept across a construction**: a
new node may grow and move the store's block, so the walker re-derives the node's address from its
number after each `lf-term-add` (the binding lesson of the validity review).

**Memory** (estimate): stored-hash slots +1-3% (group 2's estimate), leaf column -10 to +20 MB, audit
column 4 bytes per node in place of the audit memo's table: Init's peak 643 MB -> about 650-680 MB.
nanoda's is 364 MB; a smaller footprint is not this design's aim.

**What each pass gains** (estimates, Appendix C): instantiate, abstract and shift: closed roots and
kept children without frames, one read per visit (40-65 s); universe substitution as one memoized walk,
level-closed subterms kept inline (33-52 s); whnf's spine reads and the caches' keys: through the
cheaper reads and stored-hash probes (in slices 1 and 5); the audit and the memo by marks and slot reuse
(30-50 s).

## 4. What stays fixed

- **Verdicts, diagnostics, reports**: identical, compared on Init (both reports identical outside
  `measured`, `settings`, `run`), the decide slice at 1 and 4 workers, and every pinned-Lean comparison.
- **Fuel**: identical numbers, by construction: a kept child is charged one unit at the moment its visit
  would have started, after the same exhaustion test (`frame-admit`'s fuel test: zero or negative is
  exhausted), so the same declaration exhausts at the same unit with the same diagnostic; a closed root
  is charged its unit. The memo hits where it hits today (a hit costs one unit; skipping lookups would
  change fuel). Slice 3 must reproduce the substitution's charges as a formula; if it cannot, it stops and
  asks (question 2): a change of fuel numbers is visible in the JSON report and needs the owner.
- **Fail-closed checks on export data**: the stage's and feed's checks unchanged; the per-read range check
  is replaced, inside a checked pass, by the invariant the validity design states (a root and its store
  count checked at entry; children of a valid node are older and valid by construction, the tier's by its
  builder's check); the input-leaf entry test stays per read (one load); malformed-input tests must still
  fail closed.
- **Re-entrancy**: no module-level state: tables, columns and the walker's frames are per context; the leaf
  column is borrowed read-only as the view's tables are; workers unchanged.
- **Formats**: no change to the tier, snapshots (`--save-snapshot`, ADR 0020 saves the tier's expressions,
  never the term store, leaf tables, audit marks or hash layouts), certificates or reports.
- **Names**: the front end's 43 files that read terms (`lf-term-first@`, `lf-term-tag@`, ...) keep the names
  and stack effects; `htab-put`'s new stack effect touches five call sites in two `src/front` files
  (group 2's count), changed last.
- **Portability**: 32-bit cells (every field 32 bits through lib/u32.fs; the stored hash masked to 32
  bits; columns of 32-bit units), Forth-2012 words only in `src/` (macros by `POSTPONE`), Gforth 0.7.3 in
  the nightly run.

## 5. Slices

Each slice is one group: one architect step, one Forth review, one tier (the full one: kernel and core),
one done check that runs Init at 1 and 4 threads beside Lean's checker (31.0 s) and nanoda (30.7 s at 1,
9.7 s at 4) and the decide slice at 1 and 4. Seconds are estimates of Init's check phase at one thread
(Appendix C); 4 threads scale by today's 182.1 / 656.5.

| # | Slice | Forth lines | Tests / faults | Saves (s) | Check after, 1 thread / 4 | Times Lean | Tokens |
| --- | --- | ---: | --- | ---: | --- | ---: | ---: |
| 1 | Tables keep their hashes; the find's slot reused; one probe per input leaf, then the leaf column (group 2 with its candidate 4b) | 130-190 | 180-260 / 16-20 | 35-55 | 600-620 / 166-172 | 19.4-20.0 | 1.0 M |
| 2 | Lean walks: closed roots at once, kept children inline with `frame-charge`, one read per visit, frames only for rebuilt nodes (instantiate, instantiate_rev, abstract, shift) | 150-250 | 200-300 / 10-14 | 40-65 | 535-580 / 148-161 | 17.3-18.7 | 1.1 M |
| 3 | Universe substitution on the same walker, memoized, level-closed subterms kept inline; the set, sort and binary search retired | 150-250 | 150-250 / 8-12 | 33-52 | 485-545 / 134-151 | 15.6-17.6 | 0.9 M |
| 4 | Marks instead of probes: the audit column, the memo's slot reused and its hash kept, identity reads out of pass interiors | 80-150 | 120-200 / 8-12 | 30-50 | 435-515 / 120-143 | 14.0-16.6 | 0.9 M |
| 5 | Measured macros (`POSTPONE`) for the read chain, the probe and the frame step on the words slices 1-4 leave hottest; then the measured native proposal (no native code) | 40-100 | 80-150 / 6-10 | 30-60 | 375-485 / 104-134 | 12.1-15.6 | 0.8 M |

Order: by gain over risk; 1 is the reviewed-ready, lowest-risk table work; 2 is the measure that decides
the route; 3 and 4 reuse 2's walker; 5 needs the profile after 4. **Slice 2 first shows whether 3-5 times
is reachable in pure Forth**: its done check reports instantiation's ns per visit on Init (today about
860 ns, estimated from decide). Target: 200 ns or less (go: rewrite whnf, inference and definitional
equality the same way, three or four more groups, toward 3.5-6 times); 200-400 ns (pure Forth stops near
6-9 times: bring the native question forward); above 400 ns (stop; the layering is not the cause).

Keeping each group under 1.2 M tokens: this design is the architect step's input (the step only checks
it against the code of the day); the brief names files, words and the faults; the reviewer probes and
plants faults, it does not re-run suites; one tier on the final head; the done check's Init runs cost
wall time (about 11 min at 1 thread, 3.5 at 4), not tokens; profiling only in slices 2 and 5.

## 6. Gates

All five slices are behaviour-preserving refactoring of kernel and core code (owner, 2026-11-19): no
change to what the checker accepts, rejects, reads or writes; Forth review and the full tier with every
pinned-Lean comparison; reported afterwards. They become gate items only if: fuel numbers change (slice 3
if its formula fails: owner's approval of a one-time change); the tier's records or data word change
(snapshot format: not proposed); native code is added (new runtime dependency and trusted-base question:
owner's approval and the review gate; slice 5 only measures and proposes).

## 7. Reuse and work in flight

**Reuse.** `lib/htab.fs` (gains stored hashes and slot reuse: the one table library of every family),
`lib/hash32.fs` (`hash-3`, `hash-fmix` as fused), `lib/frame.fs` (gains `frame-charge`: one unit of fuel
without a frame, exhausted alike, a library word with its own tests), `lib/store-columns.fs` (the audit
column and the leaf column are columns), `lib/store.fs` marks and rollback (unchanged), `lib/memo.fs`
(the replace memo's table), `core/terms.fs` (read words keep their names). New: the shared walker in
`kernel/mixed-rebuild.fs`, which replaces the per-pass visit words of `mixed-open.fs`, `mixed-shift.fs`
and `mixed-level-substitute.fs` (slice 3 retires the substitution's set, its `lib/sort.fs` call and its
binary search), and the macro words of slice 5 in `lib/` beside the colon words they inline (both kept:
the colon words are the reference the tests compare). No hand-written table, sort or stack.

**Work in flight.** The front-end simp branch under `src/front` reads terms by name only: unaffected
except the five `htab-put` call sites (slice 1, changed last and rebased). The on-hold group 2 design is
slice 1 here (with its candidate 4b); its 4a (memo) is slice 4. The validity checks' slices 2-3
(KERNEL_VALIDITY_CHECKS.md) touch `caches.fs` and the audits: slice 4 follows them or takes them in.

## 8. Questions for the owner

1. **Route.** The store and walk changes reach about 14 times Lean, not 3-5; 3-5 needs the slice-2 style
   rewrite of whnf, inference and definitional equality too. Do slices 1 and 2 now and decide the rest
   from slice 2's ns per visit? *Recommendation: yes; it is the cheapest way to learn whether pure Forth
   can get there.*
2. **Fuel.** If universe substitution cannot charge exactly today's fuel as one walk, may its fuel numbers
   change once (Init's total would change; verdicts not)? *Recommendation: only if the exact formula
   fails, with a before/after table; first try to keep them.*
3. **Memory.** May Init's peak grow from 643 MB to about 680 MB (stored hashes, leaf column) for these
   gains? *Recommendation: yes; slice 1 measures it and falls back if it grows more than 5%.*
4. **Native code.** Prepare a measured proposal for three to six C primitives (hashing, the probe, the
   child read, the frame step) after slice 5, with the Forth words kept as reference and fallback?
   *Recommendation: yes, as a proposal only; it adds a runtime dependency and needs your approval.*

## Appendix A. Counts on the decide slice

Scratch copy of main f0f552fd's `src/` with entry counters on 25 words and timers around four
(`count-patch.py`), `bin/leanforth check --jobs 1 --no-manifest --resources --json
tests/front/decide-slice.ndjson`, Gforth 1.0 `gforth-fast`, 2026-11-25 21:56-22:01, load 0.6-3.6;
1,290 declarations accepted, fuel 2,649,895, check phase 2.66 s with counters (2.52 s without, recorded),
3.04 s with timers too.

| Count | Value | Count | Value |
| --- | ---: | --- | ---: |
| instantiation passes (`lf-open-run`) | 134,665 | of them on a closed root | 62,684 |
| visits (`lf-open-visit`) | 1,322,249 | leaves / bound variables replaced | 516,370 / 247,826 |
| binary visits / kept closed | 805,879 / 150,022 | memo hits / rebuilt | 62,065 / 593,792 |
| frame visits of every pass | 1,929,334 | replace memo lookups / inserts | 771,674 / 597,261 |
| `lf-term-cons` / input probes found | 833,837 / 62,068 | store probes / new nodes | 771,769 / 416,153 |
| reads: tag / first / second / data | 7.10 M / 4.78 M / 2.67 M / 4.32 M | validity / identity | 8.23 M / 5.29 M |
| input record decodes / leaf probes | 16.64 M / 2.08 M | `htab-find`, every table | 6.32 M |
| audits / universe substitutions | 123,363 / 14,985 | timed: `lf-open-pass` / `lf-term-add` | 1.140 s / 0.356 s |
| timed: `lf-cterm-check` / substitution | 0.229 s / 0.644 s | | |

## Appendix B. Micro-benchmark results

Sources and the raw output: [term-store-2026-11-25](../development/measurements/term-store-2026-11-25/README.md).
Milliseconds, three runs (21:58 at load 0.5-2.7; 22:04 twice at load 2.0-2.7); 2^24 chase steps, 2^22
conses, one rebuild of 327,767 visits.

| Run | chase small raw / col / cur / C | chase large raw / col / cur / C | cons raw / cur / C | rebuild raw / C |
| --- | --- | --- | --- | --- |
| 1 | 63.9 / 121.8 / 229.9 / 19.2-20.1 | 773 / 810 / 764 / 866-955 | 751 / 1,380 / 294-299 | 5.15 / 1.32-1.36 |
| 2 | 70.7 / 128.1 / 213.6 / 23.7 | 1,019 / 1,068 / 1,063 / 794 | 801 / 1,482 / 254 | 5.51 / 1.82 |
| 3 | 76.4 / 145.8 / 229.1 / 17.1 | 1,087 / 1,108 / 1,254 / 864 | 880 / 1,718 / 266 | 7.90 / 1.33 |

## Appendix C. How the seconds were estimated

- Slice 1: group 2's 4.5-7.5 points of 656.5 s (30-49 s) plus the leaf column's part of `lf-tin-leaf`'s
  2.80% (about 6-12 s beyond group 2's one probe per leaf): 35-55 s.
- Slice 2: closed roots 13 s; kept children (leaves and closed nodes, 50% of visits on decide; Init about
  327 M visits, estimated as decide's 0.499 visits per unit of fuel times 654.7 M) without frame,
  dispatch and readability test, 150-200 ns each of the 257 ns residual per visit: 25-33 s; one read per
  rebuilt node and no identity reads inside: 7-15 s; less the new inline tests: 40-65 s.
- Slice 3: KERNEL_SPEED candidate 2's 5-8 points re-based on 656.5 s: 33-52 s.
- Slice 4: the audit's 29 s to about 9 (a column load per node instead of a memo probe): 20 s; the
  replace memo's 62 s (`lf-rmemo@` 3.87%, `lf-rmemo!` 5.55%) by a quarter: 15 s; identity reads
  (`lf-term-identity` 2.91%) by half: 10 s; together 30-50 s with the overlap of slice 1 removed.
- Slice 5: the reads family's exclusive share after slices 1-4 (estimate about 25% of 450 s), halved
  for its instruction part as in the chase benchmark's col -> raw step: 30-60 s.

## Corrections after the design review (2026-11-25 22:16, binding; they replace the text above where they differ)

From the independent review, [2026-11-25-term-store.md](../development/design-reviews/2026-11-25-term-store.md)
(verdict: rework the measurement and the decision rule before the walker slice; the table work may go ahead).

1. **The cost of one instantiation visit, by layer** (from the profile of main, 250 s of the pass over about
   327 M visits, about 765 ns a visit; this replaces section 1's split): hash-consing of rebuilt nodes 186 ns;
   replace-memo lookups and inserts 178 ns; the memo's end, its entries deleted one by one, 82 ns; reads and
   dispatch 111 ns; frames 66 ns; validity 51 ns; the closed test 46 ns; other pass setup 44 ns; outcome
   plumbing 2 ns. **The hash tables are 58% of a visit, the frame machinery 9%.** The pass makes no audits.
2. **The floor benchmark did not do the same work** (no memo, almost no new nodes, no input-tier reads). A
   fair floor for one visit in pure Forth is about 130-230 ns (estimate), not 16-24 ns.
3. **Work Lean does not do** also includes hash-consing (Lean's `mk_app` allocates and probes no table;
   `lf-term-cons` is about 80 s of Init) and the memo's per-entry deletion (about 20 s; Lean throws its cache
   away whole). The audit's removable part is at most about 8 s; the audit stays.
4. **"The same nodes as Lean" is approximate**: LeanForth descends into closed nodes that hold a free
   variable, for its liveness check (3-4% more visits); Lean consults its cache more often than LeanForth.
   The free-variable rule stays.
5. **Native primitives and macros are trusted kernel code**: a false hit in the cons probe or the memo probe
   gives a different term, and the fuel step decides exhaustion. The sentence "none decides verdicts" is
   withdrawn. Native code keeps the owner's gate, and needs a C compiler where libcc is used.
6. **The walker slice's conditions for identical fuel**: the second child is charged only after the first
   child's subtree returns; the binder check stays before any child is charged; every per-leaf fail-closed
   test stays (unknown tag, well-formed bound variable, live free variable); the room numbers of a "full"
   diagnostic change once and are declared and tested; depth stays bounded by the heap frame stack.
7. **The decision rule** uses separate numbers, not one ns-per-visit figure: walk ns per visit without cons
   and memo, ns per cons, ns per memo operation, and hash probes per unit of fuel (2.4 on the decide slice
   today). Reachable ratios, until a prototype shows more (estimates): plain colon words 8-12 times Lean,
   with macros 6-9, with native primitives 4-6. All five slices end near 450-500 s (13-16 times Lean).
8. **Order and grouping**: first a throwaway prototype of instantiation in a scratch copy, never merged
   (lean walker; the memo cut as one reset with a stored hash; the leaf entry by a dense array), measured on
   the decide slice and one profiled run of Init; then two groups instead of five: the table work (slices 1
   and 4 with the memo cut), and the walker with universe substitution on it (slices 2 and 3). Slice 5 is
   dropped as a slice.

