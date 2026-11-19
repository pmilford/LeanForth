# Performance and algorithm scan (2026-11-18)

A measurement of where LeanForth's time and memory go on real runs, and of which
algorithms are wrong for the sizes they meet. Branch `perf-scan` from `s2-finish-2`
(`cb12814d`); no tracked source file was changed. Measured 2026-11-17 22:30–23:15 on the
shared 10-core WSL2 machine with Gforth 1.0.0 (`gforth-fast` unless said) while other
agents ran: load average 4.4 to 13, so **wall times are noisy and counts are the evidence**.
Raw outputs, the commands' tools and the counter patches are in
[measurements/perf-scan-2026-11-18/](measurements/perf-scan-2026-11-18/) (list under
[Commands](#commands)). Estimates are marked *(estimate)*.

## For the owner: where the time goes, and the five changes that pay most

**A `.lf` check against Init through the snapshot (the 70–100 s showcase run) is 82% one
avoidable cost.** The run measured 82–91 s (86 s under the profiler; the showcase recorded
71–102 s). A sampling profiler of the Forth return stack (agent PERF1's tool, reused) put
**82%** of it in the front end's first instance query: before answering, it checks **all
2,938 instances** of Init's elaboration data, decoding **3,260** library declarations into
the run. Every decoded name goes into the run's own name store, which in that mode (a)
re-audits **every** entry of the store on every call and (b) finds a name by **linear
search**. The store grows to 26,701 names; interning them visits **5.4 billion** entries
(counted). Without those two scans the whole check would take about **16 s**: loading the
snapshot 6 s, taking its 59,349 results 5.2 s, the feed 1.9 s, and the proof itself
**0.2 s** (the same holds for the induction proof `04-nested-ih.lf`: 0.25%).

**On Mathlib it would not finish in reasonable time.** Mathlib's elaboration data has
43,808 instances (15 times Init's) and 2,450 classes. The cost grows with the square of
the names decoded: about 4 hours *(estimate, from Init's 13 ns per entry visit and 15²
times the visits)*, on top of about 3 minutes to load the 2.3 GB snapshot *(estimate,
45 ms/MB as measured on Init's and a sixth of Mathlib's snapshots)*.

**Checking an export** (no text) is a flat profile: all of Init from the export took
724 s wall, 1,353 s CPU at `--jobs 2` on the loaded machine (PERF1 measured 988 s CPU on a
quieter one; Lean's own kernel checks Init in about 40 s on one thread). No declaration
dominates: the 20 costliest use 6.4% of the fuel, the costliest 1,000 use 42%. The cost is
the per-step overhead of layered checks, as PERF1 found.

**The test suites** spend most of their command-line time starting Gforth: `test-cli-4`
ran Gforth 358 times, median 0.38 s, 347 runs under 0.6 s; compiling `src/main.fs` from
source takes 0.21 s (`gforth-fast`) to 0.34 s (`gforth`) at every start. A precompiled
image starts in 0.05–0.08 s but today faults at once, because loading allocates heap
blocks whose addresses the image cannot keep.

**The engine**: the same `.lf` check took 299 s on `gforth` against 82–91 s on
`gforth-fast` (3.3 times; the tests use `gforth`).

| # | Change | What it saves | Confidence | Gate |
| --- | --- | --- | --- | --- |
| 1 | Name store: a hash index for finding names and an audit that checks only the entries added since the last audit (or run the text's names as a view over the library's input tier, as the kernel already does) | about 70 of 86 s of every `.lf` check on Init (5 times faster); hours on Mathlib | high: counted, and the profile without the scans | core read by the kernel: [kernel] for the audit |
| 2 | Instance-table check: per class at the first query of that class (or once per data file, recorded with its SHA-256), and the root index as a hash table | after #1, 1.3 s on Init; on Mathlib most of the remaining pass *(estimate: tens of seconds)* | medium | front end (untrusted), [parser] style review |
| 3 | A start-up image for `bin/leanforth` and the tests (`gforthmi`, with the heap set-up run at start) | 0.15–0.3 s per process; about 100 s of `test-cli-4`'s 144 s *(estimate)*; across `make test`, minutes of CPU | high for the per-start figure, medium for the totals | none for the image; `lib/context.fs` start-up hook needs the Forth review |
| 4 | Keep the library loaded: a server mode or a sectioned lazy load of the snapshot | Init: about 13 s per `.lf` check after #1 → under 1 s; Mathlib: about 3 minutes per check *(estimate)* | medium | [import]/[format] for a snapshot change; a server is new runtime design |
| 5 | Kernel validity checks once per pass instead of at every gate (`lf-env-current`: 58.8 million calls on 9,202 declarations) | PERF1 put them at about 15% of Init's checking CPU | medium | [kernel] (moves a fail-closed check) |

Numbers I am least sure of: the Mathlib extrapolations (no Mathlib `.lf` run was made
here), and the totals for #3 (only one test part was counted).

## Ranked findings

Cost is measured unless marked. "Size" is what the code meets on Init (and Mathlib where
known). Front-end, CLI and library items; the [kernel] and [import] items follow
separately. Slice: the plan row that should carry it.

| # | File:line | What | Size met | Cost measured | Fix (library to use) | Expected gain | Risk | Slice |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A1 | `src/core/names.fs:147-150, 291, 345, 355` | In the stored mode (no view) every `lf-name-str`/`lf-name-num` runs `lf-name-storage-valid?`, an audit of **all** entries; also called by `lf-cref-name-valid?` | 26,701 names, 207,781 audits, 2.99 billion entries visited (Init `.lf` run) | 69% of the `.lf` check (about 59 s) | keep a watermark: audit entries from the last audited count up, reset with the generation (the pattern of PERF1's level-scope audit) | about 59 s per `.lf` check | low (same verdicts; the audit still covers every entry once) | new row under 6.5.8, [kernel] |
| A2 | `src/core/names.fs:166-171` | `lf-name-find-num`/`-str`: linear search of every entry per intern | 169,915 finds, 2.44 billion entries visited | 12.4% (about 11 s); 22 µs per intern at 1,000 names, 332 µs at 16,000 (bench) | an `htab` index over the entries (as `cons.fs`/the tier's names do), or attach the run to the stage's tier (`lf-name-attach`) so names are shared | about 11 s; the term stays linear in names | low | with A1 |
| A3 | `src/front/instances.fs:343-347, 362-364` | The first query of a run checks every instance record (step 1: decode the declaration, telescope, `isClass?`), not only the queried class's | 2,938 instances, 3,260 declarations decoded (Init); 43,808 (Mathlib) | after A1-A2: 1.47% (1.3 s); before them it is what drives A1-A2 | check a class's records at its first query; or record a passed check per data SHA-256 | 1.3 s Init; Mathlib *(estimate)* 20+ s | low: Lean does no such check; it is LeanForth's own fail-closed check of the data, kept | FE1e3 follow-up; on branch `mf2-dt` (2026-11-18, tested alone, not integrated): fixed (MF2+DT) |
| A4 | `src/front/instances.fs:321-323` | `it-root-index`: linear scan of the roots for every instance value | 2,938 × up to 290 (Init); 43,808 × 2,450 = 1.07·10⁸ key compares (Mathlib) *(estimate of compares)* | not visible on Init | `memo` keyed by the root key | seconds on Mathlib *(estimate)* | low | with A3; on branch `mf2-dt` (2026-11-18, tested alone, not integrated): fixed (MF2+DT) |
| A5 | `src/front/instances.fs:379-385` | Discrimination-tree children as linked lists: a find walks all siblings, an insert walks to the last | children per node: up to the instances of one class | not visible on Init | sorted child array with `lower-bound` (Lean's binary search), or `memo` keyed (node, key) | Mathlib-size classes *(estimate)* | low | FE1e3 follow-up; on branch `mf2-dt` (2026-11-18, tested alone, not integrated): fixed (MF2+DT) |
| A6 | `src/front/synth.fs:271-278, 597-605` | The instance-search cache and the generator table are searched linearly with `lf-meta-eqv` (Lean: hash maps) | entries per search: small on Init proofs | not visible (proof work is 0.2 s) | `memo` keyed by the hash-consed key term, `lf-meta-eqv` only on a hash match | quadratic in search size on large proofs *(estimate)* | low | S-slice of the elaborator |
| A7 | `src/front/infer.fs`, `whnf.fs`, `defeq.fs` | No Meta caches (inferType, whnf, isDefEq), by design (S2_INTERFACE.md:119) | — | 0.25% on the Init proofs | port Lean's caches on `memo` when proofs grow | none today | medium (cache keys must be Lean's) | later S-slice |
| A8 | `src/author/build.fs:47-49, 118-120, 159-161` | The authoring words find an equal term, level or reference by scanning the whole store per new node | the store, which includes decoded library terms in a `.lf` run | 0 samples in the measured runs | `lf-term-cons` (terms are hash-consed, `core/terms.fs:867`), `memo` for levels and references | quadratic in the authored text *(estimate)* | low | 8.2.1 follow-up |
| A9 | `src/cli/print.fs:93` | `print` finds a declaration by name with a linear scan | 59,349 (Init), 729,263 (Mathlib) | once per command | `stage-find`/the input's name chain | < 1 s | low | — |
| A10 | `bin/leanforth:166`, `src/main.fs` | Every run compiles all of `src/main.fs` (about 70,000 lines) | 358 runs in `test-cli-4` | 0.21 s (`gforth-fast`), 0.28–0.34 s (`gforth`) per start; image 0.05–0.08 s | `gforthmi` image (needs `-m 64M`), with the context set-up and other load-time `ALLOCATE`s moved to a start-up word | about 0.2–0.3 s per process | medium: the image faults today (THROW -9) | 9.4.6 (testing) |
| A11 | `tests/front/check_s2.py`, `tests/cli/run_group.py` | End-to-end tests re-check the same slice exports in every process, on the checking engine | about 25 runs of 1.3 s (`gforth-fast`) / 2.75 s (`gforth`) each | `test-front-e2e` 123 s, `test-cli-4` 125 s in the last push | one snapshot of each slice per test run, then `--snapshot`; or many files per process | half of those targets *(estimate)* | low | 9.4.6 |
| A12 | `src/lib/sort.fs:86` | Insertion up to 32 records: 246 ns/element at 32 against 188 at 33 (merge) | lists of ≤32 (level normalization, mdata keys) | bench | a cut-over near 16–24, or binary insertion (plan 9.4.8i) | small | low (fuel of the kernel's caller must be compared) | 9.4.8i |

**[kernel] and [import] items** (each is a review-gate change; none skips a check):

| # | File:line | What | Size met | Cost measured | Fix | Expected gain | Gate |
| --- | --- | --- | --- | --- | --- | --- | --- |
| K1 | `src/kernel/environment.fs:461` | `lf-env-current` re-validates the environment and the five input stores at every cache gate, memo gate and lookup | 58.8 million calls on 9,202 declarations (6,392 per declaration) | PERF1: about 15% of Init's checking CPU; here `between?`/`store-count-valid?` lead the snapshot import too | validate once where a pass starts and when a store changes (PERF1's proposal) | about 15% of checking CPU | [kernel] |
| K2 | `src/cli/check-run.fs` (`ck-import-pass`) → `src/kernel/env-import.fs` | Taking the snapshot's results: validity checks per result | 59,349 (Init), 729,263 (Mathlib) | 5.2 s (Init, 88 µs a result); 66.7 s (Mathlib, recorded) | as K1, per result | most of 5 s / 60 s | [kernel] |
| K3 | `src/kernel/caches.fs:337-341` | Cache hit rates on p1m: infer 35%, infer-only 60%, **whnf_core 3.7%** (184,213 of 4.92 million), whnf 63%, unfold 92%, success 9%, failure 2%; replace memo 13% (3.77 of 29.0 million) | as counted | each miss costs a hash, a probe and an insert | these are Lean's caches and must stay; measure what a miss costs and whether the whnf_core insert can be skipped where Lean's would never be read | unknown | [kernel] |
| K4 | `src/import/snapshot-tier.fs:482-486` | Loading a snapshot re-interns every record into rebuilt hash tables (`htab@` 24.5% of the tier load) and hashes the whole file (SHA-256, 27%) | 133 MB (Init), 2.3 GB (Mathlib) | 5.5 s of the Init load; Mathlib *(estimate)* 100 s | save the tables' images in their own sections and check them, or map sections lazily; keep the SHA-256 | about half the load | [import], [format] |
| K5 | `src/import/ndjson.fs`, `feed.fs` | Reading and feeding an export run on one thread | Mathlib 315 s + 228 s (recorded, d789e45f) | 543 s, 6.4% of the 8,504 s run at 8 workers; it caps the speed-up of more workers | PERF1's fast path for `{"app":...}` lines (about −25% of the stage); feed in parallel | about 80 s now, more with more workers | [import] |
| K6 | `src/core/terms.fs:867` (hash-consing) | 38.1 million `lf-term-cons`, 231.3 million `htab-find` with 1.19 compares each (p1m) | as counted | probes are short; the cost is memory latency (PERF1: `u32@` 6.5% exclusive) | none needed for the table; node size (plan 6.5.9) | — | [kernel] |

Not hot (counted on p1m, 9,202 declarations): `ALLOCATE` 390,495, `FREE` 390,364, `RESIZE`
18,118 calls (42 a declaration; 1.63 GB in all); the kernel's name store is in view mode
(no stored-mode audit or linear find ran); environment lookups by name follow the input's
name chain (`environment.fs:703-707`), not a scan.

## Phase breakdowns

**(a) `check` of one `.lf` theorem against Init through the snapshot** (`s1-rfl.lf`; the
resource report and 8,613 samples at 10 ms; `lf-check-profile.txt`):

| Phase | Seconds (of 86) | Share |
| --- | ---: | ---: |
| Loading main.fs | 0.2 | 0.2% |
| Snapshot read and check (`ck-snapshot-import`; its tier load 5.5 s, of which SHA-256 about 1.5 s and hash-table probes 1.3 s) | 6.1 | 7.1% |
| Feed | 1.9 | 2.2% |
| Elaboration data read and checked | 0.2 | 0.2% |
| Instance-table pass: name-store audits | 59.5 | 69.2% |
| Instance-table pass: linear name finds | 10.7 | 12.4% |
| Instance-table pass: the rest (decoding, telescopes) | 1.3 | 1.5% |
| Elaboration, tactic and kernel check of the theorem | 0.2 | 0.2% |
| Taking the 59,349 snapshot results (`ck-import-pass`) | 5.2 | 6.1% |
| Output (59,350 verdict lines) | 0.2 | 0.2% |

Peak resident memory 650 MB. On `gforth`: stage 252.6 s, feed 5.0 s, check 19.5 s, 299 s
in all (`gforth-fast`: 76.7, 1.9, 6.1; 3.3, 2.6 and 3.2 times).

**(b) The same from the export** (`--env`): the 18 minutes at `--jobs 2` are a full check
of Init (below, 724 s wall) plus (a)'s text work; not re-run.

**(c) Init alone, kernel only** (`check --json --jobs 2`; `init-fuel.txt`): stage 25.0 s,
feed 4.4 s, check 693 s wall / 1,323 s CPU, 724 s in all, peak 800 MB; 59,349 accepted,
654.7 million fuel. Fuel by declaration: median 1,770, 90th percentile 16,707, 99th
167,576. The 20 costliest are `omega` proofs of `Array`/`Vector.extract` lemmas (4.38
million fuel at most) and use 6.4% of all fuel; declarations of 10⁴–10⁶ fuel use 76%. What
the checking spends on (PERF1's profile, which this build has not changed in kind):
replace passes 34%, universe substitution 22%, `whnf_core` beta 20%, validity checks
18.5%, hash-consing 17%, `htab-find` 16% (inclusive, overlapping). The JSON report has no
per-declaration time, only fuel: adding microseconds per declaration to it would make the
slowest-20 list a time list.

**Mathlib** (recorded, build `d789e45f`, `--jobs 8`): stage 315 s, feed 228 s, check
7,827 s wall / 57,695 s CPU, 8,504 s in all, 23.1 GB peak. Snapshot reload with the export
(`b74a04d`): 424 s, 9.7 GB; loading a snapshot of a sixth of Mathlib (375 MB) without an
export: 28.6 s.

**(d) The test suites** (the last push, `dfa21ac6`, per-command times of
`scripts/timed.sh`; `push-targets.txt`): the slowest are `coverage-check` (483 s, one
command: all of `make test` under the coverage engine), `test-cli-4` 125 s, `test-front-e2e`
123 s (`check_s2.py` 105 s), `reference-program-verify-refuted` 113 s, `program-clamp-record`
112 s, `reference-program-verify-clamp` 108 s, `test-cli-1` 93 s, `test-cli-3` 90 s,
`test-core` 75 s (135 commands), `check-doc-examples` 70 s. Why: the `test-cli` parts and
`test-front-e2e` are hundreds of short Gforth processes, each compiling `main.fs` (A10)
and re-checking a small export (A11), on the checking engine; the program-verify and clamp
targets are each one LeanForth check of 4,277–4,295 declarations (about 90 s), which
TESTING_STRATEGY.md says no cache may replace. `test-cli-4` measured here: 358 Gforth runs,
143.7 s summed wall (`test-cli-4-runs.txt`).

## Snapshot and load path, engine and build settings

- **Is the per-`.lf` cost fixed load cost?** On Init today, no: 82% is A1–A3. After them
  the fixed part is about 13 s (snapshot 6.1 s, results 5.2 s, feed 1.9 s). A server
  mode that keeps the library loaded would make a `.lf` check about the proof's own
  0.2–0.3 s plus the instance pass's first query; a sectioned lazy load (map the tier,
  keep the hash tables in the file) would save roughly half of the 6.1 s (K4) *(estimate)*.
  On Mathlib the fixed part is about 3 minutes *(estimate)*, so keeping it loaded matters
  most there.
- **Start-up**: compiling `main.fs` costs 0.21 s on `gforth-fast` and 0.28–0.34 s on
  `gforth`; `gforthmi` builds a 14 MB image (needs `-m 64M`: the default dictionary
  overflows while saving) that starts in 0.05–0.08 s, but `cli-main` then fails with THROW
  -9 because heap blocks allocated while loading (context records) are not in the image.
  `bin/leanforth`'s own work (`git rev-parse`, `git diff --quiet`) is within the 0.21 s of
  `leanforth version`. Dictionary and stack sizes are Gforth's defaults; nothing large
  lives in the dictionary, and the walks keep their work on heap stacks, so no setting is
  needed.
- **Engines**: `gforth-fast` is 2.6–3.3 times faster per phase than `gforth` on the `.lf`
  check (above) and 2.1 times on a slice check (1.31 s against 2.75 s).

## Library profile status

The five parts (AGENTS.md: algorithm, genericity, cost as inputs grow, measured speed small
and large, callers with real sizes). The library audit of 2026-11-13
([forth-reviews/2026-11-13-library-audit.md](forth-reviews/2026-11-13-library-audit.md))
found none complete; since then FORTH_LIBRARY.md added full sections for `memo` and
`pqueue` and the callers of `sort`. Complete now: **memo, pqueue, sort, cons** (4 of 36);
partial: bignum, bytes, context, frame, htab, json, pools, sha256, task (speed or callers
missing); missing most parts: bigint, bounds, hash32, json-write, node, runs, sections,
slab, store, store-columns, text-rule, text-run, u32, walk, xt-table, and the files added
after the audit (bits, blocks, decimal) were not checked part by part; not applicable:
lib, module, outcome, portability.

Measured now (`bench.txt`; same machine, loaded):

| Library | Small | Large | Recorded |
| --- | --- | --- | --- |
| memo (htab + slab), put then find | 170 ns an operation at 1,000 keys | 403 ns at 1,000,000 | 0.12 µs an operation over 3.2 million mixed operations (2026-11-13) |
| sort, cells by value | 132–144 ns an element at 16; 246–270 at 32; 186–188 at 33 | 563–585 ns at 100,000; 685–692 at 1,000,000 | 100,000 only |
| sha256 | 2.43 µs for a 64-byte message (two blocks) | — | large inputs only |
| name store, stored mode (not a library; for A1-A2) | 22 µs an intern at 1,000 names | 332 µs at 16,000 | — |

Hash tables in use are healthy: 1.19 occupied slots compared per `htab-find` over 231
million finds (p1m). Callers' real sizes for the remaining libraries are plan 9.4.8g's
work; the counter patch used here (`tools/patch.py`) is a template for it.

**Update (2026-11-18, branch `lib-tidy-2`):** every library now has the five parts in
[FORTH_LIBRARY.md, "Measured profiles"](FORTH_LIBRARY.md#measured-profiles-2026-11-18):
speed at a small and a large size from `make lib-bench` (both engines), and the sizes
LeanForth passes each library on a check of `Init`, counted by
[the lib-profiles patch](measurements/lib-profiles-2026-11-18/).

## PROFILING.md: what still works

`scripts/profile-existing.sh 1` (`make profile-existing`'s script) still runs: 48 matching
rows, the same output SHA-256 (`844fc236…`), Lean 0.81 s, Forth 0.22 s; with today's
`main.fs` the Forth figure is almost all start-up, so it measures nothing about checking.
`make profile-history` runs the same workload. For checking speed use instead: the
`--resources` report (phases, peak memory, fuel), PERF1's sampling profiler
(`tools/sample.py` with `tools/symdump.fs`, no change to the source), counters on a scratch
copy (`tools/patch.py`), and `scripts/coverage.py -- COMMAND` for per-block run counts.

## Commands

From the worktree root, `G=.tools/gforth/bin/gforth-fast` of the main checkout, `W` its
`.claude/work`; all under `ulimit -u 500`, at most three cores in use.

- (a) `GFORTH=$G bin/leanforth check --resources --snapshot $W/showcase/init.lfsnap --elab-data $W/S1DONE/init.elab.ndjson tests/front/s1-rfl.lf` (and `04-nested-ih.lf`; and with `GFORTH=.../gforth`);
  profiled: `PROF_SYMS=... python3 tools/sample.py OUT.prof 0.01 -- $G src/main.fs tools/symdump.fs -e cli-main check ...`;
  summaries by `tools/summarise.sh` (`inc.py`, `excl.py`, `kids.py`, `callers.py`, `analyze.py`).
- counters: copy `src` and `bin` to `build/perf/inst`, add `tools/zzcnt.fs` to its `src/lib`,
  `PATCH_EXTRA=tools/patch-kernel.py python3 tools/patch.py build/perf/inst`, run its `bin/leanforth`.
- (c) `GFORTH=$G nice -n 5 bin/leanforth check --json --jobs 2 $W/S1DONE/init.ndjson`; p1m:
  `build/perf/inst/bin/leanforth check --no-manifest --resources --jobs 1 $W/IM/p1m.ndjson`.
- (d) `GTIME_ENGINE=.../gforth GTIME_LOG=... GFORTH=tools/gtime.sh python3 tests/cli/run_group.py 4`;
  the push's per-command times from `$W/ci/dfa21ac6-timing.txt` (`tools/summarise2.py`).
- start-up: `$G src/main.fs -e bye`; image: `gforthmi lf.fi -m 64M src/main.fs`, then `$G -i lf.fi -e bye`.
- benches: `$G src/main.fs tools/bench.fs -e "N memo-case bye"` (also `sha-case`, `names-case`),
  `$G src/main.fs tools/sortbench.fs -e bye`, `tools/sortcheck.fs`.
- `ELAN_HOME=... LEAN=... GFORTH=... bash scripts/profile-existing.sh 1`.

Not run: the full Mathlib check and a Mathlib `.lf` check (hours; recorded figures used),
`make coverage` (the per-block counts were not needed once the sampler and counters
located the costs), timings on an idle machine.
