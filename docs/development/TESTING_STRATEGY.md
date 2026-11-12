# Testing strategy

LeanForth aims for deliberately extensive tests across units, interfaces,
functional behavior and regressions. Coverage percentages are useful for
finding gaps, but cannot exceed 100% and do not establish correctness. Review
test quality, requirements coverage and adversarial cases as well as metrics.

## Forth test harness

Gforth 1.0 ships `test/ttester.fs`, derived from the established Forth test
suite. Its `T{ code -> expected }T` form checks both stack depth and contents;
it also supports floating-point cases. Investigate using it as the common
unit-test vocabulary instead of inventing a new framework. The installed Gforth
1.0 has a copy, but availability on other hosts and license terms must be
checked before depending on or distributing it. The bundled file requires its
copyright notice to remain if redistributed.

Printing an error alone is insufficient for CI. The test adapter assigns the
tester's `ERROR-XT` to print the assertion and throw, so the process fails on
the first error. `make test-harness` checks a passing test and two deliberate
failures. This adapter and the core tests pass locally with Gforth 1.0.0 and
the Ubuntu 24.04 Gforth 0.7.3 package extracted into a temporary directory.
CI runs `make test` on Ubuntu's Gforth package and `make check`, which adds
every pinned-Lean comparison, on pinned Gforth 1.0.0 and Lean 4.35.0. Both are
the same x86-64 Linux platform; test other hosts before claiming support.

## Layers

- Unit: each word's stack effect, expected behavior, edge cases and failure
  paths, including malformed data and resource limits.
- Interface: API and serialization schemas, stack contracts, error codes,
  deterministic behavior and supported/unsupported version boundaries.
- Functional: real end-to-end theorem and executable-program workflows once
  implemented, with correct proof artifacts and explicit runtime assumptions.
- Regression: preserve every fixed bug and previously observed discrepancy as
  a reproducible test; distinguish unsupported behavior from rejection.
- Differential and adversarial: compare supported terms with pinned Lean,
  test both false acceptance and false rejection, fuzz malformed inputs, and
  plant faults (`make mutants`, below) to check that the tests catch them.
- Portability: run portable tests on supported Forth hosts; record exact host
  versions and separate host assumptions from tested LeanForth behavior.

CI must fail closed on missing prerequisites, crashes, timeouts, malformed
inputs and failed assertions. Coverage tooling, additional packages and test
fixtures must be assessed for portability and license compatibility before
adoption. No test suite replaces human review of kernel rules or proof of
compiler and runtime correctness.

## Fail-closed safeguards (added 2026-11-02)

- **No proof by `sorry`.** Every Lean invocation in the test scripts passes
  `-DwarningAsError=true`, so `sorry` and other warnings fail the run.
  `tests/reference/sorry-must-fail.lean` is a false theorem proved with
  `sorry`; `make reference` requires Lean to reject it.
- **Static Lean guard.** `make check-lean-sources` (part of `make test`, no
  Lean needed) fails if a Lean test file uses `sorry`, `admit`,
  `native_decide`, a `warningAsError` override or an `axiom` outside the
  allowlist in `scripts/check-lean-sources.py`, or if a script runs Lean on a
  file without the strict flag.
- **Timeouts.** Every Make recipe runs its command under
  `timeout $(TEST_TIMEOUT)` (default 1,800 s; 600 s until 2026-11-10, when loaded machines hit it), and each CI job has a
  `timeout-minutes` limit, so a looping test fails instead of hanging.
- **Size guards.** Differential scripts check both tables' line counts and
  exit on mismatch before comparing them.
- **Documentation links.** `make check-docs` fails on broken links.
- **Gforth exit status.** Gforth 1.0 exits 0 after an uncaught error when
  its error report itself fails: with `BASE` 0 the report divides by `BASE`
  and ends in "Division by zero" (Gforth 0.7.3 exits 1). A test that
  crashed after `0 base !` therefore passed silently, and a planted fault
  survived. The Makefile now overrides `GFORTH` with
  `scripts/gforth-strict.sh`, which runs the real Gforth (kept in
  `LEANFORTH_GFORTH`; `GFORTH=...` on the make command line still names
  it) and exits 1 when Gforth exited 0 but its stderr holds a `Backtrace:`
  line or "uncaught exception". `scripts/mutants.py` wraps Gforth the same
  way, and the fault `base-zero-crash` in `tests/mutants/faults.toml`
  checks it. Stderr is replayed when the run ends, not live. Probes:
  `.claude/work/TS/p1.fs` to `p3.fs` (local, gitignored). Limit: it
  recognises Gforth's error report text; a run that ends early without
  an error report (for example a stray `bye`) is not caught.
  `scripts/gforth-fast` beside it runs the real `gforth-fast` through the
  same check, for scripts that look for `gforth-fast` beside `$GFORTH`
  (`tests/core/compact-init.sh`). Without it that test fell back to plain
  Gforth and timed out on CI once (run 41794140859, 600 s limit,
  2026-11-04).
  Both wrappers refuse to treat a wrapper of `scripts/` as the real Gforth
  and refuse to nest more than three deep, and the Makefile replaces a
  `GFORTH` that names a wrapper with the real Gforth: on 2026-11-04 a
  `GFORTH` naming the wrapper was passed on as `LEANFORTH_GFORTH`, the
  wrapper called itself, and about a thousand copies exhausted the
  machine's memory (39 GB and 16 GB swap) and crashed it.

The 2026-11-02 coverage review and its open items are recorded in
[the test coverage review](TEST_COVERAGE_REVIEW.md).

## Running the suites: parallel jobs and the Lean cache

Added 2026-11-03, when `make test` had grown to 36 s and `make check` to
345 s run one target at a time, and agents ran them several times per task.

**Parallel jobs.** The Makefile runs `JOBS` targets at a time (default 8,
unless `-j` is given; `JOBS=1` or `-j1` runs one at a time) and prints each
target's output in one piece (`--output-sync=target`, GNU make 4.0 or
later). Every target writes only into temporary folders of its own
(`mktemp -d`, Python's `tempfile`), never into a fixed path or the tree: a
`make -j8 check` of the unchanged suite (commit `8148f3f`) passed and left
no file of the tree changed. `tests/core/compact-verify.sh` runs its two
independent Gforth runs side by side. A failing target stops make from
starting others; make waits for the running ones, prints
`make: *** [Makefile:LINE: TARGET] Error N` naming the target, and exits
with status 2. CI runs both suites with the default 8 jobs.

**The Lean cache.** Pinned Lean's verdicts are deterministic, and most of
`make check`'s time was Lean re-checking unchanged files. Unless `LEAN_CACHE=0`, the
recipes get `LEAN` set to `scripts/lean-cache.py` and `LEANEXPORT` to
`scripts/leanexport-cache.py`, stand-ins that replay a stored run when
every input of it is unchanged and run the real tool otherwise:

- What is cached: a Lean call `lean [-D…]… [-o OUT.olean] [--run] FILE.lean`
  with nothing after the file (its output, exit status and `.olean`), and
  any `leanexport` call (its output and status). Only Lean's or the
  exporter's own run is skipped: the Forth side of every comparison, and
  every script that reads Lean's output, always runs.
- The key is the SHA-256 of everything such a call reads: the toolchain
  (SHA-256 of the `lean` binary and its shared libraries, `lean --githash`,
  the name and size of every file of its library folder; recomputed when
  the binary, a shared library or the library folder changes on disk, so a
  file edited in place deep inside the library is not noticed: reinstall a
  toolchain, never edit it), the options in order, the source text, the
  main module's name (Lean 4.35 derives it from the source's path relative
  to the working folder, and it changes the `.olean`), the SHA-256 of every
  file of each `LEAN_PATH` folder outside the toolchain, every
  other `LEAN_*` variable, the exporter's arguments, and whether stdout and
  stderr are one file. The paths Lean echoes (the source as given, the `-o`
  path, `LEAN_PATH`) are stored as placeholders and restored on replay, so a
  file checked from a new temporary folder still hits.
- Never cached, so always run: `--version`, `--githash`, `--print-prefix`,
  `--run` with program arguments (`tests/reference/program-ir-run.lean`
  reads its cases from files), any other argument, a source whose text
  names an IO input (files, stdin, the environment, processes, clocks,
  random numbers; `universe-scope-terms.lean` reads the clock), any call
  that imports an `.olean` the cache did not see compiled by a cacheable
  call (so an IO input cannot hide in an imported module), exit statuses
  other than 0 and 1, and output that reports exhausted memory or stack.
- `LEAN_CACHE=0` runs every Lean and exporter call and stores nothing; it
  is the default when the `CI` variable is set, and `.github/workflows/ci.yml`
  passes it explicitly, so CI never replays a cached run. `LEAN_CACHE=verify`
  runs every call and fails (status 125) where a stored entry's status or
  output differs from the new run. On 2026-11-03 `make check
  LEAN_CACHE=verify` over a full cache reran the 294 cached calls: 292 gave
  the same status and output as stored, none differed, and two missed:
  they import the `.olean` of `tests/reference/stack-clamp.lean`, which Lean
  4.35 writes with other bytes on every compile (four compiles, four
  files; same messages and status). So a replayed `.olean` is one Lean
  wrote for the same inputs, not always the bytes a new run would write;
  every call that imports it is keyed by the bytes replayed, and verify
  mode only logs a differing `.olean`. The other `.olean` files measured
  (`program-contracts`, `composition`, `checked-add`) were identical.
- The cache is shared by every worktree of a clone: the main checkout's
  `.claude/work/lean-cache/` (git ignores it; set `LEAN_CACHE_DIR` for
  another place). Entries are written to a temporary folder and renamed
  into place, so parallel jobs and worktrees can share it; the scripts
  delete nothing but their own temporary folders. After one `make check` it
  held 223 entries in 361 MB (344 MiB), nearly all of it the export of
  Lean's `Init` (346 MB on its own, written once per toolchain). Entries of changed inputs
  stay until the folder is deleted (by name) to empty it. `LEANFORTH_LEAN_CACHE_LOG=FILE` logs every call as hit, miss
  or run, with the reason.
- Trust: the cache is local data, trusted like the working tree. A local
  pass with the cache replays Lean's earlier verdicts on identical inputs;
  CI's run without the cache is the record. Time reports inside a replayed
  run (the SHA-256 specification's "proved in N s") show the replay's time.
- Tests: `make test-lean-cache` (in `make test`) runs the stand-ins on a
  fake toolchain: a repeated call is replayed without running the tool,
  with the same output, status and `.olean`, and a change to each input
  misses (source text, module name, option, imported `.olean`, toolchain
  binary and library, `LEAN_*` variable, exporter arguments); it checks
  what is never cached, `LEAN_CACHE=0`, verify mode (a changed output
  fails, a changed `.olean` is logged, the Makefile's own `LEAN_CACHE` and
  `LEAN_CACHE_DIR` do not change the key), restored paths, one stream's
  order, and that the Makefile uses the cache only without `LEAN_CACHE=0`
  and `CI`. Nine planted faults (`lc-*` in `tests/mutants/faults.toml`)
  are each caught by it.

**Timings.** Each target of `make check` run on its own, one after another,
on Gforth 1.0 and Lean 4.35.0 (10 cores, other work on the machine; load
average 1–8). *Before*: commit `8148f3f`, before these changes. *No cache*:
`LEAN_CACHE=0`, as CI runs. *Cached*: every Lean and exporter run replayed.

| Target | Suite | Before (s) | No cache (s) | Cached (s) |
| --- | --- | ---: | ---: | ---: |
| `check-docs` | test | 0.1 | 0.1 | 0.1 |
| `check-lean-sources` | test | 0.1 | 0.1 | 0.1 |
| `check-portable-forth` | test | 0.7 | 0.8 | 0.8 |
| `smoke` | test | 1.5 | 1.6 | 1.8 |
| `test-harness` | test | 0.0 | 0.0 | 0.0 |
| `test-lib` | test | 0.8 | 0.8 | 0.9 |
| `test-core` | test | 5.9 | 6.2 | 6.7 |
| `test-composition-fixture` | test | 4.4 | 4.7 | 5.3 |
| `test-program` | test | 0.0 | 0.0 | 0.0 |
| `test-present` | test | 0.3 | 0.3 | 0.3 (6 since plan task 6.2.0: `print-deep.fs` prints terms 10,000 deep) |
| `check-doc-examples` | test | 1.5 | 1.6 | 1.8 |
| `test-program-ir` | test | 0.4 | 0.4 | 0.5 |
| `test-program-ir-run` | test | 0.4 | 0.4 | 0.4 |
| `test-environment` | test | 3.2 | 3.4 | 3.6 |
| `test-run-records` | test | 3.1 | 3.4 | 3.7 |
| `test-bignum` | test | 4.5 | 4.7 | 5.1 |
| `test-sha256` | test | 1.5 | 1.6 | 1.8 |
| `test-manifest` | test | 0.2 | 0.2 | 0.2 |
| `test-author` | test | 1.0 | 1.0 | 1.1 |
| `test-mutants` | test | 3.2 | 3.2 | 3.2 |
| `test-reexport` | test | 1.0 | 1.0 | 1.2 |
| `test-compact` | test | 0.9 | 0.9 | 0.9 |
| `test-stage` | test | 1.0 | 0.9 | 0.9 |
| `test-doc-examples-lean` | check | 8.4 | 9.0 | 2.7 |
| `reference` | check | 39.4 | 46.3 | 1.6 |
| `reference-export` | check | 2.8 | 3.1 | 0.5 |
| `reference-first-checker` | check | 1.9 | 2.3 | 0.3 |
| `reference-binder-domains` | check | 0.9 | 1.0 | 0.1 |
| `test-name-differential` | check | 0.7 | 0.9 | 0.1 |
| `test-level-differential` | check | 0.8 | 0.9 | 0.2 |
| `test-level-assignment-differential` | check | 0.7 | 0.8 | 0.2 |
| `test-level-compare-differential` | check | 2.4 | 2.8 | 0.3 |
| `test-level-substitute-differential` | check | 0.8 | 1.0 | 0.2 |
| `test-mixed-shift-differential` | check | 0.8 | 1.0 | 0.2 |
| `test-mixed-instantiate-differential` | check | 0.8 | 0.9 | 0.1 |
| `test-mixed-beta-differential` | check | 0.8 | 1.0 | 0.1 |
| `test-mixed-convert-differential` | check | 0.8 | 1.0 | 0.2 |
| `test-mixed-level-substitute-differential` | check | 0.9 | 0.9 | 0.2 |
| `test-mixed-signature-differential` | check | 0.8 | 1.0 | 0.2 |
| `test-mixed-infer-differential` | check | 0.9 | 0.9 | 0.2 |
| `test-constant-term-scope-differential` | check | 0.9 | 0.9 | 0.2 |
| `test-mixed-shift-plain-differential` | check | 0.9 | 0.9 | 0.2 |
| `test-mixed-instantiate-plain-differential` | check | 0.8 | 1.0 | 0.2 |
| `test-mixed-beta-plain-differential` | check | 0.9 | 1.0 | 0.2 |
| `test-mixed-convert-plain-differential` | check | 0.9 | 1.0 | 0.2 |
| `test-mixed-infer-plain-differential` | check | 3.8 | 4.1 | 0.3 |
| `test-mixed-definition-differential` | check | 0.9 | 1.0 | 0.2 |
| `test-mixed-level-substitute-plain-differential` | check | 0.9 | 1.0 | 0.2 |
| `test-mixed-infer-constant-differential` | check | 0.8 | 1.0 | 0.2 |
| `test-export-signature-differential` | check | 1.2 | 1.3 | 0.4 |
| `test-export-specialization-differential` | check | 1.4 | 1.6 | 0.6 |
| `test-first-checker-differential` | check | 1.9 | 2.3 | 0.3 |
| `test-binder-domains-differential` | check | 3.5 | 4.0 | 0.3 |
| `test-universe-scope-differential` | check | 2.6 | 3.0 | 1.2 |
| `test-depth-differential`, `test-depth-fed-differential` (plan task 6.2.0, 2026-11-04; listed first in `check`) | check | — | about 40 each | about 40 each |
| `test-depth-deep-differential` (in `check` since 2026-11-11) | — | — | about 9 (770 until the depth work) | about 9 |
| `test-program-differential` | check | 0.8 | 0.9 | 0.1 |
| `test-program-stack-differential` | check | 1.2 | 1.5 | 0.2 |
| `test-program-values-differential` | check | 0.9 | 1.1 | 0.2 |
| `test-program-depth-differential` | check | 0.8 | 0.9 | 0.2 |
| `test-example-reference-differential` | check | 1.6 | 1.9 | 0.2 |
| `test-add-reference-differential` | check | 1.7 | 2.0 | 0.2 |
| `test-abs-reference-differential` | check | 1.4 | 1.9 | 0.2 |
| `test-factorial-reference-differential` | check | 1.5 | 2.0 | 0.2 |
| `test-gcd-reference-differential` | check | 1.5 | 1.8 | 0.2 |
| `test-range-64-differential` | check | 1.5 | 1.9 | 0.2 |
| `test-memory-reference-differential` | check | 1.2 | 1.5 | 0.2 |
| `test-memory-frame-differential` | check | 2.3 | 2.8 | 0.3 |
| `test-printer-differential` | check | 2.6 | 3.2 | 0.4 |
| `reference-program-ir` | check | 5.2 | 6.3 | 0.1 |
| `reference-program-ir-run` | check | 29.9 | 29.4 | 9.9 |
| `reference-bignum` | check | 10.9 | 9.9 | 3.4 |
| `reference-manifest` | check | 1.1 | 0.8 | 0.3 |
| `reference-author` | check | 69.4 | 60.6 | 13.2 |
| `reference-reexport` | check | 2.0 | 1.8 | 0.5 |
| `reference-compact-init` | check | 78.5 | 57.3 | 40.7 |
| `mutants-check` | check | 0.1 | 0.0 | 0.0 |
| `test-compact-faults` | check | 7.5 | 6.9 | 6.1 |
| `test-lean-cache` | test | — | 2.6 | 2.6 |
| sum, every target of make test | | 36 | 40 | 43 |
| sum, every target of make check | | 345 | 335 | 132 |

`reference-compact-init` fell from 78.5 s to 57.3 s by running
`compact-verify.sh`'s two Gforth runs side by side, and to 40.7 s with
the export of `Init` replayed; staging it into the compact store and
writing its manifest always run. What remains of `reference-program-ir-run`
(9.9 s) is mostly `program-ir-run.lean`, which reads its cases from files
and is never cached; of `reference-author` (13.2 s), the authoring words
and planted faults. The suites as a whole (wall time; `make test` has no
Lean runs, so the cache does not change it):

| Command (wall time, 2026-11-03) | Before | After |
| --- | ---: | ---: |
| `make test`, one target at a time (`JOBS=1`) | 36.2 s | 40.5 s |
| `make test` (8 jobs, the default) | — | 7.9–8.5 s |
| `make check`, one target at a time, without the cache (sum of the table) | 345 s | 335 s |
| `make -j8 check` | 97.0 s | — |
| `make check LEAN_CACHE=0` (8 jobs; what CI runs) | — | 75.3 s |
| `make check`, empty cache (every run stored) | — | 68.7 s |
| `make check`, cache filled (every run replayed) | — | 43.4 s |

`make check` starts its slowest targets first (they are listed first in
the Makefile); before that change the same runs took 89.5 s without the
cache, 93.7 s with an empty one and 55.6 s with a full one. Each run
passed. The longest target, `reference-compact-init`, now bounds `make
check`.

**Measured again, 2026-11-11** (agents TT and TT2; per-target tables in
`.claude/work/TT/times.tsv` and `.claude/work/TT2/{nocache,warm}.tsv`, one
target at a time with `JOBS=1`; CPU is user plus system time of the target
and its children, which stays comparable when other agents load the machine).
The 99 targets and the 430 inductive cases are the same before and after.

- Cause of the slowdown. `tests/reference/inductive-expected.lean` printed
  its 430 rows and 430 cases (11 MB) inside one `run_cmd`, that is as one
  Lean message, and Lean's handling of a message takes time quadratic in its
  size: 366 s for the run, of which the checking of all cases takes 3 s and
  the writing of the exports 16 s. Both `reference-inductive` and
  `test-inductive-table` ran that file, each 650-700 s CPU. Printing each row
  and each case as its own message (`logInfo`) gives the same output text in
  27 s; no file was split, as the cases were never the cost. The text of
  the file is part of the hygienic names in Lean's exports (module name
  hash and macro-scope counter), so the 27 check-block fixtures that hold
  such names were rewritten from Lean's own output (`inductive-table.py`
  checks all 353 fixtures against it). The file may not contain `IO.FS`,
  which the Lean cache treats as an input (hence `isolated`).
- Under `LEAN_CACHE=0` (CI), `make` now runs that Lean once: the target
  `inductive-expected-output` writes `build/inductive-expected.out` (ignored
  by git), which `reference-inductive` and `test-inductive-table` read
  through `INDUCTIVE_EXPECTED_OUT`; run alone, the two scripts still run
  Lean themselves.
- `make check` lists its slowest targets first (new order in the Makefile)
  and now includes `test-depth-deep-differential`, which takes 9 s since
  the depth work (it took about 770 s before); its 6 rows are 10,000-deep
  terms.
- Results. All targets one at a time without the cache: 3,940 s wall and
  3,187 s CPU (11-10, loaded machine) before, 670 s and 710 s after. With
  a filled cache: 441 s wall (about 385 s with the two inductive targets
  replayed: 1 s and 16 s) after. `make check LEAN_CACHE=0` (8 jobs): 171 s
  wall, 965 s CPU; `make check` with the cache filled: 93-114 s wall, 540 s
  CPU (a loaded machine; the time left is the Forth side). Largest
  targets now (no cache, seconds wall): `reference-author` 67,
  `reference` 61, `test-cli` 56, `reference-compact-init` 53,
  `reference-program-ir-run` 33, `reference-inductive` 29 (shares the Lean
  run with `test-inductive-table`, which takes 43 alone).
- Not changed: `reference-program-ir` (55 s CPU before) and
  `reference-program-ir-run` run many small Lean files whose text is
  hashed by receipts (`tests/program/ir_run_differential.py`); they stay
  whole. No checker change was found to have slowed a test.

**Testing while you work.** The inner loop is the focused test of what you
change; `make test` before each commit; `make check` once, at the end of a
task (and before pushing). Text for agent briefs:

> Testing: while you work, run only the focused tests of the files you
> change: the test file itself (`.tools/gforth/bin/gforth tests/core/names.fs
> </dev/null`), its module's target from the table in
> docs/development/TESTING_STRATEGY.md ("Testing while you work"), or
> `make test-changed` (every target of `make test` that uses a file changed
> since main). Run `make test` (about 8 s, 8 jobs) before each commit, and
> `make check` (about 45 s with the shared Lean cache, 75 s without) once
> at the end. `make check LEAN_CACHE=0` is what CI runs. Do not run
> several make commands at once: make already runs 8 jobs.

`make test-changed` and `make check-changed` (`scripts/changed-tests.py`;
`BASE=REF` for another base than `main`, `--why` lists each target's
reasons) run the targets that use a file changed since the merge base,
uncommitted and new files included. A target uses the files its recipe
names and, transitively, what those programs use: Forth `require` and
`include`, Python imports, and repository paths named in the code of
Forth, Python and shell files (not in comments or docstrings); Lean files
and data are used but not followed. A changed Forth source also selects
`smoke` and `check-portable-forth`, a changed Markdown file `check-docs`, a
changed Makefile everything. Most tests load `src/main.fs`, so a change to
a checker module still selects 25–40 of the 77 targets; a changed test, Lean
file, script or document selects a few (`tests/reference/clamp.lean`: 6,
`src/author/runner.fs`: 4, `tests/core/names.fs`: 1). It is a heuristic,
not a proof that the other targets are unaffected (a path built at run
time, as `scripts/export.sh` builds `export_manifest.py`'s, is not seen).

| You change | Focused targets |
| --- | --- |
| `src/lib/` | `test-lib`; `test-compact` (slab, htab, hash32, cons, pools), `test-bignum`, `test-sha256`, `test-environment` (store marks) |
| `src/core/` | `test-core`; `test-compact`, `test-stage` (compact store) |
| `src/kernel/` | `test-core`, `test-environment`, `test-check-block` (inductive blocks); the matching `test-*-differential`, `test-first-checker-differential` and `test-inductive-table` |
| `src/import/` | `test-core` (NDJSON reader, load), `test-manifest`, `test-stage`, `test-reexport`, `test-run-records`, `test-compact` |
| `src/program/` | `test-program`, `test-program-ir`, `test-program-ir-run` |
| `src/present/` | `test-present`; `test-printer-differential` |
| `src/author/` | `test-author`; `reference-author` |
| `tests/reference/*.lean` | the target that runs the file (`make check-changed` finds it) |
| `scripts/lean-cache.py`, the Makefile | `test-lean-cache`, then `make check` |
| `docs/` | `check-docs`, `check-doc-examples` |

## Re-running one root: the export slicer (`scripts/export-slice.py`)

A failing declaration of a library run is re-run in seconds, not hours, by
cutting the part of the export it needs (2026-11-11, untrusted tool):

```sh
python3 -I scripts/export-slice.py EXPORT NAME... > SLICE
bin/leanforth check --no-manifest SLICE
.claude/work/arena/official-435/.lake/build/bin/kernel SLICE   # Lean's checker
```

`SLICE` holds the named declarations and everything they need, in the
original order with the original header: every declaration whose constant
occurs, transitively, in a type or value; the whole inductive block of any
inductive type, constructor or recursor named; the names, levels and
expressions those use; and the declarations LeanForth looks up by name
itself (`lf-sch-builtins`: Nat, Bool, Char, List, String, Eq, Quot,
propext, Classical.choice, Quot.sound), when the export has them. Indices
are kept, so a slice has gaps, which both readers allow. Three sequential
passes, Python standard library only; about 13 bytes per expression and 12
per name in memory (Init: 22 s, 100 MB). It has no manifest. A NAME the
export does not declare is exit 2 with nothing written. `tests/cli/
test_leanforth.py` (class `Slice`) slices the small fixtures and checks the
slices. Measured 2026-11-11 on Init (five assorted theorems, 360 of 57,919
declarations): accepted by LeanForth and by Lean's official checker. A slice's
verdicts are those of its declarations only, with the same rules.

### Engine gate

`bin/leanforth` runs `check`, `replay` and `print` on `gforth-fast` by default
(owner, 2026-11-11); `make test` and `make check` keep using the checking
engine (`scripts/gforth-strict.sh` around `gforth`), and the tests set `GFORTH`,
so no test switches engines. `make engine-gate` is the evidence that the two
engines agree: it runs `check --no-manifest` on all of Lean's `Init` (with
`--jobs 8`) and on every Lean Kernel Arena test of the 435-test bundle, once
with the default engine and once with `--checked`, and compares the verdict
lines and exit codes (not times or memory). Exit 0 only if identical, 1 on a
difference. It takes about 15 minutes and is not part of `make check`. The
Init export and the arena tests are machine-local (not in the repository):
`ENGINE_GATE_INIT=FILE ENGINE_GATE_ARENA=DIR make engine-gate`
names them; the defaults are `.claude/work/IM/init.ndjson` and
`.claude/work/arena/tests435` of the main checkout. Output files are kept in
`.claude/work/engine-gate/` (git-ignored). Run it after a change that could
make the engines differ (memory-access width, stack depth, Gforth upgrades).

## Failure paths and allocation-failure injection (plan tasks 2.2.4, 1.4.6)

Added 2026-11-03. The first checker must fail closed wherever it runs out
of fuel or room, or a word throws: nothing that fails may be stored,
published, given a handle or printed as accepted.

**The hook.** `src/lib/store.fs` has one test-only hook. A program that
defines the word `store-fault-hooks` before the store library loads gets
`store-refuse? ( store -- flag )`, a `DEFER` that `store-open?` asks about
every allocation that would otherwise go ahead, in every store: the term,
level, name, reference and input stores of each context and the checked
environment's dependency pool (`store-new`, and the name table's
`store-open?` then `store-claim`). True refuses the allocation as if the
store were full, changing nothing; the word may also `THROW`. Without
`store-fault-hooks`, `store-open?` is compiled exactly as before: no
`DEFER`, no extra call, no cost. LeanForth never interprets its input as
Forth and `src/main.fs` never defines that word, so no input can turn the
hook on or reach it. `tests/support/alloc-fail.fs`, loaded before anything
else, defines it and makes the k-th allocation after `af-arm` (or
`af-arm-throw`) fail, counted across every store; only that one fails.

**The suite.** `tests/core/failure-paths.fs` (in `make test`, under a
second on either Gforth) runs check-declaration through the publisher on
the five pinned fixtures and on 18 cases in the first-checker driver's
text, most of them rows of `tests/core/check-declaration.fs`, that end
rejected, unknown, unsupported, invalid or full at each step. For
each case it records a baseline, then refuses allocation k for every k,
sweeps the fuel from 0 until the baseline returns, and throws at
allocation k for every k (each run in a new context, with a maker that
loads the same input into another one, so that the run goes on; and twice
with no maker, so that it stops). After every step it checks that only
that declaration's slot changed, that the dependency pool grew only by an
accepted declaration's dependencies (a failed publication takes its
entries back) and that every input store is back at its mark with the
input's fingerprint unchanged; after every run, that a slot is accepted
only where its baseline is and every slot it depended on is accepted now,
that the slot an injected failure reached is full (refused), invalid
(thrown) or, when the publisher failed, open and cleared with the run
stopped, that later slots keep their baseline outcome or become unknown
(K5) when an earlier one changed, that handles and printed verdicts agree
with each slot's outcome (an axiom bit planted in an accepted slot must
print), and that a refusal or fuel never spends a context while a `THROW`
in a check does. It also checks that the publisher's re-check publishes a
passed check with a false claim as invalid. About 4,500 injected runs.

It prints the outcomes reached per check step and fails unless they are
exactly these (2026-11-03):

| Step | Outcomes reached |
| --- | --- |
| 0 before a snapshot | invalid |
| 1 audit | invalid, exhausted, unsupported |
| 2 name (N2) | unknown, rejected, unsupported |
| 3 parameters (L3) | rejected |
| 4 declared type's type | invalid, exhausted, unknown, rejected, unsupported, full |
| 5 a Sort (S1) | unknown, rejected |
| 6 a proposition (S3) | exhausted, rejected |
| 7 value's type | invalid, exhausted, unknown, rejected, unsupported, full |
| 8 comparison (D1–D5) | invalid, exhausted, unknown, rejected |
| 9 every step done | ok, invalid (a failed publication) |

No run of these cases reaches the empty cells: steps 2, 3, 5 and 6
allocate nothing and steps 2 and 3 use no fuel; step 5 runs out of fuel
only in its search for a rejection, which then leaves it *unknown* (ADR
0011); a `THROW` can be injected only at an allocation; and step 8
allocates only in its search for a rejection, where a refused allocation
leaves the step *unknown* as well, not *full*: weaker than Lean's
rejection and than ADR 0008's *full*, never accepted.

**Planted faults.** `tests/core/failure_path_faults.py` (also in `make
test`, about 2 s) runs the suite in a temporary copy of the tree with one
fault planted at a time, and requires it to fail on each of nine: the
publisher marking a slot final before writing its record, a check accepted
before its comparison, a step's *full* turned into ok, the level store's
rollback and the pool's rollback after a failed publication forgotten, a
check that ends full finished ok, "axioms: none" printed without reading
the slot, the hook switched off, and a `THROW` in a check that no longer
spends its context. All nine are caught.

## Planted faults (`make mutants`)

A planted fault (a *mutant*) is a small deliberate bug: if no test fails
with it in place, the tests do not check what that code does. Reviews used
to plant faults in throwaway scripts that were then lost; `make mutants`
(plan task 1.4.2) keeps them as a checked-in list,
`tests/mutants/faults.toml`, run by `scripts/mutants.py`. Each entry names:

- `file`, the file it changes, and `old`, an exact text that must occur
  there exactly once, with `new`, its replacement;
- `test`, the shell command that must catch it (`$GFORTH` names the Gforth
  of the run), and `reason`, one line on what it breaks;
- optionally `equivalent`, why no test can tell it from the original, or
  `gap`, the missing test that would catch it; both are expected to survive;
- optionally `quick = true`, for the sample `make mutants-quick` runs.

The runner first checks every entry's `old` text: one that no longer
occurs exactly once is *stale* (the code changed under it), which fails
the run; re-target such a fault at the new code rather than deleting it.
Then it copies the tree's files (git's tracked and new files) into a new
temporary directory outside the tree, runs every distinct test once on the
unchanged copy (each must pass), and plants each fault in turn: it writes
the change, checks that the changed file still loads (a Forth module on its
own and silently, as `make smoke` requires; a Python file must parse; a
change that does not load would prove nothing and fails the run), runs the
test and restores the file. It reports each fault as caught or survived and
exits nonzero when a fault expected to be caught survives, a fault listed
as equivalent or as a gap is caught (correct the entry), or an entry is
stale. It never writes the working tree: it hashes every file of the tree
before and after the run and fails if anything changed, and
`make test-mutants` (part of `make test`) checks every verdict and exit
status on a small tree, and that the tree is untouched after each run.

| Target | What it runs |
| --- | --- |
| `make mutants` | every fault (about 25 s on Gforth 1.0; not part of `make test` or `make check`) |
| `make mutants-quick` | the faults marked `quick`, one or two per module |
| `make mutants-check` | only the stale-entry check, without running anything (part of `make check`, so the list cannot go stale unnoticed) |
| `make test-mutants` | the runner's own tests (in `make test`) |

Run it with `GFORTH=...` for another host. On 2026-11-03 (Gforth 1.0) the
list held 135 faults over `check-declaration.fs`, the checked environment
(`environment.fs`, `env-publish.fs`, `env-signature.fs`), the rejection
rules (`mixed-infer.fs`, `mixed-head.fs`, `level-value.fs`), comparison and
conversion, the NDJSON reader, the program reader, `lib/context.fs`,
`lib/json-write.fs` and the runner itself. They re-create the faults that
earlier reviews planted by hand in scratch scripts since lost (those of
check-declaration and the rejection rules, all 9 of the checked
environment's fourth review, some of the JSON writer's), and add new ones.
132 were caught; 2 survive as known gaps and 1 as equivalent, each with
its reason in the list. The gaps are tests that do not exist yet: a
binder whose two domains infer differently (`rej-d4-left-domain`) and two
Sorts whose levels differ only in a parameter (`cmp-level-params-equal`).
Eight earlier gaps now have tests: names that differ only in a numeric
component; metadata that differs from the pinned versions only in the
format or the Lean version; an upper-case `Z` in program source; an
environment record whose identity is 0; and, in check-declaration, a case
that needs the room step 7 gives back (`value-room`), one whose rejection
holds only while inference run aside records no dependency
(`aside-deps`), and the axiom label, which no phase-2 input can show
(axioms are unsupported) and the failure-path suite tests by planting a
bit in each accepted slot. Later the same day 26 more faults joined for
SHA-256 (`lib/sha256.fs`) and the export manifests (`import/manifest.fs`,
the reader's tap and tally), all caught.

Some test suites plant faults of their own and must keep doing so: the
big-number differential (`tests/lib/bignum_differential.py`, 20 faults, in
`make test`), the IR interpreter's differential
(`tests/program/ir_run_differential.py`, 2 faults in its primitive table),
the receipt validator's test (`tests/program/test_receipts.py`), the
verification-condition check (`tests/program/vc_check.py`, faults Lean must
reject, in `make check`) and the authoring words' round trips
(`tests/author/check_author.py --faults`, 7 faults, in `make check`). The
JSON writer's and the packed-field module's reviews planted their faults by
hand (`FORTH_LIBRARY.md`); the list above re-creates some of them.

## The trial digest (behaviour kept across a refactor)

A change meant to keep the checker's behaviour -- a new store, explicit
stacks, a speed fix -- is checked against 2,000 random checker trials of
300 steps (`tests/support/checker-trial.fs`: random terms, levels, names and
references through inference, conversion, comparison, beta, shift,
instantiation, the level passes, universe substitution, the signature index
and the definition probe). Each step folds every outcome, result, fuel
left, count and diagnostic into a digest; `tests/support/trial-digest.fs`
prints one line per trial and the mix of outcomes, and
`bash scripts/trial-digest.sh` prints the first 12 hex digits of that
output's MD5 digest, the *trial digest* reports quote (`175cba45dbdc` for
main `cae8075`, about 15 s with gforth-fast). The same output in two trees
means the same behaviour on every trial; a changed digest needs an
explanation (`diff` the two outputs to find the trial). It is not part of
`make test`: run it before and after the change.

## Block coverage (`make coverage`)

`make coverage` (plan task 1.4.1) reports which Forth code `make test`
runs. `scripts/coverage.py` runs `make test` with `GFORTH` set to
`scripts/coverage-gforth.sh`, which starts Gforth 1.0 (through the strict
wrapper) with `scripts/coverage-prelude.fs` before the test's own arguments.
The Makefile keeps that `GFORTH` instead of replacing it with
`scripts/gforth-strict.sh`; `bin/leanforth --fast` finds `scripts/gforth-fast`
beside it, which hands over to the wrapper under coverage (gforth-fast cannot
load `coverage.fs`); the Python tests' Gforth runs use `$GFORTH`. The prelude
loads Gforth 1.0's `coverage.fs`, which puts a counter on every basic block
compiled after it (at each colon definition's start, each control-flow word
and each source line inside a definition), and writes the counts when Gforth
ends, also after an error (`BYE`, `(BYE)`, an uncaught `THROW` out of a
command-line argument, `DOERROR`). The script then joins the counts of all
runs and prints, for each folder of `src/`, the blocks compiled in any run and
how many ran at least once; `make test`'s smoke check loads every module on
its own, so modules that no test runs count too. Options: `--files` prints
every file, `--uncovered FILE` writes each block that never ran as
`file:line:column`, `--keep DIR` keeps the raw counts (about 3.5 GB for a
full run), `--check`, `--update-baseline`, `--baseline FILE`.

The tool cannot stop counting silently any more (it did, unnoticed, between
2026-11-03 and 2026-11-12: the Makefile began to force the strict wrapper,
which refused the coverage wrapper, so no run was counted and the report said
"no counts were collected" with exit status 0). It now exits 1 when no run
left counts, when more than 10% of the runs left none, or when fewer runs left
counts than 90% of the baseline's `runs`; `tests/support/test_coverage.py`
(`make test-coverage`, part of `make test`) runs it on a command that starts
no Gforth, one that bypasses `$GFORTH`, and one that runs it.

**The ratchet.** `tests/coverage-baseline.json` lists, for each `src/` file, its
blocks and the blocks that never ran, with a `reason` where some did not, and
the number of runs counted. `make coverage-check` (`scripts/coverage.py
--check`) runs `make test` under coverage and fails when a file's never-run
blocks grow, or when a file the baseline lacks has any never-run block. It is
part of `make check` (not of `make test`), needs Gforth 1.0 and, at `JOBS=2`
with nice, takes about 6 minutes (5 min 18 s for the measurement, plus about
20 s to join the counts; with 8 jobs, expect about 2 minutes). After tests
are added or code is removed, lower the numbers with `python3
scripts/coverage.py --update-baseline`; a new file with never-run blocks needs
`--reason TEXT`. Never raise a number to make the check pass: add tests.
Runs on copies of the tree outside it (the big-number planted faults) are not
counted. On 2026-11-12 (commit 3ac0558 plus this fix; the earlier measurement
of 2026-11-03 was 12,093 blocks, 96.6%; the code has grown since, `src/cli`
is new) it reported over 1,580 Gforth runs
(22 more left no counts), with the list of the 2,743 never-run blocks in
`.claude/work/coverage/uncovered-3ac0558.txt`:

| Folder | Blocks | Ran | Coverage |
| --- | --- | --- | --- |
| `src/author` | 1,337 | 1,277 | 95.5% |
| `src/cli` | 3,007 | 2,781 | 92.5% |
| `src/core` | 5,048 | 4,749 | 94.1% |
| `src/import` | 5,487 | 5,116 | 93.2% |
| `src/kernel` | 15,013 | 13,780 | 91.8% |
| `src/lib` | 4,230 | 4,127 | 97.6% |
| `src/present` | 5,050 | 4,642 | 91.9% |
| `src/program` | 2,192 | 2,149 | 98.0% |
| total | 41,364 | 38,621 | 93.4% |

A block that ran is not a tested block: coverage finds code no test
reaches and says nothing about whether the tests check what the code does,
which is what `make mutants` asks. The 2026-11-02 review's figure (90.7% of
5,532 blocks) measured `make test-core` alone, over the code of that day.

## Self-verification

LeanForth's program correctness system should eventually verify selected
LeanForth components against explicit specifications, including checker and
runtime operations where practical. First validate the verifier with independent
tests and Lean comparisons, then apply it to narrowly specified components and
retain independent regression and adversarial tests. A verifier checking itself
does not independently establish its own soundness; record the trusted kernel,
host, compiler and runtime assumptions separately.

## Source and test filenames

Matching filenames under `src/` and `tests/` intentionally pair an
implementation module with its tests; the directory is part of the path.
For example, `src/kernel/mixed-infer.fs` defines experimental words,
while `tests/core/mixed-infer.fs` includes that module and exercises it.
Likewise `src/program/clamp.fs` is a Forth word and `tests/program/clamp.fs`
is its test suite. The two `check.sh` files run different harness and Lean
reference checks. Same names do not mean the files are copies; use full paths
in documentation, commands and review comments to avoid ambiguity.

## Retired tests of superseded code

Until 2026-11-02 the superseded plain and `tagged-*` modules had their own
tests beside them, run by `make test-legacy` and, for 18 pinned-Lean
comparisons, by `make check`. The [owner approved](../project/OWNER_DECISIONS.md)
deleting that code once the current code had at least the same test
coverage. Every coverage gap was first closed with tests of current code;
then the superseded modules and their tests (119 files) were deleted
together with their Make targets ([decisions record](../project/DECISIONS.md),
"Legacy retired — 2026-11-02"). The tests that had exercised current modules
through a superseded helper were rebuilt on current code in `tests/core/`:
the NDJSON preview suite (`tests/core/test_ndjson_preview.py`) checks the
`src/import/load.fs` staging round trip without a checker,
`tests/core/test_export_definitions.py` runs the current definition probe on
the pinned exports, and `tests/core/tagged-sort-boundary.fs`,
`declaration-chain-test.py` and `context-constant-fixture-test.py` were
rebuilt on current modules only.

### Ports of the legacy pinned-Lean comparisons

`tests/core/lean-differential.py NAME` compares a Forth table of current code
with a Lean 4.35.0 table in `tests/reference/`; each `NAME` has a Make target
in `DIFFERENTIAL_TARGETS`, so `make check` runs them all. They port the
legacy comparisons onto the current passes, with every Sort symbolic (a
concrete universe n is the level succ^n zero):

| Make target | NAME | Forth side | Lean side | Cases |
| --- | --- | --- | --- | --- |
| `test-constant-term-scope-differential` | `scope` | `constant-term-scope-table.fs` | `scope-table.lean` | 64 |
| `test-mixed-shift-plain-differential` | `shift` | `mixed-shift-plain-table.fs` | `shift-table.lean` | 80 |
| `test-mixed-instantiate-plain-differential` | `instantiate` | `mixed-instantiate-plain-table.fs` | `instantiate-table.lean` | 25 |
| `test-mixed-beta-plain-differential` | `beta` | `mixed-beta-plain-table.fs` | `beta-table.lean` | 15 |
| `test-mixed-convert-plain-differential` | `convert` | `mixed-convert-plain-table.fs` | `convert-table.lean` | 15 |
| `test-mixed-infer-plain-differential` | `infer` | `mixed-infer-plain-table.fs` | five tables | 52 |
| `test-mixed-definition-differential` | `definition` | `mixed-definition-table.fs` | `definition-table.lean` | 9 |
| `test-mixed-level-substitute-plain-differential` | `level-substitute` | `mixed-level-substitute-plain-table.fs` | `term-level-substitute-table.lean` | 48 |
| `test-mixed-infer-constant-differential` | `constant` | `mixed-infer-constant-table.fs` | `term-level-substitute-table.lean` | 96 |
| `test-export-signature-differential` | `signature-fixture` | `export-signature-stream.fs` | `signature-fixture.lean` | 4 |
| `test-export-specialization-differential` | `poly-specialization` | `export-definition-stream.fs` | `poly-specialization-table.lean` | 8 |

Rows must agree exactly, except that an ill-typed term may be invalid or
unknown and that `KNOWN_UNKNOWN` in the driver lists the two cases where the
current code is knowingly more conservative than Lean (it answers unknown
where Lean accepts): `max u v` against `max v u`, and a binder domain whose
type is an unreduced redex. Any other difference fails.
