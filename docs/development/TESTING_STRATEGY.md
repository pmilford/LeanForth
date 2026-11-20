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
- **Gforth that could not start** (2026-11-18, after one unexplained exit
  5 under coverage). Under `ulimit -u 500` the limit counts every thread
  of the user, other agents' job pools included; bash retries a refused
  fork for about 15 seconds, then ends with status 254, which a caller
  read as a Gforth failure. `scripts/gforth-strict.sh` and `bin/leanforth`
  now say "could not start Gforth: resource limit" (254; "exec failed"
  for 126 and 127) with the user's thread count and process limit, read
  from `/proc` without starting a process (`scripts/start-limit.sh`);
  `bin/leanforth` still exits 5, an internal fault, and
  `scripts/coverage-gforth.sh` starts no process before it becomes the
  strict wrapper. `tests/scripts/test_start_limit.py` (in
  `make test-harness`) runs `bin/leanforth` on a wrapper whose own limit
  is 1 (`ulimit -u 1` in that process only).
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
no file of the tree changed. A Forth test that writes files names them with
`scratch-file` (`tests/support/scratch.fs`): in the folder `LF_TEST_SCRATCH`
names, which the Makefile makes for each such command and removes after it
(`scripts/with-scratch.sh`), and `scripts/mutants.py` for its run, else in
`/tmp`; before 2026-11-12 four tests wrote fixed `/tmp` names, and two
worktrees running `tests/lib/sections.fs` at once failed a push on Gforth
0.7.3. The exceptions to "its own folders" are the shared results
`build/inductive-expected.out` and `build/program-clamp/` (below), each
made once per make run by a target the others wait for.
`tests/core/compact-verify.sh` runs its two
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
| `test-front` | test | — | — | 0.6 (new 2026-11-12, plan FE1a-b; not yet timed in the three runs) |
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
| `reference-constructions` | check | — | — | about 90 (new 2026-11-12, plan FE6; one run, `nice -n 10`, other agents running) |
| `mutants-check` | check | 0.1 | 0.0 | 0.0 |
| `test-compact-faults` | check | 7.5 | 6.9 | 6.1 |
| `test-lean-cache` | test | — | 2.6 | 2.6 |
| sum, every target of make test | | 36 | 40 | 43 |
| sum, every target of make check | | 345 | 335 | 132 |

Since plan task 5.5.1 (2026-11-12) three targets run LeanForth's checker on
an export of Lean's program proofs with `--jobs 2`, so they are listed
first in `check`: `reference-program-ir-run` now also records the clamp
receipt's evidence (Lean exports the clamp proofs' 4,277 declarations and
LeanForth checks them; 154 s), `reference-program-mutants`
checks the program, contract and proof mutants in one export of 4,284
declarations (122 s), and `reference-program-sha-export` the
SHA-256 helper words' 2,890 declarations twice (86 s); measured
with `JOBS=2 LEAN_CACHE=0` on a loaded machine (load 6-8 on 10 cores), 2026-11-12: 154 s, 122 s and 86 s.

**The same checks, done once (2026-11-12, evening).** Each of these
targets checked the same input twice. Now `program-clamp-record` records
the clamp evidence once per make run, its LeanForth check also writing a
snapshot (`check --save-snapshot`), into `build/program-clamp/`;
`reference-program-ir-run` compares that evidence with the committed one,
and `reference-program-mutants` checks its export with the seven changed
copies against the snapshot (`check --snapshot`): the 4,277 originals are
taken from it unchanged and only the copies are checked. The test requires
both that every declaration of the export alone was accepted (exit 0) and
that exactly the originals came from the snapshot (`snapshot.import`, each
declaration's `provenance`). `reference-program-sha-export` does the same
within its own run.
`reference-demos` starts all fifteen LeanForth runs of its five demos (check,
wrong twin, print) side by side, the costliest first, four at a time as
before, instead of each demo's three one after another. In `tests/cli`,
`MemoryPerCheck.test_snapshot_pair` and `Jobs.test_same_output` run their
independent cases two at a time. Every assertion is kept. Measured with
`JOBS=2`, the Lean cache on, old and new run back to back on a machine
other agents loaded (load 6-16 on 10 cores; wall seconds):

| Target or test | Before | After |
| --- | ---: | ---: |
| `program-clamp-record` (new; the clamp check, once) | — | 110.8 |
| `reference-program-ir-run` (own commands after the record) | 137.5 | 11.5 |
| `reference-program-mutants` (after the record) | 127.9 | 13.9 |
| `reference-program-sha-export` | 63.9 | 42.2 |
| the three together (`make ... JOBS=2`), CPU | 192 wall, 597 CPU | 125 wall, 308 CPU |
| `reference-demos` (two runs each) | 98.7, 84.2 | 69.7, 68.2 |
| `MemoryPerCheck.test_snapshot_pair` (two runs each) | 39.9, 30.8 | 20.4, 17.9 |
| `Jobs.test_same_output` (two runs each) | 24.1, 21.0 | 12.0, 11.4 |

The demos and the two command-line tests use the same CPU as before (about
200 s, 34 s and 22 s); only their waiting is gone.

**leanforth verify (plans 8.4.1b-d, 2026-11-13).** Five targets,
[PROGRAM_VERIFY.md](../programming/PROGRAM_VERIFY.md); seconds of the last
`make check JOBS=2` with the Lean cache on 242d056a (other agents running):

| Target | Suite | Seconds |
| --- | --- | ---: |
| `test-program-verify-driver` (stand-in tools: outcomes, Lean, limits) | test | 11.3 |
| `test-program-verify-driver-input` (stand-in tools: verdicts, malformed input, workflow) | test | 19.2 |
| `test-program-verify-command` (`bin/leanforth verify`, `--json`, `--write-ir`, replay) | test | 9.9 |
| `reference-program-verify-clamp` (`lf-clamp` end to end, LeanForth `--jobs 2`) | check | 112.9 |
| `reference-program-verify-refuted` (`wrong-clamp-swapped` end to end) | check | 116.6 |
| `reference-program-verify-all` (all thirteen contracts, by hand) | — | 737 (once) |

Lean's compile and export in the two `check` targets go through the Lean
cache like every pinned-Lean run (the driver honours `LEAN` and
`LEANEXPORT` under the Makefile's test switch `LEANFORTH_VERIFY_TEST_TOOLS=1`),
so a cached run replays them and `LEAN_CACHE=0` runs them; what remains,
about 90 s each, is LeanForth's final check of the IR semantics' closure
(4,277 and 4,295 declarations), which no cache may replace.
`program-clamp-record` (5.5.1) checks a different export (the committed
nine-contract obligations file, whose module name its private names
carry), so it cannot stand for `reference-program-verify-clamp`; one check
for both would mean re-basing the 5.5.1 receipt on the driver (review M7).
`make check JOBS=2` with the cache took 789 s on 242d056a (exit 0; the sum
of every command's time 1,433 s) against about 8 minutes for main's run
recorded at 39357876 (sum 847 s); the two end-to-end runs add about 230 s
of command time.

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
change; at the end of a branch, once, on the head you hand over, the
suites of its change tier (`make tier`, below; owner, 2026-11-13). Text for
agent briefs:

> Testing: while you work, run only the focused tests of the files you
> change: the test file itself (`.tools/gforth/bin/gforth tests/core/names.fs
> </dev/null`), its module's target from the table in
> docs/development/TESTING_STRATEGY.md ("Testing while you work"),
> `make test-changed` (every target of `make test` that uses a file changed
> since main) and the faults of the words you change
> (`make mutants FAULTS=id,...`). At the end, once: rebase on main, commit,
> and run `make tier JOBS=2` (`DRY_RUN=1` first shows the tier and its
> suites); report the head, the tier and its exit status. It reuses any pass
> already recorded for the same tree and records each new one. Do not run
> several make commands at once.

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
| `src/author/` | `test-author`, `test-author-e2e`; `reference-author` |
| `src/front/`, `src/core/mvar-leaves.fs` | `test-front`, `test-front-e2e` (`.lf` files through `bin/leanforth check`); `test-author` (the export writer's refusal, the marker); `reference-front` (pinned Lean's macro expansion); `reference-constructions` (`casesOn`, `recOn` and `ctorIdx` built for every type of Init and compared with Lean's export, and their binder names and information with pinned Lean's environment; plan FE6); `test-instances` and `reference-synth` (the instance keys and table and instance search, plans FE1e2-FE1e3 and FE1e5: every Init instance recomputed, getInstances and 30 searches against pinned Lean) |
| `tests/reference/*.lean` | the target that runs the file (`make check-changed` finds it) |
| `scripts/lean-cache.py`, the Makefile | `test-lean-cache`, then the full tier (`make tier`) |
| `docs/` | `check-docs`, `check-doc-examples` |

### Change tiers and tested-tree records (plan 9.4.6)

Added 2026-11-13 for the owner's decisions "Less repeated testing"
([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md); the count behind them
is [TEST_WORKFLOW_REVIEW.md](TEST_WORKFLOW_REVIEW.md)): a branch, and a
push, run the suites of what the change reaches, once per tree.

**Tiers.** `scripts/test-tier.py` classifies the files that differ from the
merge base with `BASE` (default `main`; uncommitted and new files included)
and gives the range its largest file tier (`python3 scripts/test-tier.py
[--base REF] [--files FILE...] [--json]` prints it with each file's reason):

| Tier | Files | Suites |
| --- | --- | --- |
| docs | Markdown anywhere, `docs/`, `.claude/`, `.codex/`, `prompts/`, `LICENSE`, `.gitignore` | `check-docs`, the targets that read the file (a page whose examples run, a catalogue a test compares), the progress check |
| tests | any other file under `tests/` (a `tests/mutants/faults.d/*.toml` is part of the fault list) | the targets that use it, their unit tests also on gforth-fast; its planted faults |
| library | a Forth file of `src/lib/` that `src/main.fs` does not load | the branch coverage check, the targets that use it (their unit tests on gforth-fast), its faults |
| front | a Forth file of `src/front/` that `src/main.fs` does not load | the same, and `test-front`, `test-front-e2e`, `reference-front` |
| tactic | only a branch `scripts/check-tactic-plugins.py` finds confined (below) | the branch coverage check, the front end's unit tests (on gforth-fast too), every end-to-end run of `.lf` files, `reference-front` (the S1/S2 pinned-Lean comparisons), the source rules, its faults |
| full | any Forth file `src/main.fs` loads (at HEAD or at the base, so a library that becomes loaded is full), `src/main.fs`, `src/kernel`, `core`, `import`, `cli` and every other folder of `src/`, the Makefile, `scripts/`, `bin/`, `schemas/`, `lean-toolchain`, `.github/`, anything else | the branch coverage check of the changed source files (`make cover-changed`), `make test`, `make test-unit` on gforth-fast, `make check-rest`, each target reused while its inputs are unchanged |

Since 2026-11-17 (owner) no tier runs Gforth 0.7.3 or `make coverage-check` of
every file, and since 2026-11-19 (owner) none runs `make coverage-focus`:
`make daily` runs the whole-suite ratchet and Gforth 0.7.3, and `make
tag-check` requires them. Every tier whose range adds or modifies a Forth file
of `src/` (the front tier too) runs the branch coverage check first
(`cover-changed`, below).

- Unit and end-to-end tests (owner, 2026-11-14): see "Unit and end-to-end
  tests" below. In a smaller tier the reached unit targets whose recipe runs
  Gforth run on gforth-fast (`targetsfast`); an end-to-end target never
  does. `scripts/test-tier.py` refuses a plan (exit 2) that would leave such
  a unit target off gforth-fast, put an end-to-end target on an engine, or
  run Gforth 0.7.3 at all.
- Gforth 0.7.3 (owner, 2026-11-17, replacing the push rule of 2026-11-14):
  only `make daily` and `make tag-check`; `tested-tree.py tier --with-073` is
  accepted and ignored with a note, and `scripts/push.sh` no longer passes
  it. A portability slip is caught by the next nightly run, and before any
  tag.
- The branch coverage check runs first in its tier: it takes seconds to a
  minute and fails a branch before its longer suites run. It runs Forth unit
  test files under coverage on their own, so its record stands only for
  itself, and `make test` runs plain. `make daily`'s `make coverage-check`
  runs `make test` instrumented and its record stands for `make test`'s
  targets but `test-cli-engines`, which runs in both `make test` and `make
  check-rest` on purpose (COVERAGE_ENGINE_DIFFERS: it compares `gforth-fast`
  with the checking engine, and coverage replaces `gforth-fast` by the
  counting Gforth).
- The tactic tier (owner, 2026-11-17; the tactic plug-in design's decision 2
  and slice (a1), `TACTIC_PLUGINS.md` of its branch
  `tactic-plugin-design`): `scripts/check-tactic-plugins.py` finds a branch
  confined when it adds `src/front/tactics/NAME.fs` and changes nothing but
  `src/front/tactics/`, `tests/front/tactics/NAME/`,
  `tests/mutants/faults.d/NAME.toml` and documentation, and its tactic files
  write no hook (`is`, `defer!`), no data word (variable, value, create,
  buffer:) another file defines, and call `lf-tactic-...!` only for a kind
  they define (comments and strings left out). Only then is the tier
  "tactic"; otherwise (exit 3) the files' own tier applies, which for a file
  `src/main.fs` loads is full, and a broken rule (exit 1) also fails `make
  tier`. The kernel and import suites are left to the daily run: a confined
  file cannot reach them.
- "Loads" is the `require`/`include`/`needs` graph from `src/main.fs`,
  comments included (more is loaded, never less). Since FE1g-1 it holds 180
  of the 192 Forth files: every front-end file but `cases-several.fs`,
  `constructions.fs`, `ctor-idx.fs` and `expr-remap.fs`, every library but
  `bigint.fs` and `sort.fs`. So a change to a front-end file that
  `src/main.fs` loads is full: `bin/leanforth` and most tests load it.
- "The targets that use a file" are `make test-changed`'s
  (`scripts/changed-tests.py`): the files a target's recipe names, followed
  through Forth loads, Python imports and repository paths named in code.
  Every changed Forth source also selects `smoke`, `check-portable-forth` and
  `check-forth-quality`; a target of `make test` whose recipe runs Gforth also
  runs on 0.7.3. A test file no target names selects the targets of its
  folder; a folder no target uses makes the range full.
- Faults: those whose `file` or `test` command names a changed file, and,
  when `tests/mutants/faults.toml` or a `faults.d` file changed, the entries new or changed since
  the base (`make mutants FAULTS=id,...`). The full tier (plan 9.4.8j, after
  the s1-synth review's B1) runs the entries new or changed since the base
  and the faults whose old text lies on or next to a line the change touched
  in its file (`git diff -U0`); a fault of a changed file whose text was left
  alone still applies as before (the stale check confirms its old text) and
  is left to the daily full `make mutants`.
- Coverage in every tier (owner, 2026-11-19, `docs/project/OWNER_DECISIONS.md`
  "Coverage in the branch in seconds, the whole-suite ratchet at night"):
  the suite `cover-changed`, `make cover-changed BASE=<the range's merge
  base>` (`scripts/coverage.py --changed`, "The branch coverage check" under
  "Paying coverage debt" below), whenever the range adds or modifies a Forth
  file of `src/`: those files' unit tests run under coverage, and the check
  fails on a never-run block of a line the branch added or changed, or on a
  touched file no unit test loads. A range that touches no source file (a
  test, the baseline, a script) runs no coverage in its tier. It replaced
  the focused ratchet (`make coverage-focus COVERAGE_FILES=...
  COVERAGE_TARGETS=...`, owner 2026-11-17, rule of 2026-11-18), which ran
  every target of `make test` that loads a touched file instrumented and
  compared the file's never-run blocks with the baseline: 712-1,064 s of a
  20-25 minute tier on 2026-11-19, and up to the whole `make test` for a
  file `src/main.fs` loads. `make coverage-focus` stays a command one can
  run by hand (name the targets), and `scripts/coverage.py --per-target
  FILE` still writes each target's compiled and run blocks of each file.
- Left to the daily full run (`make coverage-check`, the whole-suite ratchet
  of every file over all of `make test`, unit and end-to-end): (1) a change
  in file A that stops running part of file B, and a test change that stops
  running a line; (2) a block only end-to-end tests run (the branch check
  counts unit tests only, so such a changed block fails it until a unit test
  runs it); (3) Gforth 0.7.3.

**Toolchains** (2026-11-18). Every target takes Gforth and Lean the same
way: `GFORTH=` and `LEAN=` given to make win; else the pinned copies in
the checkout's `.tools/`; else those under the folder `LEANFORTH_TOOLS`
names, laid out as `.tools` is; else the PATH's. The Makefile exports both
as absolute paths (`LEANFORTH_GFORTH`, `LEANFORTH_LEAN`), and
`GFORTH_FAST` is the gforth-fast beside that Gforth (`reference-cli` runs
it); test scripts take them from the environment
(`tests/support/toolchain.py`). `make tier` and `make daily` hand the
toolchain to `scripts/tested-tree.py` (`--gforth`, `--lean`), which names
it in every suite's command, so an inner make never falls back to a bare
name (the Lean cache resolves one on PATH, or refuses it by name). An
agent's worktree has no `.tools` and must never link one: it runs `make
tier GFORTH=/abs/gforth LEAN=/abs/lean` or sets
`LEANFORTH_TOOLS=/path/to/main/checkout/.tools`.

**Tested-tree records.** `scripts/tested-tree.py` writes one JSON record per
passing scripted run, in the main checkout's `.claude/work/ci/tested/`
(shared by every worktree like the Lean cache; machine-local, never
committed). Its key is the tree (`git rev-parse HEAD^{tree}`), the
Gforth and Lean versions (`--version`) and the `LEAN_CACHE` mode; it keeps the
commit, branch, date, command and seconds, and what the run stands for:
every target make built for its goals, each fault it ran, for `make
coverage-check` the ratchet and `make test`'s targets but those of
`COVERAGE_ENGINE_DIFFERS` (below), and for `make cover-changed BASE=...` the
branch coverage check from the merge base of `BASE` and HEAD (one item per
merge base; a record of `BASE=main` and one of `BASE=<that commit>` stand for
each other).

- Only a run that exited 0 writes a record. A worktree with uncommitted
  changes to tracked files, or new files under `src/`, `tests/`, `scripts/`,
  `bin/`, `schemas/` or `docs/`, is refused before anything runs, and a run
  during which the tree changed records nothing.
- A record stands for a later command on the same tree when the Gforth and
  Lean versions are the same and its cache mode is at least as strong
  (`LEAN_CACHE=0` or `verify` stands for the cache on; for `make test`'s own
  targets, which run no Lean, any mode). Several records add up: `make
  check` stands for `make test-lib`, `check-rest` and the rest of its targets.
  Make options other than `-s` (`-n`, `-k`, `-i`) are refused, and a goal
  given another variable (`EXPORT=...`) stands only for that exact command.
- A record of an earlier commit of HEAD's history stands for what the
  change since that commit cannot reach: the change gets its own tier, and
  the record loses that tier's targets and faults (and all coverage items
  unless the change is documentation only); a full-tier change leaves it nothing, a commit of
  another branch is never used. So a review log or progress commit after a
  tested merge needs only `check-docs` and the targets that read its pages,
  and a review fix to a test needs only that test's targets, faults and
  coverage. Without this, every push after a merge's documentation commit
  would have re-run the whole suite.
- **Per-target reuse** (owner, 2026-11-17). A record also keeps, for each
  target, fault and coverage item it stands for, a digest of what that item
  read (`scripts/test-tier.py`'s `Inputs`): the recipe as `make -n` prints it
  (its prerequisites' recipes included; the checkout's path and the toolchain
  paths left out, the Gforth and Lean versions and the cache mode being the
  record's key), the variables make exports to every recipe and its special
  lines (`SHELL`, `MAKEFLAGS`, `include` ...), and the git blob of every file
  `scripts/changed-tests.py`'s `input_files` finds: the files the recipe
  names, followed through Forth loads, Python imports, named paths (also
  behind `$root/`, `{ROOT}/`), and literal names beside a program; as data,
  every file of a test program's own folder, every file of a basename a
  program names, of a folder whose name it quotes as a path, of an extension
  it globs, under the folder a path template starts in. A quoted word without
  a path separator names a folder only when it may be used as a path
  (2026-11-18; `changed-tests.py`'s `used_as_path`): joined with `/`, an
  argument of a call not known to take text, a plain assignment, a loop's
  tuple, any shell use but a comparison or a `case` pattern. It is a value —
  not an input — as a subscript (`d["ir"]`), a dict key, a dict value or
  keyword argument whose name says nothing of a path (`mode="development"`),
  an operand of `==`, `!=` or `in`, or an argument of a call that takes text
  (`assertEqual`, `get`, `startswith` ...). Before, the mode `"development"`
  in two CLI tests made `test-cli-*` and `test-run-records` read all of
  `docs/development`, so every "Record the local CI" commit re-ran them;
  `docs/development/ci-results.log` is now read only by `check-docs` and by
  targets never reused anyway (`test-tiers`, `check-lean-sources`,
  `check-test-classes`). A file name with an extension stays an input
  wherever it appears (`"README.md"`, which the CLI tests pass as a file). A record of an earlier commit
  of HEAD's history stands for each item whose digest is unchanged, whatever
  the tier: a Makefile change invalidates only the targets whose recipe or
  exported variables it changes, a script change only the targets that run
  or load it. An item's digest is none, so it is never reused across
  commits, when what it reads cannot be known: a program or recipe reads
  git's index or history (`git ls-files`, `log`, `diff`; not `rev-parse` or
  `diff --quiet`), files outside the checkout (`.tools/` beyond the
  toolchains, the home folder), an export the environment names, lists a
  folder the finder cannot name, or the recipe names no file (12 of 137
  targets on 2026-11-17: the git-reading checks, `test-tiers`,
  `test-mutants`, and three whose tests contain `${HOME}` text). A fault's
  digest covers its entry, its file and what its test command reads; a
  coverage item's, the digests of the targets it ran over, the file's
  baseline entry and the coverage tool. The branch coverage check has no
  digest: its record stands on its own tree, and on a later commit only
  across documentation.
- `make once GOALS="check"` runs `make check` unless records stand for it
  (or only the targets they do not stand for), and records the pass; `make tier` (`BASE=main`, `JOBS=2`, `DRY_RUN=1` to
  only print) runs every suite of the branch's tier so, then the progress
  check. `python3 scripts/tested-tree.py list [--all]` prints the
  records; `lookup -- make GOALS` says whether they stand for a command.

**Pushes.** `scripts/push.sh` keeps the progress check, the strict Forth
review and style check and the refusal on any failure. Its suites are the
tier of `origin/main..HEAD`, run as `make tier` runs them: what a record of
HEAD's tree, or of an earlier commit for what the change since cannot
reach, stands for is reused, the rest runs. A push runs only its own tier
(owner, 2026-11-17): a documentation push the documentation and progress
checks (minutes), a code push its tier once, with the Lean cache and
per-target reuse; until then the first push of a day ran the whole full tier
without the cache (about 35 minutes even for a documentation change). Gforth
0.7.3 runs at no push (owner, 2026-11-17). `JOBS` (owner, 2026-11-17): `JOBS=N`
in the environment wins; else 2 when `.claude/work/CPU_MODE` says `day`; else
5 when at most two heavy processes (Gforth, Lean, leanexport) of other runs
are going, 2 when more; always under `ulimit -u 500`. A dry run gives each
suite that would run an estimate: the target time of what it would run, from
the newest push's timing log (a unit test's time divided by the three suites
it ran in there), and that divided by `JOBS`, a lower bound of the wall time.
`--full` forces the full tier, `--no-cache` sets `LEAN_CACHE=0`, `--dry-run`
prints the tier and what would run or be reused and stops (also on a branch,
against `origin/main`). The push then reports how old the last daily run is
(`tested-tree.py daily-status`) and warns, without refusing or running it,
when none is recorded or it is older than 36 hours. The line it appends to
`docs/development/ci-results.log` names each suite that ran (exit status,
seconds, command), each that was reused (the record's commit and date), the
full tier's suites the tier did not need and the daily run's age. It refuses
to push from a branch other than `main`, with uncommitted changes, and when
there is nothing to push.

**The daily run** (owner, 2026-11-17) is its own command, `make daily`
(`tested-tree.py daily`; `DRY_RUN=1` prints what would run), meant to run once
a night by itself and before a tag: the full tier's four suites on HEAD with
`LEAN_CACHE=0` — `make coverage-check`, `make test-unit` on gforth-fast, `make
check-rest` and `make test-unit` on Gforth 0.7.3 — and `make parallel-init`
(below), each recorded for HEAD's exact tree (records of other trees are not
reused; a tree whose daily run is complete runs nothing). A daily run is
complete when one tree has all five records, none narrowed by `FAULTS=` or
another variable (`make check` with `LEAN_CACHE=0` stands for `make
check-rest`). **Tags:** `make tag-check`
exits 0 only when the tree to be tagged has a complete daily run, so a tag
still requires a daily run of that exact tree. The daily run does not run the
whole of `make mutants` (as before: that stays a separate run).

**One instrumented run of `make test`.** `make check` is now `make test` plus
`make check-rest`: every target of `make check` outside `make test`, and the
targets of `make test` whose Gforth changes under coverage. That is
`COVERAGE_ENGINE_DIFFERS`, since 2026-11-17 `test-cli-engines` (until then
all of `test-cli`): the Engines class's `--fast` runs use
`gforth-fast`, which `make coverage` replaces with the counting Gforth 1.0, so
its engine comparisons compare the checking engine with itself there. No
other test of `make test` compares `gforth-fast` with another engine or reads the coverage
variables. The full tier runs `make coverage-check` (all of `make test`,
instrumented, and the ratchet) and `make check-rest`, so `make test` runs
once instead of twice. `tests/scripts/test_test_tier.py` checks that `make
check`'s targets are exactly those of `make test` and `make check-rest`, and
that `check-rest` repeats no target of `make test` but `test-cli-engines`.

Measured 2026-11-13 with `JOBS=2` and `nice -n 10` while other agents
loaded the machine (load 4-6 on 10 cores); "target time" is the sum of
each target's seconds (`LF_TIMING_LOG`):

| Run | Wall | Target time |
| --- | ---: | ---: |
| `make coverage-check` (all of `make test` instrumented) | 408 s; 429 s | 1,115 s; 1,176 s |
| `make check-rest` | 480 s | 846 s (the four parts of `test-cli` 271 s, `program-clamp-record` 153 s) |
| `make check` (commit `3c5dbc0c`) | 632 s | 1,116 s |
| that morning's pushes `39357876` and `2b265cb1` (log times): `make check`, `make coverage-check`, `make test` on 0.7.3 | 7.9-8.4, 4.7-5.4, 6.1-6.7 min | |

Every target of `make test` passed instrumented as it does plain (the one
exception found was this work's own `test-tiers`, whose throw-away
repositories took the counting Gforth from the environment; fixed). At
`JOBS=2` the wall time of the full tier barely changes: `make check`'s
wall time was set by its slowest chain (`program-clamp-record`, then the
program targets, and `test-cli`), and `make test`'s other targets only
filled free job slots; what one instrumented run saves is the target time
of `make test` outside `test-cli`, about 270 of `make check`'s 1,116 s. The
large savings come from the tiers and the records: a documentation push,
14.6 minutes of suites on 2026-11-13, now runs `check-docs` and the
targets that read its pages after the day's full run, and a push whose
tree, or whose earlier commit, passed on a branch reuses that pass.

**Tests.** `make test-tiers` (in `make test`) runs
`tests/scripts/test_test_tier.py` and `tests/scripts/test_tested_tree.py` on
throw-away repositories with stub toolchains and a temporary records folder
(`LF_TESTED_DIR`): every tier, mixed ranges, a library that becomes loaded,
deleted and renamed files, the Makefile and scripts; a pass recorded and
reused, a failed run, a dirty worktree and a tree changed mid-run recording
nothing, another Gforth, Lean or weaker cache mode missing; a record of an
earlier commit standing for what a documentation or library change cannot
reach, and nothing after a full-tier change or on another branch; the tier
runner reusing, narrowing and running; the daily run (`daily` runs the four
suites without the cache and records them, a narrowed or cached run is no
daily run, `tag-check` passes only for the exact tree of a complete daily
run, `daily-status` reports its age and warns past 36 hours); and `scripts/push.sh` on a
copy with a bare repository as origin: its dry run, its refusals, a push, a
failed suite not pushed, and the record of what ran and what was reused; a
documentation push planning nothing beyond the docs tier, a code push never
adding `LEAN_CACHE=0`, and the stale daily run's warning. Since 2026-11-17 they also check the engines: a reached unit test on
gforth-fast and 0.7.3, an end-to-end test on neither, an unclassified target
on both, a plan that drops a unit test from an engine or puts an end-to-end
test on 0.7.3 refused, gforth-fast's records kept apart from Gforth 1.0's.
Since the per-target reuse (2026-11-17) `test_tested_tree.py`'s `PerTarget`
checks that a target is reused when an unrelated file (a script, a Forth file
it does not load) changes, and not when a file it loads through two requires,
a data or golden file it reads (named, or only beside its program), its
Makefile rule, an exported variable or the Gforth or Lean version changed,
that an item whose inputs cannot be known is never reused, a fault reused
while what its test reads is unchanged, and no record of another branch used;
`test_test_tier.py` that the full tier measures only the touched files, no
tier runs 0.7.3, and the fault list's `faults.d` files; `Push` that no push
plans a 0.7.3 suite and how `JOBS` follows the load;
`tests/scripts/test_check_tactic_plugins.py` each rule of the tactic check
and the tactic tier given to a confined branch and refused to one that edits
the runner, another tactic's tests, the Makefile, `faults.toml` or breaks a
rule. `tests/scripts/test_test_classes.py` checks the pattern rows and that
the real Makefile finds a tactic's targets from `tests/front/tactics/NAME/`.
`make check-test-classes` (in `make test`) runs `tests/scripts/test_test_classes.py`
(the table's rows; a target, a test file in neither class, a stale or
malformed row and a missing table fail on a throw-away repository) and then
`scripts/test-classes.py` on the real tree.

### Unit and end-to-end tests (owner, 2026-11-14)

The owner found the same code tested too many times and decided: **unit
tests** (a Forth test file that loads a module and runs its cases; Python
tests of scripts) run on both Gforth engines, `gforth` (the checking engine,
also the one `make coverage` counts with) and `gforth-fast` (`bin/leanforth`'s
default); **end-to-end tests** (anything that runs `bin/leanforth` on an
export, a snapshot or `.lf` files; the pinned-Lean comparisons; runs of
all of `Init`; faults planted in a copy of the tree) run once, on one engine,
and not again outside `make coverage-check` when it already runs them;
**Gforth 0.7.3** runs the unit tests only, in the daily run (`make daily`;
since 2026-11-17 no longer at code pushes).

- **One table.** [`tests/test-classes.txt`](../../tests/test-classes.txt)
  gives every leaf target of `make check` its class (46 unit, 91 end to
  end on 2026-11-17), and names the test programs no target runs by a path
  it can see (`manual`: benchmarks, measurements by hand) or that a target runs
  through a path built at run time. The Makefile reads it for `make
  test-unit` and `make test-e2e`; `scripts/test-tier.py` for the suites of a
  tier; `scripts/test-classes.py` (`make check-test-classes`, part of `make
  test`) fails when a leaf target of `make check` or a tracked test program
  under `tests/` is in neither class, or a row names nothing.
- **Mixed targets split.** `test-cli`'s four parts are end to end, its
  Forth side (`test-cli-forth`) unit, and the Engines class is its own part
  `test-cli-engines`; `test-front-e2e` (`check_tactics.py`, `check_elab.py`,
  `check_s2.py`), `test-author-e2e` (`check_author.py`) and
  `test-elab-data-e2e` (`test_elab_data.py`) took the `bin/leanforth` runs of
  `test-front`, `test-author` and `test-elab-data`, which keep their unit
  tests. `make test` and `make check` run the same commands as before.
- **Where each runs.** `make coverage-check` runs all of `make test` once,
  instrumented on Gforth 1.0: every unit test on the checking engine and every
  end-to-end test of `make test`, which run nowhere else. `make test-unit
  GFORTH=.tools/gforth/bin/gforth-fast` runs the unit tests on gforth-fast
  (in every branch's tier). `make check-rest` runs the end-to-end tests outside
  `make test` once, and `test-cli-engines` (about 10 s) a second time, plain, for
  its gforth-fast comparison. `make test-unit GFORTH=<0.7.3>` runs in `make daily`.
- **Engine-dependent observations.** Three host observations differ on
  gforth-fast, which checks no stack depth and reports a division overflow
  as THROW -10: the underflow checks of `tests/program/clamp.fs` and
  `examples.fs` run only where `host-checks-depth?` (`tests/support/tester.fs`,
  from the engine's program name) holds, and `tests/program/ir_reader_files.py`
  accepts -10 or -11 for the smallest number divided by -1. Every other unit
  test passed unchanged on gforth-fast (2026-11-17, 96 s at `JOBS=2`).
- **Records.** gforth-fast prints Gforth 1.0's version, so
  `scripts/tested-tree.py` adds "(gforth-fast)" to its records' Gforth: a
  pass on one engine never stands for the other.

Measured with `JOBS=2` and the Lean cache. Before: the records of the
2026-11-14 pushes (`cdb9140f`, `c740069c`, `94b5bae4`; `d2f9baaf` without
the cache). After: `make tier` on `ef6a6ee7`, 2026-11-17, while another
agent's coverage run loaded the machine (load 1.2-2.4 on 10 cores). Wall
seconds; "command time" is the sum of the timed commands of the suite
(`LF_TIMING_LOG`; targets with their own `RUN := timeout` are not timed).

| Suite | Before | After |
| --- | ---: | ---: |
| `make coverage-check` | 461, 467 | 494 |
| `make test-unit` on gforth-fast (new) | — | 106 (96 in a first run) |
| `make check-rest` | 989-1,106 (command time 1,127, of it `test-cli` 320) | 949 (command time about 710) |
| Gforth 0.7.3: `make test` → `make test-unit` (push only) | 560, 566 (command time 1,035, of it end to end 490) | not run on the branch; about 300 by command time |
| a branch's full tier | about 1,450-1,570 | 1,549 |
| a code push's full tier | about 2,010-2,130 | about 1,850 (estimate) |
| the first push of a day, documentation only | 2,430 (`d2f9baaf`: the full tier without the cache) | the docs tier, about a minute (`make daily` runs the full tier by itself) |

A branch's full tier takes about as long as before: the new gforth-fast run
costs what `check-rest` saved, whose wall time at `JOBS=2` is set by its
long chain (`program-clamp-record`, the two `leanforth verify` runs, the
`Init` runs). The push saves the end-to-end tests on 0.7.3 (about 4
minutes), and the largest saving is that no push runs the cache-off full tier.

What now runs fewer times, and why that is safe: the end-to-end tests of
`make test` (`test-cli-1`…`4`, `test-front-e2e`, `test-author-e2e`,
`test-elab-data-e2e`, `test-program-verify-command`) no longer run on
Gforth 0.7.3, and `test-cli`'s four parts no longer run a second time in
`make check-rest`; they still run once per full tier on Gforth 1.0 (with
coverage), and their Forth code is reached on 0.7.3 and gforth-fast by the
unit tests of the same modules. `test-cli-engines` keeps the real
gforth-fast comparison in `make check-rest`, `reference-cli` runs
`bin/leanforth --fast` on its exports, and `make engine-gate` compares the two
engines on all of `Init`. Every test of `make check` still runs at least once
per full tier, and every unit test now runs on one more engine than before.

## Reuse checks (plan 9.4.8f, owner 2026-11-13)

Four scripts keep the reuse rule of AGENTS.md ("Reuse first") from failing silently. `make test` runs them (the
first three in `check-forth-quality`, the index in `check-docs`); each has unit tests on throw-away source trees in
`tests/scripts/`.

- `scripts/check-lib-callers.py`: builds the require/include/needs graph of `src/**/*.fs` (paths relative to the
  requiring file) and fails for a `src/lib/` file that no file outside `lib/` reaches, unless
  `tests/lib-callers-allowlist.json` lists it with a plan row id and a reason. An entry for a file that is used
  now fails too (stale), so the list only shrinks: delete the entry in the branch that adds the first caller.
  Files used by tests only are reported, not failed.
- `scripts/check-duplicates.py`: finds colon definitions with identical bodies of at least 6 tokens (8
  until reuse-out-2, 2026-11-13), after comments are dropped and words are lower-cased, in two normal forms. The
  shape form replaces every word defined in the same file (not in `lib/`; by `:`, `constant`, `variable`,
  `create`, `+field`, `begin-structure` or any defining word ending in `:`, such as `field:` or
  `context-slab:`) by a placeholder numbered by first appearance, so `in-x` and `ib-x` copies match, and so
  do parallel words that differ only in which local helper or field they use (a family). The copy form
  replaces every call of a colon word outside `lib/` by that word's role, the hash of its own copy form
  (numeric constants by their value), so that a copy calling the original file's helpers matches the
  original. It is a ratchet on `tests/duplicates-baseline.json`: a new group or a group with more copies
  fails and prints each copy as `file:line`, and so does a baseline group without a `reason` (`false
  positive: ...`, `family, table-driven later: ...`, `accepted: ...` or `planned: <plan row> ...`).
  `--report` prints every group with its reason, `--counts` the groups by folder. Update the baseline
  (`--update-baseline`, which keeps each reason whose key or member list is unchanged) only in a reviewed
  commit, as for `tests/forth-quality-baseline.json`; merging copies shrinks it. Limits: equal normal forms of
  unrelated words are possible (hence the reasons), and copies shorter than six tokens are not compared.
- `scripts/check-forth-quality.py` also fails for a row of `forth-reviews/LOG.md` dated 2026-11-13 or later whose
  Findings or Open text proposes a new `lib/` file or library word without a plan row id (`9.4.8a`, `FE1i-4`, `S2`).
- `scripts/lib-index.py` writes [LIBRARY_WORDS.md](LIBRARY_WORDS.md), the index of the public words of `src/lib/`;
  `make check-docs` fails when it is stale: run `python3 scripts/lib-index.py --write` and commit it.

### Removing a duplicate group (owner, 2026-11-19)

A group is **exact** when its copies are the same tokens and each word in them names the same definition from
every copy's file; only then can the script itself replace the copies by one word, identical by construction
(the owner's standing rule for kernel, core and import files: [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md),
"Clean-up: the stack approved"). Every other group is a **shape** group (the same code over different words),
merged by hand as before. `tests/scripts/test_duplicates_extract.py` tests the commands on throw-away trees.

1. `python3 scripts/check-duplicates.py --plan`: the groups that are no false positive, largest first (copies
   x tokens), each exact or shape, its files and folders, the lowest folder every copy may load
   (`src/README.md`'s layering), a file every copy loads that sees the phrase's words (the suggested home) and an
   existing word: a copy the others can already call.
2. `python3 scripts/check-duplicates.py --explain KEY` (a key or a unique prefix): the phrase, exact or shape and
   why, and each copy's place, stack comment, folder, wordlist (`module-open`, `set-current`) and lines.
3. `python3 scripts/check-duplicates.py --extract KEY --word NAME --stack "( a -- b )" --home FILE
   [--after WORD] [--comment TEXT] --dry-run` shows the diff; without `--dry-run` it writes. It refuses a shape
   group, a NAME defined with another body, a home that cannot see a word of the phrase, and a copy's file that
   does not load the home (it names the `require`; `--add-require` adds it); a copy named NAME or one in the home
   is used as the word. It works on a scratch copy of `src/` first: no other group may appear or grow; the
   baseline loses the group. Many at once: `--extract-table FILE`, one `KEY NAME "( stack )" HOME [AFTER|-]
   ["comment"]` per line, all or none.
4. Re-target any planted fault it reports as moved, run `python3 scripts/forth-metrics.py` on the changed files
   and their unit tests (`make test-changed`), and paste its "EXACT EXTRACTION BY SCRIPT" list (the copies
   rewritten in `src/kernel`, `src/core`, `src/import`) into the report to the owner. The Forth review and the
   tier still run.

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

### Parallel checking (plan 9.4.8p)

Parallel checking is a routine, tested property (owner, 2026-11-18:
"re-entrancy is important as is speed from multiple internal threads").
What `check --jobs N` guarantees is in `docs/user/COMMAND_LINE.md`; three
kinds of test hold it:

- **The tiers' small runs.** `test-cli-*` (`Jobs`, `Progress`, `Snapshots`:
  every export of the JSON tests and larger ones, text and JSON, at
  `--jobs 2` to `4`) and `test-cli-forth` (`tests/cli/leanforth.fs`: every
  kept fact of the serial run, planted scheduler faults, a check that
  throws, the driving context's borrowed input hashed before and after a run
  of eight workers five times; each of the ten parts the workers read, its
  block and its count, found changed; a move of that input planted during a
  run, mid-run, at the last tick and inside the decision on readiness, which
  must stop the run as an internal fault, cut at the slots final at the last
  comparison that found no change, the report saying it stopped and no
  snapshot written; `ck-final` and the tick's cut on their own).
- **`make test-parallel-stress`** (end to end, in `make test`, about 15
  seconds): an export of 5,000 tiny declarations generated by the test
  (`tests/cli/test_parallel_stress.py`) checked 5 times (`STRESS_REPEATS`;
  20 times in `make parallel-init`) with twice as many workers as cores, each
  run's text and exit status the serial run's. Workers above the cores need
  the test-only word `task-cores-test`, which `src/lib/task.fs` reads only
  when a program defines it before the file loads; the test starts Gforth on
  `src/main.fs` itself, as `bin/leanforth` does, with that word defined.
  `bin/leanforth` never defines it, has no option or environment variable for
  it and runs Gforth with its start-up file off (`GFORTH_ENV=off`: Gforth 1.0
  otherwise loads the file `GFORTH_ENV` names, or `~/.config/gforthrc0`,
  before `src/main.fs`, and such a file could define the word; Gforth 0.7.3
  reads none); a test sets `GFORTH_ENV` to such a file and finds `--jobs`
  still cut to the cores.
- **`make parallel-init`** (`scripts/parallel-init.py`; `make daily` only,
  never `make check` or a tier): all of Lean's `Init` checked with gforth-fast
  at `--jobs 8` and at `--jobs 1`, each twice (text with `--resources` and
  `--save-snapshot`, then `--json`). It requires the same exit codes, the same
  verdict text up to the resource report, the same JSON report but for
  `"measured"`, the same snapshot but for its information section (kind 17:
  version, commit, host, engine; compared section by section from the
  sectioned file's table), and in the parallel run's resource report not
  ready, forced and workers replaced all 0. It prints both wall times and the
  speed-up and records them with the result in
  `.claude/work/ci/parallel-init/DATE-COMMIT.json` of the main checkout. The
  Init export is machine-local, found as `make engine-gate` finds it
  (`PARALLEL_INIT=FILE` names another); without it the target says so and
  exits 4 (skipped, never a pass), so the daily run on such a machine is not
  complete. A floor for the speed-up is not set yet (plan 9.4.8p (1)). First run
  (2026-11-18, branch `parallel-1`, 10 cores shared with other agents, load
  11-16): `--jobs 8` 320 s, `--jobs 1` 1,159 s (text runs; JSON 292 s and
  1,185 s), a speed-up of 3.6; 57,919 checks handed out, none run again, not
  ready, forced or replaced; everything identical (the run itself failed on
  a bug of the script, the information section taken as kind 16; with 17, the
  comparison of the saved outputs found no difference). About 50 minutes
  in all.

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
`tests/mutants/faults.toml`, run by `scripts/mutants.py`. Every
`tests/mutants/faults.d/*.toml` is read with it as one list, in name order
(tactic plug-in design, slice (a1): a tactic's faults in a file of its own);
an id given twice, in one file or two, or a file that does not parse refuses
the whole list, and the history rule below follows a fault across the files.
No fault has moved there yet. Each entry names:

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
| `make mutants-check` | only the stale-entry check and the history rule, without running anything (part of `make check`, so the list cannot go stale unnoticed) |
| `make test-mutants` | the runner's own tests and the history rule (`scripts/mutants.py --history`; in `make test`) |

The history rule (plan 9.4.8j): a commit may change the replacement text
(`new`) of a fault that existed before it only when its message names the
fault's id. `scripts/mutants.py --check` and `--history` read every commit of
`main..HEAD` (`--base REF`) that changed `tests/mutants/faults.toml` and fail
for each such change whose commit does not name the fault (a merge counts
only for a text that differs from every parent's), so that an overwritten
fault, whose file may no longer load and whose guard is then silently off
(the s1-synth review's B1: 13 faults), cannot pass unnoticed. Changing a
fault's `old` text (re-targeting it at moved code), its reason or its test
is free.

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
every file, `--uncovered OUTPUT` writes each block that never ran as
`file:line:column` to a new output file (it refuses a path under `src/`,
`tests/`, `scripts/` or `docs/` and any file git tracks: it once overwrote a
source file), `--keep DIR` keeps the raw counts (about 3.5 GB for a
full run), `--check`, `--update-baseline`, `--baseline FILE`, and
`--save-full`, with which `make coverage` and `make coverage-check` keep each
file's never-run blocks in the main checkout's untracked
`.claude/work/coverage/last-full-run.json` for `make cover`.

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

### Before a tier: the pre-tier check

`scripts/pre-tier.sh` (2026-11-19) runs every cheap whole-repository check in one keep-going pass of about two
minutes and prints one line for each: a clean tree, the test classes, duplicates, the style ratchet and review
log, library callers, the progress check, the agents' definitions, the planted-fault table, documentation links
and examples, portable Forth, the Lean source citations, the export list, the standalone libraries, no runner
falling back to an unpinned `lean`, and a scan of the Python scripts for undefined, shadowed or twice-defined
names. An implementing agent runs it before handing a branch back, and it is run before every `make tier`: a
tier is then never the first place such a failure shows. In a worktree without `.tools`, give `GFORTH=` and
`LEAN=` as absolute paths. The branch coverage check (`make cover-changed`) is not part of it: it took 29-73 s
on the three branches measured on 2026-11-19 (below), so the tier runs it; run it while working to see the
untested lines early.

## Paying coverage debt (owner, 2026-11-19)

**No new debt** (owner, 2026-11-19, evening; `docs/project/OWNER_DECISIONS.md` "Coverage debt ended"): a branch
tests every never-run branch of its new or changed words before it merges; what follows is for finding those
gaps while working and for paying debt recorded earlier. Refusal paths are reached with the sweep harness
`tests/support/meta-sweeps.fs` (`heap-sweep`, `room-sweep`, `swept?`): one line per scenario refuses each
request in turn and compares the answer with the normal run.

Finding a file's never-run blocks used to need the 6-minute run of all of
`make test`. Now, in order (`tests/scripts/test_coverage_debt.py` tests the
commands on a tiny Forth file with a known never-run branch):

1. `make cover-debt`: the baseline's entries with never-run blocks, largest
   first, with their reasons (the to-do list).
2. `make cover FILE=src/x/y.fs [TESTS="tests/a.fs tests/b.fs"]` (`python3
   scripts/coverage.py --file ... [--tests ...]`): runs only Forth unit test
   files under coverage, in seconds, and prints the file's blocks, its
   never-run blocks now, the baseline's count and reason, and each never-run
   block: `file:line:column`, the word it is in, its source text, whether the
   baseline's reason names its line, and, when a full run was kept
   (`--save-full`), whether that run left it never run too. Its tests are the
   rule below ("Which unit tests"); `TESTS=` names others (no widening),
   `--all-tests` runs all that load the file at once. Exit 0 when the count is
   not above the baseline's. It counts unit tests only: end-to-end targets run
   code too, so it can list more blocks than the ratchet; a block the last
   full run also left never run is real debt. On 2026-11-19 `make cover
   FILE=src/front/tactic-induction.fs` (a file plan 9.4.8l I deleted the same
   day) took 14 s (5 of 29 test files, 3.5 s of runs) and listed 168 blocks,
   the baseline 83; `make cover FILE=src/front/tactics/case.fs` ran only the
   three test files that name one of its words and listed all 48 blocks never
   run, though `tests/front/tactic-lib.fs` runs the `case` tactic from `.lf`
   text: with the rule below it runs 12 of the 31 files that load it, in
   15 s, and lists none.
3. Write the tests, re-run step 2 until the block is gone.
4. Lower the entry without a full run: `python3 scripts/coverage.py
   --set-baseline src/x/y.fs --blocks N` (it prints the old and new entry;
   raising needs `--reason`, and a file with no never-run block before needs a
   reason naming each new block by its line; `--total M` for a new entry;
   `--drop-baseline FILE` removes one). `make daily`'s `make coverage-check`
   then checks the count over all of `make test`; a tier checks the branch's
   own changed lines (`make cover-changed`, below).

**Which unit tests** (`make cover` and `make cover-changed`; 2026-11-19). The
unit test files that load a source file are the Forth files under `tests/`
that the recipes of `make test`'s unit targets name (`make -n`;
`tests/test-classes.txt` classes the targets), whose `require` closure holds
the file, directly or through `src/main.fs` or any other chain
(`scripts/coverage.py`'s `UnitTests`, about a second for the 150 files of
2026-11-19). When more than 8 load it, a narrowed set runs first: those that
name a word the file defines, and those of its module's test folders —
`tests/TOP/`'s files for `src/TOP/...` (`tests/front/` for
`src/front/whnf.fs` and for `src/front/tactics/case.fs`) and all of
`tests/DIR/STEM/` for `src/DIR/STEM.fs` (a plug-in's own tests,
`tests/front/tactics/case/`). When a block asked about is left never run
(any block for `make cover`, a block on a changed line for `make
cover-changed`), every other unit test file that loads the file runs too
before the report, so a test that reaches the file only through text (a
`.lf` file, a name built at run time) still counts, and the check never fails
for lack of looking. Each test file runs on its own under the counting
wrapper, `JOBS` at a time (three processes each).

### The branch coverage check (owner, 2026-11-19)

`make cover-changed [BASE=main] [JOBS=4]` (`python3 scripts/coverage.py
--changed [BASE]`; owner, 2026-11-19, `docs/project/OWNER_DECISIONS.md`
"Coverage in the branch in seconds, the whole-suite ratchet at night") is
the rule "no new debt" checked directly, and the coverage step of every tier
and push (the suite `cover-changed`, run with the range's merge base and
recorded per tree like any suite). For the merge base of `BASE` and HEAD it
takes the Forth files of `src/` added or modified since (committed,
uncommitted and new; a deleted file is skipped, a renamed one is all new),
and in each the lines the branch added or changed: the lines of each hunk of
`git diff -U0` whose code differs, comment and blank lines left out (a hunk
that only edits comments or white space, a stack comment or an indentation,
changes no code). A file that defines no word (`src/main.fs`, a load list) or
whose changes are all comments needs no run. The others' unit tests run (the
rule above; each test file once for all the files), and every block on a
changed line that never ran is printed as `file:line: word: source text`.
It exits 1 when there is one, when a touched file has no unit test that
loads it (an end-to-end test does not count), or when a test fails; else 0.
The output is in a fixed order; the time goes to standard error.

The one exception: a block no input can reach passes when the file's entry
of `tests/coverage-baseline.json` has a reason that starts with
`unreachable:` and names the block's line (it is printed as accepted). Any
other reason, or one that does not name the line, does not excuse it.

It is not part of `scripts/pre-tier.sh`: on three branches of 2026-11-18/19
(each checked out at its head in a scratch worktree, JOBS=4, the machine
shared with other runs) it took

| Branch (range) | Touched source files | Unit test files run | Wall time | Result |
| --- | --- | --- | --- | --- |
| s2-debt (`11fa22e9..5a48eee4`) | 1 (`whnf.fs`, 2 changed code lines) | 21 of the 40 that load it | 29 s | passes |
| tactic move C4 (`5ccafff0..2b7665df`) | 15 (11 measured) | all that load them (widened) | 73 s | fails: 54 blocks |
| tactic-fidelity (`11fa22e9..b80169d3`) | 11 (10 measured) | all that load them (widened) | 58 s | fails: 2 blocks |

against 712-1,064 s for the tier's earlier `make coverage-focus`. All three
had passed the whole-suite ratchet; what fails are changed lines no unit
test runs: in C4 all 48 blocks of `src/front/tactics/case.fs` (only `.lf`
end-to-end runs reached the `case` tactic then; `tests/front/tactic-lib.fs`
runs it since), five of `src/front/meta-tactic/rename.fs` (55, 56, 58, 60,
68) and `src/cli/leanforth.fs:809` (`cli-again#`); in tactic-fidelity
`src/front/elab-pending.fs:292` (`ep-none`'s metavariable without a type)
and `src/front/whnf.fs:854` (`wc-unfold-run`'s `no-result exit`). Run it while
working, and before handing a branch back. `tests/scripts/test_cover_changed.py`
(in `make test-coverage`) tests it on a tiny Forth library in a throw-away
repository: an untested new branch fails naming its line until its test is
added, a changed line that runs passes and an old gap on an unchanged line is
not reported, comment-only edits need no run, a file only an end-to-end test
loads fails, a failing test fails, only an `unreachable:` reason naming the
line excuses it, and a test that reaches the file only through included text
counts after the widening.

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
