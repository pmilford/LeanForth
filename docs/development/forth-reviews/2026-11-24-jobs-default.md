FORTH REVIEW: jobs-default
Range 5ff649a0..1d2a9012 (7 commits). Findings: 3 blocking (one trust, one format for the owner to decide, one reuse), 3 test gaps (not blocking), 5 style, 2 minor docs. Verdict: merge after fixes.

**Blocking findings**

1. **BLOCKING (trust).** `src/kernel/env-schedule.fs:546-547`, `lf-sch-timed-check`. It leaves the start time (2 cells) on the data stack between the job's sentinel and the check. `job-call` (`lib/task.fs:212`) catches a check that "consumes and replaces the cell below it", but here the check rewrites the time instead, `lf-sch-lap` clamps the result to 0, and the result is published.
   - Reproduced in a copy with `lf-env-limit 1 = if 1+ then` planted at the head of `lf-check-declaration`, on constant-fixture:
     - branch `--jobs 1`, main `--jobs 1` and main `--jobs 2`: fixturePoly invalid (diagnostic 29, -4096), "the run stopped", exit 5;
     - branch `--jobs 2`: 3 accepted, exit 0.
   - So with a faulty check the verdict depends on the worker count and the guard fails open, and the default now sends every run through it.
   - Fix (the check again sees the sentinel directly below it): `: lf-sch-timed-check ( -- ) lf-sch-now 2>r lf-sched lf-sch-check @ execute 2r> lf-sch-lap lf-sch-busy+ ;`
   - Add a worker-path twin of `tests/core/environment.fs:782` `overwriting` (3 workers: invalid, stopped, exit 5) and a planted fault for it.
   - Also say in the header that the clock xt must be ( -- d ) and must not throw.
2. **BLOCKING (format; the owner decides).** `schemas/check-report-0.4.schema.json` and `0.5`, and `docs/user/COMMAND_LINE.md:1316`.
   - `measured.workers` now appears in every default `check --json` report.
   - I validated the branch's default report of `tests/cli/unfold.ndjson` against main's `check-report-0.4.schema.json`: "$.measured: additional property 'workers' is not allowed".
   - The precedent the docs cite does not hold. `anyLeanVersion` and `memoryPerCheck` appear only when an option asks for them ("a report without the option is as before"). `workers` needs no option, so the doc line "a report of a run without them is as before" is false.
   - `save` does follow the precedent (only with `--save-snapshot`).
   - Recommendation: raise the version (both files), or emit `workers` only on request. A version bump is called for under the schemas' own rule.
3. **BLOCKING (reuse).** Two general operations are copied again:
   - "add to a double in memory": `lf-sch-busy+` (`env-schedule.fs:545`) and `lf-sch-waited+` (`:617`) copy `d+!` (`src/import/ndjson-count.fs:89`), which also exists as `rr-d+!` (`run-record.fs:214`) and inline at `manifest.fs:286`;
   - "difference, at least 0": `lf-sch-lap` (`:544`) and `ck-less` (`check-run.fs:911`) copy `ck-since` (`check-run.fs:343`).
   - Fix: move both to `src/lib` and replace every copy, for example:
     ```
     : d+! ( d addr -- ) dup >r 2@ d+ r> 2! ;  : d-floor ( d1 d2 -- d ) d- 0 0 dmax ;
     : lf-sch-lap ( d -- d' ) lf-sch-now 2swap d-floor ;  : lf-sch-busy+ ( d -- ) lf-sch-busy d+! ;
     : ck-less ( d -- d' ) ck-run-wall 2swap d-floor ;  : ck-since ( d addr -- d' ) 2@ d-floor ;
     ```
   - Keeping doubles also removes the `d>s` that goes negative past 2^31 µs (35.8 min) on 32-bit cells.

**Test gaps (not blocking)**

4. **The timing tests are weak.** Waiting is defined as run minus busy, and the driver's busy as run minus waited, so "busy + waiting = run" holds whatever busy is. The 0.0021 s tolerance is honest about rounding but tests nothing measured.
   - "Waiting always 0" is caught only because busy < run.
   - My planted fault F5 (each check's busy halved, `lf-sch-lap 2/`) passed `tests/cli/leanforth.fs` and `Jobs.test_spent`.
   - Add a unit test with `ck-check-word!` set to a check that sleeps 20 ms and then checks, on 8 declarations with 2 workers: busy_all ≥ 160 ms, each worker's busy ≥ 20 ms × its checks, and the driver's waiting > 0.
5. **The default with `--snapshot FILE EXPORT` (a layer) is untested.**
   - I planted F1 (`cli-state opt-snapshot @ 0= and` in `cli-jobs-unset`, `leanforth.fs:282`, so a snapshot run stays serial).
   - It passed `tests/cli/leanforth.fs` and all 154 tests of `test_leanforth.py`; I re-ran Imports and Layers from the root: OK.
   - Add a `--resources --snapshot slice EXPORT` assertion "workers: N (the default)". The real run shows 36 checks handed out.
6. **A THROW in the last declaration has no unit test.** Planted F4b (`ck-jobs-stopped?` reverted to `lf-input-count <`) passes `tests/cli/leanforth.fs` and is caught only by the end-to-end `ExitCodes.test_5_thrown`. Add a `throwing-check` run (as at `tests/cli/leanforth.fs:842`) that throws at the last index.

**Style (not blocking)**

7. `lf-sch-wait-at` (`env-schedule.fs:172`, used at 615-619) is a field used as a register. Use the stack and drop `lf-sch-wait-at`, `-mark` and `lf-sch-ended`:
   `: lf-sch-timed-wait ( -- k ) lf-sch-now lf-sch-any-end >r lf-sch-lap lf-sch-waited+ r> ;`
8. `check-run.fs`: `ck-planned` and `ck-sched-timed` repeat the timing bracket and spell out `ck-state ck-plan-time` where `ck-plan-clock` and `ck-run-clock` already exist:
   `: ck-timing ( xt clock -- ) >r ck-sub-begin execute r> ck-sub-end ;  : ck-planned ( -- outcome ) ['] lf-sched-plan ck-plan-clock ck-timing ;`
9. `check-json.fs:227-233`: `cj-busy` opens an object that `cj-waiting` closes, and `cj-all` repeats the key pair. On the text side, `leanforth.fs:774-779` repeats `cli-second. cli-second. cr`. Factor:
   `: cj-spent ( db dw -- ) 2swap s" busy" cj-us s" waiting" cj-us ;  : cj-task ( db dw -- ) cj-object cj-spent cj-end-object ;  : cj-worker ( k -- ) dup lf-sched-busy rot ck-waiting cj-task ;  : cj-all ( -- ) ck-busy-all ck-waiting-all cj-spent ;`
   Do the same with a `cli-spent-row ( db dw -- )` on the text side.
10. `leanforth.fs:284` `cli-workers` uses flag arithmetic (`dup 0= cli-jobs-unset and or`). Clearer: `cli-jobs ?dup 0= if cli-jobs-unset then`.
11. `cli-worker.` and `cj-worker` read `lf-sched-busy` twice (two context switches) through `ck-waiting`. Harmless.

**Docs (minor)**

12. With 1 core (`task-cores-test 1`), `--jobs 4 --resources` prints no workers line at all, so the cut to one is silent. A host without `/sys/devices/system/cpu/online` is stated in `COMMAND_LINE.md:928-930`. Consider printing "workers: 1 (--jobs 4, 1 core)". Note also that "cores" means online CPUs, not affinity or container quota.
13. `COMMAND_LINE.md:917` still says the parallel path's "[kernel] review is pending", while it is now the default. The owner decided this on 2026-11-23; just keep the wording current.

**A(i). Verdicts by worker count.** For each input I compared exit code, stdout, stderr (timing lines removed) and the JSON without `measured`, for branch `--jobs 1`, the default, `--jobs 2`, `--jobs 4` and main's default, run 2 at a time.

| Inputs | Exit codes | Difference |
|---|---|---|
| 15 accepted exports (composition, fixture, chain, inductive, nested, sharing, sharing-universe, unfold, irrelevance, let-b, let-zd, odd-names, odd-string, sibling, dependent) | 0 | none |
| rejected: wrong-argument, empty block, literal, sharing twins, `cli/bugs` ×4, dupl80 | 1 | none |
| postulate, unsafe | 0 | none |
| unsupported: kinds; unknown: the UNKNOWN case; other-lean (wrong version) | 2 | none |
| `--any-lean-version` | 0 | none |
| `--strict-axioms` on axioms, kinds, nested | 0, 2, 0 | none |
| `--fuel 0` fixture, `--fuel 30` composition, `--fuel 3000` nested | 3 | none |
| `--memory-per-check 1`; and 3 | 3; 0 | none |
| huge-number | 3 | none |
| malformed: loose (with and without manifest), README, no-such | 4 | none |
| wide60, renamed20, fan40, horizon | 0 | none |
| `--progress=1` | — | none |

- A last declaration that is full or exhausted (double12 cut after big): identical, no "stopped" line.
- `.lf` (07-add-comm accepted, wrong, `--fuel 50`; 10b-typo exit 4): identical, except that `--jobs 2/4` add the note (expected; there is no note under the default).
- `--save-snapshot` (nested, init-slice): identical text, and the files are byte-identical for `--jobs 1`, the default and `--jobs 4`. Main's files differ only in the build commit string and its hashes.
- `--snapshot` alone, `--snapshot` plus an export (40 from the snapshot, 67 checked) and `--snapshot` plus a `.lf` text: identical across all five, text and JSON.

**A(ii). A THROW in a check.** I planted `lf-env-limit N = if 4242 throw then` in a copy of `lf-check-declaration`.
- Fixture at 0, 1 and 2; nested at 0 and 53; wide60 at 30 and 59. `--jobs 1`, the default, 2/3 and 4 give identical text and JSON (`stopped` true, exit 5).
- A throw in the last declaration gives the serial run's lines at every count.
- No misfire: rejected, unsupported, full or exhausted last declarations do not say "stopped".
- `--record` never reaches the scheduler (it runs `cli-checks`).

**A(iii). Cores.** `task-cores-test` with 1, 2, 3 and 4 cores: the default gives none, 2, 3, 4 workers; `--jobs 4` gives the same. With 1 core it is silent (item 12).

**B. The kernel file.** With correct checks, nothing the kernel accepts, rejects, reads or writes changes:
- the clock only feeds counters; readiness, the order checks are handed out, fuel and the order results are published are untouched;
- with no clock everything is 0 (the `untimed?` unit test);
- `lf-sch-busy` is a context record: each worker's job writes it in its own context (`lf-context` is a USER variable, `context-new` zeroes it), and the driving task reads it after the run;
- no host word appears in the file; the CLI hands in `ck-wall-now` (`utime`) as an xt, and workers execute it.

The exception is item 1: the job wrapper weakens the stack guard, so a faulty check is accepted in a worker where it was invalid. That is not behaviour-preserving until it is fixed.

New state:
- in the shared `lf-sched` record: `lf-sch-clock` (written by the driving task before the run), `lf-sch-waited` and `lf-sch-wait-at` (written by the driving task outside jobs). ADR 0009 lists this record as shared; it is erased by init and free.
- in `ck-state`: `ck-sub-mark`, `ck-plan-time`, `ck-jobs-time`, `ck-save-tried` (driving task only, erased by `ck-start`).
- no new VARIABLE or VALUE.

**Planted faults** (temporary copy; `tests/cli/leanforth.fs` plus 7 named Python tests):

| Fault | Caught? | By |
|---|---|---|
| F1 default ignored for a snapshot | no | — (item 5) |
| F2 `--record` refused under the default | yes | `test_default_with_record` |
| F3a a worker's waiting always 0 | yes | unit test and `test_spent` |
| F3b the driving task's waits not counted | yes | unit test and `test_spent` |
| F4a `ck-jobs-stopped?` always false | yes | unit test and `test_5_thrown` |
| F4b `ck-jobs-stopped?` reverted to main's test | yes, end to end only | `test_5_thrown` |
| F5 busy halved | no | — (item 4) |

`--record` cannot run in parallel (separate path), so F2 was the realistic form of that fault.

**Reuse.** I grepped `src/` for `d+!`, `2@ d+ … 2!`, `0 0 dmax`, `um/mod` and sum loops; the findings are in item 3. The text and JSON reports share the `ck-*` numbers and do not compute them twice. `check-duplicates.py`: none new or grown. `check-lib-callers.py`: OK. `check-forth-quality.py`: the ratchet holds.

**Style metrics** (`forth-metrics.py --words 10`, 4 files): 1168 words; 69% of 1-2 lines, 29% of 3-5, 17 of 6-10, 3 over 10. All long words are older code (`cli-check-usage.`: 38 lines of help text, 2 lines changed). Every new word is 1-3 lines, with no PICK/ROLL and no raw `cells +`. Stack comments are correct.

**Not looked at or not run:** Gforth 0.7.3, gforth-fast, Init, Lean; the tier and `cover-changed` (as instructed); the rest of `COMMAND_LINE.md` (D only partly, items 2, 12, 13).

Probe scripts and outputs are in `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-jobs/` (`compare.py`, `compare.out`, `faults.py`).

## Resolution

The branch was rebased on main `3c622ac1` before the fixes; the reviewed commits are, after the rebase,
`7d77e04e`, `76c03546`, `9e9e0baa`, `eb2807e3`, `f5592a4c`, `ee8c30a4` and `20495233` (the review's range
`5ff649a0..1d2a9012`).

1. Fixed in `23edbba0`: `lf-sch-timed-check` keeps the start time on the return stack, so the check finds the
   job's sentinel directly below it; the header says the clock is ( -- d ) and must not throw. Since `ee19b32b`
   both timings share `lf-sch-timing ( i*x xt -- j*x d )`. A unit test runs a check that consumes and replaces the
   cell below it at 3 workers (tests/cli/leanforth.fs, `overwrite-facts`: invalid, stopped, the serial run's
   facts); fault `jd-time-under-check` puts the time back on the data stack and is caught. The review's
   reproduction (`lf-env-limit 1 = if 1+ then` at the head of `lf-check-declaration`, constant-fixture,
   `--jobs 2`): before, 3 accepted, exit 0; after, fixturePoly invalid (diagnostic 29), "the run stopped",
   exit 5, as at `--jobs 1`. The other wrappers of this branch hold no value on the data stack across a guarded
   call: the driving task's timed wait runs no check (`job-wait-any` only waits; the serial host runs a job inside
   `job-submit`, under `job-call`'s own sentinel), and check-run.fs's timing bracket keeps its mark in `ck-state`
   (since `e6ff4276` its clock on the return stack).
2. Fixed in `409a1d82` (the coordinator's decision under the owner's approval of 2026-11-24 of an additive
   change): `measured.workers` and the `save` phase appear only with `--resources`, as `anyLeanVersion` and
   `memoryPerCheck` appear only with their options (`ck-resources!`, `ck-spent?`, `ck-phase-shown?`). A check
   `--json` report without `--resources` is as before: `Jobs.test_default_as_before` validates default reports
   (the default's workers, `--jobs 3`, `--save-snapshot`, and a 0.5 report against a snapshot) against the schemas
   with those members taken out. No version changed. A `--resources --json` report of a run with workers (or with
   `--save-snapshot`) carries the members, and the schemas 0.4 and 0.5 as they were before 2026-11-24 refuse it
   (`measured` has `additionalProperties: false`): whether that needs a version bump is the owner's decision.
3. Fixed in `ee19b32b`: `d+! ( d addr -- )` and `d-floor ( d1 d2 -- d )` in `src/lib/bounds.fs`, with unit tests,
   faults `jd-d-add-overwrites` and `jd-d-floor-negative`, and their lines in FORTH_LIBRARY.md and
   LIBRARY_WORDS.md; every copy replaced (`lf-sch-busy+`, `lf-sch-waited+`, `lf-sch-lap`, ndjson-count.fs's
   `d+!`, run-record.fs's `rr-d+!`, manifest.fs's inline sum, `ck-since`, `ck-less`, and `ck-after?`'s test); the
   times stay doubles. `d+!`'s two return-stack operations moved with it in the style baseline (bounds.fs 6 to 8,
   ndjson-count.fs 18 to 16); env-schedule.fs keeps its count by `lf-sch-visit`'s default branch taking `nip nip`.
4. Fixed in `dd70df4e`: `sleep-facts` (a check that sleeps 20 ms, 2 workers, counted per worker); fault
   `jd-busy-halved` is caught.
5. Fixed in `dd70df4e`: `Jobs.test_default_with_snapshot`; fault `jd-snapshot-serial` is caught.
6. Fixed in `dd70df4e`: `thrown-last` (a THROW in wide60's last check at 1 and 3 workers); fault
   `jd-last-throw-unit` is caught by the unit test.
7. Fixed in `ee19b32b`: the wait is timed on the stack through `lf-sch-timing`; `lf-sch-wait-at`,
   `lf-sch-wait-mark` and `lf-sch-ended` are gone.
8. Fixed in `e6ff4276`: `ck-timing ( xt clock -- )`, with `ck-plan-clock` and `ck-run-clock`.
9. Fixed in `e6ff4276`: `cj-busy` and `cj-waiting` neither open nor close an object; `cj-spent`,
   `cj-driver-spent`, `cj-all` use them; the text rows end in `cli-row-end`. Each value is read as it is written,
   so no pair needs a `2swap` (the files' shuffle counts are at their baseline).
10. Fixed in `e6ff4276`: `cli-workers` returns `cli-jobs` or, when none was given, the default, without flag
    arithmetic (written as an early exit: the `?dup 0= if` form joins a shape group of `check-duplicates.py`).
11. No change, as the review says.
12. Fixed in `bf079f00`, `445c41e4` and `6aacd0c3` (unit tests of the line, for `make cover-changed`): with fewer cores than asked the workers line says so ("workers: 1 (--jobs 4,
    1 core)", "workers: 2 (the default 4, 2 cores)"); `Jobs.test_fewer_cores` with the test-only
    `task-cores-test`; fault `jd-cut-silent`. COMMAND_LINE.md says "cores" are the CPUs Linux has online, not
    affinity or a container's quota.
13. Fixed in `bf079f00`: COMMAND_LINE.md quotes the plan's row 7.3.1 for the scheduler's review status ("review
    rvS7 not blocking, owner-approved 2026-11-12") and names the owner's decision of 2026-11-23 for the default.

## Re-check of the fixes (2026-11-24)

The independent re-check of the fix commits (`23edbba0..a62128a5`) verified finding 1 as fixed: the job's sentinel
is directly below the check on every path, a THROW included; three planted faulty checks (the review's `1+`, an
extra cell, a dropped cell) give invalid, stopped and exit 5 at `--jobs 1`, the default, `--jobs 2` and `--jobs 4`
alike; with correct checks nothing the kernel accepts, rejects, reads or writes changes relative to main, and the
one kernel edit outside the review's list (`lf-sch-visit`'s default branch) has the same stack effect. Finding 2:
without `--resources` the report's members are those of main and validate against main's schema; the new members
follow the pattern of `anyLeanVersion` and `memoryPerCheck`, and the schema files state no rule that calls for a
version bump. Findings 3 to 12 verified. One blocking item, fixed in `d2bdd882`: `cli-workers` re-implemented
`first-nonzero` (lib/bounds.fs). One style note not applied: joining `cj-run-times`'s open with
`cj-workers-body`'s close puts the body into a shape group of the duplicate check, so the two words stay as they
are. Verdict: merge after that one-line fix.

