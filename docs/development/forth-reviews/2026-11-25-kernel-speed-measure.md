FORTH REVIEW: kernel-speed-measure
Range reviewed: 98f36c00..de002ea9 (3 commits), worktree agent-a98a4435caa691159. 12 findings: 2 blocking, 5 medium, 5 low.
Verdict: merge after fixes. Fix findings 1 and 2, or cite a plan row for 2. Fix 3 to 6 in this branch. They are small, and the document is the branch's deliverable.

Findings
1. BLOCKING (reuse). src/cli/check-run.fs:697. `ck-timer-stop` repeats `ck-since` from the same file (line 355: `2@ d-floor`). Fix: `: ck-timer-stop ( -- ) ck-wall-now ck-timer timer-began ck-since ck-took 2! ;`
2. BLOCKING unless a plan row is cited (reuse). `ck-timed-check` (check-run.fs:698) and the kernel's `lf-sch-timing` (src/kernel/env-schedule.fs:549) do the same job: read the clock, run, read it again, floored difference. The implementer says sharing them needs a kernel change. That is true, but under the owner's 2026-11-19 rule a behaviour-preserving kernel refactor is ordinary work (full tier). Suggested library word in lib/bounds.fs beside `d-floor`: `: timed ( i*x xt clock -- j*x d ) dup >r execute 2>r execute 2r> r> execute 2swap d-floor ;`. The start then waits on the return stack, as it does today in the scheduler, which is safe for job-call's sentinel and for THROW. `lf-sch-timing` becomes `['] lf-sch-now timed`. ck-timer then needs only `timer-took`, and `timer-began` goes away.
3. Medium. scripts/profile-sample.py:117-124. A sampler stopped by SIGTERM or SIGINT sent to its own pid leaves the traced child running. Reproduced: `/bin/sleep 6.5` was still alive after both signals (I killed my own leftovers). With a real check that is a gforth-fast checking Init for 16 minutes. Fix: seize with `PTRACE_O_EXITKILL` (data 0x100000), and wrap the loop in try/finally that kills and reaps the child. In the fork child, wrap `execvp` and call `os._exit(127)` with a message.
4. Medium. Unclear failures. With GFORTH_FAST=/nonexistent, the run gives two Python tracebacks (execvp in the forked child, then profile-summary's missing check.syms), not one clear message. There is no check of the machine or engine: profile-check.sh:19-23 and profile-sample.py have no `uname -m` test, and line 150 ignores PTRACE_GETREGS failure, so on aarch64 every sample would silently read "<ip?>". Fix in profile-check.sh: `[ "$(uname -m)" = x86_64 ] || { echo "profile-check: x86-64 Linux only" >&2; exit 5; }; [ -x "$GFORTH_FAST" ] || { echo "profile-check: no gforth-fast at $GFORTH_FAST" >&2; exit 5; }`. Also check the GETREGS return value.
5. Medium. docs/development/KERNEL_SPEED.md:21-25. "In short" sets an inclusive share (validity 40%, table 39.6 incl) beside exclusive ones (reads 33%, hashing 13%) as two parts of the gap, and never says they overlap. The 33% exclusive reads include reads made below validity words. "Hashing 13%" is the term-construction-and-hashing family (13.5 excl), but line 85 gives hashing by file as 16.6%. Fix: give the overlap (for example, the share of the 33.1% that lies under a validity word, from `profile-summary.py --under`), use exclusive shares only in the summary, and use one hashing figure.
6. Medium. KERNEL_SPEED.md:268 and 284-286. The projection adds up overlapping candidates. Candidate 1's validity family counts `lf-fvars-live?` (the regex `-live\?$`), which is half of candidate 6's lookup cost. Candidate 2's audit (`lf-mls-checks`, `lf-cterm-check`) is inside candidate 1's 39.6%. Candidate 7's memo hashing overlaps candidate 4. "About 10% of the 20%" can be read as 10 points or as 2 points. The arithmetic does reproduce when they are added as points: 25-35+10+2+2+4 = 43-53%, then 952 s → 430-520 s → 11-14 times Lean's 38.4 s. Candidates 3 and 4 are then taken from what remains (×0.85 → 370-450 s, 10-12 times). None of this is written out. Fix: add a short table (candidate, seconds, overlap removed, seconds left, ratio to Lean) and state whether the shares add or compound.
7. Medium. KERNEL_SPEED.md:267, candidate 1. It names the checks (environment, store, handles) but not where they are called from: the top callers by count of `lf-env-current` (384 M calls), `store-count-valid?` (3,644 M) and `between?` (13,126 M). It also does not state the invariant that lets a handle checked once at pass entry stay valid for the whole pass: no store rollback or free during a pass, handles made in the pass valid by construction, no other context's handles. Note also that `between?` is a general bounds word, so counting all of it as "validity" overstates the share. Add the callers and the per-entry checks that must remain.
8. Low. KERNEL_SPEED.md:66-81. The document's family rows are not the tool's families. The tool prints "core stores: reads of terms, names, references" plus "other library" (17% on decide-slice); the document prints "Reads of terms, stores, slabs" and has no "other library" row. A reader running `make profile-check` cannot get the 33.1% back. State which files were moved between rows, or rename the families in profile-summary.py.
9. Low. Two faults that the tests catch are not in tests/mutants/faults.d/kernel-speed.toml. Add them as D2 and D3 (see below). D3 is the regression from the earlier branch.
10. Low. check-run.fs:72-75 says the time is "0 for ... a check that threw". A check the stack guard catches has already finished, so it keeps its time. Seen in the planted run: 372 µs for the invalid declaration 1 at `--jobs 2`. Reword to "a check that threw before it ended". There is also an edge case I did not reproduce. `lf-sch-rerun` (a check that began too early) does not clear `ck-took`, so a refused begin later in the same worker would keep the discarded check's time. Fix: record `lf-env-limit` in ck-timer at start, and have `ck-keep-time` keep the time only when it is for d.
11. Low. scripts/profile-symbols.fs:17-23. `sym-buf` is a counted string. Its length byte wraps past 255 and `sym+` can write past the 512-byte buffer. The longest line today is 150 characters; a longer checkout path would silently truncate lines. Fix: write the pieces with `write-file`, without a buffer.
12. Low. tests/test-classes.txt:81. The e2e row sits in the unit section. Move it under "# make test: end to end".

A(i) planted `lf-env-limit 1 = if 1+ then` at the head of `lf-check-declaration` (a copy; constant-fixture, GFORTH=gforth 1.0):
| jobs | flags | exit | answer |
| 1 | none | 5 | "run stopped: a check threw, or publishing failed"; 1 accepted, 1 invalid, 1 not checked |
| 1 | --resources --json | 5 | same verdicts |
| default | none / --resources --json | 5 / 5 | same |
| 2 | none / --resources --json | 5 / 5 | same; `workers.each` lists 2 workers, so the parallel path ran |
`ck-timer` keeps the start in the context record (`timer-began`), not on a stack, so the job's sentinel is directly below the check on every path. On a THROW, `ck-timer-stop` is skipped and the 0 left by the previous keep is kept (the thrown-took tests cover 1 and 3 jobs).
A(ii) Six exports at `--jobs 1`, 2, 4 and the default, with and without `--resources`, text and JSON: constant-fixture, unfold, decide-slice (1290 declarations), nested, composition-wrong-argument (exit 1) and after.list-left-out… (exit 2), the last two with `--no-manifest`. Exit codes, verdict lines, summaries and every JSON member except `measured`/`settings`/`run` were identical: 0 differences. Against main (read-only), member names matched exactly without `--resources`; with it, the only addition was `/measured/declarationMicroseconds`. The times are non-negative, one per declaration, and 0 for a block's later members. Their sum is 0.5-1 µs per job below `workers.busy` (for example 9,068,142 against 9,068,754).
A(iii) Without `--resources` the clock is still read twice per check, and the 2-cell time is copied and cleared on every keep. That is about 50 ns against a 2.8 ms median declaration, and COMMAND_LINE.md says so. Acceptable.
A(iv) No new module-level state. One new context record, `ck-timer`: the task running the check writes it (a worker, or the driver serially), and `ck-keep` reads and clears it in the same context after `job-wait`. One change for workers: they now read `ck-state ck-checker` in place on each check (before, the driver read it once). It is written only before the run, by `ck-start` and `ck-filling`; the comment should name this read.
Kernel, core and import: `git diff --stat 98f36c00..de002ea9 -- src` shows only src/cli/check-json.fs and src/cli/check-run.fs changed. No kernel, core or import word changed.

Planted faults (copy; `gforth tests/cli/leanforth.fs`, about 7 s each):
- D1, the member written without `--resources`: already in the list as ks-json-unasked. I did not re-run it.
- D2, start minus now with `d-` (a negative time): caught, `INCORRECT RESULT T{ 2 took-facts }T`.
- D3, the start left on the data stack: caught by the existing `T{ 1 overwrite-facts }T`.

Tools: the sampler uses ptrace (SEIZE/INTERRUPT/GETREGS through ctypes) and /proc/PID/mem and /proc/PID/maps. No perf, no download, no new dependency. `profile-symbols.fs` is loaded only by profile-check.sh, never by bin/leanforth or main.fs. test_profile_check.py ran 5 tests in 1.3 s and left the worktree clean. Its class is right (partly unit, partly e2e). profile-check on decide-slice: exit 0. The owner column adds up to 100%. The ns/fuel figure is 1000·µs/fuel, and document rows 1-2 recompute exactly.
Spot-checked figures, all recomputed correctly: 952/38.4 = 24.8; 0.396·952 = 377 s; 114.5 s / 250.1 M = 458 ns; 147.6 s / 384.3 M = 384 ns and 6,635 per check; hashing by file 8.1+5.1+3.5 = 16.7.
Labels are present throughout, and the wording is clean: no "LeanForth proved", no result labels.

Forth style: forth-metrics on check-run.fs, check-json.fs and profile-symbols.fs. 486 words: 74% are 1-2 lines, 3 are 6-10 lines (all older code in check-json.fs), none longer; 1 new context member; no new globals in src. Every new word is 1-2 lines with stack comments. Two nits: `ck-keep-time` copies a double with `2 cells move` where `ck-took 2@ rot ck-kept cks-us 2!` reads better, and taking and clearing the time could be one named word.
Duplicate check: 186 baseline groups, none new. Lib-callers check: all clean.
Reuse searched: FORTH_LIBRARY/lib (bounds.fs `d-floor`), all of src for `d-floor`/`2@ d-floor`/timing phrases (found `ck-since`, `lf-sch-timing`), check-duplicates.py, check-lib-callers.py.

Not looked at: test_leanforth.py's new cases in detail; PROFILING.md and PROJECT_PROGRESS.md text; profile-summary.py beyond its families. Not run: gforth-fast for the Forth tests, Gforth 0.7.3, Init or Mathlib, a non-x86-64 host. Finding 10's edge case is from reading the code only. An AI review does not replace the owner's review.
Probe files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-kspeed/ (compare.py, compare.out, d2.out, d3.out, pc.out).

## Resolution (2026-11-25, after the rebase on main `87e2d451`: the reviewed commits are now `28d3056c`, `f9bf465d`, `362a4a6d`)

1. Fixed in `b23d55a3`: `ck-timer-stop` is gone; the check is timed through `timed` (finding 2).
2. Fixed in `b23d55a3`: `timed ( i*x xt clock -- j*x d )` in `lib/bounds.fs` beside `d-floor`, written
   `tuck execute 2>r swap >r execute r> execute 2r> d-floor` (no deep shuffle; the start and the clock wait on the
   return stack). `lf-sch-timing` is `['] lf-sch-now timed`, `ck-timed-check` is
   `ck-check-word ['] ck-wall-now timed ck-took 2!`; `timer-began`, `ck-timer-start` and `ck-timer-stop` are gone.
   Tests in `tests/lib/lib.fs` (a word that takes the cell below it, a clock set back, a THROW passing through with
   the return stack restored), fault `ks-timed-backwards`, `FORTH_LIBRARY.md`'s bounds row; fault
   `ks-time-untimed` re-quoted (named in the commit). Behaviour kept: the planted `lf-env-limit 1 = if 1+ then` at
   the head of `lf-check-declaration` (temporary edit, reverted), constant-fixture, Gforth 1.0:
   `--jobs 1`, `--jobs 2` and the default, each with no flags and with `--resources --json`: exit 5 every time,
   "run stopped: a check threw, or publishing failed", 1 accepted, 1 invalid, never accepted.
   Style: `src/lib/bounds.fs` return-stack operations 8 -> 12 (the baseline is 8; `env-schedule.fs` 18 -> 16).
   `timed` must keep three cells (start and clock) across xt, which takes four return-stack operations at least,
   and no other word of the file can lose one without a deep shuffle. The ratchet warns on the branch; the merge
   needs the baseline raised for this file in a reviewed commit, or a refactor the reviewer names. Open.
3. Fixed in `105f5247`: `PTRACE_O_EXITKILL` at the seize, a `finally` that kills and reaps a child still running
   (SIGTERM exits through it; a child already reaped is not killed), and the fork child's exec failure gives exit
   127 with one message. Probe: a sampler sent SIGTERM left no `sleep` behind.
4. Fixed in `105f5247`: `profile-check.sh` refuses a machine other than x86-64 and a missing gforth-fast with exit 5
   and one line; the `PTRACE_GETREGS` result is checked (exit 5, one line). Tests `Failures.test_no_engine` and
   `Failures.test_command_not_run` in `tests/scripts/test_profile_check.py`.
5. Fixed in `3c73fe27`, from a second profile of Init (run 2, 2026-11-25 07:59, 57,421
   samples, kept in `.claude/work/init-profile-2026-11-25/` of the main checkout; shares comparable, wall
   time not). "In short" now gives exclusive shares only (reads 40.3%, hashing 16.3%, validity 12.5%), the
   overlap (16.7 points of the reads and 4.1 of the hashing lie under a validity word; 35.9% inclusive) and
   one hashing figure (`htab`, `hash32`, `memo` by file). Section 1 and 2 are recomputed wholly from run 2;
   the document says which run each section's numbers are from. Computed with a scratch script over
   `check.prof` and the tool's families.
6. Fixed in the same commit: section 10 is a table (candidate, basis, overlap removed, points, seconds,
   seconds left, times Lean), shares added as points of 952 s, each row net of the rows before it. The range
   changed: the algorithm changes give 14-16 times Lean (was 11-14), with Forth macros 11-14 (was 10-12),
   native 10-13.5 (was 9-11). Candidate 6 is almost wholly inside candidate 1 (0.4 points left).
7. Fixed in the same commit: candidate 1's callers by samples (`lf-env-current` only through `lf-env-ours`,
   from `lf-whnf-env?` 11.87 and `lf-env-snapshot` 3.08; `store-count-valid?` mostly from `mark-this?` 2.12
   and `lf-pool-sound?` 0.98; `between?` 0.57 from validity callers, 1.96 from others, 1.67 of those under a
   validity word further out), and the invariant, marked as a design assumption, with the checks that stay
   at a pass's entry.
8. Fixed in the same commit, the smaller change: `profile-summary.py`'s reads family is now "reads of terms,
   stores, slabs (src/core, store.fs, slab.fs)", and the document prints the tool's rows one for one. No
   expected table in `tests/scripts/test_profile_check.py` named the old family; a new test
   (`test_store_reads_family`) pins the regrouping.
9. Fixed in `69d2bf90`: faults `ks-time-negative` (D2) and `ks-start-under-check` (D3), both caught by
   `tests/cli/leanforth.fs` (`scripts/mutants.py --only`: 4 run, 4 caught, with `ks-time-untimed` and
   `ks-timed-backwards`).
10. The comment is reworded in `b23d55a3` ("a check that threw before it ended"). The `lf-sch-rerun` edge case is
    left, open: a test needs a refused begin after an early check in the same worker, which no test reaches today.
11. Fixed in the same commit: `profile-symbols.fs` writes each piece with `write-file` (`sym-type`,
    `sym-char`, `sym-end`), no buffer. A direct run on `src/main.fs` wrote 29,026 lines in the old format;
    `make test-profile-check` passed (8 tests).
12. Fixed in `69d2bf90`: the `test-profile-check` row is in the end-to-end section.
