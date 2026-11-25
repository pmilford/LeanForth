# Done check: kernel timing and profiler

DONE CHECK: kernel timing and profiler

**Verdict: DONE for the claim as stated, at "works end to end" on a small input only.** Init was not run (not allowed here). Every Init figure in KERNEL_SPEED.md is therefore unchecked by me. The final "done" stage needs the logged Forth review, a green tier and the coverage record, none of which I checked.

**Claim (1).** A user can run `bin/leanforth check --json --resources EXPORT` and read each declaration's own check time in `measured.declarationMicroseconds`.
- I ran four runs of `tests/front/decide-slice.ndjson` (1290 declarations) with `GFORTH` set and `ulimit -u 500`. All four exited 0.

| Run | Time | `declarationMicroseconds` | Count | Min / max (µs) | Sum | Zeros |
| --- | --- | --- | --- | --- | --- | --- |
| `--jobs 1 --resources` | 9.7 s | present | 1290 | 0 / 1,225,192 | 8.69 s | 236 |
| `--jobs 4 --resources` | 4.5 s | present | 1290 | 0 / 1,238,729 | 8.97 s | 236 |
| `--jobs 1`, no flag | 9.8 s | absent | – | – | – | – |
| `--jobs 4`, no flag | 4.5 s | absent | – | – | – | – |

- All values are non-negative integers, and each count equals `declarations`.
- The sum is plausible. At jobs 1 it is 8.69 s against `microseconds.check` wall of 8.82 s. At jobs 4 it is 8.97 s against workers `busy` of 8.967 s, a little under it.
- The per-declaration sum matches the documented behaviour (COMMAND_LINE.md:1335) that members after a block's first are 0.
- I compared name and verdict per declaration across the four runs. They are identical, and all 1290 are accepted.
- Without `--resources`, `measured` holds only `microseconds`, `peakResidentBytes`, `stageBytes` and `engine`. The flag adds `workers` (jobs > 1 only) and `declarationMicroseconds`.
- The documentation says this: COMMAND_LINE.md:1335 describes the member (count, ordering, zeros, optional addition).

**Claim (2).** A user can run `make profile-check EXPORT=FILE` and get tables of where the check spent its time.
- `make profile-check EXPORT=tests/front/decide-slice.ndjson JOBS=1 GFORTH=… GFORTH_FAST=… PROFILE_OUT=<scratch>` exited 0 in about 4 s and printed 111 lines. I wrote the output to `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-kspeed/pc.out`.
- The tables are: phases (check 96.5%), families (exclusive, inclusive, owner), words exclusive, words inclusive, and the 25 slowest declarations by time. The slowest-declarations table has fuel, ns/fuel and verdict, and ends with `total 3650844 us; the 25 listed … (42.7%)`.
- With `GFORTH_FAST=/nonexistent` it printed one line, `profile-check: no gforth-fast at /nonexistent`, followed by make's `Error 5`. The exit code was 2.
- The tables were produced by the real sampler on a real run.
- The line `profile-sample: exit 100, 371 samples` looks like a failure but is not one. `scripts/profile-check.sh:35-36` subtracts Gforth's 100 offset. The check itself reported `exitStatus` 0, all 1290 accepted.
- The sampler's stderr line is not explained in PROFILING.md.

**Claim (3).** KERNEL_SPEED.md says exactly what was measured.
- I recomputed these figures and they are consistent:
  - 952 / 38.4 = 24.8 (line 22).
  - Candidate 1: 25-32% of 952 = 238-305 s (all of this row's figures below are in lines 326-332); 952 − 238 = 714 and 952 − 305 = 647; 714 / 38.4 = 18.6 and 647 / 38.4 = 16.9 (line 326).
  - Candidate 2: 5-8% = 48-76 s, leaving 571-666 s (line 327).
  - Candidate 5: 1.5% = 14 s. Candidate 7: 3.1% = 30 s. Candidate 3: 6-9% = 57-86 s. Candidate 4: 2.4% = 23 s and 4.7% = 45 s.
  - The 524 s result gives 13.6 times Lean.
- The document labels figures **measured**, **recorded** or **estimate** (lines 5-9), and every projection row is labelled an estimate (line 320).
- It claims no speed-up. Line 5 says "No kernel, core or import word was changed", and the candidates are listed as proposals under the review gate.
- Gaps:
  - Run 1 and run 2 are mixed: the summary's shares come from run 2, and the seconds from run 1's 952 s (lines 11-16, 320). This is disclosed, but sample shares times another run's seconds are estimates, and the "In short" list (lines 26-32) does not mark them as such.
  - KERNEL_SPEED.md:11 and 14 point to `.claude/work/init-profile-2026-11-25/`, which is not in the repository. A reader cannot verify run 2 from the repository.
  - I did not rerun the Init profile, so the tables at lines 77-97 and the 936.9 s and 952.5 s figures at line 203 are unverified by me.

**Corrected wording.**
- PROFILING.md, near line 31: add one sentence saying that a `profile-sample: exit 100` line means the check's own status 0 (the 100 offset is Gforth's `cli-leave`).
- KERNEL_SPEED.md:26-32: mark the percentages as run 2 sample shares and add "(**estimate**)" wherever they are converted to seconds.

## After the report (coordinator, 2026-11-25 11:29)

- The other requirements of "done" hold on main 3a8bf43c: Forth review and re-check logged
  ([2026-11-25-kernel-speed-measure.md](../forth-reviews/2026-11-25-kernel-speed-measure.md), verdict merge),
  the full tier passed on a64d047b (recorded by `scripts/push.sh`), branch coverage clean.
- `docs/development/PROFILING.md` now explains the `profile-sample: exit 100` line. The "In short" list of
  KERNEL_SPEED.md gives shares only (run 2), no seconds; its projection rows are labelled estimates.
- Init's figures were measured by the implementer's run (run 1) and the coordinator's kept profile (run 2,
  `.claude/work/init-profile-2026-11-25/`, machine-local); the done checker did not repeat them.
- Stage: **done** (the measurement; nothing is sped up yet).
