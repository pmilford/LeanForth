# Done check: the replace memo's cut and the lean instantiation walk

DONE CHECK: kernel memo cut and lean walk

**Verdict: MIXED.** The behaviour claim holds on everything I ran: same verdicts, same fuel, same output. The Init timing and memory figures I could not rerun. The documents still say "not merged", although the code is on main.

Method: `git archive ea791fac` extracted to `<scratch>/before`. I symlinked `.tools` into it, which is the one thing I added there. All commands used absolute `GFORTH=.../.tools/gforth/bin/gforth-fast`, `ulimit -u 500`, `nice -n 10`, one process at a time. Scratch is `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-ks3/`. The branch commits (2f7f1f9f, a96646ff) are ancestors of HEAD, so the change is on main. CPU mode is "day".

**Claim 1. A user can check an export with `bin/leanforth check` and get the same verdicts and fuel as before.**
- Stage: works end to end on a small export. The Init numbers were not run.
- Command: `bin/leanforth check --json --resources --no-manifest --jobs {1,4} tests/front/decide-slice.ndjson`, run from `before` and from the repository, twice each. All 8 exit codes were 0.
- A `python3 -I` diff outside `measured`, `settings` and `run` showed identical JSON in all four pairs: 1290 declarations, fuel total 2,649,895 on both sides.
- Check-phase wall times, before then after (µs):

| Jobs | Run 1 | Run 2 |
| ---: | ---: | ---: |
| 1 | 2,641,489 then 2,593,336 | 2,633,749 then 2,580,646 |
| 4 | 1,080,554 then 1,054,596 | 1,096,507 then 1,022,679 |

- Peak memory, before then after:
  - 1 job: 49.32 MB then 49.46 MB.
  - 4 jobs: 60.0 MB then 61.6 MB (run 1), and 59.3 MB then 62.0 MB (run 2).
- `uptime` before each after-run showed load about 0.5, so the machine was quiet.
- Timing: the after run is about 1.5-2% faster at one job and 2-7% faster at four. On 2 or 3 s runs with 2 runs each, that is within noise. Do not claim a speed-up from this export.
- The peak is slightly higher after (+0.3% at one job, +3-4% at four). It does not show "unchanged" at four jobs.
- The Init figures (656.5 s -> 637.0 s at one thread, 182.1 s -> 174.4 s at four) are only in `docs/development/KERNEL_SPEED.md`. I did not run Init, as instructed. They stay "one run each, recorded".

**Claim 2. Reports are identical when fuel runs out.**
- Command: `check --json --no-manifest --fuel N --jobs 2 tests/front/decide-slice.ndjson`.
- `--fuel 500` ended with exit code 5 on both sides. The reports were identical: 297 accepted, 239 exhausted, 605 unknown, 148 not-checked, 1 invalid.
- `--fuel 5000` ended with exit code 3 on both sides. The reports were identical: 879 accepted, 30 exhausted, 381 unknown.

**Claim 3. Rejected or malformed exports give the same output.** All `--no-manifest`. The `before` and `after` stdout, stderr and exit code were byte-identical (`cmp`) in all six cases:

| Export | Exit code | stdout bytes | Result line |
| --- | ---: | ---: | --- |
| `tests/core/check-declaration-cases/composition-wrong-argument.ndjson` | 1 | 200 | `rejected: argument type mismatch` |
| `tests/core/check-declaration-cases/spine-bad.ndjson` | 1 | 1001 | – |
| `tests/core/check-block-cases/after.rejected-block-then-use.ndjson` | 1 | 425 | – |
| `tests/cli/bugs/rec-missing-ih.ndjson` | 1 | 7167 | – |
| `tests/cli/bugs/rec-of-subst-prop.ndjson` | 1 | 6935 | – |
| `tests/cli/bugs/eta.structure-wrong-field.ndjson` | 4 | 30 | – |

Stderr was empty in every case.

**Claim 4. LeanForth text checks give the same output.** Output was identical in all three.
- `check --env tests/front/decide-slice.ndjson --no-manifest --elab-data tests/front/decide-slice.elab.ndjson tests/front/tactics/blocks-3/first.lf`: exit code 0, 58,901 bytes.
- `check --env tests/front/simp-slice.ndjson --no-manifest --elab-data tests/front/simp-slice.elab.ndjson tests/front/tactics/simp-2/simp-at.lf`: exit code 0, 97,761 bytes.
- An extra negative case, `tests/front/tactics/simp-2/w-at-self.lf` with the same environment and data: exit code 4 and the "Type mismatch ... not checked" error, identical on both sides.
- Not run: `.lf` input as a checked proof on the full Mathlib path.

**Claim 5. Documentation.**
- `docs/development/KERNEL_SPEED.md:97-135` has all the items you listed.
  - Runs: "one run each", with dates and times, and the load for each run.
  - Seconds at 1 and 4 threads, beside Lean's checker (31.0 s) and nanoda (30.7 s and 9.7 s), with the group 3 to Lean and group 3 to nanoda ratios.
  - Peak memory: 645.5 MB to 645.4 MB at one thread, and 901.4 MB to 919.0 MB at four, +1.95% (line 125).
  - The declared exception: "a heap refusal may land at another step, and the outcome and fuel ... may differ" (lines 140-143).
- The document is honest that the four-thread peak is +1.95%. The claim wording "peak memory unchanged" is only true at one thread.
- Stale wording:
  - `docs/project/PLAN_DRAFT.md:847` (row 9.4.8z8): "written, tested and Forth-reviewed on branch `kernel-speed-3` ... its fix round on the branch, not merged, not done". The code is on main, and 2f7f1f9f is an ancestor of HEAD.
  - `docs/project/PROJECT_PROGRESS.md:33-36`: "on its branch `kernel-speed-3` ... not merged, not done".
  - `docs/design/TERM_STORE.md:3`: "Status: **designed, not reviewed, no code.**" The code exists, and section "As landed" is at line 369.
  - `docs/design/TERM_STORE.md:371`: "landed as ... code on branch `kernel-speed-3`", which does not say it is on main.
- Corrected wording:
  - Plan row and progress entry: "integrated on main (memo cut and lean walk; no difference in verdicts or fuel on the decide slice, on rejected exports or at low fuel; Init check phase 656.5 s -> 637.0 s at one thread, one run); done once this check is cited."
  - `TERM_STORE.md:3`: "Status: P1 and P3 landed on main (see 'As landed'); P2 dropped, P4 left out; the rest designed."

Gaps:
- The row cannot be called "done" until it cites this report, and the Init timing needs an independent rerun, which the other agent's load rules out today.
- The speed claim is 3% on Init in one run each. My small export cannot show it.

## After the report (coordinator, 2026-11-26 04:16)

- **Init on main e86a8df1**, by the coordinator (`GFORTH=.tools/gforth/bin/gforth-fast bin/leanforth check
  --jobs N --no-manifest --resources --json .claude/work/IM/init.ndjson`, one run each, 02:50-03:04, no other
  heavy run): `--jobs 4`: check phase 173.7 s, whole run 191.4 s, peak resident memory 889 MB (load 2.0 at
  the start, 4.0 at the end); `--jobs 1`: check phase **625.8 s**, whole run 639.7 s, peak 630 MB (load 4.0,
  then 1.0). Both reports are identical, outside `measured`, `settings` and `run`, to main's before the
  change (656.5 s and 182.1 s of check phase; 670.4 s and 199.6 s whole run): 59,349 accepted, the same
  fuel. Beside Lean's checker (31.0 s at one thread) the whole run is 20.6 times; beside nanoda at four
  threads (9.7 s) 19.7 times. The branch's own pair gave 637.0 s; single runs.
- The stale "not merged" wording (plan row 9.4.8z8, PROJECT_PROGRESS.md, TERM_STORE.md) was corrected in the
  same commit as this file.

Stage: **done** (the memo cut and the lean walk; stored hashes were measured and dropped, the leaf array
left out).
