# Done check: kernel validity checks, slice 1

DONE CHECK: kernel validity checks slice 1

**Verdict: NOT DONE. Stage reached: integrated, and works end to end for the verdict claim. The speed claim is only partly shown, and the done checker had not been run before today. I did not run Init (told not to), so the Init 952.7 s to 823.9 s figures are unverified here.**

**Claim.** A user can run `bin/leanforth check` and get the same verdicts as before the environment stamp, and get them faster.

**Setup.** "Before" is `git archive 44029e0c` extracted to `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-kv1/before`. "After" is the repository at 0f3b3edd. `ulimit -u 500`, `nice -n 10`, GFORTH=`.tools/gforth/bin/gforth-fast`. The `before` copy has no `.tools`, so I gave it the absolute GFORTH path. Load average was 1.9 to 4.9, so the machine was busy.

**1. decide-slice, `check --json --resources --no-manifest tests/front/decide-slice.ndjson`**
- All 8 runs (before and after, `--jobs 1` and `--jobs 4`, two runs each) exited 0, with empty stderr.
- A Python diff (`python3 -I`) of the JSON with `measured`, `settings` and `run` removed shows all 8 are identical to each other.
- Check-phase wall times in seconds:

| Jobs | Before | After |
| --- | --- | --- |
| 1 | 3.75, 3.77 | 3.11, 3.99 |
| 4 | 3.04, 2.79 | 2.37, 2.87 |

- Run 1 after is about 17% faster at one worker, which matches the claimed 3.7 s to 3.0 s. Run 2 after (3.99 s) is slower than both before runs.
- At four workers the gain is 0.1 to 0.7 s.
- With two runs each and the load changing, this is **within noise**. It points the right way but is not proof.

**2. Rejected and malformed exports.** Stdout, stderr and exit code were byte-identical before and after (`cmp`) for each.
- `check --no-manifest tests/core/check-declaration-cases/composition-wrong-argument.ndjson`: exit 1, "composition: rejected … argument type mismatch".
- Same options on `spine-bad.ndjson`: exit 1, "Spine.bad: rejected … 24 declarations: 23 accepted, 1 rejected".
- Same options on `composition-unsafe.ndjson`: exit 0 both times.
- `tests/cli/composition-huge-number.ndjson`: exit 3, "number beyond 32 bits (line 12)".
- Without `--no-manifest` the case files stop at "manifest missing" with exit 4, before the kernel runs. That is also identical before and after, but it does not test the kernel.

**3. `.lf` text check.** `check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson tests/front/tactics/blocks-3/first.lf` gave exit 0 before and after. Stdout and stderr were identical ("Subtype: accepted …"). I ran only one `.lf` file.

**4. Documentation**
- `docs/development/KERNEL_SPEED.md:348-360`, "Measured after slice 1", is accurate against what I could see. It says one run each, one after the other, on a shared machine, with load averages and branch `kernel-validity-1` at 0a76195b. It gives Init 952.7 s to 823.9 s and decide-slice 3.75 s to 3.10 s, and it does not compare the `--jobs 4` run with the older figure. It does not state which Gforth engine the decide-slice runs used. The Init figures are the only ones I did not re-run. The "13.5 points" and "21.5 times Lean" figures come from a single pair of runs at different loads, which the text admits.
- **Stale: `docs/project/PLAN_DRAFT.md:841`.** The row says "Written and tested on branch `kernel-validity-1`, not reviewed, not merged, not done". `git branch --contains 297c7a56` lists main, and main's log has the Forth-review and local-CI commits (297c7a56, 0f3b3edd). Corrected wording: "Merged to main (0f3b3edd), Forth-reviewed, integrated; not done until the done-checker report is cited here."
- **Stale: `docs/project/PROJECT_PROGRESS.md:386-387`.** It says "written and tested on branch `kernel-validity-1`, not reviewed, not merged, not done". Same correction. The "Later" list still describes the branch as unmerged.
- `docs/development/KERNEL_SPEED.md:21` says "824 s with the environment stamp of branch `kernel-validity-1`". That is fine as history, but it should say the stamp is now on main.

**Remaining gaps before DONE**
- The Init run is not independently reproduced. The coordinator is timing it.
- The timing evidence for decide-slice is noisy and should not be quoted as better than "about 15%, one run".
- Check that the Forth review and local CI logs cover the exact head, and cite this report in the plan row.

## After the report (coordinator, 2026-11-25 13:38)

The checker's remaining gaps, closed:

- **Init reproduced on main 0f3b3edd** by the coordinator (`GFORTH=.tools/gforth/bin/gforth-fast bin/leanforth
  check --jobs N --no-manifest --resources --json .claude/work/IM/init.ndjson`, one run each, 13:19-13:37;
  another agent was working on the machine):
  - `--jobs 4`: check phase 246.6 s wall (967.3 s CPU), total 264.6 s; load average 2.0 at the start, 5.9 at
    the end; exit 0, 59,349 accepted, 1 not proved.
  - `--jobs 1`: check phase **779.5 s**, total 794.0 s; load 5.9 at the start, 1.0 at the end; exit 0, the
    same counts.
  Against main before the stamp (952.7 s, the implementer's run of the same day at load 0.6-2.1) that is
  173 s, 18.2 points, about 20.3 times Lean's 38.4 s; the implementer's own pair gave 13.5 points. One run
  each on a shared machine: the gain is between 13 and 18 points.
- The Forth review ([2026-11-25-kernel-validity-1.md](../forth-reviews/2026-11-25-kernel-validity-1.md)) and
  the local CI record (0f3b3edd) cover the merged head 297c7a56.
- The stale wording (plan row 9.4.8z1, PROJECT_PROGRESS.md, KERNEL_SPEED.md) was corrected in the same commit
  as this file.

Stage: **done**.
