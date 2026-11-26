# Done check: fused reads of term nodes

DONE CHECK: fused term reads

Verdict: **NOT DONE: works end to end for decide-slice, with identical verdicts and a speedup. The plan row says "not merged" and "not done", and the Init figure was not re-run (I was told not to).**

Claim: a user can run `bin/leanforth check` and get the same verdicts as before, faster, now that the fused term-node reads are on main.

The code is integrated. Commits a7da6ac4, 1b6818ad and others are on `main` (`git merge-base --is-ancestor 86e2448b HEAD` returned 0). No `kernel-reads-1` merge is needed any more. The branch still exists as `+ kernel-reads-1`.

**1. decide-slice, before (86e2448b archive) vs repository, gforth-fast, `ulimit -u 500`, nice 10.**
- Command: `bin/leanforth check --json --resources --no-manifest --jobs N tests/front/decide-slice.ndjson`.
- All 8 runs exited 0.
- The JSON was identical outside `measured`, `settings` and `run`, checked with `python3 -I`. All 8 reports match the first.
- Load average was 1.4–2.3 throughout (see `uptime`).

| Run | Check wall (s) | Check CPU (s) | Total wall (s) |
|---|---|---|---|
| before, `--jobs 1`, run a | 3.151 | 3.151 | 3.30 |
| before, `--jobs 1`, run b | 3.305 | 3.305 | 3.45 |
| after, `--jobs 1`, run a | 2.701 | 2.701 | 2.84 |
| after, `--jobs 1`, run b | 2.865 | 2.865 | 3.02 |
| before, `--jobs 4`, run a | 1.535 | 4.061 | 1.70 |
| before, `--jobs 4`, run b | 1.499 | 4.033 | 1.66 |
| after, `--jobs 4`, run a | 1.343 | 3.622 | 1.51 |
| after, `--jobs 4`, run b | 1.372 | 3.654 | 1.53 |

- At one worker, the check phase fell from about 3.2 s to about 2.8 s, roughly 13%. The claim says "about 3.1 s -> 2.5 s".
- Within a pair the runs differ by 0.1–0.15 s, and the before/after gap is about 0.45 s. So the gain at one worker is outside noise, but it is smaller than the documented "2.5 s". At four workers the gain is about 10% (1.52 s to 1.36 s), and the CPU time falls by about 11%.
- Both trees ran from the same checkout path family, with the machine shared.

**2. Rejected and malformed exports** (`--no-manifest`, stdout, stderr and exit code compared with `cmp`).

| Export | Exit before/after | stdout | stderr | Result line |
|---|---|---|---|---|
| `tests/core/check-declaration-cases/composition-wrong-argument.ndjson` | 1/1 | same | same | "rejected: argument type mismatch (D1-D5)" |
| `tests/core/check-declaration-cases/composition-unsafe.ndjson` | 0/0 | same | same | "skipped: unsafe or partial" |
| `tests/core/check-block-cases/after.acc-at-concrete.ndjson` | 0/0 | same | same | "3 accepted" |
| `tests/cli/composition-huge-number.ndjson` | 3/3 | same | same | "error: full: number beyond 32 bits (line 12)" |

- Only the first and last are rejection or malformed cases. Of the other two, one is skipped as unsafe and one is accepted (the block case).

**3. `.lf` text checks** (stdout, stderr and exit code identical before and after).
- Command: `bin/leanforth check --no-manifest --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson tests/front/tactics/blocks-3/first.lf`. Exit 0/0, output "1295 declarations: 1295 accepted".
- Command: `... --env tests/front/simp-slice.ndjson --elab-data tests/front/simp-slice.elab.ndjson tests/front/tactics/simp-1/simp-only.lf`. Exit 0/0, output "2010 declarations: 2010 accepted".
- The task names only the directory for the first file, so I chose `first.lf` in `tests/front/tactics/blocks-3/`.
- Both outputs end in "accepted: N; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED".
- These are the base environment's checks plus the `.lf` text. They show same-as-before behaviour, not that LeanForth proved anything.

**4. Documentation.** `docs/development/KERNEL_SPEED.md:369-379` gives the dates and times, the commits (2ca4449b vs 0e73e92c), the load averages, wall and CPU figures (770.3 s to 712.4 s wall, 770.2 s to 701.4 s CPU), "one run each", and "identical outside measured, settings and run". It does not mention that the code has since landed on main. It states "7.5 points" and "8.9 points" honestly as single runs.

Stale wording:
- `docs/project/PLAN_DRAFT.md:842`: row 9.4.8z3 says "Written, tested and Forth-reviewed on branch `kernel-reads-1` ..., not merged, not done". The code is on main, so the row should say "merged to main (a7da6ac4 … 1b6818ad); done after this check".
- `docs/project/PROJECT_PROGRESS.md:34`: "written, tested and Forth-reviewed on its branch `kernel-reads-1`" is stale.
- `docs/project/PROJECT_PROGRESS.md:392`: "written, tested and Forth-reviewed on branch `kernel-reads-1`, not merged" is stale.
- `docs/design/KERNEL_TERM_READS.md:4-5`: "written, tested and Forth-reviewed on branch `kernel-reads-1` ..., not merged, not done" is stale.
- Lines 34 and 392 also carry "712.4 s on the branch against 770.3 s on main (one run each, a shared machine)". That is acceptable if kept as single runs.

I did not check the Init figures (770.3 s to 712.4 s). I only confirmed that the decide-slice direction holds and that the verdicts are identical.

Corrected wording: "Merged to main on 2026-11-25 (a7da6ac4 … 1b6818ad). The done checker re-ran decide-slice: same JSON, check phase about 3.2 s to about 2.8 s at one worker, and about 1.52 s to about 1.36 s at four. Init's 770.3 s to 712.4 s is one run each."

Scratch files are in `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-kr1/`. The repository was not modified.

## After the report (coordinator, 2026-11-25 17:04)

- **Init on main 2eafd6c5**, by the coordinator (`GFORTH=.tools/gforth/bin/gforth-fast bin/leanforth check
  --jobs N --no-manifest --resources --json .claude/work/IM/init.ndjson`, one run each, 16:49-17:04, no other
  heavy run on the machine):
  - `--jobs 4`: check phase 182.1 s wall (716.1 s CPU), total 199.6 s; load average 1.9 at the start, 4.0 at
    the end; exit 0.
  - `--jobs 1`: check phase **656.5 s** (CPU 656.4 s), total 670.4 s; load 4.0 at the start, 1.0 at the end;
    exit 0; 59,349 accepted, 1 not proved; the report is identical, outside `measured`, `settings` and
    `run`, to the one-worker report of main before this change (13:24, check phase 779.5 s).
  Against that 779.5 s the fused reads take 123 s, 15.8 points; the implementer's own pair gave 57.9 s wall
  (7.5 points; 8.9 on CPU time). Single runs on one machine at different loads: the gain is between 7.5 and
  16 points. Init's check is now about 17 times Lean's 38.4 s in this run.
- The stale "not merged" wording (plan row 9.4.8z3, PROJECT_PROGRESS.md, KERNEL_TERM_READS.md) was corrected
  in the same commit as this file.

Stage: **done**.
