# Test workflow review: repeated tests on small work (2026-11-13)

The owner, 2026-11-13: "it seems like we are doing too many similar tests on small task results, that is slowing down
progress … count the repetition in testing and propose improvements in work flow, including design." This note counts
what ran on four recent tasks and proposes changes. The proposals change rules the owner set (AGENTS.md "Work process",
`.claude/CLAUDE.md` "Checks" and "Git"), and the owner decided them on 2026-11-13 (below); plan row 9.4.6 tracks the scripts they need.

## How the counts were made

- **Agent runs:** counted from the agent transcripts of the session of 2026-11-12/13. A command counts when it actually
  invokes `make`, Gforth on a test file, `mutants.py`, a style script or a pinned-Lean comparison; polling loops and log
  greps are excluded. Reviewer counts come from the review rounds whose prompt names the task, so they are approximate.
- **Pushes:** from `.claude/work/ci/<commit>-{check,coverage,test073}.log` (creation and last-change times).
- **Sizes and callers:** from `scripts/forth-metrics.py`, `wc -l` and the `require` lines in `src/`.
- **Cost of one full-suite run** (measured in day mode, `JOBS=2`): `make test` about 3 min, `make check` about 8 min,
  `make coverage-check` about 5 min (it runs `make test` again under instrumentation), `make test` on Gforth 0.7.3
  about 6 min.

## The four tasks

| Task | Code | Words | Callers in `src/` | Planted faults | Test lines |
| --- | --- | --- | --- | --- | --- |
| `lib/sort.fs` (FRK C2's library) | 266 lines | 60 | none (the kernel adopts it only in FRK C2, after its own review and the [kernel] gate) | 23 | 450 |
| `lib/bigint.fs` (FE1i-4) | 367 lines | 126 | none (its user, the omega port FE1i-5/6, waits for the owner) | 17 | 920 (with the differential script) |
| FE1g-1 goals and contexts | 690 lines in 4 new files, plus changes in 6 | 195 new | the goal printer; no user command reaches it before FE1g-3 | 27 | 775 |
| COVFU coverage follow-ups | tests only, 78 changed lines | 0 | n/a | 2 | 78 |

### What ran on each

| Task | Single test file | Same on 0.7.3 | Full `make test` | `make check` | Coverage runs of the whole suite | Focused make targets | `mutants.py` | Style scripts | Pinned Lean |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| sort, implementer | 6 | 1 | 3 | 1 | 1 | 1 | 2 | 4 | 0 |
| sort, reviewer | 2-3 | 1 | 0 | 0 | 0 | 0 | 5 | 1-3 | 0-1 |
| bigint, implementer | 12 | 1 | 2 | 2 | 0 (one coverage run of its file) | 6 | 3 | 6 | 9 |
| bigint, reviewer (review and re-check) | 1+ | 3 | 0 | 0 | 2 focused | 0 | 7 | 4 | 1 |
| FE1g-1, implementer (with the fix round) | 27 | 0 | 3 | 1 | 5 | 0 | 13 | 10 | 2 |
| FE1g-1, reviewer (review and re-check) | 4 | 2 | 0 | 0 | 0 | 0 | 2 | 1 | 2 |
| COVFU, implementer | 7 | 0 | 1 | 0 | 1 (+3 focused) | 0 | 3 | 3 | 0 |

Then the coordinator:

- **After merging:** re-ran the merged branch's test files on main. The COVFU merge was a fast-forward, so the tree was
  identical to the one the agent had just tested.
- **At each push, the whole suite three times:** inside `make check`, again under coverage, and again on Gforth 0.7.3,
  plus every pinned-Lean comparison.

### Pushes between 00:59 and 07:03

| Push | What it carried | Wall time | Result |
| --- | --- | --- | --- |
| f29a526d | front-end merges | 19.8 min | passed |
| 38184a47 | a coverage allowance | 18.4 min | passed |
| a8a08d46 | merges | 15.8 min, check only | stopped by me (a branch lacked coverage rows) |
| 2ff0e7b5 | merges (during the Mathlib run) | 70.6 min | passed |
| f24c8015 | lib-sort, lnorm, det-snapshot | 31.4 min | failed at coverage, on a file lib-sort does not touch |
| d3befe35 | the same plus one allowance | 26.5 min | passed |
| 35f43c11 | **one documentation paragraph** (the Mathlib result) | 14.6 min | passed |
| 39357876 | fe1g1, COVFU, review log | 18.7 min | passed |

Together: **3.6 hours of CI in six hours**, each push followed by its own "Record the local CI of …" commit.

### The life of `lib/sort.fs`

- **00:48:** the code was committed. The implementer then ran its test file 7 times, the full suite 5 times and its 23
  faults twice.
- **Review:** the reviewer re-ran the test file and the faults (0 blocking, two documentation findings). The branch
  merged main into itself at 01:50 and was tested again.
- **03:51:** merged to main. It took two pushes to publish (57.9 min, 6 more full-suite runs), because the first push
  failed on an unrelated file.
- **Since then:** every push and every other agent's final checks have run its test again, about 40-60 runs in five
  hours.
- **Its own test takes about 0.1 s.** The cost is not this library's tests; it is the whole suite being re-run around
  every small step.
- **No program calls the library yet.**

## What repeats, and why

1. **The same tree is tested several times.**
   - The implementer's final `make check` and coverage run, the coordinator's run after a fast-forward merge and the
     push's run all test identical files with an identical toolchain.
   - Nothing records "this tree passed", so each stage starts again.
2. **The whole suite runs where the change cannot reach.**
   - A documentation paragraph cost 14.6 minutes of tests.
   - A library with no caller re-ran the kernel, Lean comparisons and Init checks it cannot affect.
   - `make test-changed` and `make check-changed` (`scripts/changed-tests.py`) already pick the targets that use a
     changed file, but the briefs and the push gate do not use them.
3. **Each push runs the whole suite three times.** `make check` contains `make test`, `make coverage-check` runs
   `make test` again under instrumentation, and the 0.7.3 job runs it a third time.
4. **Agents run the full suite several times per branch.** Their briefs say to run the full suite at the end, but
   agents ran `make test` 1-3 times, coverage up to 5 times, and repeated both after each review fix.
5. **Reviewers re-run the implementer's tests on the same commit.** Their own probes and planted faults are the
   valuable part: the fe1c-3 review's 25 faults found 19 gaps the tests missed, and its probe found a wrong answer.
6. **Work products are small, and each one pays the full pipeline.** Every step pays separately for a brief, a branch,
   a full suite, a review, fixes, a re-check, a merge, a push and a CI-record commit:
   - a library before its caller (sort, bigint);
   - a coverage allowance in its own push;
   - a docs commit in its own push.
   Snapshot compatibility took four review rounds.
7. **Failed pushes repeat everything.**
   - Two pushes failed on coverage allowances (an `iota.fs` block that ran only sometimes under `--jobs`, and
     level-defeq.fs measured on a branch run, not the full suite).
   - Each failure re-ran the whole push after a one-line fix.
8. **Waiting is also repeated work.**
   - The bigint agent polled its `make check` 27 times while the machine was shared.
   - Several agents re-ran a full suite after a fork failure, where the rule is to report it, not retry.

## Proposals

**Tested-tree records (largest saving, no loss of checking).** `scripts/push.sh` and the agents write one record per
tested tree, keyed by:
- `git rev-parse HEAD^{tree}`;
- the Gforth and Lean versions;
- the suite (`check`, `coverage`, `test073`).

A later stage that meets the same key reuses the result instead of re-running. Agents rebase on current main before
their final run, so most merges are fast-forwards and their final run is the push's run. A merge that is not a
fast-forward makes a new tree, which is tested once.

**Run tests by what a change affects** (`scripts/changed-tests.py` extended with the `require` graph). The final checks
of a branch, and pushes, choose a tier:

| Change | Tier |
| --- | --- |
| docs only | `check-docs`, the progress check |
| tests only | the changed test files, their faults, the coverage of the files they test |
| a library nothing loads yet | its test file on both Gforths, its faults, its coverage |
| front end | `test-front`, `reference-front`, the files it loads |
| kernel, core, import, cli, or the Makefile and scripts | the whole of `make check` |

The full suite still runs at least once a day and before a tag. A tier never skips a test of a file the change can
reach.

**One instrumented run per push, not two.**
- `make coverage-check` already runs every test of `make test`, so `make check` should use that run for its
  `make test` part instead of running the suite again.
- The 0.7.3 job follows the tier above. Its whole suite runs with the daily `LEAN_CACHE=0` run and before a tag; a
  change to `src/` always runs it on the affected targets.

**Pushes by checkpoint, not by step.**
- Merge several reviewed branches, then push once: for example every two to three hours, at the end of a session, or
  when a branch someone else needs lands.
- Documentation-only commits ride with the next push.
- The CI record goes into that push's own commit, not a second commit.

The owner's protection against lost work is kept:
- every agent's work is committed on its branch;
- main is pushed at least every few hours.

Pushing work branches to GitHub without CI would protect even more. That changes the remote, so it needs the owner's
approval.

**One full run per branch, at the end.**
- Agents run focused tests while working (`make test-changed`, the test file, its faults).
- They run the tier's suite once, on the head they hand over, after rebasing.
- They run nothing again after a review fix unless the fix touches a file outside that tier.
- They wait for a background run with one blocking wait, not a polling loop.

**Reviewers probe; they do not repeat.**
- The reviewer gets the implementer's recorded results for the head and runs only what is new: its own probes, its
  own planted faults, the Lean comparisons of the questions it is asked, and a style pass.
- A re-check of a small fix reads the diff and runs only the tests that the fix touches.

**Bigger work products (design).**
- **A library lands with its first caller in one branch,** so one review and one suite pay for both, and the tests
  exercise the real use. For example: `lib/sort.fs` with FRK C2, `lib/bigint.fs` with FE1i-5. The owner's
  library-first rule (2026-11-03) still decides where the code lives.
- **Plan slices by user-visible result,** each a step a user or the next layer can use: for example FE1g-3 with FE1g-4
  (`intro`, `exact` and `rfl` running), not the runner alone.
- **Coverage allowances and small follow-ups go into the branch that caused them, never into a push of their own.**
- **The review of a stack of related branches is one review,** for example fe1g1 and fe1c-3, where one is built on
  the other's words.

**Keep:**
- the planted faults and the reviewer's own faults (they found real gaps);
- the Forth style review of every change to `src/`;
- the two-version Gforth support;
- the daily full run with `LEAN_CACHE=0`;
- the done checker.

These checks find errors; the repetitions above re-test unchanged files.

### Expected effect on a task like `lib/sort.fs`

| | Today | Proposed |
| --- | --- | --- |
| Full-suite runs to reach GitHub | about 12 (5 by the agent, 6 in two pushes, 1 after a branch merge) | 1, shared with the other branches of that push |
| Machine time | about 2-3 hours at `JOBS=2` | about 15-25 min, plus focused tests |
| Lead time, commit to GitHub | 4 hours | about 1 hour, if review starts at once and the push is a checkpoint push |

The assurance stays as it is: every test of every file the change reaches still runs on the tree that is pushed.

## Questions for the owner

1. Reuse a recorded pass for an identical tree, at merge and push? *Recommendation: yes.* It is the largest saving
   and drops no check.
2. Test by change tier, with the full suite once a day and before a tag? *Recommendation: yes.* `changed-tests.py`
   exists and only needs the `require` graph.
3. Push by checkpoint (every two to three hours or at session end) instead of after every merge? *Recommendation:
   yes,* with every branch committed in the meantime. Separately, may agents push their work branches to GitHub for
   crash safety? *Recommendation: yes, but only if you want the extra safety;* it changes the remote.
4. A library lands with its first caller? *Recommendation: yes,* except libraries you ask for on their own.
5. Run the 0.7.3 job by change tier, with its full run daily? *Recommendation: yes.*

## Decisions (owner, 2026-11-13)

The owner chose the recommendation on questions 1-4; question 5 (the 0.7.3 job by tier, its full run daily) was
decided with question 2. Recorded in [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md), "Less repeated testing";
the rules are in AGENTS.md. Until the scripts of plan 9.4.6 land, `scripts/push.sh` keeps running both CI jobs in full.

