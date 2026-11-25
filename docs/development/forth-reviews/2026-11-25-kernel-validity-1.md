FORTH REVIEW: kernel-validity-1

**Range:** 44029e0c..962e1c41 (0a76195b code, tests and faults; 42c8fc9d docs; 49f53338 measurement; 962e1c41 fault requote). Worktree `/home/peter/code/LeanForth/.claude/worktrees/agent-a097e7dd3cdf578fc`.
**Findings:** High 0, Medium 0, Low 4, Info 5.
**Verdict:** merge after fixes. The fixes are small: one factoring, about four test rows and one fault note. Each can instead be recorded as a plan task.

I could not break the claim. Under every path I traced, published verdicts are identical and no unchecked state decides a verdict. The fast path drops only two facts the full check reads: `lf-input-intact?` and the pool's soundness. Inside a real check, neither can change without changing the input's fingerprint. Both hand-overs drop the stamp before publishing, so every publication still runs the full `lf-env-current`.

This AI review does not replace the owner's review of this kernel change.

## 1. Paths traced (stamp set, read, cleared)

- **Set:** only in `lf-env-start` (environment.fs:634-636), through `lf-env-stamp`, after the full `lf-env-current` and `lf-env-open?` pass.
  - `lf-env-begin` always runs `lf-env-clear` first, which erases the whole `/lf-cand`.
  - A refused start or a spent context therefore holds nothing.
  - Even if one did hold (my fault r4), the cleared `lf-cand-identity` (0) makes `lf-env-mine?` fail, so the fast path is unreachable.
- **Cleared:**
  - `lf-env-finish` (:652), so also `lf-env-thrown` (env-publish.fs:563-565).
  - `lf-env-clear`, so every begin and every `lf-env-view` (:647).
  - `lf-env-hand-over` (env-publish.fs:556-558) and `lf-env-hand-over-at` (:573-574).
- **Every publisher goes through `lf-env-step` and then `lf-env-hand-over-at`:**
  - the serial `lf-env-run`;
  - cli/check-run.fs:698, cli/print.fs:105, import/run-record.fs:374;
  - the snapshot import's `imp-fill` (env-import.fs:438);
  - the scheduler: `lf-sch-hand` → `lf-env-hand-over-job` → `lf-env-hand-over-at`.
- **Stale stamps:** these paths can leave one set:
  - `lf-sch-rerun`;
  - a refused `job-submit` (`lf-sch-break`);
  - a THROW out of `replayed?`'s `asked?` (env-import.fs:339-340);
  - a test's check word with no finish.

  In each case the next begin or view clears it, or the context is freed. Until then, a stale stamp answers only when the address, identity and fingerprint all match, which is the same state in which the full check passes, except for a test that breaks the state on purpose.
- **`replayed?` (env-import.fs:415):** its result only selects a candidate. The verdict is published by `imp-fill` inside `lf-env-step`, which runs the full check at its exit.
- **Readers outside a check:**
  - `ck-confirm`, `ck-verdicts?`, `rr-viewed?` and `cli-made?` all take `lf-env-view` first, so they hold no stamp.
  - tally.fs's `decl-accepted?` is reached only under `ck-verdicts?`.
  - `lf-env-finished?` and env-snapshot.fs:561 call `lf-env-live?` or `lf-env-current` directly.
- **Parallel runs:**
  - The stamp is a field of the context record `lf-env-cand`. The new row in environment-tasks.fs shows it is held in the lane context and is 0 in the main context.
  - `context-new` uses allocate0, so a new context inherits no stamp.
  - The fast path reads only the env header's identity and input cells and never the pool. The old full check validated the pool block through a header cell that the caller then re-read anyway, so dropping it loses no protection against the publisher swapping blocks.
- **Identities:** written by `lf-env-identity+` and zeroed by `lf-env-forget`. The serial `lf-envs-serial` is erased only at load time (environment.fs:127) and refuses at max-n, so identities never repeat. I probed the test row at tests/core/environment.fs:407: the new environment really is at the freed address (same address, identity 9 against the held 7).
- **Fingerprint:** `lf-env-held?` compares `lf-envh-input @ lf-input-fingerprint =`, the same phrase `lf-env-input?` (:461) compares. Both read this context's `lf-input-state`.

## 2. Findings

**L1 (Low, test gap): three of the stamp's drops have no test row.** These faults of mine survived both test files:
- r4: a spent context's begin holds a stamp;
- r8: `lf-env-finish` drops the stamp only on ok;
- r9: `lf-env-thrown` sets the outcome without `lf-env-finish`, so it keeps the stamp.

Today all three are verdict-equivalent: the cleared candidate identity covers r4, and `lf-env-hand-over-at` drops the stamp anyway for r8 and r9. But design §2 test 2 lists "a spent context … leave none", and the design review says "both THROW paths clear the stamp"; no row pins either.

Fix: add rows near environment.fs:359-362, restoring the spent flag afterwards with `false lf-env-worker lf-worker-spent !`:
```forth
T{ lf-env-spend 3 lf-env-begin held@ -> outcome-invalid 0 }T
T{ 3 lf-env-begin drop outcome-rejected lf-env-finish held@ -> 0 }T
T{ 3 lf-env-begin drop -1 lf-env-thrown held@ -> 0 }T
```
Add r4, r8 and r9 to faults.d/kernel-validity.toml; their texts are in `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-kv1/tools/mine.toml`.

**L2 (Low, style and reuse): duplicated phrase, and no reader for the new field.**
- `lf-envh-input @ lf-input-fingerprint =` appears in both `lf-env-input?` (environment.fs:461) and `lf-env-held?` (:608).
- The field is read inline at :607 and again by the test helper `held@` (tests/support/env-cases.fs:205).

One word makes "the same fingerprint `lf-env-input?` compares" true by construction:
```forth
\ Whether env was made over this context's input (its fingerprint).
: lf-env-over? ( env -- flag ) lf-envh-input @ lf-input-fingerprint = ;
: lf-env-input? ( env -- flag ) lf-env-over? lf-input-intact? and ;
: lf-env-held@ ( -- env|0 ) lf-env-cand lf-cand-held @ ;
: lf-env-held? ( env -- flag )
  dup 0= over lf-env-held@ <> or if drop false exit then
  dup lf-env-mine? swap lf-env-over? and ;
```
`held@` then becomes `lf-env-held@`. The fault texts of kv1-held-no-input and kv1-input-always must be requoted, with the history rule.

**L3 (Low, faults): `fx9-input-intact-always` (faults.toml:8780) is still marked "equivalent".** Its listed test is check-declaration.fs. tests/core/environment.fs:103 (an older row) kills it, as I confirmed, and design §3 asked this slice to drop the note once the fault is killable. Fix: change its test to `$GFORTH tests/core/environment.fs`, drop `equivalent`, and name it in the commit.

**L4 (Low, test robustness): the address-reuse row (environment.fs:407) depends on the allocator** ("perhaps made where env-s was"). It reuses the address today. If it stops, the row silently stops testing the identity compare under address reuse. Fix: put the precondition in the row, e.g. `T{ lf-env env-s = held@ env-s = ours? … -> true true false … }T`.

**I1 (Info, doc): env-publish.fs:551-554 is now inaccurate.** The comment says (invalid true) "with nothing written" inside a job, but `lf-env-unhold` now writes the context's own held cell before that refusal. My fault r3, which moves the unhold after the in-job test, passes every row, so either order is equivalent. Say "nothing published" instead.

**I2 (Info): r7, which moves the unhold in `lf-env-hand-over-at` after `lf-env-still?`, survives and is equivalent.** `lf-env-hand-over`'s own unhold, and the first diagnostic (no-snapshot in both orders), cover it. Keep the order, which is defensive. If you add it as a fault, list it as equivalent.

**I3 (Info): kv1-sane-always is killed first by an older row** (environment.fs:213, the env-copy row), not by the stamp row its reason names. The test file stops at its first failure. I probed the serial-flip `broken-exit` row (:376) separately under this fault: the hand-over gives (outcome-invalid, fault? false) where the row expects fault? true, so that row would kill it too. No action needed.

**I4 (Info, history): commit 0a76195b alone leaves failure_path_faults.py's quote of `lf-env-finish` stale.** 962e1c41 fixes it, so the branch cannot be bisected at 0a76195b. Squash it on merge or accept.

**I5 (Info, docs):** PERFORMANCE_SCAN.md:53 and :83 (K1) and PARALLEL_REVIEW.md:169 still describe K1 as open. Add a pointer to the measured slice 1 when this merges.

## 3. What I ran

Tools: Gforth 1.0 (and gforth-fast where marked), on scratch `git archive` copies of the main and branch trees, under `ulimit -u 500`. Scratch root: `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-kv1/`.

**Test files:**

| Run | Result |
|---|---|
| branch environment.fs and environment-tasks.fs, gforth and gforth-fast | exit 0 |
| main environment.fs and environment-tasks.fs | exit 0 |
| branch front/meta-env.fs, core/check-declaration.fs, core/failure-paths.fs | exit 0 |
| branch failure_path_faults.py | 9 of 9 caught |
| `mutants.py --check --base 44029e0c` | 3754 entries, 0 stale, 0 texts changed unnamed |

**Faults** (each planted alone and run against both environment test files):

| Faults | Result |
|---|---|
| the 15 kv1 faults | all caught. 14 are caught first by a stamp row; kv1-sane-always first by :213 (I3) |
| pub-moved-snapshot, pub-hand-over-in-job, fx9-env-still-always | caught by stamp rows |
| fx9-input-intact-always | caught by :103 (L3) |
| my r1 (refused start holds), r2 (two of three compares), r5 (no 0 test: crash), r6 (identity against current), r10 (full path without `lf-env-mine?`), r11 (holds another address) | caught |
| my r3, r4, r7, r8, r9 | survived. All verdict-equivalent; see L1, I1, I2 |

**Planted faulty check** (`lf-env-limit 1 = if 1+ then` at the head of `lf-check-declaration`) on tests/reference/constant-fixture.ndjson, at jobs 1, 2 and the default: exit 5 each time. Verdicts were fixtureId accepted, fixturePoly invalid, fixtureUse not-checked; declaration 1 was never accepted.

**Decide slice** (`check --json --resources --no-manifest`, 1,290 declarations): main and branch at jobs 1 and 4 have 0 differences outside `measured`, `settings` and `run`, and branch j1 matches branch j4. Check phase on gforth-fast at jobs 1, load 0.5: main 3.59 and 3.75 s, branch 3.03 and 3.01 s.

**Init reports** (the implementer's, read only): main-j1 against branch-j1 and against branch-j4 show 0 differences outside `measured`, `settings` and `run`. All three: 59,349 accepted, 1 not proved, fuel total 654,719,715.

**Malformed and invalid exports, main against branch:**

| Export | Exit code | stderr | JSON |
|---|---|---|---|
| cli/composition-huge-number | 3, both | identical | identical |
| check-declaration-cases/spine-bad | 1, both | identical | identical |
| check-declaration-cases/composition-wrong-argument | 1, both | identical | identical |
| check-block-cases/names.duplicate-constructor | 1, both | identical | identical |
| cli/bugs/rec-missing-ih | 1, both | identical | identical |
| check-block-cases/quot.lift-on-mk-wrong | 1, both | identical | identical |
| my truncated constant fixture | 4, both | identical | identical |
| my dangling-index constant fixture | 4, both | identical | identical |

**KERNEL_SPEED.md "Measured after slice 1":** every number checks.
- 952.7 − 823.9 = 128.9 s (128.86 rounds to 128.9, not the brief's 128.8), which is 13.5 points.
- 823.9 / 38.4 = 21.5 and 952.7 / 38.4 = 24.8.
- Wall times from the logs: 967.4 s, 839.7 s and 352.8 s. The j4 check phase is 332.6 s wall and 1,074 s CPU.
- Loads 0.6/2.1, 2.2/6.2 and 5.9-8.5 match the logs.
- No src change between 90667b10 and 44029e0c, nor after 0a76195b.
- The decide-slice timings agree with mine.
- Nothing is claimed beyond what was run, and the plan row says "not reviewed, not merged, not done".

## 4. Forth style

`python3 scripts/forth-metrics.py --words 10` on the two files:
- **environment.fs:** 337 words (main 333). Lengths: 223 of 1-2 lines, 112 of 3-5, 2 of 6-10 (both old: `lf-env-absent-as`, `lf-axd-upto`). No missing stack comments. Deep shuffles 25 and return-stack ops 83, both unchanged; no lines over 90 characters.
- **env-publish.fs:** unchanged at 146 words, 8 deep shuffles, 46 return-stack ops, 1 long line (as on main).
- Every new word is one or two lines with an accurate stack comment, and none uses PICK, ROLL, locals, `VARIABLE` registers or raw offsets.
- `tests/forth-quality-baseline.json` is untouched. `check-forth-quality.py` holds the ratchet and warns only that 0a76195b has no logged review yet (this review).
- Style findings: L2 (repeated phrase and missing field reader) and I1 (comment).

**Re-entrancy:** no new module-level state. `lf-cand-held` is a field of the context record `lf-env-cand`; it is written by each context only for itself, and by the main thread for a lane only while that lane is idle (inside `lf-sch-in`).

**Portability:** Forth-2012 core words only; nothing Gforth-specific was added.

## 5. Reuse

I searched src/ for an existing "checked once" or tripwire word and for the fingerprint, identity and held phrases, read FORTH_LIBRARY.md's inventory, and grepped lib/context.fs and lib/store.fs. Nothing in lib/ does this job.

- `check-duplicates.py`: 187 baseline groups, none new or grown.
- `check-lib-callers.py`: every lib file has a caller or a plan row (only the old bigint.fs note).
- The only copy is the four-token phrase in L2, below the duplicate checker's six-token threshold; it is still worth naming.
- No branches in flight were named for comparison.

## 6. What I did not look at or run

- I did not run `make cover-changed`, `make tier`, the suites, Init or any pinned-Lean comparison, at the coordinator's request; the implementer's tier is recorded on this head and I did not verify that record.
- I did not run the cross-snapshot or carry tests (env-import's `replayed?`); I traced them by reading only.
- I did not run 32-bit or Gforth 0.7.3.
- I did not re-review design §§5-9.

AI review does not satisfy the human-review requirement for this kernel change: the owner's approval of the summary still applies.

## Resolution

The implementer's fix round, 2026-11-25, on branch `kernel-validity-1`: `84414aaf` ("Name the stamp's
reader and the fingerprint compare": source, tests and faults) and `7e16b072` ("Point the K1 notes at
the measured stamp": documentation).

| Finding | Resolution |
|---|---|
| L1 | Fixed in `84414aaf`. Three rows follow tests/core/environment.fs's `0 lf-env-begin` row: a spent context's begin holds nothing (`unspend` mends the flag), a finish with `outcome-rejected` drops the stamp, and `-1 lf-env-thrown` drops it. Faults added to faults.d/kernel-validity.toml: `kv1-spent-begin-holds` (r4), `kv1-finish-unholds-only-ok` (r8) and `kv1-thrown-keeps` (r9). Each was planted alone and is caught first by its own row. |
| L2 | Fixed in `84414aaf`. `lf-env-over? ( env -- flag )` is used by `lf-env-input?` and `lf-env-held?`. `lf-env-held@ ( -- env\|0 )` is used by `lf-env-held?` and by the tests in place of the helper `held@`, which is removed from tests/support/env-cases.fs. The behaviour is identical. Requoted faults: `kv1-held-no-address`, `kv1-held-no-identity`, `kv1-held-no-input` and `kv1-input-always`; all are caught. `forth-metrics.py` on environment.fs: 339 words, deep shuffles 25 and return-stack ops 83 (both unchanged), no lines over 90 characters. |
| L3 | Fixed in `84414aaf`. `fx9-input-intact-always` now runs tests/core/environment.fs and is no longer listed equivalent. It is caught by `T{ lf-input-intact? lf-input-count -> false 2 }T`. |
| L4 | Fixed in `84414aaf`. The row is split, and its first part states `lf-env env-s =` as an expected true. |
| I1 | Fixed in `84414aaf`: the comment says "nothing published". |
| I2 | Done in `84414aaf`. r7 is added as `kv1-hand-over-at-unhold-late` and listed equivalent with its reason. `mutants.py` reports it as "survived as listed". The early drop is kept. |
| I3 | No action, as the review says. |
| I4 | Left as is: pushed history is not rewritten. `0a76195b` alone leaves failure_path_faults.py's quote of `lf-env-finish` stale, and `962e1c41` fixes it. Whether to squash on merge is the merger's choice. |
| I5 | Fixed in `7e16b072`. PERFORMANCE_SCAN.md (row 5 and K1) and PARALLEL_REVIEW.md (K1) point to KERNEL_SPEED.md, "Measured after slice 1". |

**Evidence for the fix round.**
- `python3 scripts/mutants.py --only` on the four new faults, the four requoted faults and `fx9-input-intact-always`: 8 caught, 1 known equivalent.
- `python3 scripts/mutants.py --check --history --base main`: 3,758 entries, 0 replacement texts changed unnamed.
- tests/core/environment.fs and environment-tasks.fs exit 0.
- `bin/leanforth check --json --resources` on tests/front/decide-slice.ndjson at `--jobs 1` and `--jobs 4`: 0 differences outside `measured`, `settings` and `run`, against both the reviewer's main reports and branch reports.
