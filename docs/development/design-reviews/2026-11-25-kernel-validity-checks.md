# Design review: kernel validity checks out of the inner walks

Independent review (architect agent, 2026-11-25) of [KERNEL_VALIDITY_CHECKS.md](../../design/KERNEL_VALIDITY_CHECKS.md) at 0d03a9a5. Its changes are taken into the design's section "Changes after the design review".

DESIGN REVIEW: kernel validity checks

**Verdict: approve with changes.** The main idea holds up when checked against the code: one full check when a declaration's check begins, a two-cell tripwire inside it, and a full check at the hand-over. The invariant holds on main at 0c0c49ac. One trust hole needs fixing before code starts: one publication path skips the full exit check (finding 1). One robustness gap should also be closed (finding 2). Several "to be verified" items are now verified, so the architect step becomes small. The gain is a little higher than the design says.

## Findings (most severe first)

**1. High: the full exit check is not on every publication path.**
- The design clears the stamp in `lf-env-finish`, `lf-env-clear` and `lf-env-hand-over-at` (env-publish.fs:571-572).
- But the word that actually publishes is `lf-env-hand-over` (env-publish.fs:555-557). Its `lf-env-target` (:187-189) asks `lf-env-checking`, and that would answer from a stamp that is still set.
- Tests call `lf-env-hand-over` directly after `lf-env-begin`, with no finish and no `-at`:
  - tests/core/environment.fs:250, 254, 304, 310, 314, 401
  - tests/core/environment-tasks.fs:229, 246
- So "every exit runs the full check" is false for that path, and the exit check is the one that carries the trust (finding 4).
- **Change:** clear the stamp at the top of `lf-env-hand-over` as well as in `-at`. Add a row: begin, break the input, call `lf-env-hand-over` with no finish; expect `invalid true`. Plant a fault that drops this clear.

**2. Medium: the stamp should not depend on every exit clearing it.**
- `lf-env-begin` always erases the candidate first (environment.fs:625, `lf-env-clear`). So a stale stamp can never reach the next declaration's check. Good; state this as the main reset rule.
- A stale stamp can still survive in two windows:
  - `lf-sch-rerun` (env-schedule.fs:596-598): no finish and no hand-over; the stamp is cleared only at the next begin.
  - `replayed?` (env-import.fs:338-340): begin, then `asked?`, then `lf-env-clear`, not under CATCH. A THROW out of `asked?` leaves the stamp set.
- The address-plus-identity compare catches a freed or replaced environment. It does not catch a new or reset input in the same context (cli/check-run.fs:454 does exactly that).
- **Change:** add a third compare to `lf-env-held?`: `lf-env lf-envh-input @ = lf-input-fingerprint`, as `lf-env-input?` does at :459. It costs one cell and makes a stale stamp harmless after a new input.

**3. Medium: the planted-fault claims are partly wrong.**
- `fx9-env-still-always` (faults.toml:8790) will not be killed by the new rows. With `lf-env-still?` forced true, `lf-env-target`'s full check refuses with the same result (`invalid true`). The first diagnostic is also the same: `lf-env-unseen`'s `lf-diag-no-snapshot`, and diagnostics are first-wins (core/diagnostics.fs:165). Only a moved-snapshot row (a nested begin of another declaration) kills it. Add that row or keep its "equivalent" note.
- `fx9-input-intact-always` will be killed by the `lf-name-used` row: the rollback then succeeds and the declaration is published ok.
- Today there are no planted faults at all on `lf-env-sane?`, `lf-env-pooled?`, `lf-env-input?`, `lf-env-valid?` or `lf-env-live?` (grep of faults.toml and faults.d/*.toml finds none). After slice 1 these run only at begin and exit. Add faults for them (for example `lf-env-input?` → true) that the new mid-check rows must kill.

**4. Low-medium: the fail-closed table overstates the per-pass store roots.**
- `lf-term-count-valid?` is only `store-count-valid?` (terms.fs:436). It catches a broken seal. It does not catch a rollback below a mark, and a `store-clear` (generation +1) passes it.
- For those breaks the only catches are step 7's rollback (check-declaration.fs:216, if the break came before it) and the hand-over.
- Say so in the table. It is why finding 1 matters.

**5. Low: the architect step's items are now verified, so its scope shrinks.**
- **Pool readers.** The callers of `lf-dep-at` and `lf-look-cell` (environment.fs:1331, :1334) are:
  - env-snapshot.fs:372, 412, 487, 505, 877, 881: the snapshot writer and the import's after-run compare;
  - `lf-axd`, environment.fs:1384, 1394: the axiom report.

  None runs inside a check. Drop risk (b) and the 0-1.3 point deduction.
- **Scheduler and context maker.** env-schedule.fs has no `lf-env-use`, `-free` or `-new`. import/feed.fs (the context maker) uses no environment word. The only other users are drivers before and after a run (check-run.fs:734-744, leanforth.fs:1471-1476, run-record.fs:310-399).
- **Store resets.** No `store-clear`, `store-poison` or input reset is reachable from the kernel. They occur only in cli/check-run.fs:454 and cli/check-lf.fs:234 (drivers), and the slab clears in front/ are front-end slabs.
- **Nested begins.** `lf-env-begin`'s callers are only env-publish.fs:613, env-schedule.fs:559 and env-import.fs:339. Block checks take one begin, so they get one stamp.
- **THROW paths.**
  - Serial: `lf-env-thrown` → `lf-env-finish` (env-publish.fs:562-564).
  - Parallel: `lf-env-hand-over-job` (:580-582), or rerun with renew, which frees the context.
  - Both are covered.
- **Front end.** It uses views (cli/leanforth.fs:356, cli/print.fs:114). Under a view `lf-whnf-env?` is false (whnf.fs:175-176, limit = length). The front end keeps today's cost and today's checks: no gain and no risk.

**6. Low: one wrong statement in the design text.**
- `lf-check-begin`'s `lf-env-checking` (check-declaration.fs:368) will take the fast path, because the stamp was set just before it. The design lists it as staying full.
- This is harmless, because `lf-input-read` re-runs `lf-input-intact?` itself (input.fs:343). Correct the text.

**7. Low: drop the cross-check counter, or confine it.**
- It is a second compile-time variant plus a module-level variable. That goes against the owner's 2026-11-18 rule of no new module-level state; precedent is `lf-i2-misses`, environment.fs:359.
- It can only catch faults someone plants; the exit check plus finding 3's rows test the invariant on the shipped build.
- **Change:** drop it. If kept, limit it to one named test target with its own fault.

**8. Gate: agree it is ordinary behaviour-preserving work.**
- Published outcomes and fuel do not change, and no input reaches the facts that move.
- The only possible difference is which step's diagnostic is noted first on rows where we deliberately break LeanForth's own state mid-check. No export can reach that.
- **Change:** decide now instead of "stop and ask": accept a different first diagnostic on those rows only, and report it afterwards.
- Also record that `replayed?`'s lookups (env-import.fs:338-340) have no exit check. They feed only the "why" explanation (env-import.fs:415), never a verdict.

**9. Claim 3 ("a malformed export can never reach the moved checks") holds,** with one qualification. The export's data cannot write these cells, and no refusal or exhaustion path resets a store or slab: `store-poison` has no caller and `store-grow` does not reset. Only a LeanForth bug can break them.

**10. Size and cost.**
- Forth is about 15-20 lines, not 30-40: a field, a hold in `lf-env-start`, `lf-env-held?` plus one branch in `lf-env-ours`, and two clears. The other clears come free through `lf-env-clear` and `lf-env-finish`. Tests of 70-100 lines are fine.
- The 0.7-1.0 M tokens go mostly on process, not code:
  - four Init timings of about 16 minutes each plus a 20-minute profile, each to be watched;
  - the Forth review;
  - the full tier and the done check.
- Cuts:
  - this review replaces most of the architect step;
  - drop the counter (finding 7);
  - time one before/after pair at `--jobs 1` and one after at `--jobs 4`;
  - make the profile optional.

  Estimate after cuts: about 0.4-0.6 M tokens.
- Work in flight: no local branch has unmerged changes to environment.fs, env-publish.fs, input.fs or whnf.fs (only the stale `cf3-backup` from 11-19). The dependency on `kernel-speed-measure` for `make profile-check` is as stated.

## Recomputed gain (run 2 profile, scripts/profile-summary.py --under)

- `lf-env-ours`: 8,587 of 57,421 samples = 14.95 points. Of these, `lf-env-current` is 8,376 samples = 14.59 points, and 99.5% sit inside `lf-env-as-check`.
- The hand-over's share: about 31 samples (0.05 points). It stays full but costs nothing.
- `lf-env-ours`'s own overhead today: 211 samples = 0.37 points, about 11 ns a call over 384 M calls.
- The fast path does the same work: one context-record read and two or three compares. A gforth-fast micro-benchmark gave 4.4 ns a call on the loaded machine, so the fast path should cost 0.2-0.45 points.
- **Gain: about 14.1-14.6 points ≈ 134-139 s of 952 s.** Init ≈ 813-818 s, about 21.2× Lean. The design said 12.5-14; its low end assumed a pool check that is not needed (finding 5).
- Caveat: these shares come from a profiled run of 1,188 s wall time and are applied to the unprofiled 952 s.
- A bigger restructuring would not gain more. Asking once per pass would leave at most the same 0.2-0.4 points, and it touches nine `lf-whnf-env?` call sites in six files plus `lf-env-snapshot`'s callers. The stamp in one word is the right shape.

## What to tell the owner (plain language)

1. Every declaration check currently re-proves about 384 million times that LeanForth's own memory is intact. The change proves it once when the check starts and once before the result is published. Inside the check a two-cell tripwire stays. Expected gain: about 14 points, about 135 s off Init's 952 s (Init goes from about 24.8× to about 21.2× Lean).
2. No proof file can change what is skipped. Those checks only guard against bugs in LeanForth itself, and such a bug is still caught before anything is published. Only the kernel decides a verdict; nothing here changes what it accepts or rejects.
3. Two fixes are needed before coding: the final full check must also run when a result is published directly (finding 1), and the tripwire should also compare the input's fingerprint (finding 2).
4. Recommendation: treat this as ordinary refactoring with the Forth review, the full test tier and every pinned-Lean comparison, reported afterwards. Accept that the error note recorded inside a deliberately broken test check may name a different step.
5. Expected cost after cuts: about 0.4-0.6 M tokens.

I changed no files. Scratch micro-benchmark: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/stamp.fs
