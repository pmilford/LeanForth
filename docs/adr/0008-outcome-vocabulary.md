# ADR 0008: one outcome vocabulary — proposal

Status: **accepted** by the owner, 2026-11-02, with the split of
*exhausted* into fuel and room ([owner decisions](../project/OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)).
A code-structure decision for untrusted,
in-progress modules. It changes no typing or conversion rule. Adding the
*rejected* outcome to the checker (step 3 below) is a checker change and
goes through the review gate in `AGENTS.md`.

## Problem

Every walker in `src/core/` and `src/kernel/` defines its own status
constants (`lf-mshift-ok`, `lf-repr-invalid`, `lf-mconvert-unknown`, …), and
callers translate them with 34 `CASE` words such as
`lf-minfer-shift-status`. The numbers already agree everywhere: ok (or
equal) 0, invalid 1, exhausted 2, unknown 3. The translation words therefore
only rename codes and turn any unexpected code into *invalid*. They add
about 150 lines, hide the data flow, and invite a mapping mistake in the one
place where a mistake could turn a failure into success.

The owner's decision of 2026-11-02 requires three distinguishable checker
outcomes: accepted, rejected, and unsupported/unknown. There is no
*rejected* code today; a definitely wrong value returns *unknown*
(coverage finding T11), so rejection cannot be tested.

## Decision (proposed)

1. `src/lib/outcome.fs` defines one vocabulary, keeping today's numbers:

   | Outcome | Value | Meaning |
   | --- | --- | --- |
   | ok | 0 | The operation succeeded (for comparison: shown equal). |
   | invalid | 1 | Malformed input or corrupted state; fails closed. |
   | exhausted | 2 | Out of fuel: the processing budget ran out. |
   | unknown | 3 | Supported, but not decided by this cautious rule. |
   | rejected | 4 | Shown wrong: ill-typed, or definitely not equal. |
   | unsupported | 5 | Uses a feature LeanForth does not implement yet. |
   | full | 6 | Out of room: a store, stack or depth limit was reached. |

   *Exhausted* and *full* are different, at the owner's suggestion: the fix
   for the first is more fuel (time), for the second more memory or a larger
   limit, and at Mathlib scale the report must say which limit was hit.
   The split is implemented in every module (see *Implemented 2026-11-02*
   below).

   *Unsupported* and *unknown* are different, at the owner's suggestion.
   Unsupported means the input uses a construct LeanForth has not built
   yet (for example `let` expressions, projections, literals or inductive
   types): the fix is more code, and counting these by construct shows
   what to build next and how much of Mathlib each step unlocks. Unknown
   means the construct is supported but the cautious rule could not decide
   (for example two terms that may be equal only after unfolding a
   definition): the fix is a stronger algorithm. Both are reported to the
   user as the owner's single "unsupported/unknown" outcome, and neither is
   ever accepted. The NDJSON preview already distinguishes unsupported
   input (exit code 2).

   With a predicate for success and one word that maps any value outside
   the vocabulary to *invalid*. That single word replaces every translation
   word, so the fail-closed safety net stays in one reviewed place.
2. Modules adopt it bottom-up as they are refactored (roadmap Q10): module
   constants become the shared ones and translation words are deleted.
   Values are unchanged, so tests, fixtures and the Python and Lean scripts
   that print or compare status numbers are unaffected.
3. Later, separately reviewed: the checker returns *rejected* where Lean's
   rules show a term ill-typed or two terms definitely different, and
   *unsupported* where it meets a construct it does not implement (today
   such inputs return *invalid* or *unknown*), with pinned-Lean tests for
   every outcome.

Status codes and flags stay distinct: a status is tested with the success
predicate or compared with a named outcome, never consumed by `IF` as a
truth value, because 0 means success for a status but false for a flag.

## Implemented 2026-11-02: exhausted and full

`outcome-full` (6) is in `src/lib/outcome.fs`, and `outcome?` and
`outcome-sane` accept 0 to 6. Every place that reported *exhausted* was
classified: running out of the fuel budget stays *exhausted*; reaching a
store, stack, frame, depth, binder or cell-size limit is now *full*. No
typing or conversion rule changed: only the number reported for a room
failure, which was never accepted before and is not now.

**Which limit decides.** Where a visit is admitted against both fuel and
room (a frame, a depth limit, or a context level), the fuel decides: with
no fuel left the outcome is *exhausted* whatever the room, and only with
fuel left does missing room give *full*. One word states this rule,
`visit-outcome ( fuel room? -- outcome )` in `outcome.fs`, used by
`frame-room` (and through it `frame-call`, `frame-call2` and
`frame-under`), `lf-lvalue-room`, `lf-lcmp-room` and `lf-minfer-room`.

The exception, by design: limits that are checked where the work happens
inside a visit that has already been paid for are checked independently of
fuel. A work-stack push (`walk-push-outcome`, `walk-push2`,
`walk-pair-outcome`, `walk-children-at`), a binder depth at `max-n` in
`lf-cts-binary` and `lf-rebuild-binary` (`lf-rebuild-stuck?`), and
mixed-infer's binder context (`lf-minfer-under`) report *full* even when
the visit in progress took the last unit of fuel. Moving those checks
behind a fuel check would mean charging or testing fuel for work that is
not a visit; tests pin the behaviour (`tests/lib/lib.fs`,
`tests/core/mixed-shift.fs`, `constant-term-scope.fs`, `mixed-infer.fs`).

**Corrupted records are invalid.** A frames record whose limit is below 1
(`frame-init` never makes one) and a walk whose root cannot be pushed
(`walk-start` empties the stack and every walk record holds at least one
item, so only a corrupted capacity) report *invalid*, before fuel or room
is considered.

The per-module status aliases (`lf-mshift-exhausted`, `lf-repr-ok`,
`lf-mcompare-equal` and the rest, 49 constants in 14 modules) are gone:
the tests use the shared `outcome-*` names, so there is one vocabulary.

| Module | Word | Cause | Outcome |
| --- | --- | --- | --- |
| `lib/walk.fs` | `walk-step` | no fuel left | exhausted |
| `lib/walk.fs` | `walk-push-outcome`, `walk-push2`, `walk-pair-outcome`, `walk-children-at` | work stack has no room (whatever fuel is left) | full |
| `lib/walk.fs` | `walk-run`, `walk-run-pair` | root cannot be pushed (corrupted capacity) | invalid |
| `lib/frame.fs` | `frame-call`, `frame-call2` (`frame-room`) | limit below 1 / no fuel left / every frame in use | invalid / exhausted / full |
| `lib/frame.fs` | `frame-under` (`frame-deeper`) | as `frame-room`, then context at `max-n` cannot grow | as `frame-room` / full |
| `core/constant-term-scope.fs` | `lf-cts-binary` | binder depth at `max-n` (whatever fuel is left) | full |
| `kernel/level-value.fs` | `lf-lvalue-room` (`lf-lvalue-enter`) | no fuel / `lf-lvalue-depth-limit` | exhausted / full |
| `kernel/level-value.fs` | `lf-lvalue-succ+` | successor of `max-n` | full |
| `kernel/level-compare.fs` | `lf-lcmp-room` (`lf-lcmp-enter`) | no fuel / `lf-lcmp-depth-limit` | exhausted / full |
| `kernel/level-compare.fs` | `lf-lcmp-shrink` | no fuel | exhausted |
| `kernel/level-substitute.fs` | `lf-lsubst-stage` | level store has no room for a staged node | full |
| `kernel/level-substitute.fs` | `lf-lsubst-plan` | level identity serial would run out | full |
| `kernel/mixed-rebuild.fs` | `lf-rebuild-allocated` | term store full or its serial spent | full |
| `kernel/mixed-rebuild.fs` | `lf-rebuild-binary` | binder context at `max-n` (whatever fuel is left) | full |
| `kernel/mixed-shift.fs` | `lf-mshift-up` | index plus amount past `max-n` | full |
| `kernel/mixed-compare.fs` | `lf-mcompare-children` | work stack has no room | full |
| `kernel/mixed-compare.fs` | `lf-mcompare-names` | no fuel | exhausted |
| `kernel/mixed-infer.fs` | `lf-minfer-sort`, `lf-minfer-sort-type`, `lf-minfer-lam-type`, `lf-minfer-pi-sort` | term or level allocation fails (store full or serial spent) | full |
| `kernel/mixed-infer.fs` | `lf-minfer-under` | binder context full (whatever fuel is left) | full |
| `kernel/mixed-infer.fs` | `lf-minfer-room` (`lf-minfer-in-frame`) | no fuel / every frame in use | exhausted / full |
| `kernel/mixed-level-substitute.fs` | `lf-mls-made`, `lf-mls-new-constant`, `lf-mls-binary` | term or reference allocation fails (store full or serial spent) | full |
| `kernel/mixed-signature-audit.fs` | `lf-msa-run` | zero fuel | exhausted |
| `kernel/mixed-signature-probe.fs` | `lf-msp-room` | signature index full | full |

Every other module passes these outcomes on unchanged (`outcome-sane`
keeps 6). The Forth tables that the pinned-Lean differentials compare
produce the same output as before (no table case reaches a limit), so no
Lean, Python or shell table changed. Unit tests reach both outcomes at
every site, white-box where a limit is unreachable through the public
words (the depth limits of `level-value` and `level-compare`, the frame
and binder limits of `mixed-infer`, and `max-n` binder depth in
`constant-term-scope`, all one step beyond what a 64-node store allows).

## Rejected alternatives

- **Keep per-module codes.** Leaves 34 translation words and the risk they
  carry.
- **Renumber to make success nonzero (a flag).** Breaks the numbers that
  tests and scripts rely on, for no safety gain once statuses are never
  used as flags.
- **`CATCH`/`THROW` for invalid and exhausted.** Possibly cleaner rollback,
  but it changes control flow throughout the checker; it needs its own ADR
  (style guide, section 6).
