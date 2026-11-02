# ADR 0008: one outcome vocabulary — proposal

Status: **proposed**, 2026-11-02. A code-structure decision for untrusted,
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
   | exhausted | 2 | A fuel, capacity or depth limit was reached. |
   | unknown | 3 | Supported, but not decided by this cautious rule. |
   | rejected | 4 | Shown wrong: ill-typed, or definitely not equal. |
   | unsupported | 5 | Uses a feature LeanForth does not implement yet. |

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

## Rejected alternatives

- **Keep per-module codes.** Leaves 34 translation words and the risk they
  carry.
- **Renumber to make success nonzero (a flag).** Breaks the numbers that
  tests and scripts rely on, for no safety gain once statuses are never
  used as flags.
- **`CATCH`/`THROW` for invalid and exhausted.** Possibly cleaner rollback,
  but it changes control flow throughout the checker; it needs its own ADR
  (style guide, section 6).
