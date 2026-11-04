# Beyond Lean: limitations noticed, for a later improved mode

**Purpose.** LeanForth's checker gives exactly Lean 4.35.0's verdicts
(owner's rule, 2026-11-03; [decisions](OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)).
While matching Lean, the project keeps finding places where Lean's kernel
rejects, or cannot decide, something that is true. The owner asked that each
be noted carefully: "we need 100% compatibility with lean, but, also, if we
can have an improved solver mode, that would be great!"

**Rules.**

1. **Compatibility mode is the only mode for now.** No entry here changes
   what LeanForth answers; every entry is a candidate for a separate,
   later *improved mode*.
2. **An improved mode would be opt-in and labelled.** A declaration it
   accepts that Lean rejects is marked as such
   (for example *accepted in improved mode — Lean 4.35.0 rejects this*), so
   that it is never mistaken for a Lean-compatible result, and a library
   that depends on it is marked too.
3. **Soundness first.** Each entry records why accepting more would be
   sound (for example, a semantic argument in the standard model); every
   rule of the improved mode goes through the same gate as the checker
   (an ADR citing the argument, Lean comparisons, an independent review
   and the owner's approval).
4. **Everyone records.** Any agent or person who finds such a case adds a
   row with a Lean-checked reproducer; it is not fixed silently.

## Ledger

| ID | Found | What Lean 4.35.0 does | What could be decided instead | Why it would be sound | Evidence | Status |
| --- | --- | --- | --- | --- | --- | --- |
| BL-1 | 2026-11-03, review of the declaration check | Lean builds universe levels with simplifying constructors (`mk_max`, `mk_imax`) and compares levels by structure, or by structure after its `normalize`. That comparison is incomplete: it rejects levels that are equal for every value of their parameters, for example a declared `Sort (imax 1 (u+1))` against an inferred sort Lean simplifies differently; Lean reports `declTypeMismatch` or `appTypeMismatch` for declarations its own elaborator produced | Decide level equality completely: two levels built from `0`, `+1`, `max`, `imax` and parameters are equal for all parameter values exactly when they agree after splitting each parameter into zero and non-zero, a finite check | Universe levels denote natural numbers; levels that are equal for every assignment denote the same universe in every model, so identifying them adds no new provable statement about ordinary mathematics | Lean-checked rows of `tests/reference/universe-scope-terms.lean` (ADR 0011 Amendment 1): the review's `pi-imax-swapped` (T1), `pi-imax-prop-domain` (T4), `app-imax` (th) and `instance-imax-nonzero` (d); and, found by agent LV with the same cause — `normalize` gives an `imax` the `mk_imax` of its normalized sides and never re-sorts or re-normalizes the `max` that makes, so the other side's sorted, subsumed form differs — `zero-rewrite-gone` (`max 0 (imax 1 (u+1))` against `imax 1 (u+1)`, under `+1`), its reverse, `instance-imax-order` (`T.{w+1, 1}` against `imax (w+1) 1`) and `instance-swapped-imax`; every pair has equal values for all parameters. `make test-universe-scope-differential` checks Lean's verdict on each | Compatibility fix done (agent LV, ADR 0011 Amendment 1): LeanForth rejects these exactly as Lean does; improved mode not started |
| BL-3 | 2026-11-03, agent LV (ADR 0011 Amendment 1, rule K6) | Lean's verdict on a declaration can depend on how its objects share memory, which no export or text records: specializing a constant whose stored type holds a level that `mk_max`/`mk_imax` would simplify (`imax 1 (u+1)`), the kernel keeps it when the universe argument is the very object of the stored type (`update_max`'s pointer test, `level.cpp` 308-315) and simplifies it otherwise, so the same text is accepted or rejected (`declTypeMismatch`). LeanForth answers *unknown* there | Decide such a declaration by level values (BL-1), so that both memory layouts get the same answer | As BL-1: the two levels Lean may build have the same value for every assignment | `universe.shared-object`, `fresh-object`, `shared-object-max`, `fresh-object-max` in `tests/reference/universe-scope-terms.lean` (two verdicts each pair, checked by the file); probe `.claude/work/LV/probes/sharing.lean` | Compatibility: *unknown* (K6); improved mode not started |
| BL-2 | 2026-11-02, big-number library | Lean's kernel computes `Nat.add`, `Nat.mul`, `Nat.pow` and eleven other `Nat` operations on literals directly (GMP), but not `Nat.log2`, which it evaluates by unfolding its definition, very slowly on large numbers | Compute `Nat.log2` (and possibly other `Nat` functions with simple specifications) directly | The computed value equals the definition's; it would need a proof that the fast computation matches the definition, as for the existing operations | `src/lib/bignum.fs` header (Lean's `type_checker.cpp` calls no log2) | Candidate; speed only, not more theorems |

## Related plan items

- Plan [W8, the improved mode](PLAN_DRAFT.md#w8-improved-mode-beyond-lean):
  designed only after the compatibility checker covers Mathlib (phase 6),
  so that compatibility is never delayed.
- The level comparison itself: ADR 0011's amendment for levels (agent LV)
  and plan tasks 4.1.2 and 4.2.1.
