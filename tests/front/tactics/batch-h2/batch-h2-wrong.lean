-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-h2/w-*.lf (plan row
-- TB2, piece E, slice E2b): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's. by_contra is batch-h2.lean's copy of Batteries'.
import Lean
open Lean Meta Elab Tactic Parser.Tactic
set_option linter.unusedVariables false

macro "by_contra_core" : tactic => `(tactic| first
  | guard_target = Not _; change _ → False
  | refine @Decidable.byContradiction _ _ ?_
  | refine @Classical.byContradiction _ ?_)
syntax (name := byContra) "by_contra" (ppSpace colGt rcasesPatMed)? (" : " term)? : tactic
macro_rules
| `(tactic| by_contra $[$pat?]? $[: $ty?]?) => do
  let pat ← pat?.getDM `(rcasesPatMed| $(mkIdent `this):ident)
  `(tactic| (by_contra_core; rintro ($pat:rcasesPatMed) $[: $ty?]?))

theorem w_contra_alts (a b : Nat) (h : ¬a = b) : ¬(a = b ∨ b = a) := by
  by_contra h1 | h2
  contradiction
  exact h1
theorem w_looks_empty (a : Nat) (h : False ∧ a = a) : False := by
  contradiction
theorem w_one_ctor (h : True) : False := by
  contradiction
theorem x_indexed (a b : Nat) (h : a ≤ b) : False := by
  contradiction
