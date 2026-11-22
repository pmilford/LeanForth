-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-c/w-*.lf (plan row
-- TB2, tactic batch 2b): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's. Batteries' exacts and by_contra copied as in batch-c.lean.
import Lean
open Lean Meta Elab Tactic Parser.Tactic
set_option linter.unusedVariables false

elab "exacts " "[" hs:term,* "]" : tactic => do
  for stx in hs.getElems do
    evalTactic (← `(tactic| exact $stx))
  evalTactic (← `(tactic| done))
macro "by_contra_core" : tactic => `(tactic| first
  | guard_target = Not _; change _ → False
  | refine @Decidable.byContradiction _ _ ?_
  | refine @Classical.byContradiction _ ?_)
syntax (name := byContra) "by_contra" (ppSpace colGt rcasesPatMed)? (" : " term)? : tactic
macro_rules
| `(tactic| by_contra $[$pat?]? $[: $ty?]?) => do
  let pat ← pat?.getDM `(rcasesPatMed| $(mkIdent `this):ident)
  `(tactic| (by_contra_core; rintro ($pat:rcasesPatMed) $[: $ty?]?))

theorem w_rs (a b : Nat) (h : a = b) : a + 0 = a := by
  rw [← h]
theorem w_ra (a b c : Nat) (h : a = b) (h2 : c = b) : a = c := by
  rwa [h]
theorem w_ex (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  exacts [h1]
theorem w_ex_type (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  exacts [h2, h1]
theorem w_bc (a b : Nat) (h1 : b ≤ a) : a ≤ b := by
  by_cases h : a ≤ b
  exact h1
theorem w_bk (a b : Nat) (h : a ≤ b) : a ≤ b := by
  by_contra k
  exact h
theorem w_sy (a b : Nat) (h : ¬a ≤ b) : ¬a ≤ b := by
  symm
theorem w_ai (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  and_intros
  exact h2
theorem w_nx (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  next => exact h2
