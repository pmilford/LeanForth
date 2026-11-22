-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-b/w-*.lf (plan row
-- TB2, tactic batch 2): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's. Mathlib's have_goal copied as in batch-b.lean.
import Lean
open Lean Meta Elab Tactic Term
set_option linter.unusedVariables false

def haveLetCore (goal : MVarId) (n : Name) (t : Term) : TermElabM (MVarId × MVarId) :=
  goal.withContext do
    let t ← withRef t do
      let e ← Term.elabType t
      Term.synthesizeSyntheticMVars (postpone := .no)
      instantiateMVars e
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, goal2) ← (← goal.assert n t p).intro1P
    pure (p.mvarId!, goal2)
elab "have_goal " n:ident " : " t:term : tactic => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n.getId t
  replaceMainGoal [goal1, goal2]

theorem w_hv (a b : Nat) (h : a ≤ b) : a ≤ b := by
  have k : b ≤ a := h
theorem w_hv_this (a b : Nat) (h : a ≤ b) : b ≤ a := by
  have := h
  exact this
theorem w_lt (a b : Nat) (h : a ≤ b) : a ≤ b := by
  let x : Nat := h
theorem w_sf (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : a ≤ b := by
  suffices k : a ≤ b from h2
theorem w_rp (a b : Nat) (h : a ≤ b) : a ≤ b := by
  replace h : b ≤ a := h
theorem w_hg (a b : Nat) (h : a ≤ b) : a ≤ b := by
  have_goal k : b ≤ a
  exact h
