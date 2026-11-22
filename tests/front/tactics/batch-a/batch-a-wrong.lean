-- Pinned Lean's errors for the wrong twins of tests/front/tactics/batch-a/w-*.lf (plan row
-- TB2, tactic batch 1): tactic_check.py --lean checks that each message the LeanForth file
-- must print is Lean's. Batteries' swap and absurd copied as in batch-a.lean.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

syntax goalNum := "-"? num
def elabGoalNum (goalNum : Syntax) : TacticM Nat := withRef goalNum do
  let nGoals := (← getGoals).length
  let some nth := goalNum[1].isNatLit? | Elab.throwUnsupportedSyntax
  if nth = 0 then throwError "goals are 1-indexed"
  if nth > nGoals then throwError "goal index `{nth}` is out of bounds"
  return if goalNum[0].isNone then nth - 1 else nGoals - nth
elab "pick_goal " n:goalNum : tactic => do
  let n ← elabGoalNum n
  let (gl, g :: gr) := (← getGoals).splitAt n | throwNoGoalsToBeSolved
  setGoals $ g :: (gl ++ gr)
macro "swap" : tactic => `(tactic| pick_goal 2)
macro "absurd " h:term : tactic =>
  `(tactic|
    first
    | refine @absurd _ _ ?_ $h
    | refine @absurd _ _ $h ?_)

theorem w_ch (a b : Nat) (h : b ≤ a) : a ≥ b := by
  change a ≤ b
  exact h
theorem w_sh (a b : Nat) (h : b ≤ a) : a ≥ b := by
  show a ≤ b
  exact h
theorem w_sh_many (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  show a = b
theorem w_sh_type (a b : Nat) (h : b ≤ a) : a ≥ b := by
  show a
theorem w_sw (a b : Nat) (h : a ≤ b) : a ≤ b := by
  swap
theorem w_sp (a b : Nat) (h : a ≤ b) : a ≤ b := by
  specialize Nat.le_refl a
theorem w_sp_exact (a b : Nat) (h2 : b ≤ a) (h : a ≤ b) : a ≤ b := by
  specialize h
  exact h2
theorem w_rv (a b : Nat) (h : a ≤ b) : a ≤ b := by
  revert Nat.le_refl
theorem w_de (a b : Nat) (h : b ≤ a) : a ≥ b := by
  delta Ne
theorem w_cn (a b : Nat) (h : a = b) : b = a := by
  contradiction
theorem w_tr (a b : Nat) (h : a = b) : b = a := by
  trivial
theorem w_ab (a b : Nat) (h : a ≤ b) (h2 : a ≤ b) : a = b := by
  absurd h
  assumption
