-- The Lean twins of tests/front/tactics/batch-a/*.lf (plan row TB2, tactic batch 1): each
-- theorem's type and value as S-expressions (tests/front/tactics/goal-layer.lean's printer),
-- which tactic_check.py compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and
-- keeps in batch-a.golden. Batteries' swap (pick_goal 2) and absurd are copied from
-- .tools/mathlib/mathlib4/.lake/packages/batteries/Batteries/Tactic/PermuteGoals.lean:31-54 and
-- Init.lean:67-73, as plain `lean` loads no Batteries.
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

-- change and show: @id T ?g, or the goal itself when the pattern is its type.
theorem ch_target (a b : Nat) (h : b ≤ a) : a ≥ b := by
  change b ≤ a
  exact h
theorem ch_same (a b : Nat) (h : a ≤ b) : a ≤ b := by
  change a ≤ b
  exact h
theorem sh_target (a b : Nat) (h : b ≤ a) : a ≥ b := by
  show b ≤ a
  exact h
theorem sh_second (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  show b ≤ a
  exact h2
  exact h1
-- swap, revert, specialize.
theorem sw_and (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  swap
  exact h2
  exact h1
theorem rv_hyp (a b : Nat) (h : a ≤ b) : a ≤ b := by
  revert h
  intro k
  exact k
theorem rv_dep (a b : Nat) (h : a ≤ b) : a ≤ b := by
  revert a
  intro x
  intro hx
  exact hx
theorem sp_self (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : a ≤ b := by
  specialize h
  assumption
theorem sp_exact (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : a ≤ b := by
  specialize h
  exact h
theorem sp_later (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : b ≤ a := by
  specialize h
  exact h2
theorem rv_reuse (a b : Nat) (h : a ≤ b) : a ≤ b := by
  revert a
  intro a
  intro h
  exact h
-- delta, contradiction, trivial, absurd.
theorem de_ge (a b : Nat) (h : b ≤ a) : a ≥ b := by
  delta GE.ge
  exact h
theorem cn_false (a b : Nat) (h : False) : a = b := by contradiction
theorem cn_not (a b : Nat) (h : ¬ a ≤ b) (h2 : a ≤ b) : a = b := by contradiction
theorem cn_ne (a b : Nat) (h : a ≠ a) : a = b := by contradiction
theorem tr_rfl (a : Nat) : a = a := by trivial
theorem tr_and : True ∧ True := by trivial
theorem tr_decide : 2 + 2 = 4 := by trivial
theorem tr_false (a b : Nat) (h : False) : a = b := by trivial
theorem tr_assumption (a b : Nat) (h : a = b) : a = b := by trivial
theorem ab_neg (a b : Nat) (h : ¬ a ≤ b) (h2 : a ≤ b) : a = b := by
  absurd h
  exact h2
theorem ab_pos (a b : Nat) (h : a ≤ b) (h2 : ¬ a ≤ b) : a = b := by
  absurd h
  assumption

def pl (l : Level) : String := match l.toNat with
  | some n => toString n
  | none => "?l"

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .const n us => return n.toString ++ ".{" ++ String.intercalate "," (us.map pl) ++ "}"
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | .sort l => return "Sort " ++ pl l
  | .lit (.natVal n) => return toString n
  | .mdata _ e => sx e
  | e => return s!"?? {e}"

def dump (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} type {← sx i.type}"
  IO.println s!"{n} value {← sx i.value}"

#eval do
  for n in [``ch_target, ``ch_same, ``sh_target, ``sh_second, ``sw_and, ``rv_hyp, ``rv_dep,
      ``sp_self, ``sp_exact, ``sp_later, ``rv_reuse, ``de_ge, ``cn_false, ``cn_not, ``cn_ne, ``tr_rfl, ``tr_and, ``tr_decide,
      ``tr_false, ``tr_assumption, ``ab_neg, ``ab_pos] do
    dump n
