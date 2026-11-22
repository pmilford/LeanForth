-- The Lean twins of tests/front/tactics/batch-b/*.lf (plan row TB2, tactic batch 2): each
-- theorem's type and value as S-expressions (batch-a.lean's printer with Lean's letE as
-- (let T V B), and (let-nd T V B) for a nondependent one, a have), which tactic_check.py
-- compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps in
-- batch-b.golden. Mathlib's valueless have h : T (Mathlib/Tactic/Have.lean:71-96,
-- haveLetCore with keepTerm false) is copied as have_goal, as plain `lean` loads no Mathlib.
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

-- have, have :=, have_goal.
theorem hv_named (a b : Nat) (h : a ≤ b) : a ≤ b := by
  have k : a ≤ b := h
  exact k
theorem hv_this (a b : Nat) (h : a ≤ b) : a ≤ b := by
  have := h
  exact this
theorem hv_type (a b : Nat) (h : a ≤ b) : b ≥ a := by
  have k : b ≥ a := h
  exact k
theorem hv_case (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  have k : a ≤ b := h1
  exact k
  exact h2
theorem hg_goal (a b : Nat) (h : a ≤ b) : a ≤ b := by
  have_goal k : a ≤ b
  exact h
  exact k
theorem hg_unused (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : a ≤ b := by
  have_goal k : b ≤ a
  exact h2
  exact h
-- let, suffices, replace.
theorem lt_basic (a b : Nat) (h : a ≤ b) : a ≤ b := by
  let x : Nat := a
  exact h
theorem lt_use (a : Nat) : a ≤ a := by
  let x : Nat := a
  exact Nat.le_refl x
theorem sf_basic (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : a ≤ b := by
  suffices k : b ≤ a from h
  exact h2
theorem sf_shadow (a b : Nat) (h : a ≤ b) : a ≤ b := by
  suffices h : b ≥ a from h
  exact h
theorem rp_ge (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : b ≥ a := by
  replace h : b ≥ a := h
  exact h
theorem rp_new (a b : Nat) (h : a ≤ b) : a ≤ b := by
  replace k : a ≤ b := h
  exact k

def pl (l : Level) : String := match l.toNat with
  | some n => toString n
  | none => "?l"

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .const n us => return n.toString ++ ".{" ++ String.intercalate "," (us.map pl) ++ "}"
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | .letE _ t v b nd => return s!"({if nd then "let-nd" else "let"} {← sx t} {← sx v} {← sx b})"
  | .sort l => return "Sort " ++ pl l
  | .lit (.natVal n) => return toString n
  | .mdata _ e => sx e
  | e => return s!"?? {e}"

def dump (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} type {← sx i.type}"
  IO.println s!"{n} value {← sx i.value}"

#eval do
  for n in [``hv_named, ``hv_this, ``hv_type, ``hv_case, ``hg_goal, ``hg_unused, ``lt_basic,
      ``lt_use, ``sf_basic, ``sf_shadow, ``rp_ge, ``rp_new] do
    dump n
