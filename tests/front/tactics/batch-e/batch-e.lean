-- The Lean twins of tests/front/tactics/batch-e/*.lf (plan row TB2, tactic batch 3b): each
-- theorem's type and value as S-expressions (batch-b.lean's printer), which tactic_check.py
-- compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps in
-- batch-e.golden.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

-- Lists of names (names.lf).
theorem nl_intro (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  revert h k
  intro x y
  exact x
theorem nl_holes (a b : Nat) (h : a = b) (k : b = a) : b = a := by
  revert h k
  intro _
  intro
  assumption
theorem nl_revert_dep (a b : Nat) (h : a = b) (k : h = h) : a = b := by
  revert a
  intro x y z
  exact y
theorem nl_clear (a b : Nat) (h : a = b) (k : h = h) (j : b = a) : b = a := by
  clear h k
  exact j
theorem nl_rename (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  revert h k
  intro _ _
  rename_i x y
  exact x
theorem nl_rename_hole (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  revert h k
  intro _ _
  rename_i x _
  exact x
-- Holes and refine (holes.lf).
theorem rf_and (a b : Nat) (h1 : a = b) (h2 : b = a) : a = b ∧ b = a := by
  refine And.intro ?_ ?_
  exact h1
  exact h2
theorem rf_and_case (a b : Nat) (h1 : a = b) (h2 : b = a) : a = b ∧ b = a := by
  refine And.intro ?_ ?_
  case refine_2 => exact h2
  case refine_1 => exact h1
theorem rf_named (a b : Nat) (h1 : a = b) (h2 : b = a) : a = b ∧ b = a := by
  refine And.intro ?left ?right
  case right => exact h2
  case left => exact h1
theorem rf_one (a b : Nat) (h1 : a = b) (h2 : b = a) : a = b ∧ b = a := by
  refine And.intro h1 ?_
  exact h2
theorem rf_or (a b : Nat) (h : a = b) : a = b ∨ b = a := by
  refine Or.inl ?_
  exact h
theorem rf_natural (a : Nat) : a = a := by
  refine Eq.refl _
theorem ex_hole (a : Nat) : a = a := by
  exact Eq.refl _
theorem ap_hole (a : Nat) : a ≤ a := by
  apply Nat.le_refl _
theorem hv_hole (a : Nat) : a ≤ a := by
  have h : a ≤ a := Nat.le_refl _
  exact h

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
  for n in [``nl_intro, ``nl_holes, ``nl_revert_dep, ``nl_clear, ``nl_rename,
      ``nl_rename_hole, ``rf_and, ``rf_and_case, ``rf_named, ``rf_one, ``rf_or, ``rf_natural,
      ``ex_hole, ``ap_hole, ``hv_hole] do
    dump n
