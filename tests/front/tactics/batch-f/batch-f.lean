-- The Lean twins of tests/front/tactics/batch-f/*.lf (plan row TB2, tactic batch 3c): each
-- theorem's type and value as S-expressions (batch-b.lean's printer), which tactic_check.py
-- compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps in
-- batch-f.golden.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

-- The anonymous constructor (anon.lf).
theorem an_and (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  exact ⟨h, k⟩
theorem an_three (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a ∧ a = b := by
  exact ⟨h, k, h⟩
theorem an_nested (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a ∧ a = b := by
  exact ⟨h, ⟨k, h⟩⟩
theorem an_id (a b : Nat) (h : a = b) (k : b = a) : id (a = b ∧ b = a) := by
  exact ⟨h, k⟩
theorem an_true (a : Nat) : True := by
  exact ⟨⟩
theorem an_exists (a : Nat) : Exists (Eq a) := by
  exact ⟨a, Eq.refl a⟩
theorem an_have (a b : Nat) (h : a = b) (k : b = a) : b = a ∧ a = b := by
  have x : a = b ∧ b = a := ⟨h, k⟩
  exact ⟨And.right x, And.left x⟩
theorem an_refine (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  refine ⟨?_, ?_⟩
  exact h
  exact k
theorem an_case (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  refine ⟨?_, ?_⟩
  case refine_2 => exact k
  case refine_1 => exact h

-- exists (exists.lf).
theorem ex_eq (a : Nat) : Exists (Eq a) := by
  exists a
theorem ex_and (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  exists h
theorem ex_and3 (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a ∧ a = b := by
  exists h, k
theorem ex_open (a b : Nat) (h : a = b) : Exists (Eq b) := by
  exists a
  exact Eq.symm h

-- Lists over several lines (lines.lf): the same proofs on one line.
theorem ml_names (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  revert h k
  intro x y
  exact x
theorem ml_rw (a b c : Nat) (h : a = b) (h2 : a ≤ c) (h3 : c ≤ a) : b ≤ c := by
  rewrite [h] at h2 h3
  exact h2
-- (Batteries' exacts [h, k], as core exact steps: batch-b's twin)
theorem ml_exacts (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  exact h
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
  for n in [``an_and, ``an_three, ``an_nested, ``an_id, ``an_true, ``an_exists, ``an_have,
      ``an_refine, ``an_case, ``ex_eq, ``ex_and, ``ex_and3, ``ex_open, ``ml_names, ``ml_rw,
      ``ml_exacts] do
    dump n
