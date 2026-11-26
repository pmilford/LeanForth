-- Pinned Lean twins of tests/front/tactics/simp-3/*.lf (plan row FE9, simp group 3: simp only
-- below binders and through congruence lemmas): tactic_check.py --lean writes simp-3.golden from
-- this file's terms, which LeanForth's must equal node for node.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem simp_binder_arrow (a b c : Nat) (h2 : a = c) (h : a = b) : c = b := by
  revert h
  simp only [h2]
  intro h
  exact h
theorem simp_binder_forall (a : Nat) : a + 0 = a := by
  revert a
  simp only [Nat.add_zero]
  intro a
  exact True.intro
theorem simp_binder_forall_hyp (c d : Nat) (h : c = d) (a : Nat) : a + c = a + d := by
  revert a
  simp only [h]
  intro a
  exact True.intro
theorem simp_binder_nested (b a : Nat) (h : a + 0 = b) : a = b := by
  revert h
  revert a
  simp only [Nat.add_zero]
  intro a
  intro h
  exact h
theorem simp_ite (a b : Nat) (h : a = b) :
    (if a = 0 then 1 else 2) = (if b = 0 then 1 else 2) := by
  simp only [h]
theorem simp_ite_branch (a b c : Nat) (h : a = b) :
    (if c = 0 then a else 2) = (if c = 0 then b else 2) := by
  simp only [h]
theorem simp_decide (a b : Nat) (h : a = b) : decide (a = 0) = decide (b = 0) := by
  simp only [h]

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
  | .proj s i e => return s!"(proj {s} {i} {← sx e})"
  | e => return s!"?? {e}"

def dump (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} type {← sx i.type}"
  IO.println s!"{n} value {← sx i.value}"

#eval do
  for n in [``simp_binder_arrow, ``simp_binder_forall, ``simp_binder_forall_hyp,
      ``simp_binder_nested, ``simp_ite, ``simp_ite_branch, ``simp_decide] do
    dump n
