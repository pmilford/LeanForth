-- Pinned Lean twins of tests/front/tactics/simp-4/simp-4.lf (plan row FE9, simp group 4,
-- pass 1: plain simp with the default set): tactic_check.py --lean writes simp-4.golden from
-- this file's terms, which LeanForth's must equal node for node. The file imports Lean for
-- its printer, so its default set is Lean's, not Init's alone: each goal here is one whose
-- lemmas are Init's (the kernel checks LeanForth's term against the Init slice), and the
-- Init-only reference is the harness of tests/front/simp-init.lean (simp group 4, pass 3).
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

theorem simp_true : True := by simp
theorem simp_true_and : True ∧ True := by simp
theorem simp_add_zero (a : Nat) : a + 0 = a := by simp
theorem simp_or_true : False ∨ True := by simp
theorem simp_not_not (a : Nat) : ¬¬(a = a) := by simp
theorem simp_mul_one (a : Nat) : a * 1 + 0 = a := by simp
-- Pass 2: the default simprocs (tests/front/tactics/simp-4/simprocs.lf).
theorem simp_ite_true (a b : Nat) : (if True then a else b) = a := by simp
theorem simp_ite_false (a b : Nat) : (if False then a else b) = b := by simp
theorem simp_add_lits : 2 + 3 = 5 := by simp
theorem simp_mul_add : 7 * 6 + 2 = 44 := by simp

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
  for n in [``simp_true, ``simp_true_and, ``simp_add_zero, ``simp_or_true, ``simp_not_not,
      ``simp_mul_one, ``simp_ite_true, ``simp_ite_false, ``simp_add_lits,
      ``simp_mul_add] do
    dump n
