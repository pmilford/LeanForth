-- Pinned Lean twins of tests/front/tactics/simp-1/*.lf (plan row FE9, simp slice SL1a-1:
-- simp only on the target): tactic_check.py --lean writes simp-1.golden from this file's
-- terms, which LeanForth's must equal node for node. u_def, u_at, u_hyp_prop and u_literal
-- are the texts LeanForth answers 99 (not supported yet) for; Lean accepts them.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem simp_add_zero (n : Nat) : n + 0 + 0 = n := by
  simp only [Nat.add_zero]
theorem simp_hyp (a b : Nat) (h : a = b) : a * 2 = b * 2 := by
  simp only [h]
theorem simp_hyp_whole (a c : Nat) (h : a * 6 = c) : a * 6 = c := by
  simp only [h]
theorem simp_true : True := by
  simp only []
theorem simp_self (n : Nat) : n = n := by
  simp only []
theorem u_at (a b : Nat) (h : a + 0 = b) : a = b := by
  simp only [Nat.add_zero] at h
  exact h
theorem simp_symm (a b : Nat) (h : b = a) : a = b := by
  simp only [← h]
theorem simp_prop (a b : Nat) (h : a ≤ b) : a ≤ b ∧ a ≤ b := by
  simp only [h, and_self]
theorem simp_same_head (a b : Nat) (h : a + 1 = b + 1) : a + 1 + 1 = b + 1 + 1 := by
  simp only [h]
theorem simp_mul_zero (n : Nat) : n * 0 = 0 := by
  simp only [Nat.mul_zero]
theorem simp_mul_one (n : Nat) : n * 1 = n := by
  simp only [Nat.mul_one]
theorem simp_mul_one_twice (a : Nat) : a * 1 * 1 = a := by
  simp only [Nat.mul_one]
theorem simp_zero_add_mul_one (n : Nat) : 0 + n = n * 1 := by
  simp only [Nat.zero_add, Nat.mul_one]
theorem simp_sub_self (a : Nat) : (a + 1) - (a + 1) = 0 := by
  simp only [Nat.sub_self]
theorem simp_chain (a b c : Nat) (h : a = b) (h2 : b = c) : a = c := by
  simp only [h, h2]
theorem u_hyp_prop (h : True) : True := by
  simp only [h]
theorem u_def (a : Nat) : Nat.add a 0 = a := by
  simp only [Nat.add]
theorem u_literal (a c : Nat) (h : a * 6 = c) : a * (2 * 3) = c := by
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
  | e => return s!"?? {e}"

def dump (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} type {← sx i.type}"
  IO.println s!"{n} value {← sx i.value}"


#eval do
  for n in [``simp_add_zero, ``simp_hyp, ``simp_hyp_whole, ``simp_true, ``simp_self,
      ``simp_symm, ``simp_prop, ``simp_same_head, ``simp_mul_zero, ``simp_mul_one,
      ``simp_mul_one_twice, ``simp_zero_add_mul_one, ``simp_sub_self, ``simp_chain, ``u_at, ``u_hyp_prop, ``u_def, ``u_literal] do
    dump n
