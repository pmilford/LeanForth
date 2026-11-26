-- Pinned Lean twins of tests/front/tactics/simp-2/*.lf (plan row FE9, simp slice SL1a-2:
-- simp only at hypotheses): tactic_check.py --lean writes simp-2.golden from this file's
-- terms, which LeanForth's must equal node for node. u_at_star is the text LeanForth
-- answers 99 (not supported yet) for; Lean accepts it. (A hypothesis changed by defeq that
-- another depends on, also 99, is unit-tested: LeanForth's text cannot state `h = h`.)
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem simp_at_defeq (a b : Nat) (h : a + 0 = b) : a = b := by
  simp only [Nat.add_zero] at h
  exact h
theorem simp_at_proof (a b c : Nat) (h : a = b) (k : a + 0 = c) : b = c := by
  simp only [h, Nat.add_zero] at k
  exact k
theorem simp_at_goal (a b c : Nat) (h : a = b) (k : a + 0 = c) : b + 0 = c := by
  simp only [h, Nat.add_zero] at k ⊢
  exact k
theorem simp_at_two (a b c d : Nat) (h : a = b) (k1 : a + 0 = c) (k2 : a = d) : b = c := by
  simp only [h, Nat.add_zero] at k1 k2
  exact k1
theorem simp_at_mixed (a b c : Nat) (h : a = b) (k1 : c + 0 = b) (k2 : a = c) : c = b := by
  simp only [h, Nat.add_zero] at k1 k2
  exact k1
theorem simp_at_false (a b : Nat) (k : (a = b) = False) (h : a = b) : a = 0 := by
  simp only [k] at h
theorem simp_at_false_defeq (a : Nat) (h : False) : a = 0 := by
  simp only [] at h
theorem simp_at_true (a b : Nat) (h : a = b) (k : b = a) : b = a := by
  simp only [h] at h
  exact k
theorem simp_at_one_still (a b c : Nat) (h : a = b) (k1 : a = c) (k2 : b = c) : b = c := by
  simp only [h] at k1 k2
  exact k1
theorem simp_at_goal_kept (a b : Nat) (h : a = b) (k : a + 0 = b) : a = b := by
  simp only [Nat.add_zero] at k ⊢
  exact k
theorem u_at_star (a b : Nat) (h : a + 0 = b) : a = b := by
  simp only [Nat.add_zero] at *
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
  for n in [``simp_at_defeq, ``simp_at_proof, ``simp_at_goal, ``simp_at_two, ``simp_at_mixed,
      ``simp_at_false, ``simp_at_false_defeq, ``simp_at_true, ``simp_at_one_still,
      ``simp_at_goal_kept, ``u_at_star] do
    dump n
