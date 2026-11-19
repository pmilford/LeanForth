-- The Lean twins of tests/front/tactics/{apply,assumption,constructor}/*.lf
-- (slice a2-iii of docs/design/TACTIC_PLUGINS.md): each theorem's type and
-- value as S-expressions (the printer of tests/front/s2-proofs.lean),
-- which tests/front/tactics/tactic_check.py compares with LeanForth's
-- (tests/front/elab-dump.fs) and keeps in tests/front/tactics/goal-layer.golden.
import Lean
open Lean Meta
set_option linter.unusedVariables false

-- apply: a theorem, a hypothesis, implicit arguments left as goals in
-- Lean's order (non-dependent first). (A range of more than one argument
-- count needs a goal with a binder, which natural LeanForth cannot write
-- yet: tests/front/tactics/apply/test.fs reaches it.)
theorem ap_le_succ (n : Nat) : n ≤ n + 1 := by apply Nat.le_succ
theorem ap_le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans
  apply h1
  apply h2
theorem ap_hyp (a b : Nat) (h : a ≤ b) : a ≤ b := by apply h
theorem ap_partial (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans h1
  exact h2
theorem ap_tag (n : Nat) : True ∧ True := by
  induction n with
  | zero => apply And.intro; constructor; constructor
  | succ k ih => apply And.intro; constructor; constructor
theorem ap_and (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  apply And.intro
  exact h1
  exact h2
-- assumption: the newest hypothesis that fits, up to definitional equality.
theorem as_one (a b : Nat) (h : a ≤ b) : a ≤ b := by assumption
theorem as_newest (a b : Nat) (h1 : a ≤ b) (h2 : a ≤ b) : a ≤ b := by assumption
theorem as_defeq (a : Nat) (h : a ≤ a) : a ≤ a + 0 := by assumption
-- constructor: the first constructor that applies.
theorem co_and (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a ≤ b ∧ b ≤ a := by
  constructor
  exact h1
  exact h2
theorem co_true : True := by constructor
theorem co_or (a : Nat) (h : a ≤ a) : a ≤ a ∨ a ≤ a + 1 := by
  constructor
  exact h
theorem co_le (n : Nat) : n ≤ n := by constructor

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
  | e => return s!"?? {e}"

def dump (n : Name) : MetaM Unit := do
  let some (.thmInfo i) := (← getEnv).find? n | IO.println s!"{n} ??"
  IO.println s!"{n} type {← sx i.type}"
  IO.println s!"{n} value {← sx i.value}"

#eval do
  for n in [``ap_le_succ, ``ap_le_trans, ``ap_hyp, ``ap_partial, ``ap_tag, ``ap_and, ``as_one, ``as_newest,
      ``as_defeq, ``co_and, ``co_true, ``co_or, ``co_le] do
    dump n
