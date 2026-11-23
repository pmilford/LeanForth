-- The Lean twins of tests/front/tactics/blocks-2/*.lf (plan row TB2, blocks slice 2): each
-- theorem's type and value as S-expressions (batch-b.lean's printer), which tactic_check.py
-- compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps in
-- blocks-2.golden.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

-- t1 <;> t2 (and-then.lf): Lean's macro focus (t1; all_goals t2).
theorem at_and (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor <;> assumption
theorem at_none (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  exact h <;> exact k
theorem at_one (a b : Nat) (h : a = b) : a = b := by
  revert h
  intro x <;> exact x
theorem at_three (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a ∧ a = b := by
  and_intros <;> assumption
theorem at_chain (a b : Nat) (h : a = b) : (a = b ∧ a = b) ∧ (a = b ∧ a = b) := by
  constructor <;> constructor <;> exact h
theorem at_rest (a b : Nat) (h : a = b) (k : b = a) : (a = b ∧ a = b) ∧ b = a := by
  constructor
  constructor <;> exact h <;> exact h
  exact k
theorem at_ind (n : Nat) : n + 0 = n := by
  (induction n with
   | zero => rfl
   | succ m ih => rfl) <;> rfl
theorem at_induct (n : Nat) : n + 0 = n := by
  induction n <;> rfl
theorem at_brace (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor <;> { assumption }
theorem at_inner (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ (b = a ∧ b = a) := by
  constructor
  · exact h
  · constructor <;> exact k
theorem at_alt (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl <;> rfl
  | succ m ih => rfl
theorem at_loc (a b : Nat) (h : a = b) : b = a := by
  revert h
  intro x <;> symm at x
  exact x
theorem at_names (a b : Nat) (h : a = b) : a = b ∧ a = b := by
  constructor <;> have x : a = b := h
  exact x
  exact x

-- by-all-goals (all-goals.lf): Lean's all_goals.
theorem ag_and (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  all_goals assumption
theorem ag_left (a b : Nat) (h : a = b) (k : b = a) : (a = b ∧ a = b) ∧ (b = a ∧ b = a) := by
  constructor
  all_goals constructor
  exact h
  exact h
  exact k
  exact k
theorem ag_assigned (a : Nat) : Exists (Eq a) := by
  constructor
  all_goals rfl
theorem ag_steps (a b : Nat) (h : a = b) : a = b ∧ a = b := by
  constructor
  all_goals
    have x : a = b := h
    · exact x

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
  for n in [``at_and, ``at_none, ``at_one, ``at_three, ``at_chain, ``at_rest, ``at_ind,
      ``at_induct, ``at_brace, ``at_inner, ``at_alt, ``at_loc, ``at_names, ``ag_and,
      ``ag_left, ``ag_assigned, ``ag_steps] do
    dump n
