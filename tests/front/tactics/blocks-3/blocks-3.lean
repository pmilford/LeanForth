-- Pinned Lean twins of tests/front/tactics/blocks-3/*.lf (plan row TB2, blocks slice 3: try,
-- first, repeat, any_goals): tactic_check.py --lean writes blocks-3.golden from this file's
-- terms, which LeanForth's must equal node for node. u_any_gap is the known gap: Lean
-- accepts, LeanForth answers 490 (u-any-gap.lf).
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

theorem try_skip (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try exact k
  exact h
theorem try_runs (a b : Nat) (h : a = b) : a = b := by
  try exact h
theorem try_partial (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  try (exact h; exact h)
  exact h
  exact k
theorem try_then (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor <;> try exact h
  exact k
theorem try_brace (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try (· exact k)
  exact h
theorem try_deep (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try first | (· exact k) | (focus exact h)
theorem first_second (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  first
  | exact k
  | exact h
theorem first_one (a b : Nat) (h : a = b) : a = b := by
  first | exact h
theorem first_rollback (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  first
  | (exact h; exact h)
  | (exact h; exact k)
theorem first_then (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor <;> first | exact k | exact h
theorem first_chain (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  first
  | (constructor <;> exact h)
  | (constructor; exact h; exact k)
theorem repeat_ctor (a b : Nat) (h : a = b) (k : b = a) : (a = b ∧ a = b) ∧ b = a := by
  repeat constructor
  exact h
  exact h
  exact k
theorem repeat_none (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  repeat exact k
  exact h
theorem repeat_rollback (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  repeat (constructor; exact h; exact h)
  constructor
  exact h
  exact k
theorem any_some (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  any_goals exact h
  exact k
theorem any_all_goals (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a ∧ a = b := by
  and_intros
  any_goals all_goals exact h
  exact k
theorem any_chain (a b : Nat) (h : a = b) (k : b = a) :
    (a = b ∧ a = b) ∧ (a = b ∧ b = a) := by
  constructor
  any_goals (constructor <;> exact h)
  constructor
  exact h
  exact k
theorem rec_q8 (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try (have j : b = a := by exact ⟨h⟩)
  exact h
theorem rec_q8_inner (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try (have j : b = a := by (have i : a = b := by exact ⟨h⟩); exact k)
  exact h
theorem names_try (a b : Nat) (h : a = b) : a = b := by
  try have x : a = b := h
  exact x
theorem names_first (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  first
  | (have y : b = a := k; exact k)
  | (have z : a = b := h)
  exact z
theorem names_mvar (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ a = b := by
  first
  | (refine And.intro ?x ?y; exact k)
  | (refine And.intro ?x ?y; exact h; exact h)
theorem rec_try_have (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try (have j : b = a := by have x : a = b := h)
  exact h
theorem rec_try_brace (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try (have j : b = a := by show b = a; (· exact h))
  exact h
theorem rec_try_brace_fail (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  try (have j : b = a := by show b = a; (· exact h)); exact k
  exact h
theorem rec_brace_try (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  · try ((have j : b = a := by show b = a; (· exact h)); exact k)
    exact h
theorem rec_then_try (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor <;> try ((have j : b = a := by show b = a; (· exact h)); exact j; exact h)
  exact h
  exact k
theorem u_any_gap (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  constructor
  any_goals first | exact h | ((· exact h); exact k)
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
  for n in [``try_skip, ``try_runs, ``try_partial, ``try_then, ``try_brace, ``try_deep,
      ``first_second, ``first_one, ``first_rollback, ``first_then, ``first_chain,
      ``repeat_ctor, ``repeat_none, ``repeat_rollback, ``any_some, ``any_all_goals,
      ``any_chain, ``rec_q8, ``rec_q8_inner, ``rec_try_have, ``names_try, ``names_first,
      ``names_mvar, ``rec_try_brace, ``rec_try_brace_fail, ``rec_brace_try, ``rec_then_try,
      ``u_any_gap] do
    dump n
