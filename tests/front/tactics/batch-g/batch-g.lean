-- The Lean twins of tests/front/tactics/batch-g/*.lf (plan row TB2, piece E, slice E1: obtain
-- and rcases): each theorem's type and value as S-expressions (batch-b.lean's printer), which
-- tactic_check.py compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps
-- in batch-g.golden.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

-- obtain (obtain.lf).
theorem ob_and (a b : Nat) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨hab, hba⟩ := h
  exact hba
theorem ob_exists (a : Nat) (h : Exists (Eq a)) : Exists (Eq a) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, hw⟩
theorem ob_nested (a b c : Nat) (h : a = b ∧ b = c ∧ c = a) : c = a := by
  obtain ⟨h1, h2, h3⟩ := h
  exact h3
theorem ob_fewer (a b c : Nat) (h : a = b ∧ b = c) : a = b := by
  obtain ⟨h1⟩ := h
  exact h1
theorem ob_clear (a b : Nat) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨-, h2⟩ := h
  exact h2
theorem ob_term (a b : Nat) (h : a = b) (k : b = a) : b = a := by
  obtain ⟨p, q⟩ := And.intro h k
  exact q
theorem ob_term_name (a b : Nat) (h : a = b) (k : b = a) : a = b ∧ b = a := by
  obtain x := And.intro h k
  exact x
theorem ob_name (a b : Nat) (h : a = b) : a = b := by
  obtain x := h
  exact h

-- rcases (rcases.lf).
theorem rc_or (a b : Nat) (h : a = b ∨ b = a) : b = a ∨ a = b := by
  rcases h with h1 | h2
  exact Or.inr h1
  exact Or.inl h2
theorem rc_three (a b c : Nat) (h : a = b ∨ b = c ∨ c = a) : c = a ∨ b = c ∨ a = b := by
  rcases h with h1 | h2 | h3
  exact Or.inr (Or.inr h1)
  exact Or.inr (Or.inl h2)
  exact Or.inl h3
theorem rc_or_and (a b c : Nat) (h : (a = b ∨ b = a) ∧ c = c) : b = a ∨ a = b := by
  rcases h with ⟨h1 | h2, h3⟩
  exact Or.inr h1
  exact Or.inl h2
theorem rc_nat (n : Nat) : n = n := by
  rcases n with _ | n
  rfl
  rfl
theorem rc_comment (a b : Nat) (h : a = b ∧ b = a) : b = a := by
  rcases h with ⟨h1, h2⟩
  exact h2

-- Nested alternatives (nest.lf).
theorem ns_left (a b c : Nat) (h : (a = b ∨ b = c) ∨ c = a) : a = b ∨ b = c ∨ c = a := by
  rcases h with (x | y) | z
  exact Or.inl x
  exact Or.inr (Or.inl y)
  exact Or.inr (Or.inr z)
theorem ns_flat (a b c : Nat) (h : (a = b ∨ b = c) ∨ (c = a ∨ a = c)) :
    (a = b ∨ b = c) ∨ (c = a ∨ a = c) := by
  rcases h with x | y | z
  exact Or.inl x
  exact Or.inr (Or.inl y)
  exact Or.inr (Or.inr z)
theorem ns_right (a b c : Nat) (h : a = b ∨ b = c ∨ c = a) : c = a ∨ b = c ∨ a = b := by
  rcases h with x | (y | z)
  exact Or.inr (Or.inr x)
  exact Or.inr (Or.inl y)
  exact Or.inl z

-- Goal order and tags (order.lf).
theorem od_depth (a b c d : Nat) (h : (a = b ∨ b = a) ∧ (c = d ∨ d = c)) : b = a ∨ a = b := by
  rcases h with ⟨h1 | h2, h3 | h4⟩
  exact Or.inr h1
  exact Or.inr h1
  exact Or.inl h2
  exact Or.inl h2
theorem od_tags (a b c d : Nat) (h : (a = b ∨ b = a) ∧ (c = d ∨ d = c)) : b = a ∨ a = b := by
  rcases h with ⟨h1 | h2, h3 | h4⟩
  case inr.inr => exact Or.inl h2
  case inl.inl => exact Or.inr h1
  case inr.inl => exact Or.inl h2
  case inl.inr => exact Or.inr h1
theorem od_one (a b : Nat) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨hab, hba⟩ := h
  case _ => exact hba

-- Hidden names (hidden.lf).
theorem hd_kept (a b c : Nat) (right : c = c) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨hab, _⟩ := h
  rcases b with _ | d
  assumption
  assumption

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
  for n in [``ob_and, ``ob_exists, ``ob_nested, ``ob_fewer, ``ob_clear, ``ob_term,
      ``ob_term_name, ``ob_name, ``rc_or, ``rc_three, ``rc_or_and, ``rc_nat, ``rc_comment,
      ``ns_left, ``ns_flat, ``ns_right, ``od_depth, ``od_tags, ``od_one, ``hd_kept] do
    dump n
