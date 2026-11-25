-- The Lean twins of tests/front/tactics/batch-h/*.lf (plan row TB2, piece E, slice E2a: subst,
-- rfl in patterns, rintro, subst_vars): each theorem's type and value as S-expressions
-- (batch-b.lean's printer), which tactic_check.py compares with LeanForth's
-- (tests/front/elab-dump.fs's decide-dump) and keeps in batch-h.golden.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

-- subst (subst.lf).
theorem sb_right (a b : Nat) (h : a = b) : b = a := by
  subst h
  rfl
theorem sb_left (a b : Nat) (h : a = Nat.succ b) : a = Nat.succ b := by
  subst h
  rfl
theorem sb_dep_before (a b : Nat) (k : b = a) (h : a = b) : a = b := by
  subst h
  exact k
theorem sb_dep_after (a b : Nat) (h : a = b) (k : b = a) : a = b := by
  subst h
  exact k
theorem sb_rec (a b : Nat) (h : a = b) : h = h := by
  subst h
  rfl
theorem sb_rec_left (a b : Nat) (h : a = Nat.succ b) : h = h := by
  subst h
  rfl
theorem sb_heq (a b : Nat) (h : HEq a b) : b = a := by
  subst h
  rfl
theorem sb_reduced (n m : Nat) (h : n = id m) : m = n := by
  subst h
  rfl
theorem sb_var_right (a b : Nat) (h : a = b) : b = a := by
  subst b
  rfl
theorem sb_var_left (a b : Nat) (h : a = b) : b = a := by
  subst a
  rfl
theorem sb_var_free (x y : Nat) (h1 : x = x) (h2 : y = x) : y = y := by
  subst x
  exact h1
theorem sb_many (a b c : Nat) (h1 : a = b) (h2 : b = c) : c = a := by
  subst h1 h2
  rfl
theorem sb_skip (a b : Nat) (h : a = b) (p : True) : True := by
  subst h
  exact p
theorem sb_hidden (a b c : Nat) (h : a = b ∧ b = a) : b = a := by
  obtain ⟨hab, _⟩ := h
  subst hab
  assumption

-- rfl in a pattern (rfl.lf).
theorem rf_exists (a : Nat) (h : Exists (Eq a)) (k : a = a) : a = a := by
  obtain ⟨x, rfl⟩ := h
  exact k
theorem rf_right (a b : Nat) (h : a = b ∧ True) : b = a := by
  obtain ⟨rfl, -⟩ := h
  rfl
theorem rf_left (a b : Nat) (h : a = Nat.succ b ∧ True) : a = Nat.succ b := by
  obtain ⟨rfl, -⟩ := h
  rfl
theorem rf_alts (a b : Nat) (h : a = b ∨ b = a) : b = a := by
  rcases h with rfl | rfl
  rfl
  rfl
theorem rf_cleared (h : Exists (Eq Nat.zero)) : True := by
  obtain ⟨-, rfl⟩ := h
  trivial

-- rintro (rintro.lf).
theorem ri_name (a b : Nat) (h : a = b) : a = b := by
  revert h
  rintro k
  exact k
theorem ri_alts (a b : Nat) (h : a = b ∨ b = a) (k : a = a) : b = a ∨ a = b := by
  revert h k
  rintro (h1 | h2) k
  exact Or.inr h1
  exact Or.inl h2
theorem ri_tuple (a b : Nat) (h : a = b ∧ b = a) : b = a := by
  revert h
  rintro ⟨hab, hba⟩
  exact hba
theorem ri_rfl (a b : Nat) (h : a = b) : b = a := by
  revert h
  rintro rfl
  rfl
theorem ri_clear_rfl (x : Nat) (h : Nat.zero = x) : x = x := by
  revert x
  rintro - rfl
  rfl
theorem ri_nat (n : Nat) (h : n = n) : n = n := by
  revert n
  rintro (_ | m) h
  rfl
  rfl

-- subst_vars (subst-vars.lf).
theorem sv_two (a b c : Nat) (h1 : a = b) (h2 : c = b) : c = a := by
  subst_vars
  rfl
theorem sv_var_first (a b : Nat) (k : b = b) (h : a = b) : a = b := by
  subst_vars
  rfl

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
  for n in [``sb_right, ``sb_left, ``sb_dep_before, ``sb_dep_after, ``sb_rec, ``sb_rec_left,
      ``sb_heq, ``sb_reduced, ``sb_var_right, ``sb_var_left, ``sb_var_free, ``sb_many, ``sb_skip,
      ``sb_hidden, ``rf_exists, ``rf_right, ``rf_left, ``rf_alts, ``rf_cleared, ``ri_name,
      ``ri_alts, ``ri_tuple, ``ri_rfl, ``ri_clear_rfl, ``ri_nat, ``sv_two, ``sv_var_first] do
    dump n
