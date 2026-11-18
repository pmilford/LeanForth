-- The Lean twins of S2's tactic files (tests/front/01-zero-add-rw.lf,
-- 04-nested-ih.lf and the owner's proof set, tests/front/ps-*.lf;
-- docs/design/S2_INTERFACE.md appendix G): each theorem's type and value
-- as S-expressions (the printer of tests/front/s1-now.lean), which
-- tests/front/check_tactics.py compares with LeanForth's
-- (tests/front/elab-dump.fs) and keeps in tests/front/s2-proofs.golden.
-- Where a step of appendix G needs smart unfolding (S2 merge B), the
-- form here rewrites with Init lemmas instead (Nat.add_zero, Nat.mul_zero
-- for rfl on n + 0 = n and n * 0 = 0), as the LeanForth files do. Merge
-- B's midpoint files (tests/front/00-add-zero.lf, 02-add-zero-rfl.lf)
-- prove n + 0 = n by unfolding: add_zero' and add_zero_rfl' (the second
-- file's add_zero', renamed here so that both have a line).
import Lean
open Lean Meta

theorem zero_add'' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
theorem zero_add_nested (n m : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    induction m with
    | zero => rw [Nat.add_succ, ih]
    | succ j ih => exact ih
theorem ps_zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
theorem ps_succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) := by
  induction m with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ k ih => rw [Nat.add_succ, ih, Nat.add_succ]
theorem ps_add_comm (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => rw [ps_zero_add, Nat.add_zero]
  | succ k ih => rw [Nat.add_succ, ih, ps_succ_add]
theorem ps_add_assoc (n m k : Nat) : n + (m + k) = (n + m) + k := by
  induction k with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ j ih => rw [Nat.add_succ, Nat.add_succ, ih, Nat.add_succ]
theorem ps_mul_add (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction k with
  | zero => rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero]
  | succ j ih => rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, ps_add_assoc]
theorem ps_length_append (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => rw [List.nil_append, List.length_nil, ps_zero_add]
  | cons x t ih => rw [List.cons_append, List.length_cons, List.length_cons, ih, ps_succ_add]
theorem add_zero' (n : Nat) : n + 0 = n := Eq.refl n
theorem add_zero_rfl' (n : Nat) : n + 0 = n := by rfl

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
  for n in [``zero_add'', ``zero_add_nested, ``ps_zero_add, ``ps_succ_add, ``ps_add_comm,
      ``ps_add_assoc, ``ps_mul_add, ``ps_length_append, ``add_zero', ``add_zero_rfl'] do
    dump n
