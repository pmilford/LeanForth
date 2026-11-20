-- The Lean twins of S2's tactic files (tests/front/01-zero-add-rw.lf,
-- 04-nested-ih.lf, 04-nested-first.lf (zero_add_inner, last in the list
-- below) and the owner's proof set, tests/front/ps-*.lf;
-- docs/design/S2_INTERFACE.md appendix G): each theorem's type and value
-- as S-expressions (the printer of tests/front/s1-now.lean), which
-- tests/front/check_tactics.py compares with LeanForth's
-- (tests/front/elab-dump.fs) and keeps in tests/front/s2-proofs.golden.
-- The proof set is appendix G's exactly (its zero cases by rfl, through
-- smart unfolding, S2 merge B). FE1's case form (tests/front/01-zero-add.lf)
-- is zero_add'; tests/front/s2-case.lf's c_* use case's tag matching (in
-- order, by suffix, by prefix, the exact pass first), its renaming of a
-- shadowed hypothesis and of _, and the other goals kept in their order
-- (c_order, c_rest). Merge B's midpoint files (tests/front/00-add-zero.lf,
-- 02-add-zero-rfl.lf) prove n + 0 = n by unfolding: add_zero' and
-- add_zero_rfl' (the second file's add_zero', renamed here so that both
-- have a line).
import Lean
open Lean Meta

theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ k ih => exact congrArg Nat.succ ih
theorem c_rev (n : Nat) : 0 + n = n := by
  induction n
  case succ k ih => exact congrArg Nat.succ ih
  case zero => rfl
theorem c_suffix (n m : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    induction m
    case zero => rw [Nat.add_succ, ih]
    case succ j ih2 => exact ih2
theorem c_prefix (n m : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    induction m
    case succ j ih2 => exact ih2
    case succ => rw [Nat.add_succ, ih]
theorem c_shadow (n m : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    induction m with
    | zero => rw [Nat.add_succ, ih]
    | succ k ih2 =>
      case succ x => exact ih2
theorem c_under (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ _ ih => exact congrArg Nat.succ ih
theorem c_order (n m : Nat) : 0 + n = n := by
  induction n
  induction m
  case succ k ih => exact congrArg Nat.succ ih
  case zero => rfl
  case zero j ih2 => exact ih2
theorem c_rest (n m : Nat) : 0 + n = n := by
  induction n
  induction m
  case zero.succ j ih2 => exact ih2
  rfl
  case succ k ih => exact congrArg Nat.succ ih

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
theorem zero_add_inner (n m : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    induction m with
    | zero => rfl
    | succ j ih => exact ih
  | succ k ih => rw [Nat.add_succ, ih]
theorem ps_zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
theorem ps_succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih, Nat.add_succ]
theorem ps_add_comm (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => rw [ps_zero_add]; rfl
  | succ k ih => rw [Nat.add_succ, ih, ps_succ_add]
theorem ps_add_assoc (n m k : Nat) : n + (m + k) = (n + m) + k := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ, Nat.add_succ, ih, Nat.add_succ]
theorem ps_mul_add (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, ps_add_assoc]
theorem ps_length_append (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => rw [List.nil_append, List.length_nil, ps_zero_add]
  | cons x t ih => rw [List.cons_append, List.length_cons, List.length_cons, ih, ps_succ_add]
theorem add_zero' (n : Nat) : n + 0 = n := Eq.refl n
theorem add_zero_rfl' (n : Nat) : n + 0 = n := by rfl
-- rfl on an equation after whnf (plan 9.4.8l, tests/front/s2-rfl-id.lf):
-- eq_refl's getType' unfolds id.
theorem rfl_id (a : Nat) : id (a = a) := by rfl
-- exact of a library theorem (tests/front/03-zero-add-exact.lf, checked on
-- all of Init; the S2 slice leaves out an instance its search needs).
theorem zero_add_ex (n : Nat) : 0 + n = n := by exact Nat.zero_add n

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
  for n in [``zero_add', ``c_rev, ``c_suffix, ``c_prefix, ``c_shadow, ``c_under, ``c_order, ``c_rest,
      ``zero_add'', ``zero_add_nested, ``ps_zero_add, ``ps_succ_add, ``ps_add_comm,
      ``ps_add_assoc, ``ps_mul_add, ``ps_length_append, ``add_zero', ``add_zero_rfl',
      ``zero_add_inner, ``rfl_id, ``zero_add_ex] do
    dump n
