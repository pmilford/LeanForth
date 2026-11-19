-- The Lean twin of tests/front/bk-init.lf (plan FE1c-bk): three Init
-- statements whose lemma's binder kinds lean4export gives otherwise than
-- Lean (Nat.mod_eq_sub_mul_div takes {x k}, the export (x k);
-- Nat.not_lt_eq (a b), the export {a b}; Nat.lt_one_iff {n}, the export
-- (n)); then each theorem's type and value as S-expressions (the printer of
-- tests/front/s1-now.lean), which tests/front/check_bk_init.py compares
-- with LeanForth's (tests/front/elab-dump.fs) and keeps in
-- tests/front/bk-init.golden.
import Lean
open Lean Meta

theorem bk_mod (x k : Nat) : x % k = x - k * (x / k) := by exact Nat.mod_eq_sub_mul_div
theorem bk_not_lt (a b : Nat) : (¬ a < b) = (b ≤ a) := by exact Nat.not_lt_eq a b
theorem bk_lt_one (n : Nat) : n < 1 ↔ n = 0 := by exact Nat.lt_one_iff

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
  for n in [``bk_mod, ``bk_not_lt, ``bk_lt_one] do
    dump n
