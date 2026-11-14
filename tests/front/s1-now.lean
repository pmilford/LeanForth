-- The Lean twin of tests/front/s1-now.lf: the same #check lines and
-- theorems; then each theorem's type and value as S-expressions (the
-- printer of tests/front/defeq-cases.lean), which tests/front/check_elab.py
-- compares with LeanForth's (tests/front/elab-dump.fs) and keeps in
-- tests/front/s1-now.golden.
import Lean
open Lean Meta

#check Nat.zero = Nat.zero
#check Eq.refl Nat.zero
theorem zero_eq : Nat.zero = Nat.zero := by rfl
theorem zero_eq_term : Nat.zero = Nat.zero := Eq.refl Nat.zero
theorem self_eq (n : Nat) : n = n := Eq.refl n
theorem succ_eq (n : Nat) : Nat.succ n = Nat.succ n := by rfl
theorem succ_eq_exact (n : Nat) : Nat.succ n = Nat.succ n := by exact Eq.refl (Nat.succ n)

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
  for n in [``zero_eq, ``zero_eq_term, ``self_eq, ``succ_eq, ``succ_eq_exact] do
    dump n
