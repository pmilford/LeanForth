-- Pinned Lean twins of tests/front/tactics/batch-small-1/*.lf (plan row TB2, small tactics 1:
-- funext, infer_instance, rename, generalize, skip, done): tactic_check.py --lean writes
-- batch-small-1.golden from this file's terms, which LeanForth's must equal node for node.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

theorem fx_one : Nat.succ = Nat.succ := by
  funext x
  rfl
theorem fx_plain : Nat.succ = Nat.succ := by
  funext
  rfl
theorem fx_none (a b : Nat) (h : a = b) : a = b := by
  funext
  exact h
theorem fx_blank : Nat.succ = Nat.succ := by
  funext _
  rfl
theorem ii_sub (a b : Nat) : Subsingleton (Decidable (a = b)) := by
  infer_instance
theorem ii_have (a b : Nat) (h : a = b) : a = b := by
  have d : Decidable (a = b) := by infer_instance
  exact h
theorem ii_and (a b : Nat) (h : a = b) : a = b := by
  have d : Decidable (a = b ∧ a ≤ b) := by infer_instance
  exact h
theorem rn_one (a b : Nat) (h : a = b) : a = b := by
  rename a = b => k
  exact k
theorem rn_newest (a b : Nat) (h : a = b) (h2 : a = b) : a = b := by
  rename a = b => k
  exact h
theorem rn_hole (a b : Nat) (k : b = a) (h : a = b) : b = a := by
  rename _ = a => j
  exact j
theorem rn_defeq (a b : Nat) (h : a + 0 = b) : a = b := by
  rename a = b => k
  exact k
theorem gz_one (a b : Nat) : a + b = a + b := by
  generalize a + b = x
  rfl
theorem gz_eq (a b : Nat) : a + b = a + b := by
  generalize h : a + b = x
  rfl
theorem gz_eq_used (a b c : Nat) (k : a + b = c) : a + b = c := by
  generalize h : a + b = x
  rw [← h]
  exact k
theorem gz_at (a b c : Nat) (h : a + b = c) : a + b = c := by
  generalize a + b = x at h
  exact h
theorem gz_at_eq (a b c : Nat) (h : a + b = c) : a + b = c := by
  generalize k : a + b = x at h
  exact h
theorem gz_at_skip (a b c : Nat) (h : c = c) : a + b = a + b := by
  generalize a + b = x at h
  rfl
theorem gz_absent (a b : Nat) (h : a = b) : a = b := by
  generalize a + b = x
  exact h
theorem sk_one (a b : Nat) (h : a = b) : a = b := by
  skip
  exact h
  done
theorem sk_after (a b : Nat) (h : a = b) : a = b := by
  exact h
  skip
theorem dn_try (a b : Nat) (h : a = b) : a = b := by
  try done
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
  for n in [``fx_one, ``fx_plain, ``fx_none, ``fx_blank, ``ii_sub, ``ii_have, ``ii_and,
            ``rn_one, ``rn_newest, ``rn_hole, ``rn_defeq, ``gz_one, ``gz_eq, ``gz_eq_used,
            ``gz_at, ``gz_at_eq, ``gz_at_skip, ``gz_absent, ``sk_one, ``sk_after, ``dn_try] do
    dump n
