-- The Lean twins of tests/front/tactics/batch-d/*.lf (plan row TB2, tactic batch 3a): each
-- theorem's type and value as S-expressions (batch-b.lean's printer), which tactic_check.py
-- compares with LeanForth's (tests/front/elab-dump.fs's decide-dump) and keeps in
-- batch-d.golden.
import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false
set_option linter.unnecessaryRwa false
set_option linter.deprecated false

-- rw and rewrite at: (rw-at.lf).
theorem at_hyp (a b c : Nat) (h : a = b) (h2 : a ≤ c) : b ≤ c := by
  rw [h] at h2
  exact h2
theorem at_closes (a b : Nat) (h : a = b) (h2 : a + 0 = b) : b = b := by
  rw [h] at h2
theorem at_two (a b c : Nat) (h : a = b) (h2 : a ≤ c) (h3 : c ≤ a) : b ≤ c := by
  rewrite [h] at h2 h3
  exact h2
theorem at_goal (a b c : Nat) (h : a = b) (h2 : a ≤ c) : a ≤ c := by
  rw [h] at h2 ⊢
  exact h2
theorem at_rules (a b c d : Nat) (h : a = b) (k : c = b) (h2 : a ≤ d) : c ≤ d := by
  rw [h, ← k] at h2
  exact h2
theorem at_turnstile (a b c : Nat) (h : a = b) (k : c ≤ a) : c ≤ a := by
  rw [h] at k ⊢
  exact k
-- rwa (rwa-at.lf).
theorem rwa_at (a b c : Nat) (h : a = b) (h2 : a ≤ c) : b ≤ c := by
  rwa [h] at h2
theorem rwa_none (a b : Nat) (h : a ≤ b) : a ≤ b := by
  rwa [] at h
theorem rwa_legacy (a b c : Nat) (h : a = b) (h2 : a ≤ c) : a ≤ c := by
  rwa [h] at h2 ⊢
theorem rwa_le (a b c : Nat) (h : a = b) (h2 : b ≤ c) : a ≤ c := by
  rwa [h]
theorem rwa_not (a b c : Nat) (h : a = b) (h2 : ¬b ≤ c) : ¬a ≤ c := by
  rwa [h]
-- change, symm and rfl (change-at.lf).
theorem ch_at (a b : Nat) (h : a + 0 = b) : a = b := by
  change a = b at h
  exact h
theorem ch_goal (a b : Nat) (h : a + 0 = b) : a + 0 = b := by
  change a = b at h ⊢
  exact h
theorem sy_at (a b : Nat) (h : a = b) (h2 : b = a) : a = b := by
  symm at h2
  exact h2
theorem sy_at_ne (a b : Nat) (h : a ≠ b) : a ≠ b := by
  symm at h ⊢
  assumption
theorem rf_iff (a b : Nat) : a ≤ b ↔ a ≤ b := by
  rfl
theorem rf_rw_iff (a b : Nat) (h : a = b) : a ≤ b ↔ b ≤ b := by
  rw [h]

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
  for n in [``at_hyp, ``at_closes, ``at_two, ``at_goal, ``at_rules, ``at_turnstile, ``rwa_at,
      ``rwa_none, ``rwa_legacy, ``rwa_le, ``rwa_not, ``ch_at, ``ch_goal, ``sy_at, ``sy_at_ne,
      ``rf_iff, ``rf_rw_iff] do
    dump n
