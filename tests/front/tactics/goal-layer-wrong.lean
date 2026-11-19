-- Pinned Lean's errors for the wrong twins of tests/front/tactics/*/w-*.lf
-- (slice a2-iii): tests/front/tactics/tactic_check.py --lean checks that
-- each message the LeanForth file must print is Lean's.
theorem w_ap_le_succ (n : Nat) : n + 1 ≤ n := by apply Nat.le_succ
theorem w_ap_hyp (a b : Nat) (h : a ≤ b) : b ≤ a := by apply h
theorem w_as (a b : Nat) (h : a ≤ b) : b ≤ a := by assumption
theorem w_co_false : False := by constructor
theorem w_co_not (a b : Nat) : ¬ a = b := by constructor
