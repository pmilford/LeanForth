-- The Lean twin of tests/front/bk-init-wrong.lf (plan FE1c-bk): refused
-- with a type mismatch.
theorem bk_not_lt_wrong (a b : Nat) : (¬ a < b) = (a ≤ b) := by exact Nat.not_lt_eq a b
