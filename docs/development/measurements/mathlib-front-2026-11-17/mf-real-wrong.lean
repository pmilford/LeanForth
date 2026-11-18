-- The wrong twin of mf-real.lean: x + 1 = x is false, and exact must
-- refuse add_zero x for it (pinned Lean exits 1 with a type mismatch).
import Mathlib.Basic.Real.Basic

theorem real_add_one_wrong (x : ℝ) : x + 1 = x := by exact add_zero x
