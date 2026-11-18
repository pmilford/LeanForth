-- What a Lean user waits for: all of Mathlib imported, one small proof.
-- The time to compare LeanForth's load of the Mathlib snapshot with.
import Mathlib

theorem real_add_zero (x : ℝ) : x + 0 = x := by exact add_zero x
