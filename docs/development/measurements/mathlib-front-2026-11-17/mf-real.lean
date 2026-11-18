-- Slice MF's acceptance target (docs/design/MATHLIB_FRONT.md, section 8):
-- two small true statements about real numbers whose proofs need only the
-- tactics LeanForth has today (exact, rw). Checked with pinned Lean 4.35.0
-- against pinned Mathlib (commit 56a0058); see this folder's README.
import Mathlib.Basic.Real.Basic

theorem real_add_zero (x : ℝ) : x + 0 = x := by exact add_zero x

theorem real_add_comm (x y : ℝ) : x + y = y + x := by rw [add_comm]

-- The wrong twin, which must fail (here it is commented out so that the
-- file's exit code records the two good proofs; mf-real-wrong.lean has it).

set_option pp.all true in
#print real_add_zero
set_option pp.all true in
#print real_add_comm
#print axioms real_add_zero
#print axioms real_add_comm
