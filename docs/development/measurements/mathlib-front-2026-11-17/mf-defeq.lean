-- How much unification mf-real.lean's two proofs need (MATHLIB_FRONT.md
-- section 5): the isDefEq and delta traces of each, whose lines the README
-- counts (an instance diamond: Real.instAdd against the Add that
-- add_zero's AddZeroClass and add_comm's AddCommMagma reach).
import Mathlib.Basic.Real.Basic

set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.delta true in
theorem real_add_zero (x : ℝ) : x + 0 = x := by exact add_zero x

set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.delta true in
theorem real_add_comm (x y : ℝ) : x + y = y + x := by rw [add_comm]

#print Real.instAddMonoid
#print Real.instAddCommSemigroup
#print Real.instAdd
