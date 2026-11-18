-- The instance problems mf-real.lean's statements and proofs pose, with
-- Lean's synthInstance trace, to size FE3 on Mathlib (MATHLIB_FRONT.md
-- section 5). The README counts the trace's lines per problem.
import Mathlib.Basic.Real.Basic

set_option trace.Meta.synthInstance true
#synth HAdd ℝ ℝ ℝ
#synth OfNat ℝ 0
#synth AddZeroClass ℝ
#synth AddCommMagma ℝ
#synth OfNat ℝ 2
#synth LT ℝ
#synth Field ℝ
