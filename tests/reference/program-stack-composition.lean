/- Composition over the existing abstract stack model. Integers are unbounded;
   this does not prove correspondence with Forth source or any host runtime. -/
import «stack-clamp»

namespace LeanForthStackComposition

open LeanForthStackModel

-- Replace every terminal node with a continuation, including both branches.
-- This is model sequencing: it does not independently model Forth EXIT.
def seq : Code → Code → Code
  | .done, second => second
  | .op op next, second => .op op (seq next second)
  | .branch yes no, second => .branch (seq yes second) (seq no second)

theorem execute_seq (first second : Code) (s : State) :
    execute (seq first second) s = (execute first s).bind (execute second) := by
  induction first generalizing s with
  | done => rfl
  | op op next ih =>
    simp only [seq, execute]
    cases h : step op s <;> simp [ih]
  | branch yes no ihYes ihNo =>
    cases s with
    | mk data returns =>
      cases data with
      | nil => rfl
      | cons flag tail =>
        simp only [seq, execute]
        split <;> simp_all

-- Successful components can be composed while independently preserving an
-- arbitrary suffix on each stack. Success premises prevent a continuation
-- from consuming a cell from either frame.
theorem compose_frame (first second : Code) (s middle result : State)
    (ds rs : List Int) (hfirst : execute first s = some middle)
    (hsecond : execute second middle = some result) :
    execute (seq first second) ⟨s.data ++ ds, s.returns ++ rs⟩ =
      some ⟨result.data ++ ds, result.returns ++ rs⟩ := by
  rw [execute_seq, execute_frame first s middle ds rs hfirst]
  simpa using execute_frame second middle result ds rs hsecond

-- The ordered-bounds branch mirrors lf-clamp followed by DROP, which removes
-- its true flag. The frame theorem lifts the small-stack derivation to any
-- surrounding data and return stacks.
theorem clamp_then_drop (lower upper value : Int) (ds rs : List Int)
    (ordered : lower ≤ upper) :
    execute (seq clampCode (.op .drop .done))
      ⟨[upper, lower, value] ++ ds, rs⟩ =
      some ⟨clampSpec lower upper value :: ds, rs⟩ := by
  have first : execute clampCode ⟨[upper, lower, value], []⟩ =
      some ⟨[-1, clampSpec lower upper value], []⟩ := by
    simpa [show ¬ lower > upper by omega] using
      clampCode_spec lower upper value [] []
  have second : execute (.op .drop .done)
      ⟨[-1, clampSpec lower upper value], []⟩ =
      some ⟨[clampSpec lower upper value], []⟩ := by
    rfl
  simpa using compose_frame clampCode (.op .drop .done)
    ⟨[upper, lower, value], []⟩ ⟨[-1, clampSpec lower upper value], []⟩
    ⟨[clampSpec lower upper value], []⟩ ds rs first second

-- The success premise is essential: an appended frame can supply an operand.
example : execute (.op .drop .done) ⟨[], []⟩ = none := by decide
example : execute (.op .drop .done) ⟨[7], []⟩ = some ⟨[], []⟩ := by decide

end LeanForthStackComposition
