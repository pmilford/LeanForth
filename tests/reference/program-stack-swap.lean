/- Abstract stack-model reasoning only: integer cells are unbounded and this
   does not establish correspondence with Forth source or a host runtime. -/
import «program-stack-composition»

namespace LeanForthStackSwap

open LeanForthStackModel LeanForthStackComposition

-- Top-first data stack. Two copies let us save the second and first cells
-- on the return stack, discard the remaining copy, then restore in reverse.
def swapCode : Code :=
  .op .twoDup <| .op .drop <| .op .toReturn <| .op .toReturn <|
  .op .drop <| .op .fromReturn <| .op .fromReturn .done

-- The original return stack and the data-stack suffix are preserved.
theorem swap_spec (a b : Int) (ds rs : List Int) :
    execute swapCode ⟨a :: b :: ds, rs⟩ = some ⟨b :: a :: ds, rs⟩ := by
  rfl

-- Sequencing two swaps restores both stacks, including arbitrary frames.
theorem swap_twice (a b : Int) (ds rs : List Int) :
    execute (seq swapCode swapCode) ⟨a :: b :: ds, rs⟩ =
      some ⟨a :: b :: ds, rs⟩ := by
  rw [execute_seq, swap_spec, Option.bind_some, swap_spec]

-- Too few data cells fail even if the return stack contains available cells;
-- sequencing propagates that failure instead of executing its continuation.
theorem swap_underflow (data rs : List Int) (short : data.length < 2)
    (continuation : Code) :
    execute (seq swapCode continuation) ⟨data, rs⟩ = none := by
  rw [execute_seq]
  rcases data with _ | ⟨a, _ | ⟨b, tail⟩⟩
  · rfl
  · rfl
  · simp only [List.length_cons] at short
    omega

-- A mistaken claim that swap leaves distinct cells in place is refuted.
example : execute swapCode ⟨[1, 2], [9]⟩ ≠ some ⟨[1, 2], [9]⟩ := by decide

end LeanForthStackSwap
