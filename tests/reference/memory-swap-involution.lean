/- Abstract bounded-memory and stack semantics only. This is not a claim about
   Forth execution, its runtime, compiler, or machine-cell arithmetic. -/
import «memory-swap-reference»

namespace LeanForthMemorySwapInvolution

open LeanForthProgramReference (Memory)
open LeanForthMemoryProgramReference (Item Op State execute step)
open LeanForthMemorySwapReference (swapProgram swapped swap_success swap_out_of_bounds)

-- Equality includes the size and every cell, including cells outside the bound.
-- The equal-address case is included: swapping a cell with itself is harmless.
theorem swapped_involution (m : Memory) (a b : Nat) :
    swapped (swapped m a b) a b = m := by
  cases m with
  | mk size cells =>
    simp only [swapped]
    congr 1
    funext i
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      by_cases hab : a = b <;> simp_all

-- Composition propagates failure and passes the entire resulting state on.
theorem execute_append (first rest : List Op) (s : State) :
    execute (first ++ rest) s = (execute first s).bind (execute rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons op first ih =>
    simp only [List.cons_append, execute]
    cases step op s <;> simp [ih]

-- Both swaps succeed exactly when both addresses are in bounds. The arbitrary
-- stack is restored, as is the complete memory, whether or not a = b.
theorem double_swap (m : Memory) (a b : Nat) (tail : List Item)
    (ha : a < m.size) (hb : b < m.size) :
    execute (swapProgram a b ++ swapProgram a b) ⟨tail, m⟩ = some ⟨tail, m⟩ := by
  rw [execute_append, swap_success m a b tail ha hb]
  simp only [Option.bind_some]
  rw [swap_success (swapped m a b) a b tail ha hb, swapped_involution]

-- A suffix sees precisely the original state after success; on a bad address
-- the first swap fails and the suffix cannot observe a partial state.
theorem double_swap_continuation (m : Memory) (a b : Nat) (tail : List Item)
    (rest : List Op) (ha : a < m.size) (hb : b < m.size) :
    execute ((swapProgram a b ++ swapProgram a b) ++ rest) ⟨tail, m⟩ =
      execute rest ⟨tail, m⟩ := by
  rw [execute_append, double_swap m a b tail ha hb]
  rfl

theorem double_swap_failure (m : Memory) (a b : Nat) (tail : List Item)
    (rest : List Op) (h : m.size ≤ a ∨ m.size ≤ b) :
    execute ((swapProgram a b ++ swapProgram a b) ++ rest) ⟨tail, m⟩ = none := by
  simpa [List.append_assoc] using
    swap_out_of_bounds m a b tail (swapProgram a b ++ rest) h

theorem double_swap_succeeds_iff (m : Memory) (a b : Nat) (tail : List Item) :
    (∃ result, execute (swapProgram a b ++ swapProgram a b) ⟨tail, m⟩ = some result) ↔
      a < m.size ∧ b < m.size := by
  constructor
  · intro ⟨result, hs⟩
    by_cases ha : a < m.size
    · by_cases hb : b < m.size
      · exact ⟨ha, hb⟩
      · have hf := double_swap_failure m a b tail [] (Or.inr (Nat.not_lt.mp hb))
        simp only [List.append_nil] at hf
        rw [hf] at hs
        contradiction
    · have hf := double_swap_failure m a b tail [] (Or.inl (Nat.not_lt.mp ha))
      simp only [List.append_nil] at hf
      rw [hf] at hs
      contradiction
  · rintro ⟨ha, hb⟩
    exact ⟨⟨tail, m⟩, double_swap m a b tail ha hb⟩

end LeanForthMemorySwapInvolution
