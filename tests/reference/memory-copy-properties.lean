/- Properties of the abstract memory model only; this does not verify Forth. -/
import «memory-copy-reference»

namespace LeanForthMemoryCopyProperties

open LeanForthProgramReference (Memory load store copyCell)
open LeanForthMemoryProgramReference (Item Op State execute step)
open LeanForthMemoryCopyReference (copyProgram copy_execution)

-- Sequential composition retains failures; a continuation cannot recover them.
theorem execute_append (first rest : List Op) (s : State) :
    execute (first ++ rest) s = (execute first s).bind (execute rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons op first ih =>
    simp only [List.cons_append, execute]
    cases step op s <;> simp [ih]

theorem copy_empty_stack (m : Memory) (destination : Nat) (rest : List Op) :
    execute (copyProgram destination ++ rest) ⟨[], m⟩ = none := by
  rfl

theorem copy_value_instead_of_address (m : Memory) (v : Int)
    (destination : Nat) (tail : List Item) (rest : List Op) :
    execute (copyProgram destination ++ rest) ⟨.value v :: tail, m⟩ = none := by
  rfl

-- Both addresses must be in range, including when a continuation follows.
theorem copy_failure_with_continuation (m : Memory) (source destination : Nat)
    (tail : List Item) (rest : List Op)
    (h : m.size ≤ source ∨ m.size ≤ destination) :
    execute (copyProgram destination ++ rest) ⟨.address source :: tail, m⟩ = none := by
  rw [execute_append, copy_execution]
  rcases h with hs | hd
  · simp [LeanForthProgramReference.copyCell_source_out_of_bounds m source destination hs]
  · simp [LeanForthProgramReference.copyCell_destination_out_of_bounds m source destination hd]

-- Exact success condition excludes any successful result for bad addresses.
theorem copy_succeeds_iff_in_bounds (m : Memory) (source destination : Nat)
    (tail : List Item) :
    (∃ result, execute (copyProgram destination) ⟨.address source :: tail, m⟩ =
      some result) ↔ source < m.size ∧ destination < m.size := by
  rw [copy_execution]
  by_cases hs : source < m.size <;> by_cases hd : destination < m.size <;>
    simp [copyCell, load, store, hs, hd]

-- A successful copy hands the complete unchanged stack frame to any suffix.
theorem copy_continuation (m : Memory) (source destination : Nat)
    (tail : List Item) (rest : List Op) (updated : Memory)
    (h : copyCell m source destination = some updated) :
    execute (copyProgram destination ++ rest) ⟨.address source :: tail, m⟩ =
      execute rest ⟨tail, updated⟩ := by
  simp [execute_append, copy_execution, h]

-- STORE requires both operands with their proper tags, regardless of suffix.
theorem store_missing_value (m : Memory) (a : Nat) (rest : List Op) :
    execute (.store :: rest) ⟨[.address a], m⟩ = none := by rfl

theorem store_address_wrong_tag (m : Memory) (v w : Int) (tail : List Item)
    (rest : List Op) :
    execute (.store :: rest) ⟨.value v :: .value w :: tail, m⟩ = none := by rfl

theorem store_value_wrong_tag (m : Memory) (a b : Nat) (tail : List Item)
    (rest : List Op) :
    execute (.store :: rest) ⟨.address a :: .address b :: tail, m⟩ = none := by rfl

end LeanForthMemoryCopyProperties
