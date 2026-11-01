/- Independent mathematical reference, not a runtime correctness proof. -/
import «memory-program-reference»

namespace LeanForthMemoryCopyReference

open LeanForthProgramReference (Memory load copyCell copyCell_success
  copyCell_self copyCell_source_out_of_bounds copyCell_destination_out_of_bounds)
open LeanForthMemoryProgramReference (Item Op State execute step)

-- The source address is supplied on the stack. After loading it, push the
-- destination above the value for store: ( source -- ), preserving the tail.
def copyProgram (destination : Nat) : List Op :=
  [.load, .push (.address destination), .store]

-- Relate the entire composed program to the separately defined memory copy,
-- including both failure cases and the arbitrary stack frame.
theorem copy_execution (m : Memory) (source destination : Nat) (tail : List Item) :
    execute (copyProgram destination) ⟨.address source :: tail, m⟩ =
      (copyCell m source destination).map (fun updated => ⟨tail, updated⟩) := by
  simp [copyProgram, execute, step, copyCell]
  cases load m source <;> rfl

theorem copy_success (m : Memory) (source destination : Nat) (tail : List Item)
    (hs : source < m.size) (hd : destination < m.size) :
    ∃ updated, execute (copyProgram destination) ⟨.address source :: tail, m⟩ =
        some ⟨tail, updated⟩ ∧
      updated.size = m.size ∧ load updated destination = load m source ∧
      ∀ other, other ≠ destination → updated.cells other = m.cells other := by
  obtain ⟨updated, hc, hz, hr, hf⟩ := copyCell_success m source destination hs hd
  exact ⟨updated, by simp [copy_execution, hc], hz, hr, hf⟩

-- Aliasing is allowed: even the destination cell remains unchanged.
theorem copy_same_address (m : Memory) (address : Nat) (tail : List Item)
    (h : address < m.size) :
    ∃ updated, execute (copyProgram address) ⟨.address address :: tail, m⟩ =
        some ⟨tail, updated⟩ ∧ updated.size = m.size ∧
      ∀ i, updated.cells i = m.cells i := by
  obtain ⟨updated, hc, hz, hf⟩ := copyCell_self m address h
  exact ⟨updated, by simp [copy_execution, hc], hz, hf⟩

theorem copy_source_failure (m : Memory) (source destination : Nat) (tail : List Item)
    (h : m.size ≤ source) :
    execute (copyProgram destination) ⟨.address source :: tail, m⟩ = none := by
  simp [copy_execution, copyCell_source_out_of_bounds m source destination h]

theorem copy_destination_failure (m : Memory) (source destination : Nat) (tail : List Item)
    (h : m.size ≤ destination) :
    execute (copyProgram destination) ⟨.address source :: tail, m⟩ = none := by
  simp [copy_execution, copyCell_destination_out_of_bounds m source destination h]

end LeanForthMemoryCopyReference
