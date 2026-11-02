/- Abstract bounded-memory and tagged-stack semantics only. This proves no
   correspondence with Forth execution, a compiler, or a machine runtime. -/
import «memory-copy-properties»

namespace LeanForthMemoryCopyTwice

open LeanForthProgramReference (Memory load store copyCell)
open LeanForthMemoryProgramReference (Item Op execute step)
open LeanForthMemoryCopyReference (copyProgram copy_execution)
open LeanForthMemoryCopyProperties (execute_append copy_failure_with_continuation)

-- Mathematical result of a successful copy, including all backing cells.
def copied (m : Memory) (source destination : Nat) : Memory :=
  ⟨m.size, fun i => if i = destination then m.cells source else m.cells i⟩

theorem copy_cell_result (m : Memory) (source destination : Nat)
    (hs : source < m.size) (hd : destination < m.size) :
    copyCell m source destination = some (copied m source destination) := by
  simp [copyCell, load, store, copied, hs, hd]

-- No distinctness assumption: the source may alias the destination.
theorem copied_idempotent (m : Memory) (source destination : Nat) :
    copied (copied m source destination) source destination = copied m source destination := by
  cases m with
  | mk size cells =>
    simp only [copied]
    congr 1
    funext i
    by_cases hi : i = destination <;> by_cases h : source = destination <;> simp_all

-- The first copy consumes the source address; push it again for the second.
def copyTwice (source destination : Nat) : List Op :=
  copyProgram destination ++ [.push (.address source)] ++ copyProgram destination

theorem twice_success (m : Memory) (source destination : Nat) (tail : List Item)
    (hs : source < m.size) (hd : destination < m.size) :
    execute (copyTwice source destination) ⟨.address source :: tail, m⟩ =
      some ⟨tail, copied m source destination⟩ := by
  have hs' : source < (copied m source destination).size := hs
  have hd' : destination < (copied m source destination).size := hd
  simp only [copyTwice, execute_append, copy_execution,
    copy_cell_result m source destination hs hd, Option.map_some, Option.bind_some,
    execute, step, copy_cell_result (copied m source destination) source destination hs' hd',
    copied_idempotent]

-- Equal to one execution as an entire state, not just the destination value.
theorem twice_equals_once (m : Memory) (source destination : Nat) (tail : List Item)
    (hs : source < m.size) (hd : destination < m.size) :
    execute (copyTwice source destination) ⟨.address source :: tail, m⟩ =
      execute (copyProgram destination) ⟨.address source :: tail, m⟩ := by
  rw [twice_success m source destination tail hs hd, copy_execution,
    copy_cell_result m source destination hs hd]
  rfl

theorem twice_continuation (m : Memory) (source destination : Nat) (tail : List Item)
    (rest : List Op) (hs : source < m.size) (hd : destination < m.size) :
    execute (copyTwice source destination ++ rest) ⟨.address source :: tail, m⟩ =
      execute rest ⟨tail, copied m source destination⟩ := by
  rw [execute_append, twice_success m source destination tail hs hd]
  rfl

theorem twice_out_of_bounds (m : Memory) (source destination : Nat) (tail : List Item)
    (rest : List Op) (h : m.size ≤ source ∨ m.size ≤ destination) :
    execute (copyTwice source destination ++ rest) ⟨.address source :: tail, m⟩ = none := by
  simpa [copyTwice, List.append_assoc] using
    copy_failure_with_continuation m source destination tail
      (.push (.address source) :: (copyProgram destination ++ rest)) h

theorem twice_succeeds_iff (m : Memory) (source destination : Nat) (tail : List Item) :
    (∃ result, execute (copyTwice source destination) ⟨.address source :: tail, m⟩ =
      some result) ↔ source < m.size ∧ destination < m.size := by
  constructor
  · rintro ⟨result, he⟩
    by_cases h : source < m.size ∧ destination < m.size
    · exact h
    · have bad : m.size ≤ source ∨ m.size ≤ destination := by omega
      have hf := twice_out_of_bounds m source destination tail [] bad
      simp only [List.append_nil] at hf
      rw [he] at hf
      contradiction
  · rintro ⟨hs, hd⟩
    exact ⟨_, twice_success m source destination tail hs hd⟩

theorem twice_empty_stack (m : Memory) (source destination : Nat) (rest : List Op) :
    execute (copyTwice source destination ++ rest) ⟨[], m⟩ = none := by rfl

theorem twice_wrong_tag (m : Memory) (source destination : Nat) (v : Int)
    (tail : List Item) (rest : List Op) :
    execute (copyTwice source destination ++ rest) ⟨.value v :: tail, m⟩ = none := by rfl

end LeanForthMemoryCopyTwice
