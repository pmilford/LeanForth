/- Abstract bounded-memory and stack model only; no Forth runtime claim.
   Both reads precede both writes, including when the addresses alias. -/
import «memory-program-reference»

namespace LeanForthMemorySwapReference

open LeanForthProgramReference (Memory load store)
open LeanForthMemoryProgramReference (Item Op State execute step)

-- The two addresses are parameters; the arbitrary initial stack is preserved.
def swapProgram (a b : Nat) : List Op :=
  [.push (.address a), .load, .push (.address b), .load,
   .push (.address a), .store, .push (.address b), .store]

def swapped (m : Memory) (a b : Nat) : Memory :=
  ⟨m.size, fun i => if i = b then m.cells a
                     else if i = a then m.cells b else m.cells i⟩

theorem swap_success (m : Memory) (a b : Nat) (tail : List Item)
    (ha : a < m.size) (hb : b < m.size) :
    execute (swapProgram a b) ⟨tail, m⟩ = some ⟨tail, swapped m a b⟩ := by
  simp [swapProgram, execute, step, load, store, swapped, ha, hb]

theorem swap_reads (m : Memory) (a b : Nat)
    (ha : a < m.size) (hb : b < m.size) :
    load (swapped m a b) a = load m b ∧
    load (swapped m a b) b = load m a := by
  by_cases h : a = b
  · subst b; simp [swapped, load, ha]
  · simp [swapped, load, ha, hb, h]

theorem swap_frame (m : Memory) (a b i : Nat)
    (hia : i ≠ a) (hib : i ≠ b) :
    (swapped m a b).size = m.size ∧ (swapped m a b).cells i = m.cells i := by
  simp [swapped, hia, hib]

-- Aliasing is valid and leaves every cell unchanged.
theorem swap_alias (m : Memory) (a i : Nat) :
    (swapped m a a).cells i = m.cells i := by
  by_cases h : i = a <;> simp [swapped, h]

-- Failed reads cannot be rescued by a suffix; no final state is returned.
theorem swap_out_of_bounds (m : Memory) (a b : Nat) (tail : List Item)
    (rest : List Op) (h : m.size ≤ a ∨ m.size ≤ b) :
    execute (swapProgram a b ++ rest) ⟨tail, m⟩ = none := by
  rcases h with ha | hb
  · simp [swapProgram, execute, step, load, Nat.not_lt.mpr ha]
  · by_cases ha : a < m.size
    · simp [swapProgram, execute, step, load, ha, Nat.not_lt.mpr hb]
    · simp [swapProgram, execute, step, load, ha]

-- A deliberately wrong postcondition is refuted by a concrete execution.
theorem swap_is_not_copy :
    (swapped ⟨2, fun i => if i = 0 then 10 else 20⟩ 0 1).cells 0 ≠ 10 := by
  decide

end LeanForthMemorySwapReference
