/- Abstract memory and stack semantics only; no Forth runtime claim. -/
import «memory-copy-properties»

namespace LeanForthMemoryCopyFrameComposition

open LeanForthProgramReference (Memory load store)
open LeanForthMemoryProgramReference (Item Op State execute step)
open LeanForthMemoryCopyReference (copyProgram copy_success)
open LeanForthMemoryCopyProperties (execute_append)

-- A successful continuation may write only addresses in its footprint, and
-- must preserve the memory size. This is a contract, not an automatic
-- footprint analysis; the continuation may still read arbitrary addresses.
def PreservesOutside (rest : List Op) (writes : Nat → Prop) : Prop :=
  ∀ initial final, execute rest initial = some final →
    final.memory.size = initial.memory.size ∧
    ∀ i, ¬ writes i → final.memory.cells i = initial.memory.cells i

-- If the continuation succeeds and cannot write the copy destination,
-- the copied value survives. All cells outside both write footprints retain
-- their original values, even when source and destination alias.
theorem copy_then_frame (m : Memory) (source destination : Nat)
    (tail : List Item) (rest : List Op) (writes : Nat → Prop) (final : State)
    (hs : source < m.size) (hd : destination < m.size)
    (hframe : PreservesOutside rest writes) (hdisjoint : ¬ writes destination)
    (hrun : execute (copyProgram destination ++ rest)
      ⟨.address source :: tail, m⟩ = some final) :
    final.memory.size = m.size ∧
    load final.memory destination = load m source ∧
    ∀ i, i ≠ destination → ¬ writes i → final.memory.cells i = m.cells i := by
  obtain ⟨middle, hc, hz, hl, hf⟩ := copy_success m source destination tail hs hd
  have hrest : execute rest ⟨tail, middle⟩ = some final := by
    simpa [execute_append, hc] using hrun
  obtain ⟨hsize, hcells⟩ := hframe ⟨tail, middle⟩ final hrest
  have hsize' : final.memory.size = m.size := hsize.trans hz
  refine ⟨hsize', ?_, ?_⟩
  · calc
      load final.memory destination = load middle destination := by
        simp [load, hsize, hcells destination hdisjoint]
      _ = load m source := hl
  · intro i hi hw
    exact (hcells i hw).trans (hf i hi)

-- An empty continuation satisfies the contract for any footprint.
theorem empty_preserves_outside (writes : Nat → Prop) :
    PreservesOutside [] writes := by
  intro initial final h
  simp [execute] at h
  subst final
  simp

-- A real modeled write satisfies the contract, including failed stores:
-- only successful executions have a final memory to frame.
theorem write_preserves_outside (address : Nat) (value : Int) :
    PreservesOutside [.push (.value value), .push (.address address), .store]
      (fun i => i = address) := by
  intro initial final h
  simp only [execute, step, Option.bind_some] at h
  by_cases hb : address < initial.memory.size
  · simp [store, hb] at h
    subst final
    simp
    intro i hne heq
    exact False.elim (hne heq)
  · simp [store, hb] at h

end LeanForthMemoryCopyFrameComposition
