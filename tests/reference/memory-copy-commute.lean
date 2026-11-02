/- Abstract bounded memory and tagged-stack semantics only: no claim about
   Forth execution, a compiler, or machine memory. -/
import «memory-copy-properties»

namespace LeanForthMemoryCopyCommute

open LeanForthProgramReference (Memory load store copyCell)
open LeanForthMemoryProgramReference (Item Op execute step)
open LeanForthMemoryCopyReference (copyProgram copy_execution)
open LeanForthMemoryCopyProperties (execute_append)

-- Mathematical update, defined on all backing cells, including out of bounds.
def copied (m : Memory) (source destination : Nat) : Memory :=
  ⟨m.size, fun i => if i = destination then m.cells source else m.cells i⟩

theorem copy_result (m : Memory) (s d : Nat) (hs : s < m.size) (hd : d < m.size) :
    copyCell m s d = some (copied m s d) := by
  simp [copyCell, load, store, copied, hs, hd]

-- Each destination is distinct from the other destination and the other
-- copy's source. Sources may coincide, and either copy may be a self-copy.
theorem copied_commute (m : Memory) (s₁ d₁ s₂ d₂ : Nat)
    (hdd : d₁ ≠ d₂) (hds : d₁ ≠ s₂) (hsd : d₂ ≠ s₁) :
    copied (copied m s₁ d₁) s₂ d₂ = copied (copied m s₂ d₂) s₁ d₁ := by
  cases m with
  | mk size cells =>
    simp only [copied]
    congr 1
    funext i
    by_cases h₁ : i = d₁ <;> by_cases h₂ : i = d₂ <;>
      simp_all [Ne.symm hdd, Ne.symm hds, Ne.symm hsd]

-- Both inputs are pushed explicitly, so either order starts from the same
-- arbitrary stack and consumes neither its contents nor its frame.
def copyPair (s₁ d₁ s₂ d₂ : Nat) : List Op :=
  [.push (.address s₁)] ++ copyProgram d₁ ++
    [.push (.address s₂)] ++ copyProgram d₂

theorem pair_success (m : Memory) (s₁ d₁ s₂ d₂ : Nat) (tail : List Item)
    (hs₁ : s₁ < m.size) (hd₁ : d₁ < m.size)
    (hs₂ : s₂ < m.size) (hd₂ : d₂ < m.size) :
    execute (copyPair s₁ d₁ s₂ d₂) ⟨tail, m⟩ =
      some ⟨tail, copied (copied m s₁ d₁) s₂ d₂⟩ := by
  have hs₂' : s₂ < (copied m s₁ d₁).size := hs₂
  have hd₂' : d₂ < (copied m s₁ d₁).size := hd₂
  simp only [copyPair, execute, step, Option.bind_some, execute_append,
    copy_execution, copy_result m s₁ d₁ hs₁ hd₁, Option.map_some,
    copy_result (copied m s₁ d₁) s₂ d₂ hs₂' hd₂']

theorem pair_commute (m : Memory) (s₁ d₁ s₂ d₂ : Nat) (tail : List Item)
    (hs₁ : s₁ < m.size) (hd₁ : d₁ < m.size)
    (hs₂ : s₂ < m.size) (hd₂ : d₂ < m.size)
    (hdd : d₁ ≠ d₂) (hds : d₁ ≠ s₂) (hsd : d₂ ≠ s₁) :
    execute (copyPair s₁ d₁ s₂ d₂) ⟨tail, m⟩ =
      execute (copyPair s₂ d₂ s₁ d₁) ⟨tail, m⟩ := by
  rw [pair_success m s₁ d₁ s₂ d₂ tail hs₁ hd₁ hs₂ hd₂,
    pair_success m s₂ d₂ s₁ d₁ tail hs₂ hd₂ hs₁ hd₁,
    copied_commute m s₁ d₁ s₂ d₂ hdd hds hsd]

-- A dependency: the second copy reads the first destination. All addresses
-- are in bounds and destinations differ, yet the final memories differ.
def exampleMemory : Memory := ⟨3, fun i => if i = 0 then 7 else 0⟩

theorem dependency_counterexample :
    execute (copyPair 0 1 1 2) ⟨[], exampleMemory⟩ ≠
      execute (copyPair 1 2 0 1) ⟨[], exampleMemory⟩ := by
  intro h
  have hread := congrArg (fun result => result.map (fun state => state.memory.cells 2)) h
  simp [copyPair, copyProgram, execute, step, load, store, exampleMemory] at hread

end LeanForthMemoryCopyCommute
