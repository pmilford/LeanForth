/- Untrusted mathematical reference; not a Forth or runtime correctness proof. -/
import «program-contracts»

namespace LeanForthMemoryProgramReference

open LeanForthProgramReference (Memory load store store_read_frame out_of_bounds_access)

-- Addresses and values are distinct mathematical stack items, top first.
inductive Item where
  | address (a : Nat)
  | value (v : Int)
  deriving Repr, DecidableEq

structure State where
  stack : List Item
  memory : Memory

inductive Op where
  | push (item : Item)
  | load
  | store

-- push: ( -- item ); load: ( addr -- value );
-- store: ( value addr -- ). Underflow, wrong tags, and bounds fail.
def step : Op → State → Option State
  | .push x, ⟨s, m⟩ => some ⟨x :: s, m⟩
  | .load, ⟨.address a :: s, m⟩ =>
      (load m a).map fun v => ⟨.value v :: s, m⟩
  | .store, ⟨.address a :: .value v :: s, m⟩ =>
      (store m a v).map fun m' => ⟨s, m'⟩
  | _, _ => none

def execute : List Op → State → Option State
  | [], s => some s
  | op :: rest, s => (step op s).bind (execute rest)

-- Push the value and address, store, push the address and load. The arbitrary
-- stack tail and every memory cell outside the written address are framed.
theorem write_then_read (m : Memory) (a : Nat) (v : Int) (tail : List Item)
    (h : a < m.size) :
    ∃ updated, execute [.push (.value v), .push (.address a), .store,
        .push (.address a), .load] ⟨tail, m⟩ =
        some ⟨.value v :: tail, updated⟩ ∧
      updated.size = m.size ∧ load updated a = some v ∧
      ∀ other, other ≠ a → updated.cells other = m.cells other := by
  obtain ⟨updated, hs, hz, hl, hf⟩ := store_read_frame m a v h
  refine ⟨updated, ?_, hz, hl, hf⟩
  simp [execute, step, hs, hl]

-- Failure propagates through the entire instruction sequence, even if
-- additional instructions follow the failed access.
theorem load_out_of_bounds (m : Memory) (a : Nat) (tail : List Item)
    (rest : List Op) (h : m.size ≤ a) :
    execute (.load :: rest) ⟨.address a :: tail, m⟩ = none := by
  have hl := (out_of_bounds_access m a 0 h).1
  simp [execute, step, hl]

theorem store_out_of_bounds (m : Memory) (a : Nat) (v : Int)
    (tail : List Item) (rest : List Op) (h : m.size ≤ a) :
    execute (.store :: rest) ⟨.address a :: .value v :: tail, m⟩ = none := by
  have hs := (out_of_bounds_access m a v h).2
  simp [execute, step, hs]

theorem load_underflow (m : Memory) (rest : List Op) :
    execute (.load :: rest) ⟨[], m⟩ = none := by rfl

theorem store_wrong_tag (m : Memory) (a : Nat) (tail : List Item)
    (rest : List Op) :
    execute (.store :: rest) ⟨.address a :: .address a :: tail, m⟩ = none := by rfl

end LeanForthMemoryProgramReference
