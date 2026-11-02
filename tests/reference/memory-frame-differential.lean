/- Finite step observations of the existing abstract model, not a runtime proof. -/
import «memory-copy-reference»
import «memory-swap-reference»

open LeanForthProgramReference (Memory)
open LeanForthMemoryProgramReference (Item Op State step)
open LeanForthMemoryCopyReference (copyProgram)
open LeanForthMemorySwapReference (swapProgram)

def initial : Memory := ⟨4, fun i => Int.ofNat (11 * (i + 1))⟩

-- Negative host indices have no Nat representation. Map them to an invalid
-- model address, retaining their position in the instruction sequence.
def address (i : Int) : Nat := if i < 0 then 4 else i.toNat

-- Unlike execute's none, retain the state immediately before the failed
-- instruction. The number identifies the access that failed, not a proof.
def trace (ops : List Op) (state : State) (access : Nat) : Nat × State := Id.run do
  let mut s := state
  let mut n := access
  for op in ops do
    match op with
    | .load | .store => n := n + 1
    | _ => pure ()
    match step op s with
    | none => return (n, s)
    | some next => s := next
  return (0, s)

def emit (source dest a b : Int) : IO Unit := do
  let ops := copyProgram (address dest) ++ swapProgram (address a) (address b)
  let (status, result) := trace ops ⟨[.address (address source), .value 12345], initial⟩ 0
  if status == 0 && result.stack != [.value 12345] then
    throw <| IO.userError "unexpected model stack"
  IO.print s!"{source} {dest} {a} {b} {status} "
  for i in [0:4] do IO.print s!"{result.memory.cells i} "
  IO.println ""

def main : IO Unit := do
  for s in [0:6] do
    for d in [0:6] do
      for a in [0:6] do
        for b in [0:6] do
          emit (Int.ofNat s - 1) (Int.ofNat d - 1)
            (Int.ofNat a - 1) (Int.ofNat b - 1)
