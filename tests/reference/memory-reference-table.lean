/- Finite observations of the existing model, not a runtime proof. -/
import «memory-program-reference»
open LeanForthMemoryProgramReference
open LeanForthProgramReference (Memory)

def initial : Memory := ⟨4, fun i => Int.ofNat (11 * (i + 1))⟩

def emit (write : Bool) (a v : Int) : IO Unit := do
  let code := if write then
    [.push (.value v), .push (.address a.toNat), .store,
     .push (.address a.toNat), .load]
  else [.push (.address a.toNat), .load]
  -- Negative host indices have no Nat representation: reject in the adapter.
  let result := if a < 0 then none else execute code ⟨[.value 12345], initial⟩
  IO.print s!"{if write then 1 else 0} {a} {v} "
  match result with
  | some ⟨[.value x, .value 12345], m⟩ =>
      IO.print s!"ok {x}"
      for i in [0:4] do IO.print s!" {m.cells i}"
  | none =>
      IO.print "invalid 0"
      for i in [0:4] do IO.print s!" {initial.cells i}"
  | _ => throw <| IO.userError "unexpected model stack"
  IO.println " "

def main : IO Unit := do
  for i in [0:7] do
    let a := Int.ofNat i - 1
    emit false a 0
    for v in [-9, 0, 57] do emit true a v
