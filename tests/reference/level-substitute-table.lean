import Lean

open Lean

-- Substitute symbolic caller levels for callee parameters, then independently
-- instantiate the caller's variables and evaluate. This compares finite
-- observations; it does not establish equality of symbolic levels in general.
def main : IO Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let source := Level.imax (Level.max (.succ u) v) (Level.imax v u)
  let replacements := [[v, u], [.succ v, .max u v], [v, .succ u]]
  for (args, caseNo) in replacements.zipIdx do
    let result := source.instantiateParams [`u, `v] args
    for a in [0:4] do
      for b in [0:4] do
        let concrete := result.instantiateParams [`u, `v] [Level.ofNat a, Level.ofNat b]
        match concrete.normalize.toNat with
        | some value => IO.println s!"{caseNo} {a} {b} {value}"
        | none => throw <| IO.userError "substituted level is not concrete"
