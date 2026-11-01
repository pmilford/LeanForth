import ProgramContracts
open LeanForthProgramReference

-- Emit exact reference depths for all opcode lists up to six instructions.
-- Push carries zero because literal values do not affect the depth rule.
def codeFor (length index : Nat) : List Op :=
  (List.range length).map fun position =>
    match (index / 3 ^ position) % 3 with
    | 0 => .push 0
    | 1 => .dup
    | _ => .add

def main : IO Unit := do
  for length in [0:7] do
    for index in [0:3 ^ length] do
      IO.println s!"{length} {index} {requiredDepth (codeFor length index)} "
