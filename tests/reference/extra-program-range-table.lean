import ProgramExamples

-- Finite comparison with the mathematical specification, not a proof of
-- Forth execution or a proof certificate for the program.
def emitRange64 (lo hi value : Int) : IO Unit := do
  let result := match ProgramExamplesReference.inRange value lo hi with
    | none => "invalid"
    | some true => "true"
    | some false => "false"
  IO.println s!"{lo} {hi} {value} {result}"

def main : IO Unit := do
  let xs : List Int := [-9223372036854775808, -9223372036854775807,
    -1, 0, 1, 9223372036854775806, 9223372036854775807]
  for lo in xs do
    for hi in xs do
      for value in xs do
        emitRange64 lo hi value
