import ProgramExamples

/- Finite executable comparison only: this does not establish Forth semantics,
   compiler correctness, or correspondence between the model and the host. -/
def emitRange (lower upper value : Int) : IO Unit := do
  let result := match ProgramExamplesReference.inRange value lower upper with
    | none => "invalid"
    | some true => "true"
    | some false => "false"
  IO.println s!"{lower} {upper} {value} {result}"

def main : IO Unit := do
  for lo in [0:7] do
    for hi in [0:7] do
      for v in [0:7] do
        emitRange (Int.ofNat lo - 3) (Int.ofNat hi - 3) (Int.ofNat v - 3)
  let boundaries : List Int := [-2147483648, -2147483647, -1, 0, 1, 2147483646, 2147483647]
  for lo in boundaries do
    for hi in boundaries do
      for v in boundaries do
        emitRange lo hi v
