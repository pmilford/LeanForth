import ProgramExamples

/- Finite observations of the mathematical model, not a proof of the Forth
   implementation, host runtime, or compiler. -/
def emitAbs (n : Int) : IO Unit := do
  let min : Int := -9223372036854775808
  match ProgramExamplesReference.checkedAbs min n with
  | none => IO.println s!"{n} invalid"
  | some magnitude => IO.println s!"{n} {magnitude} ok"

def main : IO Unit := do
  for i in [0:257] do
    emitAbs (Int.ofNat i - 128)
  for n in ([-9223372036854775808, -9223372036854775807,
              -9223372036854775806, 9223372036854775805,
              9223372036854775806, 9223372036854775807] : List Int) do
    emitAbs n
