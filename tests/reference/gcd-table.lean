import GcdReference
open GcdReference

-- Match the finite host inputs and report the independent Lean model result.
def emit (a b : Int) : IO Unit := do
  IO.print s!"{a} {b} "
  match checked a b with
  | some result => IO.println s!"{result} ok"
  | none => IO.println "invalid"

def main : IO Unit := do
  for i in [0:12] do
    for j in [0:12] do
      emit (Int.ofNat i - 3) (Int.ofNat j - 3)
  let hi : Int := 9223372036854775807
  let lo : Int := -9223372036854775808
  for (a, b) in [(hi, 0), (0, hi), (hi, hi), (hi, 1), (lo, 1), (1, lo)] do
    emit a b
