import FactorialReference

/- Finite model observations; neither Forth semantics nor its runtime is proved. -/
def emitFactorial (n : Int) : IO Unit := do
  match FactorialReference.checked 9223372036854775807 n with
  | none => IO.println s!"{n} invalid"
  | some result => IO.println s!"{n} {result} ok"

def main : IO Unit := do
  for i in [0:150] do
    emitFactorial (Int.ofNat i - 128)
  for n in ([-9223372036854775808, -9223372036854775807] : List Int) do
    emitFactorial n
