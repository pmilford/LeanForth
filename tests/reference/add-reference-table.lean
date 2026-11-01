import CheckedAdd

/- Finite execution comparison, not a proof of Forth or its runtime. -/
def emitAdd (a b : Int) : IO Unit := do
  let result := match CheckedAddReference.checkedAdd (-9223372036854775808) 9223372036854775807 a b with
    | none => "overflow"
    | some n => s!"ok {n}"
  IO.println s!"{a} {b} {result}"

def main : IO Unit := do
  for a in [0:17] do
    for b in [0:17] do
      emitAdd (Int.ofNat a - 8) (Int.ofNat b - 8)
  let boundaries : List Int :=
    [-9223372036854775808, -9223372036854775807,
     -2147483648, -2147483647, -1, 0, 1, 2147483646, 2147483647,
     9223372036854775806, 9223372036854775807]
  for a in boundaries do
    for b in boundaries do
      emitAdd a b
