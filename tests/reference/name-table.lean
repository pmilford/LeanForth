import Lean

open Lean

-- Compare structured names directly using pinned Lean's Name equality.
def main : IO Unit := do
  let root := Name.anonymous
  let u := Name.str root "u"
  let v := Name.str root "v"
  let nested := Name.str u "u"
  let number := Name.num root 1
  let stringNumber := Name.str root "1"
  let unicode := Name.str root "é"
  let decomposed := Name.str root "é"
  let empty := Name.str root ""
  let cases := [(u, Name.str root "u"), (u, v), (u, nested),
    (number, stringNumber), (number, Name.num root 1),
    (unicode, Name.str root "é"), (unicode, decomposed),
    (empty, Name.str root ""), (Name.num u 1, Name.num (Name.str root "u") 1)]
  for ((left, right), index) in cases.zipIdx do
    IO.println s!"{index} {if left == right then 1 else 0}"
