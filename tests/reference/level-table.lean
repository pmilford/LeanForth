import Lean

open Lean

-- Reference evaluation uses Lean's own level normalization and extraction.
def main : IO Unit := do
  for left in [0:6] do
    for right in [0:6] do
      for kind in [0:2] do
        let a := Level.ofNat left
        let b := Level.ofNat right
        let level := if kind == 0 then Level.max a b else Level.imax a b
        match level.normalize.toNat with
        | some n => IO.println s!"{kind} {left} {right} {n}"
        | none => throw <| IO.userError "normalized concrete level is not a numeral"
  let zeroFromImax := Level.imax (Level.ofNat 2) .zero
  let nested := [Level.imax (Level.ofNat 1) zeroFromImax,
                 Level.max zeroFromImax (Level.ofNat 1),
                 Level.imax (Level.ofNat 2) zeroFromImax,
                 Level.max zeroFromImax (Level.ofNat 2)]
  for (level, index) in nested.zipIdx do
    match level.normalize.toNat with
    | some n => IO.println s!"2 {index} 0 {n}"
    | none => throw <| IO.userError "nested level is not a numeral"
