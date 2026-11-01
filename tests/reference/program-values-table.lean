import ProgramContracts
open LeanForthProgramReference

-- Exhaust all lists of up to five operations. Digits are execution order.
def codeFor (length index : Nat) : List Op :=
  (List.range length).map fun p =>
    match (index / 5 ^ p) % 5 with
    | 0 => .push (-2)
    | 1 => .push 0
    | 2 => .push 3
    | 3 => .dup
    | _ => .add

def initial : Nat → Stack
  | 0 => []
  | 1 => [-3]
  | 2 => [2, -1]
  | _ => [-2, 3, 7]

def main : IO Unit := do
  for length in [0:6] do
    for index in [0:5 ^ length] do
      for seed in [0:4] do
        IO.print s!"{length} {index} {seed} "
        match execute (codeFor length index) (initial seed) with
        | none => IO.println "fail"
        | some stack =>
          IO.print s!"ok {stack.length} "
          for value in stack do IO.print s!"{value} "
          IO.println ""
