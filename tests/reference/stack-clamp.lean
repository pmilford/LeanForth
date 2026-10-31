import Lean

/-
Untrusted reference model of the particular stack operations in `lf-clamp`.
Data and return stacks are mathematical integer lists, top first. The model
does not execute Forth source or establish correctness of a host Forth runtime.
-/
namespace LeanForthStackModel

structure State where
  data : List Int
  returns : List Int
  deriving Repr, DecidableEq

inductive Op where
  | twoDup | greater | twoDrop | drop | toReturn | fromReturn | max | min
  | push (value : Int)
  deriving Repr

-- One instruction either produces a state or explicitly reports underflow.
def step (op : Op) (state : State) : Option State :=
  match op, state.data, state.returns with
  | .twoDup, a :: b :: rest, rs => some ⟨a :: b :: a :: b :: rest, rs⟩
  | .greater, a :: b :: rest, rs => some ⟨(if b > a then -1 else 0) :: rest, rs⟩
  | .twoDrop, _ :: _ :: rest, rs => some ⟨rest, rs⟩
  | .drop, _ :: rest, rs => some ⟨rest, rs⟩
  | .toReturn, a :: rest, rs => some ⟨rest, a :: rs⟩
  | .fromReturn, ds, a :: rs => some ⟨a :: ds, rs⟩
  | .max, a :: b :: rest, rs => some ⟨(if b < a then a else b) :: rest, rs⟩
  | .min, a :: b :: rest, rs => some ⟨(if b < a then b else a) :: rest, rs⟩
  | .push value, ds, rs => some ⟨value :: ds, rs⟩
  | _, _, _ => none

-- A finite program consists of instructions and a flag-consuming branch.
inductive Code where
  | done
  | op (operation : Op) (next : Code)
  | branch (ifTrue ifFalse : Code)

-- Structural recursion on code ensures termination of this finite model.
def execute : Code → State → Option State
  | .done, state => some state
  | .op op next, state => (step op state).bind (execute next)
  | .branch yes no, ⟨flag :: rest, rs⟩ =>
      if flag != 0 then execute yes ⟨rest, rs⟩ else execute no ⟨rest, rs⟩
  | .branch _ _, ⟨[], _⟩ => none

-- The instruction order mirrors `2dup > if 2drop drop false exit then
-- >r max r> min true`. Zero is false and -1 represents the host true flag.
def clampCode : Code :=
  .op .twoDup <| .op .greater <|
  .branch (.op .twoDrop <| .op .drop <| .op (.push 0) .done)
          (.op .toReturn <| .op .max <| .op .fromReturn <| .op .min <|
           .op (.push (-1)) .done)

def clampSpec (lower upper value : Int) : Int :=
  if value < lower then lower else if value > upper then upper else value

-- Both the data-stack suffix and preexisting return stack are preserved.
theorem clampCode_spec (lower upper value : Int) (tail rs : List Int) :
    execute clampCode ⟨upper :: lower :: value :: tail, rs⟩ =
      some ⟨(if lower > upper then [0] else [-1, clampSpec lower upper value]) ++ tail, rs⟩ := by
  simp only [clampCode, execute, step, Option.bind_some]
  split <;> simp_all [clampSpec] <;> omega

-- Under the stated ordered-bounds precondition, execution returns a value in
-- range while preserving both surrounding stacks.
theorem clampCode_bounds (lower upper value : Int) (tail rs : List Int)
    (ordered : lower ≤ upper) :
    ∃ result, execute clampCode ⟨upper :: lower :: value :: tail, rs⟩ =
        some ⟨(-1) :: result :: tail, rs⟩ ∧ lower ≤ result ∧ result ≤ upper := by
  refine ⟨clampSpec lower upper value, ?_, ?_, ?_⟩
  · simpa [show ¬ lower > upper by omega] using clampCode_spec lower upper value tail rs
  · unfold clampSpec
    split <;> (try split) <;> omega
  · unfold clampSpec
    split <;> (try split) <;> omega

-- Fewer than three data cells always underflow, irrespective of their values
-- and of the existing return stack. This is a property of this model: an
-- actual Forth host need not detect stack underflow or fail in the same way.
theorem clampCode_underflow (data rs : List Int) (short : data.length < 3) :
    execute clampCode ⟨data, rs⟩ = none := by
  rcases data with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · rfl
  · simp only [clampCode, execute, step, Option.bind_some]
    split <;> rfl
  · simp only [List.length_cons] at short
    omega

-- Concrete examples exercise both outcomes of the initial comparison.
example : execute clampCode ⟨[1, 2], []⟩ = none := by decide
example : execute clampCode ⟨[2, 1], []⟩ = none := by decide
example : execute (.branch (.op (.push 9) .done) (.op (.push 4) .done))
    ⟨[-5], []⟩ = some ⟨[9], []⟩ := by decide
example : execute (.branch (.op (.push 9) .done) (.op (.push 4) .done))
    ⟨[0], []⟩ = some ⟨[4], []⟩ := by decide

-- Emit the same bounded cases as the Gforth runtime table. Reversed bounds are
-- represented by the model's zero flag; all other modeled outcomes must have
-- the documented success flag and single result.
def emit (lower upper value : Int) : IO Unit := do
  match execute clampCode ⟨[upper, lower, value], []⟩ with
  | some ⟨[0], []⟩ => IO.println s!"{lower} {upper} {value} invalid"
  | some ⟨[-1, result], []⟩ => IO.println s!"{lower} {upper} {value} {result} "
  | _ => throw <| IO.userError "unexpected stack-model result"

def main : IO Unit := do
  for lowerNat in [0:7] do
    for upperNat in [0:7] do
      for valueNat in [0:7] do
        emit (Int.ofNat lowerNat - 3) (Int.ofNat upperNat - 3) (Int.ofNat valueNat - 3)
  let boundaries : List Int := [-2147483648, -2147483647, -1, 0, 1, 2147483646, 2147483647]
  for lower in boundaries do
    for upper in boundaries do
      for value in boundaries do
        emit lower upper value

end LeanForthStackModel

def main : IO Unit := LeanForthStackModel.main
