import Lean

/-
Reference semantics of the LeanForth program IR, version 0.1
(docs/programming/PROGRAM_IR.md). Untrusted: Lean, not LeanForth, checks
everything in this file.

The file has five parts:
1. Verbatim copies of the reference models of the six example words.
   `tests/program/check_program_ir.py` (part of `make test`) checks that
   every block between BEGIN VERBATIM and END VERBATIM equals the named
   lines of the named file, so the theorems are about exactly those.
2. The IR and its semantics: signed cells of any width of at least two bits,
   two's-complement wrapping, separate data and return stacks, explicit
   failures, fuel that bounds call nesting and loop repetitions, and names
   in the reader's spelling (A-Z folded to lower case), compared exactly.
3. The six example words of src/program/clamp.fs and src/program/examples.fs
   in the IR, and theorems that their IR semantics equals the reference
   models for every input that fits in a cell and every stack below them.
4. A printer for the IR's text form; `main` prints the programs so that
   `make reference-program-ir` can compare them with the reader's output.
5. The contracts of the five words other than clamp, copied from their
   reference files: the IR meets each one (the two loops through stated
   invariants), and a deliberately wrong IR program for each is refuted.

What this does not show: that the IR is a faithful translation of the Forth
source (the reader is trusted for that, see PROGRAM_IR.md), that Gforth
executes the source as the IR semantics says, or anything about LeanForth's
own checker.
-/

-- Part 1. Copies of the reference models.

-- BEGIN VERBATIM tests/reference/clamp.lean 3-4
def clamp (lower upper value : Int) : Int :=
  if value < lower then lower else if value > upper then upper else value
-- END VERBATIM

namespace LeanForthStackModel
-- BEGIN VERBATIM tests/reference/stack-clamp.lean 10-46
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
-- END VERBATIM
-- BEGIN VERBATIM tests/reference/stack-clamp.lean 96-110
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
-- END VERBATIM
end LeanForthStackModel

namespace ProgramExamplesReference
-- BEGIN VERBATIM tests/reference/program-examples.lean 8-12
def checkedAbs (min n : Int) : Option Int :=
  if n = min then none else some (if n < 0 then -n else n)

def inRange (value lower upper : Int) : Option Bool :=
  if lower > upper then none else some (decide (lower ≤ value ∧ value ≤ upper))
-- END VERBATIM
end ProgramExamplesReference

namespace CheckedAddReference
-- BEGIN VERBATIM tests/reference/checked-add.lean 9-14
def checkedAdd (min max a b : Int) : Option Int :=
  if 0 < b then
    if max - b < a then none else some (a + b)
  else if b < 0 then
    if a < min - b then none else some (a + b)
  else some (a + b)
-- END VERBATIM
end CheckedAddReference

namespace FactorialReference
-- BEGIN VERBATIM tests/reference/factorial-reference.lean 6-45
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

-- Each multiplication is performed in mathematical Nat and checked before
-- being returned as a bounded-cell result. `none` denotes failure.
def bounded : Nat → Nat → Option Nat
  | limit, 0 => if 1 ≤ limit then some 1 else none
  | limit, n + 1 =>
    match bounded limit n with
    | none => none
    | some a => if a * (n + 1) ≤ limit then some (a * (n + 1)) else none

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.mul_pos ih]

theorem previous_le (n : Nat) : factorial n ≤ factorial (n + 1) := by
  simp only [factorial]
  exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ n)

theorem bounded_exact (limit n : Nat) :
    bounded limit n = if factorial n ≤ limit then some (factorial n) else none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bounded, ih]
    by_cases h : factorial n ≤ limit
    · simp only [h, ↓reduceIte, factorial]
      rfl
    · have hn : ¬ factorial (n + 1) ≤ limit := by
        have hp := previous_le n
        omega
      simp only [h, ↓reduceIte, hn]

-- Signed input and maximum are modeled explicitly; the precondition on cell
-- representability is stated by the caller, not enforced by this function.
def checked (limit : Nat) (input : Int) : Option Nat :=
  if input < 0 then none else bounded limit input.toNat
-- END VERBATIM
end FactorialReference

namespace GcdReference
-- BEGIN VERBATIM tests/reference/gcd-reference.lean 6-19
def euclid (a b : Nat) : Nat :=
  if _h : b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

theorem euclid_correct (a b : Nat) : euclid a b = Nat.gcd a b := by
  fun_induction euclid a b with
  | case1 a => simp
  | case2 a b _ ih =>
    rw [ih, Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a,
      Nat.gcd_comm]

def checked (a b : Int) : Option Nat :=
  if a < 0 ∨ b < 0 then none else some (euclid a.toNat b.toNat)
-- END VERBATIM
end GcdReference

-- Part 2. The IR and its semantics.

namespace ProgramIR

/-- A host cell of `bits` bits holding a two's-complement signed integer.
Forth-2012 cells have at least 16 bits; narrower cells are allowed here so
that small cases can be checked exhaustively. -/
structure Cells where
  bits : Nat
  two_le : 2 ≤ bits

namespace Cells
variable (c : Cells)

def half : Int := ((2 ^ (c.bits - 1) : Nat) : Int)
def max : Int := c.half - 1
def min : Int := -c.half
def modulus : Int := 2 * c.half
def Fits (x : Int) : Prop := c.min ≤ x ∧ x ≤ c.max
/-- Two's-complement wrapping: the cell value congruent to `x`. -/
def wrap (x : Int) : Int := (x - c.min) % c.modulus + c.min
/-- The bit pattern of a cell, read as an unsigned number. -/
def unsigned (x : Int) : Nat := (if x < 0 then x + c.modulus else x).toNat
/-- An unsigned bit pattern read back as a signed cell. -/
def signed (u : Nat) : Int := if (u : Int) > c.max then (u : Int) - c.modulus else u

theorem two_le_half : 2 ≤ c.half := by
  have h := c.two_le
  have : 2 ^ 1 ≤ 2 ^ (c.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [half]
  omega

theorem min_eq : c.min = -c.max - 1 := by
  simp only [min, max]
  omega

theorem max_pos : 0 < c.max := by
  have := c.two_le_half
  simp only [max]
  omega

theorem wrap_of_fits {x : Int} (h : c.Fits x) : c.wrap x = x := by
  have := c.two_le_half
  simp only [Fits, max, min] at h
  simp only [wrap, modulus, min]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem signed_zero : c.signed 0 = 0 := by
  have := c.max_pos
  simp [signed]
  omega

theorem signed_unsigned_neg_one : c.signed (c.unsigned (-1)) = -1 := by
  have := c.two_le_half
  simp only [signed, unsigned, max, modulus]
  split <;> omega

theorem unsigned_zero : c.unsigned 0 = 0 := by
  simp [unsigned]

-- The literals the example words use fit every cell.
theorem fits_zero : c.Fits 0 := by
  have := c.two_le_half
  simp only [Fits, max, min]
  omega

theorem fits_one : c.Fits 1 := by
  have := c.two_le_half
  simp only [Fits, max, min]
  omega

theorem fits_neg_one : c.Fits (-1) := by
  have := c.two_le_half
  simp only [Fits, max, min]
  omega

theorem rshift_neg_one : c.signed (c.unsigned (-1) >>> 1) = c.max := by
  have := c.two_le_half
  simp only [signed, unsigned, max, modulus, Nat.shiftRight_eq_div_pow]
  split <;> simp <;> omega

end Cells

/-- The primitive words of IR 0.1, named after the Forth words they model. -/
inductive Prim where
  | dup | drop | swap | over | nip | tuck | rot | twoDup | twoDrop
  | toR | fromR | rFetch
  | add | sub | mul | div | mod | negate | abs | onePlus | oneMinus
  | eq | ne | lt | gt | zeroEq | zeroNe | zeroLt | zeroGt
  | and | or | xor | invert | rshift
  | max | min | true | false
  deriving Repr, DecidableEq

/-- An instruction. `ifElse` is `IF yes ELSE no THEN`; `loop` is
`BEGIN test WHILE body REPEAT`; `exit` leaves the current word. -/
inductive Instr where
  | prim (p : Prim)
  | lit (n : Int)
  | call (name : String)
  | ifElse (yes no : List Instr)
  | loop (test body : List Instr)
  | exit
  deriving Repr

/-- Data and return stacks, top of stack first. -/
structure State where
  data : List Int
  rets : List Int
  deriving Repr, DecidableEq

/-- Every way a run can fail. None of them is ever a success. -/
inductive Failure where
  | underflow    -- a data- or return-stack item was missing
  | unmodeled    -- an operation whose result IR 0.1 does not define
  | unbalanced   -- a word returned with items left on its return stack
  | unknownWord  -- a call to a name the program does not define
  | badConstant  -- a constant's body did not leave exactly one value
  | outOfFuel    -- the call-depth or loop-iteration budget ran out
  deriving Repr, DecidableEq

/-- `next`: the block ran to its end; `exited`: it ran EXIT. -/
inductive Result where
  | next (s : State)
  | exited (s : State)
  | failed (f : Failure)
  deriving Repr, DecidableEq

inductive Def where
  | word (body : List Instr)
  | constant (body : List Instr)
  deriving Repr

/-- Definitions in source order. -/
abbrev Program := List (String × Def)

def flag (b : Bool) : Int := if b then -1 else 0

def lookup (p : Program) (name : String) : Option Def :=
  (p.find? (fun d => d.1 == name)).map (·.2)

def bitwise (c : Cells) (op : Nat → Nat → Nat) (a b : Int) : Int :=
  c.signed (op (c.unsigned a) (c.unsigned b))

/-- One primitive. Operands are named as in the Forth-2012 stack comments:
for `a b -` the top of the stack is `b`. Arithmetic wraps; `/` and `MOD`
are defined only for a nonnegative dividend and a positive divisor, where
floored and symmetric division agree, and `RSHIFT` only for a shift count
below the cell width. -/
def step (c : Cells) : Prim → State → Result
  | .dup, ⟨a :: d, r⟩ => .next ⟨a :: a :: d, r⟩
  | .drop, ⟨_ :: d, r⟩ => .next ⟨d, r⟩
  | .swap, ⟨b :: a :: d, r⟩ => .next ⟨a :: b :: d, r⟩
  | .over, ⟨b :: a :: d, r⟩ => .next ⟨a :: b :: a :: d, r⟩
  | .nip, ⟨b :: _ :: d, r⟩ => .next ⟨b :: d, r⟩
  | .tuck, ⟨b :: a :: d, r⟩ => .next ⟨b :: a :: b :: d, r⟩
  | .rot, ⟨x3 :: x2 :: x1 :: d, r⟩ => .next ⟨x1 :: x3 :: x2 :: d, r⟩
  | .twoDup, ⟨b :: a :: d, r⟩ => .next ⟨b :: a :: b :: a :: d, r⟩
  | .twoDrop, ⟨_ :: _ :: d, r⟩ => .next ⟨d, r⟩
  | .toR, ⟨a :: d, r⟩ => .next ⟨d, a :: r⟩
  | .fromR, ⟨d, a :: r⟩ => .next ⟨a :: d, r⟩
  | .rFetch, ⟨d, a :: r⟩ => .next ⟨a :: d, a :: r⟩
  | .add, ⟨b :: a :: d, r⟩ => .next ⟨c.wrap (a + b) :: d, r⟩
  | .sub, ⟨b :: a :: d, r⟩ => .next ⟨c.wrap (a - b) :: d, r⟩
  | .mul, ⟨b :: a :: d, r⟩ => .next ⟨c.wrap (a * b) :: d, r⟩
  | .div, ⟨b :: a :: d, r⟩ =>
      if 0 ≤ a ∧ 0 < b then .next ⟨a / b :: d, r⟩ else .failed .unmodeled
  | .mod, ⟨b :: a :: d, r⟩ =>
      if 0 ≤ a ∧ 0 < b then .next ⟨a % b :: d, r⟩ else .failed .unmodeled
  | .negate, ⟨a :: d, r⟩ => .next ⟨c.wrap (-a) :: d, r⟩
  | .abs, ⟨a :: d, r⟩ => .next ⟨c.wrap (if a < 0 then -a else a) :: d, r⟩
  | .onePlus, ⟨a :: d, r⟩ => .next ⟨c.wrap (a + 1) :: d, r⟩
  | .oneMinus, ⟨a :: d, r⟩ => .next ⟨c.wrap (a - 1) :: d, r⟩
  | .eq, ⟨b :: a :: d, r⟩ => .next ⟨flag (a == b) :: d, r⟩
  | .ne, ⟨b :: a :: d, r⟩ => .next ⟨flag (a != b) :: d, r⟩
  | .lt, ⟨b :: a :: d, r⟩ => .next ⟨flag (decide (a < b)) :: d, r⟩
  | .gt, ⟨b :: a :: d, r⟩ => .next ⟨flag (decide (a > b)) :: d, r⟩
  | .zeroEq, ⟨a :: d, r⟩ => .next ⟨flag (a == 0) :: d, r⟩
  | .zeroNe, ⟨a :: d, r⟩ => .next ⟨flag (a != 0) :: d, r⟩
  | .zeroLt, ⟨a :: d, r⟩ => .next ⟨flag (decide (a < 0)) :: d, r⟩
  | .zeroGt, ⟨a :: d, r⟩ => .next ⟨flag (decide (a > 0)) :: d, r⟩
  | .and, ⟨b :: a :: d, r⟩ => .next ⟨bitwise c (· &&& ·) a b :: d, r⟩
  | .or, ⟨b :: a :: d, r⟩ => .next ⟨bitwise c (· ||| ·) a b :: d, r⟩
  | .xor, ⟨b :: a :: d, r⟩ => .next ⟨bitwise c (· ^^^ ·) a b :: d, r⟩
  | .invert, ⟨a :: d, r⟩ => .next ⟨(-a - 1) :: d, r⟩
  | .rshift, ⟨n :: a :: d, r⟩ =>
      if 0 ≤ n ∧ n < c.bits then .next ⟨c.signed (c.unsigned a >>> n.toNat) :: d, r⟩
      else .failed .unmodeled
  | .max, ⟨b :: a :: d, r⟩ => .next ⟨(if a < b then b else a) :: d, r⟩
  | .min, ⟨b :: a :: d, r⟩ => .next ⟨(if a < b then a else b) :: d, r⟩
  | .true, ⟨d, r⟩ => .next ⟨-1 :: d, r⟩
  | .false, ⟨d, r⟩ => .next ⟨0 :: d, r⟩
  | _, _ => .failed .underflow

-- Lean generates the equation of each of the 38 primitive cases when it is
-- first named; naming them here also lets `simp` use them.
attribute [local simp] step.eq_1 step.eq_2 step.eq_3 step.eq_4 step.eq_5 step.eq_6 step.eq_7
  step.eq_8 step.eq_9 step.eq_10 step.eq_11 step.eq_12 step.eq_13 step.eq_14 step.eq_15
  step.eq_16 step.eq_17 step.eq_18 step.eq_19 step.eq_20 step.eq_21 step.eq_22 step.eq_23
  step.eq_24 step.eq_25 step.eq_26 step.eq_27 step.eq_28 step.eq_29 step.eq_30 step.eq_31
  step.eq_32 step.eq_33 step.eq_34 step.eq_35 step.eq_36 step.eq_37 step.eq_38

/-- Run a block. A called word starts with an empty return stack of its own
and must leave it empty. A literal must fit in a cell; one that does not is
`unmodeled` (the reader writes only literals that fit in 32 bits, so on
cells of 32 bits or more every literal it writes fits). Fuel bounds the nesting depth
of calls and the repetitions of each loop: a callee runs with one unit
less than its caller, which continues with its own fuel afterwards, and
each repetition of a loop leaves one unit less for the repetitions after
it. So every run terminates; running out is the failure `outOfFuel`. -/
def run (c : Cells) (p : Program) : Nat → List Instr → State → Result
  | _, [], s => .next s
  | fuel, .prim op :: rest, s =>
      match step c op s with
      | .next s' => run c p fuel rest s'
      | other => other
  | fuel, .lit n :: rest, ⟨d, r⟩ =>
      if c.min ≤ n ∧ n ≤ c.max then run c p fuel rest ⟨n :: d, r⟩ else .failed .unmodeled
  | _, .exit :: _, s => .exited s
  | _, .ifElse _ _ :: _, ⟨[], _⟩ => .failed .underflow
  | fuel, .ifElse yes no :: rest, ⟨f :: d, r⟩ =>
      match (if f ≠ 0 then run c p fuel yes ⟨d, r⟩ else run c p fuel no ⟨d, r⟩) with
      | .next s' => run c p fuel rest s'
      | other => other
  | 0, .call _ :: _, _ => .failed .outOfFuel
  | fuel + 1, .call name :: rest, ⟨d, r⟩ =>
      match lookup p name with
      | none => .failed .unknownWord
      | some (.word body) =>
          match run c p fuel body ⟨d, []⟩ with
          | .next ⟨d', []⟩ => run c p (fuel + 1) rest ⟨d', r⟩
          | .exited ⟨d', []⟩ => run c p (fuel + 1) rest ⟨d', r⟩
          | .failed e => .failed e
          | _ => .failed .unbalanced
      | some (.constant body) =>
          match run c p fuel body ⟨[], []⟩ with
          | .next ⟨[v], []⟩ => run c p (fuel + 1) rest ⟨v :: d, r⟩
          | .failed e => .failed e
          | _ => .failed .badConstant
  | 0, .loop _ _ :: _, _ => .failed .outOfFuel
  | fuel + 1, .loop test body :: rest, s =>
      match run c p (fuel + 1) test s with
      | .next ⟨[], _⟩ => .failed .underflow
      | .next ⟨f :: d, r⟩ =>
          if f = 0 then run c p (fuel + 1) rest ⟨d, r⟩
          else
            match run c p (fuel + 1) body ⟨d, r⟩ with
            | .next s' => run c p fuel (.loop test body :: rest) s'
            | other => other
      | other => other
termination_by fuel code => (fuel, sizeOf code)

/-- Run one word, as a caller would: `[CALL name]`. -/
def callWord (c : Cells) (p : Program) (fuel : Nat) (name : String) (s : State) : Result :=
  run c p fuel [.call name] s

/-- The data stack a word body returns with, if it returns normally with an
empty return stack. -/
def Result.returned : Result → Option (List Int)
  | .next ⟨d, []⟩ => some d
  | .exited ⟨d, []⟩ => some d
  | _ => none

-- One-step equations for `run`, used by every proof below.
section Equations
variable (c : Cells) (p : Program)

@[simp] theorem run_nil (fuel : Nat) (s : State) : run c p fuel [] s = .next s := by
  rw [run]

theorem run_prim (fuel : Nat) (op : Prim) (rest : List Instr) (s : State) :
    run c p fuel (.prim op :: rest) s =
      match step c op s with
      | .next s' => run c p fuel rest s'
      | other => other := by
  rw [run]

theorem run_lit (fuel : Nat) (n : Int) (rest : List Instr) (d r : List Int)
    (fits : c.Fits n) :
    run c p fuel (.lit n :: rest) ⟨d, r⟩ = run c p fuel rest ⟨n :: d, r⟩ := by
  rw [run]
  exact ite_eq_left fits

theorem run_lit_unfit (fuel : Nat) (n : Int) (rest : List Instr) (d r : List Int)
    (unfit : ¬ c.Fits n) :
    run c p fuel (.lit n :: rest) ⟨d, r⟩ = .failed .unmodeled := by
  rw [run]
  exact ite_eq_right unfit

theorem run_exit (fuel : Nat) (rest : List Instr) (s : State) :
    run c p fuel (.exit :: rest) s = .exited s := by
  rw [run]

theorem run_if (fuel : Nat) (yes no rest : List Instr) (f : Int) (d r : List Int) :
    run c p fuel (.ifElse yes no :: rest) ⟨f :: d, r⟩ =
      match (if f ≠ 0 then run c p fuel yes ⟨d, r⟩ else run c p fuel no ⟨d, r⟩) with
      | .next s' => run c p fuel rest s'
      | other => other := by
  rw [run]

theorem run_call (fuel : Nat) (name : String) (rest : List Instr) (d r : List Int) :
    run c p (fuel + 1) (.call name :: rest) ⟨d, r⟩ =
      match lookup p name with
      | none => .failed .unknownWord
      | some (.word body) =>
          match run c p fuel body ⟨d, []⟩ with
          | .next ⟨d', []⟩ => run c p (fuel + 1) rest ⟨d', r⟩
          | .exited ⟨d', []⟩ => run c p (fuel + 1) rest ⟨d', r⟩
          | .failed e => .failed e
          | _ => .failed .unbalanced
      | some (.constant body) =>
          match run c p fuel body ⟨[], []⟩ with
          | .next ⟨[v], []⟩ => run c p (fuel + 1) rest ⟨v :: d, r⟩
          | .failed e => .failed e
          | _ => .failed .badConstant := by
  rw [run]

theorem run_call_zero (name : String) (rest : List Instr) (s : State) :
    run c p 0 (.call name :: rest) s = .failed .outOfFuel := by
  rw [run]

theorem run_loop_zero (test body rest : List Instr) (s : State) :
    run c p 0 (.loop test body :: rest) s = .failed .outOfFuel := by
  rw [run]

theorem run_loop (fuel : Nat) (test body rest : List Instr) (s : State) :
    run c p (fuel + 1) (.loop test body :: rest) s =
      match run c p (fuel + 1) test s with
      | .next ⟨[], _⟩ => .failed .underflow
      | .next ⟨f :: d, r⟩ =>
          if f = 0 then run c p (fuel + 1) rest ⟨d, r⟩
          else
            match run c p (fuel + 1) body ⟨d, r⟩ with
            | .next s' => run c p fuel (.loop test body :: rest) s'
            | other => other
      | other => other := by
  rw [run]

/-- A call to a word that returns normally continues with its result. The
callee runs with one unit of fuel less than its caller. -/
theorem run_call_word {fuel : Nat} {name : String} {body rest : List Instr}
    {d r d' : List Int} (found : lookup p name = some (.word body))
    (returns : (run c p (fuel - 1) body ⟨d, []⟩).returned = some d') (pos : 0 < fuel) :
    run c p fuel (.call name :: rest) ⟨d, r⟩ = run c p fuel rest ⟨d', r⟩ := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [run_call, found]
  simp only [Nat.add_sub_cancel] at returns ⊢
  generalize run c p f body ⟨d, []⟩ = result at returns ⊢
  rcases result with ⟨⟨d1, _ | ⟨x, r1⟩⟩⟩ | ⟨⟨d1, _ | ⟨x, r1⟩⟩⟩ | e <;>
    simp_all [Result.returned]

/-- A call to a constant pushes its value. -/
theorem run_call_constant {fuel : Nat} {name : String} {body rest : List Instr}
    {d r : List Int} {v : Int} (found : lookup p name = some (.constant body))
    (value : run c p (fuel - 1) body ⟨[], []⟩ = .next ⟨[v], []⟩) (pos : 0 < fuel) :
    run c p fuel (.call name :: rest) ⟨d, r⟩ = run c p fuel rest ⟨v :: d, r⟩ := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [run_call, found]
  simp only [Nat.add_sub_cancel] at value ⊢
  simp only [value]

end Equations

@[simp] theorem flag_true : flag true = -1 := rfl
@[simp] theorem flag_false : flag false = 0 := rfl

@[simp] theorem flag_ne_zero (b : Bool) : flag b ≠ 0 ↔ b = true := by
  cases b <;> simp [flag]

@[simp] theorem flag_beq_zero (b : Bool) : (flag b == 0) = !b := by
  cases b <;> rfl

theorem and_flags (c : Cells) (x y : Bool) :
    bitwise c (· &&& ·) (flag x) (flag y) = flag (x && y) := by
  cases x <;> cases y <;>
    simp [bitwise, flag, c.unsigned_zero, c.signed_zero, c.signed_unsigned_neg_one]

theorem or_flags (c : Cells) (x y : Bool) :
    bitwise c (· ||| ·) (flag x) (flag y) = flag (x || y) := by
  cases x <;> cases y <;>
    simp [bitwise, flag, c.unsigned_zero, c.signed_zero, c.signed_unsigned_neg_one]

/-- Execute known IR code symbolically: unfold `run` instruction by
instruction, and `step` only where the stacks have a known shape (the
equations `step.eq_1` to `step.eq_38` are its 38 primitive cases). -/
macro "ir_simp" : tactic => `(tactic| simp only [run_prim, run_lit, run_exit, run_nil, run_if,
  Cells.fits_zero, Cells.fits_one, Cells.fits_neg_one,
  flag_ne_zero, flag_beq_zero, flag_true, flag_false, and_flags, or_flags, beq_iff_eq,
  bne_iff_ne, decide_eq_true_eq, ↓reduceIte,
  step.eq_1, step.eq_2, step.eq_3, step.eq_4, step.eq_5, step.eq_6, step.eq_7, step.eq_8,
  step.eq_9, step.eq_10, step.eq_11, step.eq_12, step.eq_13, step.eq_14, step.eq_15,
  step.eq_16, step.eq_17, step.eq_18, step.eq_19, step.eq_20, step.eq_21, step.eq_22,
  step.eq_23, step.eq_24, step.eq_25, step.eq_26, step.eq_27, step.eq_28, step.eq_29,
  step.eq_30, step.eq_31, step.eq_32, step.eq_33, step.eq_34, step.eq_35, step.eq_36,
  step.eq_37, step.eq_38])

-- Part 3. The six example words in the IR.

section Words
open Instr

/-- src/program/clamp.fs -/
def clampBody : List Instr :=
  [prim .twoDup, prim .gt, ifElse [prim .twoDrop, prim .drop, prim .false, exit] [],
   prim .toR, prim .max, prim .fromR, prim .min, prim .true]

def clampProgram : Program := [("lf-clamp", .word clampBody)]

/- src/program/examples.fs, in source order. -/
def exampleMaxBody : List Instr := [lit (-1), lit 1, prim .rshift]
def exampleMinBody : List Instr := [call "lf-example-max", prim .invert]
def addAboveBody : List Instr :=
  [call "lf-example-max", prim .swap, prim .sub, prim .gt]
def addBelowBody : List Instr :=
  [call "lf-example-min", prim .swap, prim .sub, prim .lt]
def addOverflowBody : List Instr :=
  [prim .dup, prim .zeroGt, ifElse [call "lf-add-above?", exit] [],
   prim .dup, prim .zeroLt, ifElse [call "lf-add-below?"] [prim .twoDrop, prim .false]]
def checkedAddBody : List Instr :=
  [prim .twoDup, call "lf-add-overflow?",
   ifElse [prim .twoDrop, prim .false] [prim .add, prim .true]]
def checkedAbsBody : List Instr :=
  [prim .dup, call "lf-example-min", prim .eq,
   ifElse [prim .drop, prim .false] [prim .abs, prim .true]]
def productOverBody : List Instr :=
  [call "lf-example-max", prim .swap, prim .div, prim .gt]
def factorialFromBody : List Instr :=
  [loop [prim .dup, lit 1, prim .gt]
     [prim .twoDup, call "lf-product-over?",
      ifElse [prim .twoDrop, prim .false, exit] [],
      prim .tuck, prim .mul, prim .swap, prim .oneMinus],
   prim .drop, prim .true]
def factorialBody : List Instr :=
  [prim .dup, prim .zeroLt,
   ifElse [prim .drop, prim .false] [lit 1, prim .swap, call "lf-factorial-from"]]
def euclidBody : List Instr :=
  [loop [prim .dup, prim .zeroNe] [prim .tuck, prim .mod], prim .drop]
def gcdBody : List Instr :=
  [prim .twoDup, prim .zeroLt, prim .swap, prim .zeroLt, prim .or,
   ifElse [prim .twoDrop, prim .false] [call "lf-euclid", prim .true]]
def withinClosedBody : List Instr :=
  [prim .toR, prim .over, prim .gt, prim .zeroEq, prim .swap, prim .fromR, prim .gt,
   prim .zeroEq, prim .and]
def inRangeBody : List Instr :=
  [prim .twoDup, prim .gt,
   ifElse [prim .twoDrop, prim .drop, prim .false] [call "lf-within-closed?", prim .true]]

def examplesProgram : Program := [
  ("lf-example-max", .constant exampleMaxBody),
  ("lf-example-min", .constant exampleMinBody),
  ("lf-add-above?", .word addAboveBody),
  ("lf-add-below?", .word addBelowBody),
  ("lf-add-overflow?", .word addOverflowBody),
  ("lf-checked-add", .word checkedAddBody),
  ("lf-checked-abs", .word checkedAbsBody),
  ("lf-product-over?", .word productOverBody),
  ("lf-factorial-from", .word factorialFromBody),
  ("lf-factorial", .word factorialBody),
  ("lf-euclid", .word euclidBody),
  ("lf-gcd", .word gcdBody),
  ("lf-within-closed?", .word withinClosedBody),
  ("lf-in-range", .word inRangeBody)]

end Words


-- Each name resolves to its definition.
theorem lookup_clamp : lookup clampProgram "lf-clamp" = some (.word clampBody) := rfl
theorem lookup_max :
    lookup examplesProgram "lf-example-max" = some (.constant exampleMaxBody) := rfl
theorem lookup_min :
    lookup examplesProgram "lf-example-min" = some (.constant exampleMinBody) := rfl
theorem lookup_above : lookup examplesProgram "lf-add-above?" = some (.word addAboveBody) := rfl
theorem lookup_below : lookup examplesProgram "lf-add-below?" = some (.word addBelowBody) := rfl
theorem lookup_overflow :
    lookup examplesProgram "lf-add-overflow?" = some (.word addOverflowBody) := rfl
theorem lookup_checkedAdd :
    lookup examplesProgram "lf-checked-add" = some (.word checkedAddBody) := rfl
theorem lookup_checkedAbs :
    lookup examplesProgram "lf-checked-abs" = some (.word checkedAbsBody) := rfl
theorem lookup_withinClosed :
    lookup examplesProgram "lf-within-closed?" = some (.word withinClosedBody) := rfl
theorem lookup_inRange :
    lookup examplesProgram "lf-in-range" = some (.word inRangeBody) := rfl

/-- How `( ... -- x true | false )` encodes an optional result. -/
def encode : Option Int → List Int
  | some v => [-1, v]
  | none => [0]

/-- How `( ... -- flag true | false )` encodes an optional truth value. -/
def encodeFlag : Option Bool → List Int
  | some b => [-1, flag b]
  | none => [0]

/-- A word whose body returns normally gives its caller that stack. -/
theorem callWord_of_returns {c : Cells} {p : Program} {fuel : Nat} {name : String}
    {body : List Instr} {d d' rs : List Int} (found : lookup p name = some (.word body))
    (returns : (run c p (fuel - 1) body ⟨d, []⟩).returned = some d') (pos : 0 < fuel) :
    callWord c p fuel name ⟨d, rs⟩ = .next ⟨d', rs⟩ := by
  rw [callWord, run_call_word c p found returns pos]
  simp

-- lf-clamp

theorem clamp_returns (c : Cells) (fuel : Nat) (lower upper value : Int) (tail : List Int) :
    (run c clampProgram fuel clampBody ⟨upper :: lower :: value :: tail, []⟩).returned =
      some ((if lower > upper then [0] else [-1, clamp lower upper value]) ++ tail) := by
  simp only [clampBody]
  ir_simp
  by_cases h : lower > upper
  · simp only [h, ↓reduceIte]
    simp [Result.returned]
  · simp only [h, ↓reduceIte]
    ir_simp
    simp only [Result.returned, clamp, List.cons_append, List.nil_append, Option.some.injEq,
      List.cons.injEq, true_and, and_true]
    repeat' split
    all_goals omega

/-- The IR clamp equals `clamp` of tests/reference/clamp.lean for every
integer input and every stack below it; it has no arithmetic to wrap. -/
theorem clamp_correct (c : Cells) (fuel : Nat) (lower upper value : Int) (tail rs : List Int)
    (enough : 1 ≤ fuel) :
    callWord c clampProgram fuel "lf-clamp" ⟨upper :: lower :: value :: tail, rs⟩ =
      .next ⟨(if lower > upper then [0] else [-1, clamp lower upper value]) ++ tail, rs⟩ :=
  callWord_of_returns lookup_clamp (clamp_returns c _ lower upper value tail) enough

/-- The IR clamp and the stack model of tests/reference/stack-clamp.lean
give the same stacks. -/
theorem clamp_matches_stack_model (c : Cells) (fuel : Nat) (lower upper value : Int)
    (tail rs : List Int) (enough : 1 ≤ fuel) :
    (match callWord c clampProgram fuel "lf-clamp" ⟨upper :: lower :: value :: tail, rs⟩ with
     | .next s => some (LeanForthStackModel.State.mk s.data s.rets)
     | _ => none) =
      LeanForthStackModel.execute LeanForthStackModel.clampCode
        ⟨upper :: lower :: value :: tail, rs⟩ := by
  rw [clamp_correct c fuel lower upper value tail rs enough, LeanForthStackModel.clampCode_spec]
  rfl

-- The two constants: on a two's-complement cell `-1 1 RSHIFT` is the
-- largest cell and its INVERT the smallest.

theorem max_value (c : Cells) (fuel : Nat) :
    run c examplesProgram fuel exampleMaxBody ⟨[], []⟩ = .next ⟨[c.max], []⟩ := by
  have := c.two_le
  simp only [exampleMaxBody]
  ir_simp
  simp [show (1 : Int) < c.bits by omega, c.rshift_neg_one]

theorem run_max (c : Cells) (fuel : Nat) (rest : List Instr) (d r : List Int)
    (enough : 1 ≤ fuel) :
    run c examplesProgram fuel (.call "lf-example-max" :: rest) ⟨d, r⟩ =
      run c examplesProgram fuel rest ⟨c.max :: d, r⟩ :=
  run_call_constant c examplesProgram lookup_max (max_value c _) enough

theorem min_value (c : Cells) (fuel : Nat) (enough : 1 ≤ fuel) :
    run c examplesProgram fuel exampleMinBody ⟨[], []⟩ = .next ⟨[c.min], []⟩ := by
  simp only [exampleMinBody, run_max c fuel _ _ _ enough]
  ir_simp
  rw [c.min_eq]

theorem run_min (c : Cells) (fuel : Nat) (rest : List Instr) (d r : List Int)
    (enough : 2 ≤ fuel) :
    run c examplesProgram fuel (.call "lf-example-min" :: rest) ⟨d, r⟩ =
      run c examplesProgram fuel rest ⟨c.min :: d, r⟩ :=
  run_call_constant c examplesProgram lookup_min (min_value c _ (by omega)) (by omega)

-- lf-checked-add and its helpers.

theorem above_returns (c : Cells) (fuel : Nat) (a b : Int) (d : List Int)
    (enough : 1 ≤ fuel) (positive : 0 < b) (fits : c.Fits b) :
    (run c examplesProgram fuel addAboveBody ⟨b :: a :: d, []⟩).returned =
      some (flag (decide (a > c.max - b)) :: d) := by
  have := c.max_pos
  simp only [Cells.Fits] at fits
  simp only [addAboveBody, run_max c fuel _ _ _ enough]
  ir_simp
  rw [c.wrap_of_fits (x := c.max - b) (by simp only [Cells.Fits, c.min_eq]; omega)]
  rfl

theorem below_returns (c : Cells) (fuel : Nat) (a b : Int) (d : List Int)
    (enough : 2 ≤ fuel) (negative : b < 0) (fits : c.Fits b) :
    (run c examplesProgram fuel addBelowBody ⟨b :: a :: d, []⟩).returned =
      some (flag (decide (a < c.min - b)) :: d) := by
  have := c.max_pos
  simp only [Cells.Fits] at fits
  simp only [addBelowBody, run_min c fuel _ _ _ enough]
  ir_simp
  rw [c.wrap_of_fits (x := c.min - b) (by simp only [Cells.Fits, c.min_eq] at *; omega)]
  rfl

/-- The overflow test of `lf-add-overflow?`, in its own order. -/
def overflows (c : Cells) (a b : Int) : Bool :=
  if 0 < b then decide (a > c.max - b) else if b < 0 then decide (a < c.min - b) else false

theorem overflow_returns (c : Cells) (fuel : Nat) (a b : Int) (d : List Int)
    (enough : 3 ≤ fuel) (fits : c.Fits b) :
    (run c examplesProgram fuel addOverflowBody ⟨b :: a :: d, []⟩).returned =
      some (flag (overflows c a b) :: d) := by
  simp only [addOverflowBody]
  ir_simp
  by_cases positive : 0 < b
  · simp only [positive, ↓reduceIte]
    rw [run_call_word c examplesProgram lookup_above
      (above_returns c (fuel - 1) a b d (by omega) positive fits) (by omega)]
    ir_simp
    simp [Result.returned, overflows, positive]
  · simp only [positive, ↓reduceIte]
    ir_simp
    by_cases negative : b < 0
    · simp only [negative, ↓reduceIte]
      rw [run_call_word c examplesProgram lookup_below
        (below_returns c (fuel - 1) a b d (by omega) negative fits) (by omega)]
      simp [Result.returned, overflows, positive, negative]
    · simp only [negative, ↓reduceIte]
      simp [Result.returned, overflows, positive, negative]

theorem checkedAdd_eq (c : Cells) (a b : Int) :
    CheckedAddReference.checkedAdd c.min c.max a b =
      if overflows c a b then none else some (a + b) := by
  simp only [CheckedAddReference.checkedAdd, overflows]
  by_cases positive : 0 < b <;> by_cases negative : b < 0 <;> simp [positive, negative]

theorem sum_fits (c : Cells) (a b : Int) (fa : c.Fits a)
    (ok : overflows c a b = false) : c.Fits (a + b) := by
  simp only [Cells.Fits, overflows] at fa ok ⊢
  by_cases positive : 0 < b <;> by_cases negative : b < 0 <;>
    simp [positive, negative] at ok <;> omega

theorem checkedAdd_returns (c : Cells) (fuel : Nat) (a b : Int) (d : List Int)
    (enough : 4 ≤ fuel) (fa : c.Fits a) (fb : c.Fits b) :
    (run c examplesProgram fuel checkedAddBody ⟨b :: a :: d, []⟩).returned =
      some (encode (CheckedAddReference.checkedAdd c.min c.max a b) ++ d) := by
  simp only [checkedAddBody]
  ir_simp
  rw [run_call_word c examplesProgram lookup_overflow
    (overflow_returns c (fuel - 1) a b (b :: a :: d) (by omega) fb) (by omega)]
  ir_simp
  rw [checkedAdd_eq]
  cases ov : overflows c a b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [c.wrap_of_fits (sum_fits c a b fa ov)]
    simp [Result.returned, encode]
  · simp only [↓reduceIte]
    simp [Result.returned, encode]

/-- The IR `lf-checked-add` equals `checkedAdd` of tests/reference/checked-add.lean
for all inputs that fit in a cell, and its additions never wrap. -/
theorem checkedAdd_correct (c : Cells) (fuel : Nat) (a b : Int) (tail rs : List Int)
    (enough : 5 ≤ fuel) (fa : c.Fits a) (fb : c.Fits b) :
    callWord c examplesProgram fuel "lf-checked-add" ⟨b :: a :: tail, rs⟩ =
      .next ⟨encode (CheckedAddReference.checkedAdd c.min c.max a b) ++ tail, rs⟩ :=
  callWord_of_returns lookup_checkedAdd
    (checkedAdd_returns c _ a b tail (by omega) fa fb) (by omega)

-- lf-checked-abs

theorem checkedAbs_returns (c : Cells) (fuel : Nat) (n : Int) (d : List Int)
    (enough : 2 ≤ fuel) (fits : c.Fits n) :
    (run c examplesProgram fuel checkedAbsBody ⟨n :: d, []⟩).returned =
      some (encode (ProgramExamplesReference.checkedAbs c.min n) ++ d) := by
  simp only [checkedAbsBody]
  ir_simp
  rw [run_min c fuel _ _ _ enough]
  ir_simp
  simp only [ProgramExamplesReference.checkedAbs]
  by_cases h : n = c.min
  · simp only [h, ↓reduceIte]
    simp [Result.returned, encode]
  · simp only [h, ↓reduceIte]
    have := c.min_eq
    rw [c.wrap_of_fits (x := if n < 0 then -n else n)
      (by simp only [Cells.Fits] at *; split <;> omega)]
    simp [Result.returned, encode]

/-- The IR `lf-checked-abs` equals `checkedAbs` of tests/reference/program-examples.lean
for every input that fits in a cell. -/
theorem checkedAbs_correct (c : Cells) (fuel : Nat) (n : Int) (tail rs : List Int)
    (enough : 3 ≤ fuel) (fits : c.Fits n) :
    callWord c examplesProgram fuel "lf-checked-abs" ⟨n :: tail, rs⟩ =
      .next ⟨encode (ProgramExamplesReference.checkedAbs c.min n) ++ tail, rs⟩ :=
  callWord_of_returns lookup_checkedAbs
    (checkedAbs_returns c _ n tail (by omega) fits) (by omega)

-- lf-in-range

theorem withinClosed_returns (c : Cells) (fuel : Nat) (value lower upper : Int)
    (d : List Int) :
    (run c examplesProgram fuel withinClosedBody ⟨upper :: lower :: value :: d, []⟩).returned =
      some (flag (decide (lower ≤ value ∧ value ≤ upper)) :: d) := by
  simp only [withinClosedBody]
  ir_simp
  simp only [Result.returned]
  have same : (!decide (lower > value) && !decide (value > upper)) =
      decide (lower ≤ value ∧ value ≤ upper) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  rw [same]

theorem inRange_returns (c : Cells) (fuel : Nat) (value lower upper : Int) (d : List Int)
    (enough : 1 ≤ fuel) :
    (run c examplesProgram fuel inRangeBody ⟨upper :: lower :: value :: d, []⟩).returned =
      some (encodeFlag (ProgramExamplesReference.inRange value lower upper) ++ d) := by
  simp only [inRangeBody]
  ir_simp
  simp only [ProgramExamplesReference.inRange]
  by_cases h : lower > upper
  · simp only [h, ↓reduceIte]
    simp [Result.returned, encodeFlag]
  · simp only [h, ↓reduceIte]
    rw [run_call_word c examplesProgram lookup_withinClosed
      (withinClosed_returns c (fuel - 1) value lower upper d) (by omega)]
    ir_simp
    simp [Result.returned, encodeFlag]

/-- The IR `lf-in-range` equals `inRange` of tests/reference/program-examples.lean
for all integer inputs; it has no arithmetic to wrap. -/
theorem inRange_correct (c : Cells) (fuel : Nat) (value lower upper : Int)
    (tail rs : List Int) (enough : 2 ≤ fuel) :
    callWord c examplesProgram fuel "lf-in-range" ⟨upper :: lower :: value :: tail, rs⟩ =
      .next ⟨encodeFlag (ProgramExamplesReference.inRange value lower upper) ++ tail, rs⟩ :=
  callWord_of_returns lookup_inRange
    (inRange_returns c _ value lower upper tail (by omega)) (by omega)


theorem lookup_productOver :
    lookup examplesProgram "lf-product-over?" = some (.word productOverBody) := rfl
theorem lookup_factorialFrom :
    lookup examplesProgram "lf-factorial-from" = some (.word factorialFromBody) := rfl
theorem lookup_factorial :
    lookup examplesProgram "lf-factorial" = some (.word factorialBody) := rfl
theorem lookup_euclid : lookup examplesProgram "lf-euclid" = some (.word euclidBody) := rfl
theorem lookup_gcd : lookup examplesProgram "lf-gcd" = some (.word gcdBody) := rfl

/-- How `( ... -- n true | false )` encodes an optional natural number. -/
def encodeNat : Option Nat → List Int
  | some v => [-1, (v : Int)]
  | none => [0]

-- lf-gcd

theorem euclid_run (c : Cells) (fuel : Nat) : ∀ (a b : Nat) (d r : List Int), b + 1 ≤ fuel →
    run c examplesProgram fuel euclidBody ⟨(b : Int) :: (a : Int) :: d, r⟩ =
      .next ⟨(GcdReference.euclid a b : Int) :: d, r⟩ := by
  induction fuel with
  | zero => intro a b d r enough; omega
  | succ f ih =>
    intro a b d r enough
    simp only [euclidBody] at ih ⊢
    rw [run_loop]
    ir_simp
    by_cases zero : b = 0
    · subst zero
      simp [GcdReference.euclid.eq_1 a 0]
    · have positive : (0 : Int) ≤ a ∧ (0 : Int) < b := by omega
      have test : flag ((b : Int) != 0) = -1 := by simp [flag, zero]
      simp only [test, positive, and_self, show ¬((-1 : Int) = 0) by decide, ↓reduceIte]
      rw [← Int.natCast_emod, ih b (a % b) d r (by have := Nat.mod_lt a (by omega : b > 0); omega),
        GcdReference.euclid.eq_1 a b]
      simp [zero]

theorem gcd_returns (c : Cells) (fuel : Nat) (a b : Int) (d : List Int)
    (enough : b.toNat + 2 ≤ fuel) :
    (run c examplesProgram fuel gcdBody ⟨b :: a :: d, []⟩).returned =
      some (encodeNat (GcdReference.checked a b) ++ d) := by
  simp only [gcdBody]
  ir_simp
  simp only [GcdReference.checked]
  by_cases negative : a < 0 ∨ b < 0
  · have test : (decide (b < 0) || decide (a < 0)) = true := by simp; omega
    simp only [test, negative, ↓reduceIte]
    simp [Result.returned, encodeNat]
  · have test : (decide (b < 0) || decide (a < 0)) = false := by simp; omega
    simp only [test, negative, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨a, rfl⟩ : ∃ n : Nat, a = n := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    obtain ⟨b, rfl⟩ : ∃ n : Nat, b = n := ⟨b.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    simp only [Int.toNat_natCast] at enough ⊢
    rw [run_call_word c examplesProgram lookup_euclid
      (by rw [euclid_run c (fuel - 1) a b d [] (by omega)]; rfl) (by omega)]
    ir_simp
    simp [Result.returned, encodeNat]

/-- The IR `lf-gcd` equals `checked` of tests/reference/gcd-reference.lean for
all integer inputs; Euclid's loop needs at most `b + 1` iterations. -/
theorem gcd_correct (c : Cells) (fuel : Nat) (a b : Int) (tail rs : List Int)
    (enough : b.toNat + 3 ≤ fuel) :
    callWord c examplesProgram fuel "lf-gcd" ⟨b :: a :: tail, rs⟩ =
      .next ⟨encodeNat (GcdReference.checked a b) ++ tail, rs⟩ :=
  callWord_of_returns lookup_gcd (gcd_returns c _ a b tail (by omega)) (by omega)

-- lf-factorial

theorem productOver_returns (c : Cells) (fuel : Nat) (product n : Int) (d : List Int)
    (enough : 1 ≤ fuel) (positive : 0 < n) :
    (run c examplesProgram fuel productOverBody ⟨n :: product :: d, []⟩).returned =
      some (flag (decide (product > c.max / n)) :: d) := by
  have operands : 0 ≤ c.max ∧ 0 < n := ⟨Int.le_of_lt c.max_pos, positive⟩
  simp only [productOverBody, run_max c fuel _ _ _ enough]
  ir_simp
  simp only [operands, and_self, ↓reduceIte]
  ir_simp
  rfl

theorem le_mul_of_one_le {x y : Int} (hx : 0 ≤ x) (hy : 1 ≤ y) : x ≤ x * y := by
  have := Int.mul_le_mul_of_nonneg_left hy hx
  simpa using this

/-- The factorial of `k + 1`, multiplied in the loop's order. -/
theorem product_factorial_succ (product : Int) (k : Nat) :
    product * (FactorialReference.factorial (k + 1) : Int) =
      product * ((k + 1 : Nat) : Int) * (FactorialReference.factorial k : Int) := by
  simp only [FactorialReference.factorial, Int.natCast_mul]
  rw [Int.mul_comm (FactorialReference.factorial k : Int), Int.mul_assoc]

theorem factorialFrom_run (c : Cells) (k : Nat) : ∀ (fuel : Nat) (product : Int)
    (d r : List Int), k + 2 ≤ fuel → 1 ≤ product → product ≤ c.max → (k : Int) ≤ c.max →
    run c examplesProgram fuel factorialFromBody ⟨(k : Int) :: product :: d, r⟩ =
      if product * (FactorialReference.factorial k : Int) ≤ c.max
      then .next ⟨-1 :: product * (FactorialReference.factorial k : Int) :: d, r⟩
      else .exited ⟨0 :: d, r⟩ := by
  induction k with
  | zero =>
    intro fuel product d r enough low high _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [factorialFromBody]
    rw [run_loop]
    ir_simp
    simp [FactorialReference.factorial, high]
  | succ k ih =>
    intro fuel product d r enough low high small
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [factorialFromBody] at ih ⊢
    rw [run_loop]
    ir_simp
    by_cases one : k = 0
    · subst one
      simp [FactorialReference.factorial, high]
    · have test : flag (decide (((k + 1 : Nat) : Int) > 1)) = -1 := by simp [flag]; omega
      simp only [test, show ¬((-1 : Int) = 0) by decide, ↓reduceIte]
      rw [run_call_word c examplesProgram lookup_productOver
        (productOver_returns c (f + 1 - 1) product ((k + 1 : Nat) : Int) _ (by omega) (by omega))
        (by omega)]
      ir_simp
      have positive : (0 : Int) < ((k + 1 : Nat) : Int) := by omega
      have grows := le_mul_of_one_le (x := product * ((k + 1 : Nat) : Int))
        (y := (FactorialReference.factorial k : Int)) (Int.mul_nonneg (by omega) (by omega))
        (by have := FactorialReference.factorial_pos k; omega)
      rw [product_factorial_succ]
      by_cases over : product > c.max / ((k + 1 : Nat) : Int)
      · have exceeds : ¬(product * ((k + 1 : Nat) : Int) ≤ c.max) := fun fits =>
          absurd ((Int.le_ediv_iff_mul_le positive).mpr fits) (by omega)
        simp only [over, ↓reduceIte]
        simp only [show ¬(product * ((k + 1 : Nat) : Int) * (FactorialReference.factorial k : Int)
          ≤ c.max) by omega, ↓reduceIte]
      · have below : product * ((k + 1 : Nat) : Int) ≤ c.max :=
          (Int.le_ediv_iff_mul_le positive).mp (by omega)
        have atLeast := le_mul_of_one_le (x := product) (y := ((k + 1 : Nat) : Int))
          (by omega) (by omega)
        have := c.max_pos
        simp only [over, ↓reduceIte]
        ir_simp
        rw [c.wrap_of_fits (x := product * ((k + 1 : Nat) : Int))
            (by simp only [Cells.Fits, c.min_eq]; omega),
          c.wrap_of_fits (x := ((k + 1 : Nat) : Int) - 1)
            (by simp only [Cells.Fits, c.min_eq]; omega)]
        rw [show ((k + 1 : Nat) : Int) - 1 = (k : Int) by omega,
          ih f (product * ((k + 1 : Nat) : Int)) d r (by omega) (by omega) below (by omega)]

theorem factorial_returns (c : Cells) (fuel : Nat) (n : Int) (d : List Int)
    (enough : n.toNat + 3 ≤ fuel) (fits : c.Fits n) :
    (run c examplesProgram fuel factorialBody ⟨n :: d, []⟩).returned =
      some (encodeNat (FactorialReference.checked c.max.toNat n) ++ d) := by
  simp only [factorialBody]
  ir_simp
  simp only [FactorialReference.checked]
  by_cases negative : n < 0
  · simp only [negative, ↓reduceIte]
    simp [Result.returned, encodeNat]
  · simp only [negative, ↓reduceIte]
    obtain ⟨n, rfl⟩ : ∃ m : Nat, n = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    simp only [Int.toNat_natCast] at enough ⊢
    have := c.max_pos
    simp only [Cells.Fits] at fits
    have returns : (run c examplesProgram (fuel - 1) factorialFromBody
        ⟨(n : Int) :: 1 :: d, []⟩).returned =
        some ((if (FactorialReference.factorial n : Int) ≤ c.max
          then [-1, (FactorialReference.factorial n : Int)] else [0]) ++ d) := by
      rw [factorialFrom_run c n (fuel - 1) 1 d [] (by omega) (by omega) (by omega) (by omega)]
      simp only [Int.one_mul]
      by_cases small : (FactorialReference.factorial n : Int) ≤ c.max <;>
        simp only [small, ↓reduceIte, Result.returned, List.cons_append, List.nil_append]
    rw [run_call_word c examplesProgram lookup_factorialFrom returns (by omega),
      FactorialReference.bounded_exact]
    by_cases small : (FactorialReference.factorial n : Int) ≤ c.max
    · have : FactorialReference.factorial n ≤ c.max.toNat := by omega
      simp [small, this, Result.returned, encodeNat]
    · have : ¬FactorialReference.factorial n ≤ c.max.toNat := by omega
      simp [small, this, Result.returned, encodeNat]

/-- The IR `lf-factorial` equals `checked` of tests/reference/factorial-reference.lean,
with the largest cell as its limit, for every input that fits in a cell: it
multiplies in the opposite order and tests for overflow before each product,
and none of its products wraps. -/
theorem factorial_correct (c : Cells) (fuel : Nat) (n : Int) (tail rs : List Int)
    (enough : n.toNat + 4 ≤ fuel) (fits : c.Fits n) :
    callWord c examplesProgram fuel "lf-factorial" ⟨n :: tail, rs⟩ =
      .next ⟨encodeNat (FactorialReference.checked c.max.toNat n) ++ tail, rs⟩ :=
  callWord_of_returns lookup_factorial (factorial_returns c _ n tail (by omega) fits) (by omega)


/-- A 64-bit cell, as on the development host. -/
def cells64 : Cells := ⟨64, by decide⟩

/-- Evaluate a run on known inputs with the equations of `run`, `step`
unfolded on known stacks, and `simp`'s integer arithmetic. -/
macro "ir_eval" : tactic => `(tactic| simp [callWord, run_call, run_prim, run_lit, run_exit,
  Cells.fits_zero, Cells.fits_one, Cells.fits_neg_one,
  run_if, run_loop, run_nil, run_call_zero, run_loop_zero, step, flag, bitwise, cells64,
  Cells.wrap, Cells.min, Cells.max, Cells.half, Cells.modulus, Cells.unsigned, Cells.signed,
  lookup_clamp, clampBody, lookup_max, exampleMaxBody, lookup_min, exampleMinBody,
  lookup_productOver, productOverBody, lookup_factorialFrom, factorialFromBody,
  lookup_factorial, factorialBody, lookup_euclid, euclidBody, lookup_gcd, gcdBody])

-- Every failure outcome is reachable, so no theorem above is true merely
-- because the semantics cannot fail.

theorem clamp_underflow (c : Cells) :
    callWord c clampProgram 1 "lf-clamp" ⟨[1, 2], []⟩ = .failed .underflow := by
  ir_eval

theorem call_out_of_fuel (c : Cells) (p : Program) (name : String) (s : State) :
    callWord c p 0 name s = .failed .outOfFuel := by
  rw [callWord, run]

theorem call_unknown (c : Cells) :
    callWord c clampProgram 1 "lf-gcd" ⟨[], []⟩ = .failed .unknownWord := by
  rw [callWord, run_call]
  rfl

/-- Division by zero is not given a meaning. -/
theorem productOver_by_zero :
    callWord cells64 examplesProgram 2 "lf-product-over?" ⟨[0, 5], []⟩ =
      .failed .unmodeled := by
  ir_eval

/-- Euclid's loop on (3, 5) needs more than one iteration. -/
theorem euclid_out_of_fuel :
    callWord cells64 examplesProgram 2 "lf-euclid" ⟨[5, 3], []⟩ = .failed .outOfFuel := by
  ir_eval

def leakProgram : Program := [("leak", .word [.lit 1, .prim .toR])]
def twoValues : Program := [("two", .constant [.lit 0, .lit 1])]

/-- A word may not return with items on its return stack. -/
theorem leak_unbalanced (c : Cells) :
    callWord c leakProgram 1 "leak" ⟨[], []⟩ = .failed .unbalanced := by
  rw [callWord, run_call]
  simp [leakProgram, lookup, run_lit, Cells.fits_one, run_prim, step]

/-- A constant must leave exactly one value. -/
theorem two_values_bad (c : Cells) :
    callWord c twoValues 1 "two" ⟨[], []⟩ = .failed .badConstant := by
  rw [callWord, run_call]
  simp [twoValues, lookup, run_lit, Cells.fits_zero, Cells.fits_one]

/-- A literal outside the cell is not given a meaning. -/
theorem big_literal_unmodeled (c : Cells) :
    run c [] 0 [.lit (c.max + 1)] ⟨[], []⟩ = .failed .unmodeled :=
  run_lit_unfit c [] 0 _ [] [] [] (by simp only [Cells.Fits]; omega)

-- Deliberately wrong programs are refuted, so the correctness theorems are
-- not true of any program.

/-- `lf-clamp` with MAX and MIN exchanged. -/
def swappedClampProgram : Program :=
  [("lf-clamp", .word [.prim .twoDup, .prim .gt,
     .ifElse [.prim .twoDrop, .prim .drop, .prim .false, .exit] [],
     .prim .toR, .prim .min, .prim .fromR, .prim .max, .prim .true])]

theorem swapped_clamp_refuted (c : Cells) :
    ¬ ∀ lower upper value : Int,
      callWord c swappedClampProgram 1 "lf-clamp" ⟨[upper, lower, value], []⟩ =
        .next ⟨if lower > upper then [0] else [-1, clamp lower upper value], []⟩ := by
  intro claim
  have bad := claim 0 10 (-1)
  simp [callWord, run_call, swappedClampProgram, lookup, run_prim, run_if, step, clamp] at bad

/-- `lf-checked-add` without its overflow test: on 64-bit cells
`max + 1` wraps to `min` instead of failing. -/
def uncheckedAddProgram : Program := [("lf-checked-add", .word [.prim .add, .prim .true])]

theorem unchecked_add_refuted :
    ¬ ∀ a b : Int, cells64.Fits a → cells64.Fits b →
      callWord cells64 uncheckedAddProgram 1 "lf-checked-add" ⟨[b, a], []⟩ =
        .next ⟨encode (CheckedAddReference.checkedAdd cells64.min cells64.max a b), []⟩ := by
  intro claim
  have bad := claim cells64.max 1
    ⟨by simp [cells64, Cells.min, Cells.max, Cells.half], Int.le_refl _⟩
    ⟨by simp [cells64, Cells.min, Cells.half], by simp [cells64, Cells.max, Cells.half]⟩
  simp [callWord, run_call, uncheckedAddProgram, lookup, run_prim, step, encode, cells64,
    CheckedAddReference.checkedAdd, Cells.wrap, Cells.min, Cells.max, Cells.half,
    Cells.modulus] at bad

-- Spot checks on 64-bit cells, computed from the IR.
example : callWord cells64 clampProgram 1 "lf-clamp" ⟨[10, 0, 11], []⟩ = .next ⟨[-1, 10], []⟩ := by
  ir_eval
example : callWord cells64 examplesProgram 21 "lf-gcd" ⟨[18, 48], []⟩ = .next ⟨[-1, 6], []⟩ := by
  ir_eval
example : callWord cells64 examplesProgram 8 "lf-factorial" ⟨[4], []⟩ = .next ⟨[-1, 24], []⟩ := by
  ir_eval

-- The axioms each correctness theorem uses. `make reference-program-ir`
-- accepts only Lean's propext, Classical.choice and Quot.sound here.
#print axioms clamp_correct
#print axioms clamp_matches_stack_model
#print axioms checkedAdd_correct
#print axioms checkedAbs_correct
#print axioms inRange_correct
#print axioms gcd_correct
#print axioms factorial_correct
#print axioms swapped_clamp_refuted
#print axioms unchecked_add_refuted

end ProgramIR

-- Part 4. The text form (PROGRAM_IR.md, "Text form"), without source
-- locations; `make reference-program-ir` compares it with the reader's.

namespace ProgramIR

def irVersion : String := "0.1"

/-- The Forth word a primitive models. -/
def Prim.word : Prim → String
  | .dup => "dup" | .drop => "drop" | .swap => "swap" | .over => "over" | .nip => "nip"
  | .tuck => "tuck" | .rot => "rot" | .twoDup => "2dup" | .twoDrop => "2drop"
  | .toR => ">r" | .fromR => "r>" | .rFetch => "r@"
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "mod"
  | .negate => "negate" | .abs => "abs" | .onePlus => "1+" | .oneMinus => "1-"
  | .eq => "=" | .ne => "<>" | .lt => "<" | .gt => ">"
  | .zeroEq => "0=" | .zeroNe => "0<>" | .zeroLt => "0<" | .zeroGt => "0>"
  | .and => "and" | .or => "or" | .xor => "xor" | .invert => "invert" | .rshift => "rshift"
  | .max => "max" | .min => "min" | .true => "true" | .false => "false"

mutual
def renderInstr (pad : String) : Instr → List String
  | .prim p => [pad ++ "prim " ++ p.word]
  | .lit n => [pad ++ "lit " ++ toString n]
  | .call name => [pad ++ "call " ++ name]
  | .exit => [pad ++ "exit"]
  | .ifElse yes no =>
      [pad ++ "if"] ++ renderBlock (pad ++ "  ") yes ++
        (if no.isEmpty then [] else [pad ++ "else"] ++ renderBlock (pad ++ "  ") no) ++
        [pad ++ "then"]
  | .loop test body =>
      [pad ++ "begin"] ++ renderBlock (pad ++ "  ") test ++ [pad ++ "while"] ++
        renderBlock (pad ++ "  ") body ++ [pad ++ "repeat"]

def renderBlock (pad : String) : List Instr → List String
  | [] => []
  | i :: rest => renderInstr pad i ++ renderBlock pad rest
end

def renderDef : String × Def → List String
  | (name, .word body) => ["word " ++ name] ++ renderBlock "  " body ++ ["end"]
  | (name, .constant body) => ["constant " ++ name] ++ renderBlock "  " body ++ ["end"]

def render (source : String) (p : Program) : String :=
  String.intercalate "\n" (["lf-ir " ++ irVersion, "source " ++ source] ++
    p.flatMap renderDef) ++ "\n"

/-- tests/program/ir/all-primitives.fs: every primitive once, in the order
of `Prim`, so that the comparison with the reader covers every spelling. -/
def allPrimitivesProgram : Program :=
  [("all-primitives", .word ([Prim.dup, .drop, .swap, .over, .nip, .tuck, .rot, .twoDup,
    .twoDrop, .toR, .fromR, .rFetch, .add, .sub, .mul, .div, .mod, .negate, .abs, .onePlus,
    .oneMinus, .eq, .ne, .lt, .gt, .zeroEq, .zeroNe, .zeroLt, .zeroGt, .and, .or, .xor,
    .invert, .rshift, .max, .min, .true, .false].map Instr.prim))]

def main : IO Unit := do
  IO.print (render "src/program/clamp.fs" clampProgram)
  IO.print (render "src/program/examples.fs" examplesProgram)
  IO.print (render "tests/program/ir/all-primitives.fs" allPrimitivesProgram)

end ProgramIR

-- Part 5. The contracts of the five example words other than clamp (plan task
-- 1.5.3). Each reference file states its word's contract in the style of
-- `ClampContract` (tests/reference/clamp.lean), proves that its reference
-- model meets it, and refutes deliberately wrong models; the blocks below are
-- verbatim copies of those contracts. Here Lean proves that each word's IR
-- meets the same clauses, for every cell width, every stack below the inputs
-- and every caller's return stack, and refutes a deliberately wrong IR program
-- for each word. The loops of lf-gcd and lf-factorial are proved through
-- stated loop invariants and a loop rule, without their reference models.

namespace CheckedAddReference
-- BEGIN VERBATIM tests/reference/checked-add.lean 6-6
def inCell (min max n : Int) : Prop := min ≤ n ∧ n ≤ max
-- END VERBATIM
-- BEGIN VERBATIM tests/reference/checked-add.lean 16-33
-- The contract of lf-checked-add, in the style of `ClampContract` (clamp.lean).
-- `CheckedAddSpec min max a b r`: `r` is a right answer for the inputs `a b`
-- of a cell with bounds `min` and `max`, namely the exact sum when it fits
-- the cell and no result when it does not. tests/reference/program-ir.lean
-- copies this block and proves that the word's IR meets the same clauses.
def CheckedAddSpec (min max a b : Int) (r : Option Int) : Prop :=
  (inCell min max (a + b) → r = some (a + b)) ∧
  (¬ inCell min max (a + b) → r = none)

def CheckedAddContract (f : Int → Int → Int → Int → Option Int) : Prop :=
  ∀ min max a b : Int, 0 ≤ max → min = -max - 1 → inCell min max a → inCell min max b →
    CheckedAddSpec min max a b (f min max a b)

theorem checkedAdd_contract : CheckedAddContract checkedAdd := by
  intro min max a b _ hmin ha hb
  simp only [CheckedAddSpec, inCell] at *
  unfold checkedAdd
  constructor <;> intro h <;> (repeat' split) <;> simp_all <;> omega
-- END VERBATIM
end CheckedAddReference

namespace ProgramExamplesReference
-- BEGIN VERBATIM tests/reference/program-examples.lean 14-56
-- The contracts of lf-checked-abs and lf-in-range, in the style of
-- `ClampContract` (clamp.lean). `CheckedAbsSpec min max n r` and
-- `InRangeSpec value lower upper r` say that `r` is a right answer for those
-- inputs. tests/reference/program-ir.lean copies this block and proves that
-- the words' IR meets the same clauses.

-- The smallest cell has no magnitude in the cell and gives no result; every
-- other input gives its magnitude, which lies in the cell.
def CheckedAbsSpec (min max n : Int) (r : Option Int) : Prop :=
  (n = min → r = none) ∧
  (n ≠ min → r = some (n.natAbs : Int)) ∧
  (∀ m, r = some m → 0 ≤ m ∧ m ≤ max)

def CheckedAbsContract (f : Int → Int → Option Int) : Prop :=
  ∀ min max n : Int, 0 ≤ max → min = -max - 1 → min ≤ n → n ≤ max →
    CheckedAbsSpec min max n (f min n)

theorem checkedAbs_contract : CheckedAbsContract checkedAbs := by
  intro min max n _ hmin low high
  simp only [CheckedAbsSpec, checkedAbs]
  by_cases h : n = min
  · simp [h]
  · simp only [h, ↓reduceIte, false_implies, Option.some.injEq, forall_eq', true_and]
    constructor <;> split <;> omega

-- Reversed bounds give no result; for ordered bounds the answer is true
-- exactly inside the closed interval and false exactly outside it.
def InRangeSpec (value lower upper : Int) (r : Option Bool) : Prop :=
  (lower > upper → r = none) ∧
  (lower ≤ upper → (r = some true ↔ lower ≤ value ∧ value ≤ upper)) ∧
  (lower ≤ upper → (r = some false ↔ value < lower ∨ upper < value))

def InRangeContract (f : Int → Int → Int → Option Bool) : Prop :=
  ∀ value lower upper : Int, InRangeSpec value lower upper (f value lower upper)

theorem inRange_contract : InRangeContract inRange := by
  intro value lower upper
  simp only [InRangeSpec, inRange]
  by_cases h : lower > upper
  · simp only [h, ↓reduceIte, forall_const, true_and]
    constructor <;> intro _ <;> omega
  · simp only [h, ↓reduceIte, false_implies, Option.some.injEq, true_and]
    constructor <;> intro _ <;> simp <;> omega
-- END VERBATIM
end ProgramExamplesReference

namespace GcdReference
-- BEGIN VERBATIM tests/reference/gcd-reference.lean 21-56
-- The contract of lf-gcd, in the style of `ClampContract` (clamp.lean).
-- `GcdSpec a b r`: `r` is a right answer for the inputs `a b`, namely no
-- result if either is negative, and otherwise a common divisor of both that
-- every common divisor divides (so the answer for 0 and 0 is 0). It does not
-- mention Euclid's algorithm. tests/reference/program-ir.lean copies this
-- block and proves that the word's IR meets the same clauses.
def GcdSpec (a b : Int) (r : Option Nat) : Prop :=
  (a < 0 ∨ b < 0 → r = none) ∧
  (0 ≤ a → 0 ≤ b → ∃ g : Nat, r = some g ∧ (g : Int) ∣ a ∧ (g : Int) ∣ b ∧
    ∀ d : Int, d ∣ a → d ∣ b → d ∣ (g : Int))

def GcdContract (f : Int → Int → Option Nat) : Prop :=
  ∀ a b : Int, GcdSpec a b (f a b)

-- Lean's `Nat.gcd` of the inputs, rejecting negative ones, meets the clauses.
theorem natGcd_spec (a b : Int) :
    GcdSpec a b (if a < 0 ∨ b < 0 then none else some (Nat.gcd a.toNat b.toNat)) := by
  by_cases negative : a < 0 ∨ b < 0
  · exact ⟨fun _ => by simp [negative], fun ha hb => by omega⟩
  · refine ⟨fun h => absurd h negative,
      fun ha hb => ⟨Nat.gcd a.toNat b.toNat, by simp [negative], ?_⟩⟩
    obtain ⟨x, rfl⟩ : ∃ x : Nat, a = x := ⟨a.toNat, (Int.toNat_of_nonneg ha).symm⟩
    obtain ⟨y, rfl⟩ : ∃ y : Nat, b = y := ⟨b.toNat, (Int.toNat_of_nonneg hb).symm⟩
    simp only [Int.toNat_natCast]
    refine ⟨Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left x y),
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right x y), fun d hx hy => ?_⟩
    have both := Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hx) (Int.natAbs_dvd_natAbs.mpr hy)
    exact Int.natAbs_dvd_natAbs.mp (by simpa using both)

theorem checked_contract : GcdContract checked := by
  intro a b
  have same : checked a b =
      if a < 0 ∨ b < 0 then none else some (Nat.gcd a.toNat b.toNat) := by
    simp only [checked, euclid_correct]
  rw [same]
  exact natGcd_spec a b
-- END VERBATIM
end GcdReference

namespace FactorialReference
-- BEGIN VERBATIM tests/reference/factorial-reference.lean 47-76
-- The contract of lf-factorial, in the style of `ClampContract` (clamp.lean).
-- `FactorialSpec limit n r`: `r` is a right answer for the input `n` when
-- `limit` is the largest cell, namely no result for a negative n or when n!
-- exceeds the limit, and n! otherwise. tests/reference/program-ir.lean copies
-- this block and proves that the word's IR meets the same clauses.
def FactorialSpec (limit : Nat) (n : Int) (r : Option Nat) : Prop :=
  (n < 0 → r = none) ∧
  (0 ≤ n → factorial n.toNat ≤ limit → r = some (factorial n.toNat)) ∧
  (0 ≤ n → limit < factorial n.toNat → r = none)

def FactorialContract (f : Nat → Int → Option Nat) : Prop :=
  ∀ (limit : Nat) (n : Int), FactorialSpec limit n (f limit n)

-- Rejecting negative inputs and factorials above the limit meets the clauses.
theorem guarded_spec (limit : Nat) (n : Int) :
    FactorialSpec limit n
      (if n < 0 then none else if factorial n.toNat ≤ limit then some (factorial n.toNat)
        else none) := by
  refine ⟨fun h => by simp [h], fun h fits => ?_, fun h over => ?_⟩
  · simp [Int.not_lt.mpr h, fits]
  · simp [Int.not_lt.mpr h, Nat.not_le.mpr over]

theorem checked_contract : FactorialContract checked := by
  intro limit n
  have same : checked limit n =
      if n < 0 then none else if factorial n.toNat ≤ limit then some (factorial n.toNat)
        else none := by
    simp only [checked, bounded_exact]
  rw [same]
  exact guarded_spec limit n
-- END VERBATIM
end FactorialReference

namespace ProgramIR

theorem Cells.fits_min (c : Cells) : c.Fits c.min := by
  have := c.two_le_half
  simp only [Cells.Fits, Cells.max, Cells.min]
  omega

theorem Cells.fits_max (c : Cells) : c.Fits c.max := by
  have := c.two_le_half
  simp only [Cells.Fits, Cells.max, Cells.min]
  omega

/-- A word meets a contract on given inputs (top first) when, for every stack
below them and every caller's return stack, it returns normally, keeps both,
and leaves the encoding of a result that satisfies `spec`. A failure of any
kind never meets a contract. -/
def Meets {α : Type} (c : Cells) (p : Program) (fuel : Nat) (name : String)
    (inputs : List Int) (enc : α → List Int) (spec : α → Prop) : Prop :=
  ∀ tail rs : List Int, ∃ r, callWord c p fuel name ⟨inputs ++ tail, rs⟩ =
    .next ⟨enc r ++ tail, rs⟩ ∧ spec r

-- The three words without loops follow from their correctness theorems in
-- Part 3 and the reference contracts.

/-- The contract of `lf-checked-add ( a b -- sum true | false )` for a program
`p`: the clauses of `CheckedAddSpec` for the cell's own bounds, given five
units of fuel and inputs that fit in a cell. -/
def CheckedAddWordContract (p : Program) : Prop :=
  ∀ (c : Cells) (fuel : Nat) (a b : Int), 5 ≤ fuel → c.Fits a → c.Fits b →
    Meets c p fuel "lf-checked-add" [b, a] encode
      (CheckedAddReference.CheckedAddSpec c.min c.max a b)

theorem checkedAdd_meets_contract : CheckedAddWordContract examplesProgram :=
  fun c fuel a b enough fa fb tail rs =>
    ⟨_, checkedAdd_correct c fuel a b tail rs enough fa fb,
      CheckedAddReference.checkedAdd_contract c.min c.max a b (Int.le_of_lt c.max_pos)
        c.min_eq fa fb⟩

/-- The contract of `lf-checked-abs ( n -- magnitude true | false )`. -/
def CheckedAbsWordContract (p : Program) : Prop :=
  ∀ (c : Cells) (fuel : Nat) (n : Int), 3 ≤ fuel → c.Fits n →
    Meets c p fuel "lf-checked-abs" [n] encode
      (ProgramExamplesReference.CheckedAbsSpec c.min c.max n)

theorem checkedAbs_meets_contract : CheckedAbsWordContract examplesProgram :=
  fun c fuel n enough fits tail rs =>
    ⟨_, checkedAbs_correct c fuel n tail rs enough fits,
      ProgramExamplesReference.checkedAbs_contract c.min c.max n (Int.le_of_lt c.max_pos)
        c.min_eq fits.1 fits.2⟩

/-- The contract of `lf-in-range ( value lower upper -- flag true | false )`,
for all integer inputs: the word does no arithmetic. -/
def InRangeWordContract (p : Program) : Prop :=
  ∀ (c : Cells) (fuel : Nat) (value lower upper : Int), 2 ≤ fuel →
    Meets c p fuel "lf-in-range" [upper, lower, value] encodeFlag
      (ProgramExamplesReference.InRangeSpec value lower upper)

theorem inRange_meets_contract : InRangeWordContract examplesProgram :=
  fun c fuel value lower upper enough tail rs =>
    ⟨_, inRange_correct c fuel value lower upper tail rs enough,
      ProgramExamplesReference.inRange_contract value lower upper⟩

/-- A loop invariant for `BEGIN test WHILE body REPEAT` followed by `rest`,
stated as a verification-condition generator would state it (total
correctness). From every state `s` satisfying `inv`, given at least
`need + measure s` units of fuel: the test returns normally with a flag on
top; if the flag is zero, `rest` gives a result satisfying `goal`; otherwise
the body either returns normally to a state satisfying `inv` with a smaller
`measure`, or stops, by EXIT or a failure, with a result satisfying `goal`.
`need` is the fuel that calls in the test, body and rest need beyond one unit
for each repetition still to come. -/
def LoopInvariant (c : Cells) (p : Program) (test body rest : List Instr)
    (inv : State → Prop) (measure : State → Nat) (need : Nat) (goal : Result → Prop) :
    Prop :=
  ∀ fuel s, inv s → need + measure s ≤ fuel →
    ∃ f d r, run c p fuel test s = .next ⟨f :: d, r⟩ ∧
      (f = 0 → goal (run c p fuel rest ⟨d, r⟩)) ∧
      (f ≠ 0 → match run c p fuel body ⟨d, r⟩ with
        | .next s' => inv s' ∧ measure s' < measure s
        | other => goal other)

/-- The loop rule: from a state satisfying a loop invariant, the loop and the
rest of its block give a result satisfying the invariant's goal, with one unit
of fuel for each repetition. -/
theorem loop_rule {c : Cells} {p : Program} {test body rest : List Instr}
    {inv : State → Prop} {measure : State → Nat} {need : Nat} {goal : Result → Prop}
    (h : LoopInvariant c p test body rest inv measure need goal) :
    ∀ fuel s, inv s → need + measure s + 1 ≤ fuel →
      goal (run c p fuel (.loop test body :: rest) s) := by
  intro fuel
  induction fuel with
  | zero => intro s _ enough; omega
  | succ f ih =>
    intro s holds enough
    obtain ⟨flag, d, r, tested, stop, again⟩ := h (f + 1) s holds (by omega)
    rw [run_loop, tested]
    by_cases zero : flag = 0
    · simp only [zero, ↓reduceIte]
      exact stop zero
    · simp only [zero, ↓reduceIte]
      have next := again zero
      cases ran : run c p (f + 1) body ⟨d, r⟩ with
      | next s' =>
        rw [ran] at next
        exact ih s' next.1 (by omega)
      | exited s' => rw [ran] at next; exact next
      | failed e => rw [ran] at next; exact next

/-- The top cell as a natural number, 0 if it is negative or missing: the
measure of both loops. -/
def topNat : State → Nat
  | ⟨x :: _, _⟩ => x.toNat
  | ⟨[], _⟩ => 0

-- lf-euclid: `BEGIN DUP 0<> WHILE TUCK MOD REPEAT DROP`.

/-- Euclid's loop keeps two naturals, `b` on top of `a`, whose greatest common
divisor is that of the inputs `a0 b0`; below them the caller's cells `d`. -/
def euclidInv (a0 b0 : Nat) (d r : List Int) (s : State) : Prop :=
  ∃ a b : Nat, s = ⟨(b : Int) :: (a : Int) :: d, r⟩ ∧ Nat.gcd a b = Nat.gcd a0 b0

theorem euclid_invariant (c : Cells) (a0 b0 : Nat) (d r : List Int) :
    LoopInvariant c examplesProgram [.prim .dup, .prim .zeroNe] [.prim .tuck, .prim .mod]
      [.prim .drop] (euclidInv a0 b0 d r) topNat 0
      (· = .next ⟨(Nat.gcd a0 b0 : Int) :: d, r⟩) := by
  intro fuel s ⟨a, b, same, keeps⟩ _
  subst same
  refine ⟨flag ((b : Int) != 0), (b : Int) :: (a : Int) :: d, r, by ir_simp, ?_, ?_⟩
  · intro zero
    have : b = 0 := by simp [flag] at zero; omega
    subst this
    ir_simp
    simp [← keeps]
  · intro nonzero
    have positive : 0 < b := by
      cases b with
      | zero => simp [flag] at nonzero
      | succ b => omega
    have operands : (0 : Int) ≤ a ∧ (0 : Int) < b := by omega
    ir_simp
    simp only [operands, and_self, ↓reduceIte]
    refine ⟨⟨b, a % b, by simp [Int.natCast_emod], ?_⟩, ?_⟩
    · rw [← keeps, Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]
    · simp only [topNat]
      have := Nat.mod_lt a positive
      omega

/-- Euclid's loop, by its invariant: it leaves Lean's `Nat.gcd` of its
inputs, given one unit of fuel more than the smaller input. -/
theorem euclid_by_invariant (c : Cells) (fuel a b : Nat) (d r : List Int)
    (enough : b + 1 ≤ fuel) :
    run c examplesProgram fuel euclidBody ⟨(b : Int) :: (a : Int) :: d, r⟩ =
      .next ⟨(Nat.gcd a b : Int) :: d, r⟩ :=
  loop_rule (euclid_invariant c a b d r) fuel _ ⟨a, b, rfl, rfl⟩
    (by simp only [topNat, Int.toNat_natCast]; omega)

theorem gcd_returns_by_invariant (c : Cells) (fuel : Nat) (a b : Int) (d : List Int)
    (enough : b.toNat + 2 ≤ fuel) :
    (run c examplesProgram fuel gcdBody ⟨b :: a :: d, []⟩).returned =
      some (encodeNat (if a < 0 ∨ b < 0 then none else some (Nat.gcd a.toNat b.toNat)) ++ d) := by
  simp only [gcdBody]
  ir_simp
  by_cases negative : a < 0 ∨ b < 0
  · have test : (decide (b < 0) || decide (a < 0)) = true := by simp; omega
    simp only [test, negative, ↓reduceIte]
    simp [Result.returned, encodeNat]
  · have test : (decide (b < 0) || decide (a < 0)) = false := by simp; omega
    simp only [test, negative, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨a, rfl⟩ : ∃ n : Nat, a = n := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    obtain ⟨b, rfl⟩ : ∃ n : Nat, b = n := ⟨b.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    simp only [Int.toNat_natCast] at enough ⊢
    rw [run_call_word c examplesProgram lookup_euclid
      (by rw [euclid_by_invariant c (fuel - 1) a b d [] (by omega)]; rfl) (by omega)]
    ir_simp
    simp [Result.returned, encodeNat]

/-- The contract of `lf-gcd ( a b -- gcd true | false )`, for all integer
inputs, given three units of fuel more than `b`. -/
def GcdWordContract (p : Program) : Prop :=
  ∀ (c : Cells) (fuel : Nat) (a b : Int), b.toNat + 3 ≤ fuel →
    Meets c p fuel "lf-gcd" [b, a] encodeNat (GcdReference.GcdSpec a b)

theorem gcd_meets_contract : GcdWordContract examplesProgram :=
  fun c fuel a b enough tail rs =>
    ⟨_, callWord_of_returns lookup_gcd (gcd_returns_by_invariant c _ a b tail (by omega))
      (by omega), GcdReference.natGcd_spec a b⟩

-- lf-factorial-from: `BEGIN DUP 1 > WHILE 2DUP lf-product-over? IF 2DROP FALSE
-- EXIT THEN TUCK * SWAP 1- REPEAT DROP TRUE`.

/-- The loop of lf-factorial-from keeps a counter `k` on top of a product `q`,
with 1 ≤ q, q and k in the cell, and q * k! equal to `total`, which is
q * k! of its inputs; below them the caller's cells `d`. -/
def factorialInv (c : Cells) (total : Int) (d r : List Int) (s : State) : Prop :=
  ∃ (k : Nat) (q : Int), s = ⟨(k : Int) :: q :: d, r⟩ ∧ 1 ≤ q ∧ q ≤ c.max ∧
    (k : Int) ≤ c.max ∧ q * (FactorialReference.factorial k : Int) = total

/-- What the loop and the rest of lf-factorial-from give: `total` and true if
it fits in a cell, otherwise false through EXIT. -/
def factorialGoal (c : Cells) (total : Int) (d r : List Int) (res : Result) : Prop :=
  res = if total ≤ c.max then .next ⟨-1 :: total :: d, r⟩ else .exited ⟨0 :: d, r⟩

theorem factorial_le_one {k : Nat} (small : k ≤ 1) : FactorialReference.factorial k = 1 := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k => omega

theorem factorialFrom_invariant (c : Cells) (total : Int) (d r : List Int) :
    LoopInvariant c examplesProgram [.prim .dup, .lit 1, .prim .gt]
      [.prim .twoDup, .call "lf-product-over?", .ifElse [.prim .twoDrop, .prim .false, .exit] [],
       .prim .tuck, .prim .mul, .prim .swap, .prim .oneMinus]
      [.prim .drop, .prim .true] (factorialInv c total d r) topNat 0
      (factorialGoal c total d r) := by
  intro fuel s ⟨k, q, same, low, high, small, product⟩ enough
  subst same
  simp only [topNat, Int.toNat_natCast, Nat.zero_add] at enough
  refine ⟨flag (decide ((k : Int) > 1)), (k : Int) :: q :: d, r, by ir_simp, ?_, ?_⟩
  · intro zero
    have one : FactorialReference.factorial k = 1 :=
      factorial_le_one (by simp [flag] at zero; omega)
    ir_simp
    rw [one, Int.natCast_one, Int.mul_one] at product
    subst product
    simp [factorialGoal, high]
  · intro nonzero
    have two : 2 ≤ k := by simp [flag] at nonzero; omega
    ir_simp
    rw [run_call_word c examplesProgram lookup_productOver
      (productOver_returns c (fuel - 1) q (k : Int) _ (by omega) (by omega)) (by omega)]
    ir_simp
    have positive : (0 : Int) < (k : Int) := by omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have grows := le_mul_of_one_le (x := q * ((j + 1 : Nat) : Int))
      (y := (FactorialReference.factorial j : Int)) (Int.mul_nonneg (by omega) (by omega))
      (by have := FactorialReference.factorial_pos j; omega)
    rw [product_factorial_succ] at product
    by_cases over : q > c.max / ((j + 1 : Nat) : Int)
    · have exceeds : ¬(q * ((j + 1 : Nat) : Int) ≤ c.max) := fun fits =>
        absurd ((Int.le_ediv_iff_mul_le positive).mpr fits) (by omega)
      simp only [over, ↓reduceIte, factorialGoal, show ¬(total ≤ c.max) by omega]
    · have below : q * ((j + 1 : Nat) : Int) ≤ c.max :=
        (Int.le_ediv_iff_mul_le positive).mp (by omega)
      have atLeast := le_mul_of_one_le (x := q) (y := ((j + 1 : Nat) : Int)) (by omega) (by omega)
      have := c.max_pos
      simp only [over, ↓reduceIte]
      ir_simp
      rw [c.wrap_of_fits (x := q * ((j + 1 : Nat) : Int))
          (by simp only [Cells.Fits, c.min_eq]; omega),
        c.wrap_of_fits (x := ((j + 1 : Nat) : Int) - 1)
          (by simp only [Cells.Fits, c.min_eq]; omega),
        show ((j + 1 : Nat) : Int) - 1 = (j : Int) by omega]
      refine ⟨⟨j, q * ((j + 1 : Nat) : Int), rfl, by omega, below, by omega, product⟩, ?_⟩
      simp only [topNat, Int.toNat_natCast]
      omega

/-- The loop of lf-factorial-from, by its invariant: the same result as
`factorialFrom_run` in Part 3, given one unit of fuel more than `k`. -/
theorem factorialFrom_by_invariant (c : Cells) (fuel k : Nat) (q : Int) (d r : List Int)
    (enough : k + 1 ≤ fuel) (low : 1 ≤ q) (high : q ≤ c.max) (small : (k : Int) ≤ c.max) :
    run c examplesProgram fuel factorialFromBody ⟨(k : Int) :: q :: d, r⟩ =
      if q * (FactorialReference.factorial k : Int) ≤ c.max
      then .next ⟨-1 :: q * (FactorialReference.factorial k : Int) :: d, r⟩
      else .exited ⟨0 :: d, r⟩ :=
  loop_rule (factorialFrom_invariant c _ d r) fuel _ ⟨k, q, rfl, low, high, small, rfl⟩
    (by simp only [topNat, Int.toNat_natCast]; omega)

theorem factorial_returns_by_invariant (c : Cells) (fuel : Nat) (n : Int) (d : List Int)
    (enough : n.toNat + 2 ≤ fuel) (fits : c.Fits n) :
    (run c examplesProgram fuel factorialBody ⟨n :: d, []⟩).returned =
      some (encodeNat (if n < 0 then none
        else if FactorialReference.factorial n.toNat ≤ c.max.toNat
        then some (FactorialReference.factorial n.toNat) else none) ++ d) := by
  simp only [factorialBody]
  ir_simp
  by_cases negative : n < 0
  · simp only [negative, ↓reduceIte]
    simp [Result.returned, encodeNat]
  · simp only [negative, ↓reduceIte]
    obtain ⟨n, rfl⟩ : ∃ m : Nat, n = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    simp only [Int.toNat_natCast] at enough ⊢
    have := c.max_pos
    simp only [Cells.Fits] at fits
    have returns : (run c examplesProgram (fuel - 1) factorialFromBody
        ⟨(n : Int) :: 1 :: d, []⟩).returned =
        some ((if (FactorialReference.factorial n : Int) ≤ c.max
          then [-1, (FactorialReference.factorial n : Int)] else [0]) ++ d) := by
      rw [factorialFrom_by_invariant c (fuel - 1) n 1 d [] (by omega) (by omega) (by omega)
        (by omega)]
      simp only [Int.one_mul]
      by_cases small : (FactorialReference.factorial n : Int) ≤ c.max <;>
        simp only [small, ↓reduceIte, Result.returned, List.cons_append, List.nil_append]
    rw [run_call_word c examplesProgram lookup_factorialFrom returns (by omega)]
    by_cases small : (FactorialReference.factorial n : Int) ≤ c.max
    · have : FactorialReference.factorial n ≤ c.max.toNat := by omega
      simp [small, this, Result.returned, encodeNat]
    · have : ¬FactorialReference.factorial n ≤ c.max.toNat := by omega
      simp [small, this, Result.returned, encodeNat]

/-- The contract of `lf-factorial ( n -- factorial true | false )`, with the
largest cell as the limit, given three units of fuel more than `n` and an
input that fits in a cell. -/
def FactorialWordContract (p : Program) : Prop :=
  ∀ (c : Cells) (fuel : Nat) (n : Int), n.toNat + 3 ≤ fuel → c.Fits n →
    Meets c p fuel "lf-factorial" [n] encodeNat
      (FactorialReference.FactorialSpec c.max.toNat n)

theorem factorial_meets_contract : FactorialWordContract examplesProgram :=
  fun c fuel n enough fits tail rs =>
    ⟨_, callWord_of_returns lookup_factorial
      (factorial_returns_by_invariant c _ n tail (by omega) fits) (by omega),
      FactorialReference.guarded_spec c.max.toNat n⟩

-- Deliberately wrong programs, one for each word, are refuted: no program
-- meets a contract merely because the contracts are weak. Each is a
-- realistic mistake in the Forth source.

/-- `lf-checked-add` without its overflow test (`uncheckedAddProgram`
above): the largest cell plus 1 wraps to the smallest instead of failing. -/
theorem unchecked_add_violates_contract : ¬ CheckedAddWordContract uncheckedAddProgram := by
  intro claim
  have := cells64.max_pos
  obtain ⟨r, runs, spec⟩ := claim cells64 5 cells64.max 1 (by decide) cells64.fits_max
    cells64.fits_one [] []
  rw [spec.2 (by simp only [CheckedAddReference.inCell]; omega)] at runs
  simp [callWord, run_call, uncheckedAddProgram, lookup, run_prim, step, encode] at runs

/-- `lf-checked-abs` as Forth's ABS alone: the smallest cell gives true and a
negative "magnitude" instead of false. -/
def plainAbsProgram : Program := [("lf-checked-abs", .word [.prim .abs, .prim .true])]

theorem plain_abs_violates_contract : ¬ CheckedAbsWordContract plainAbsProgram := by
  intro claim
  obtain ⟨r, runs, spec⟩ := claim cells64 3 cells64.min (by decide) cells64.fits_min [] []
  rw [spec.1 rfl] at runs
  simp [callWord, run_call, plainAbsProgram, lookup, run_prim, step, encode] at runs

/-- `lf-in-range` without its test for reversed bounds: lower 1 above upper 0
gives true and a flag instead of false. -/
def unguardedInRangeProgram : Program :=
  [("lf-within-closed?", .word withinClosedBody),
   ("lf-in-range", .word [.call "lf-within-closed?", .prim .true])]

theorem unguarded_in_range_violates_contract :
    ¬ InRangeWordContract unguardedInRangeProgram := by
  intro claim
  obtain ⟨r, runs, spec⟩ := claim cells64 2 0 1 0 (by decide) [] []
  rw [spec.1 (by decide)] at runs
  simp [callWord, run_call, unguardedInRangeProgram, lookup, withinClosedBody, run_prim, step,
    encodeFlag] at runs

/-- `lf-gcd` that tests only its top input for a negative value: for -4 and 6
Euclid's loop reaches `-4 6 MOD`, which IR 0.1 does not model, instead of
answering false. -/
def gcdTopOnlyProgram : Program :=
  [("lf-euclid", .word euclidBody),
   ("lf-gcd", .word [.prim .dup, .prim .zeroLt,
     .ifElse [.prim .twoDrop, .prim .false] [.call "lf-euclid", .prim .true]])]

theorem gcd_top_only_violates_contract : ¬ GcdWordContract gcdTopOnlyProgram := by
  intro claim
  obtain ⟨r, runs, spec⟩ := claim cells64 9 (-4) 6 (by decide) [] []
  rw [spec.1 (by decide)] at runs
  simp [callWord, run_call, run_loop, gcdTopOnlyProgram, lookup, euclidBody, run_prim, run_if,
    step, flag, encodeNat] at runs

/-- A 16-bit cell, the smallest Forth-2012 allows. -/
def cells16 : Cells := ⟨16, by decide⟩

/-- `lf-factorial-from` without its overflow test: on 16-bit cells 8! = 40320
wraps to -25216, returned with true instead of false. -/
def wrappingFactorialProgram : Program :=
  [("lf-factorial-from", .word [.loop [.prim .dup, .lit 1, .prim .gt]
       [.prim .tuck, .prim .mul, .prim .swap, .prim .oneMinus], .prim .drop, .prim .true]),
   ("lf-factorial", .word factorialBody)]

theorem wrapping_factorial_violates_contract :
    ¬ FactorialWordContract wrappingFactorialProgram := by
  intro claim
  obtain ⟨r, runs, spec⟩ := claim cells16 11 8 (by decide)
    (by simp [Cells.Fits, cells16, Cells.min, Cells.max, Cells.half]) [] []
  rw [spec.2.2 (by decide) (by decide)] at runs
  simp [callWord, run_call, run_loop, wrappingFactorialProgram, lookup, factorialBody, run_prim,
    run_lit, Cells.fits_one, run_if, step, flag, encodeNat, cells16, Cells.wrap, Cells.min,
    Cells.half, Cells.modulus] at runs

-- The axioms each contract theorem uses; `make reference-program-ir` accepts
-- only Lean's propext, Classical.choice and Quot.sound here.
#print axioms CheckedAddReference.checkedAdd_contract
#print axioms ProgramExamplesReference.checkedAbs_contract
#print axioms ProgramExamplesReference.inRange_contract
#print axioms GcdReference.checked_contract
#print axioms FactorialReference.checked_contract
#print axioms checkedAdd_meets_contract
#print axioms checkedAbs_meets_contract
#print axioms inRange_meets_contract
#print axioms loop_rule
#print axioms euclid_by_invariant
#print axioms gcd_meets_contract
#print axioms factorialFrom_by_invariant
#print axioms factorial_meets_contract
#print axioms unchecked_add_violates_contract
#print axioms plain_abs_violates_contract
#print axioms unguarded_in_range_violates_contract
#print axioms gcd_top_only_violates_contract
#print axioms wrapping_factorial_violates_contract

end ProgramIR

-- Part 6. Well-formedness (ADR 0019, test plan 4; MiniForth's linker
-- idea): a decidable predicate on a program as the program words write it,
-- checked by `decide` on the three programs above and refuted on programs
-- no accepted source gives. A theorem that a well-formed program never
-- fails with `unknownWord` is a follow-up (ADR 0019).

namespace ProgramIR

mutual
/-- Every name an instruction calls, also inside IF and loops. -/
def Instr.calls : Instr → List String
  | .call name => [name]
  | .ifElse yes no => blockCalls yes ++ blockCalls no
  | .loop test body => blockCalls test ++ blockCalls body
  | _ => []

def blockCalls : List Instr → List String
  | [] => []
  | i :: rest => i.calls ++ blockCalls rest
end

def Def.body : Def → List Instr
  | .word b => b
  | .constant b => b

def Def.isConstant : Def → Bool
  | .constant _ => true
  | .word _ => false

/-- An instruction the program words keep before CONSTANT: a primitive
other than the return-stack words and the divisions, a literal or a call. -/
def Instr.straight : Instr → Bool
  | .prim p => !(p == .toR || p == .fromR || p == .rFetch || p == .div || p == .mod)
  | .lit _ | .call _ => true
  | _ => false

def definedIn (earlier : Program) (name : String) : Bool := earlier.any (·.1 == name)

def constantIn (earlier : Program) (name : String) : Bool :=
  earlier.any (fun e => e.1 == name && e.2.isConstant)

/-- A definition after `earlier`: a new name, calls only of earlier
definitions (so no recursion and no forward call), and for a constant a
straight-line body calling only earlier constants. -/
def defOk (earlier : Program) : String × Def → Bool
  | (name, d) =>
    !definedIn earlier name && (blockCalls d.body).all (definedIn earlier) &&
      match d with
      | .word _ => true
      | .constant b => b.all Instr.straight && (blockCalls b).all (constantIn earlier)

def wellFormedFrom (earlier : Program) : Program → Bool
  | [] => true
  | d :: rest => defOk earlier d && wellFormedFrom (earlier ++ [d]) rest

def WellFormed (p : Program) : Bool := wellFormedFrom [] p

theorem clamp_wellFormed : WellFormed clampProgram = true := by decide
theorem examples_wellFormed : WellFormed examplesProgram = true := by decide
theorem allPrimitives_wellFormed : WellFormed allPrimitivesProgram = true := by decide
theorem forward_call_not_wellFormed :
    WellFormed [("f", .word [.call "g"]), ("g", .word [])] = false := by decide
theorem recursion_not_wellFormed :
    WellFormed [("f", .word [.ifElse [.call "f"] []])] = false := by decide
theorem redefinition_not_wellFormed :
    WellFormed [("f", .word []), ("g", .word [.call "f"]), ("f", .word [])] = false := by
  decide
theorem constant_calling_word_not_wellFormed :
    WellFormed [("f", .word []), ("k", .constant [.call "f"])] = false := by decide
theorem constant_with_if_not_wellFormed :
    WellFormed [("k", .constant [.lit 1, .ifElse [] []])] = false := by decide

#print axioms clamp_wellFormed
#print axioms examples_wellFormed
#print axioms allPrimitives_wellFormed
#print axioms forward_call_not_wellFormed
#print axioms recursion_not_wellFormed
#print axioms redefinition_not_wellFormed
#print axioms constant_calling_word_not_wellFormed
#print axioms constant_with_if_not_wellFormed

end ProgramIR

def main : IO Unit := ProgramIR.main
