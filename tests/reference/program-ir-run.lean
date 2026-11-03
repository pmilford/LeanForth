import Lean

/-
Lean's evaluation of the program IR model, version 0.1, for the three-way
comparison of task 2.5.4 (docs/programming/PROGRAM_IR_RUN.md). Untrusted:
it proves nothing; it runs the model's own `callWord` on concrete inputs so
that the Forth IR interpreter (src/program/ir-run.fs) and the host's own
execution of the source can be compared with the model's result.

Part 1 copies, verbatim, the model's definitions from
tests/reference/program-ir.lean: cells, primitives, instructions, `step`,
`run`, `callWord`, the six example words as IR terms, and the primitives'
names. `tests/program/ir_run_differential.py` (part of `make test`) checks
that every block between BEGIN VERBATIM and END VERBATIM equals the named
lines of that file, so the results below are the model's. The IR terms of
the six words are tied to the reader's output from the actual Forth source
by `make reference-program-ir`.

Part 2 reads cases `program word fuel x1 ... xn -> ...` (inputs bottom
first, as Forth writes them) from the file named on the command line and
prints each with the model's result on 64-bit cells: `ok` and the data
stack bottom first, or `fail` and the failure. The program is `clamp` or
`examples` (the copied terms) or the path of an IR text file, which a
small parser reads back into terms (used for randomly generated programs).
-/

namespace ProgramIR

-- Part 1. The model, copied.
-- BEGIN VERBATIM tests/reference/program-ir.lean 187-265
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
-- END VERBATIM

-- BEGIN VERBATIM tests/reference/program-ir.lean 267-437
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
-- END VERBATIM

-- BEGIN VERBATIM tests/reference/program-ir.lean 581-646
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
-- END VERBATIM

-- BEGIN VERBATIM tests/reference/program-ir.lean 1215-1227
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
-- END VERBATIM

end ProgramIR

-- Part 2. Lean's evaluation of the model on given cases.

namespace ProgramIRRun
open ProgramIR

/-- The development host's cells: 64 bits. -/
def cells64 : Cells := ⟨64, by decide⟩

/-- Every primitive, in the order of `Prim`. -/
def allPrims : List Prim :=
  [.dup, .drop, .swap, .over, .nip, .tuck, .rot, .twoDup, .twoDrop, .toR, .fromR, .rFetch,
   .add, .sub, .mul, .div, .mod, .negate, .abs, .onePlus, .oneMinus,
   .eq, .ne, .lt, .gt, .zeroEq, .zeroNe, .zeroLt, .zeroGt,
   .and, .or, .xor, .invert, .rshift, .max, .min, .true, .false]

def primNamed (word : String) : Option Prim := allPrims.find? (fun p => p.word == word)

/-- The tokens of a line of the text form, without indentation or location. -/
def tokens (line : String) : List String :=
  let ws := (line.splitOn " ").filter (· ≠ "")
  match ws.getLast? with
  | some w => if w.startsWith "@" then ws.dropLast else ws
  | none => []

/-- The IR text form read back into terms. The structure comes from the
keywords; indentation and locations are ignored. Untrusted, like any
reader: a mistake here can only make Lean's results differ from the Forth
interpreter's, which the comparison reports.

This parser accepts more than the text form and the Forth loader do: any
indentation, repeated spaces, blank lines, a last token that starts with
`@` but is no location `@line:column`, an empty source path, and literals
as `String.toInt?` reads them, which includes digits grouped by
underscores (`1_000` is 1000). The loader refuses all of these. That direction is safe: text the loader
refuses stops the Forth run (tests/program/ir-run-cases.fs), so it can
never count as agreement, and the generator writes none of it. Leading
zeros (`007`, `-0001`) are read alike by both, as the same number. -/
partial def parseBlock : List (List String) → Except String (List Instr × List (List String))
  | [] => .ok ([], [])
  | line :: rest =>
    let more (i : Instr) (r : List (List String)) : Except String (List Instr × List (List String)) := do
      let (is, r') ← parseBlock r
      pure (i :: is, r')
    match line with
    | ["prim", w] => match primNamed w with
      | some p => more (.prim p) rest
      | none => .error s!"unknown primitive: {w}"
    | ["lit", n] => match n.toInt? with
      | some v => more (.lit v) rest
      | none => .error s!"bad literal: {n}"
    | ["call", name] => more (.call name) rest
    | ["exit"] => more .exit rest
    | ["if"] => do
      let (yes, r1) ← parseBlock rest
      match r1 with
      | ["else"] :: r2 => do
        let (no, r3) ← parseBlock r2
        match r3 with
        | ["then"] :: r4 => more (.ifElse yes no) r4
        | _ => .error "IF ... ELSE without THEN"
      | ["then"] :: r2 => more (.ifElse yes []) r2
      | _ => .error "IF without THEN"
    | ["begin"] => do
      let (test, r1) ← parseBlock rest
      match r1 with
      | ["while"] :: r2 => do
        let (body, r3) ← parseBlock r2
        match r3 with
        | ["repeat"] :: r4 => more (.loop test body) r4
        | _ => .error "BEGIN ... WHILE without REPEAT"
      | _ => .error "BEGIN without WHILE"
    | _ => .ok ([], line :: rest)

partial def parseDefs : List (List String) → Except String Program
  | [] => .ok []
  | [kind, name] :: rest => do
    let (body, r) ← parseBlock rest
    let d ← match kind with
      | "word" => pure (Def.word body)
      | "constant" => pure (Def.constant body)
      | _ => .error s!"not a definition: {kind}"
    match r with
    | ["end"] :: r2 => do
      let ds ← parseDefs r2
      pure ((name, d) :: ds)
    | _ => .error s!"definition {name} not closed"
  | line :: _ => .error s!"unexpected line: {line}"

def parseProgram (text : String) : Except String Program :=
  match (text.splitOn "\n").filter (· ≠ "") with
  | version :: source :: rest =>
    if version == "lf-ir " ++ irVersion && source.startsWith "source " then
      parseDefs (rest.map tokens)
    else .error "not IR 0.1 text"
  | _ => .error "not IR 0.1 text"

def failureName : Failure → String
  | .underflow => "underflow"
  | .unmodeled => "unmodeled"
  | .unbalanced => "unbalanced"
  | .unknownWord => "unknownWord"
  | .badConstant => "badConstant"
  | .outOfFuel => "outOfFuel"

/-- A stack, bottom first as Forth prints it; the model keeps the top first. -/
def showStack (d : List Int) : String :=
  String.join (d.reverse.map (fun x => " " ++ toString x))

/-- `callWord` starts from an empty return stack, so a normal end has one. -/
def showResult : Result → String
  | .next ⟨d, []⟩ => "ok" ++ showStack d
  | .next _ => "returns-left"
  | .exited _ => "exited"
  | .failed f => "fail " ++ failureName f

/-- The program a case names: `clamp` and `examples` are the copied terms,
anything else the path of an IR text file. -/
def programFor (name : String) : IO Program := do
  match name with
  | "clamp" => pure clampProgram
  | "examples" => pure examplesProgram
  | path => match parseProgram (← IO.FS.readFile path) with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"{path}: {e}")

def parseInt (token : String) : IO Int :=
  match token.toInt? with
  | some n => pure n
  | none => throw (IO.userError s!"not an integer: {token}")

/-- One case, `program word fuel x1 ... xn -> ...` with the inputs bottom
first: the same line with the model's result after the arrow. -/
def evalCase (line : String) : IO String := do
  match line.splitOn " -> " with
  | [args, _] =>
    match args.splitOn " " with
    | program :: word :: fuel :: inputs =>
      let p ← programFor program
      let some f := fuel.toNat? | throw (IO.userError s!"bad fuel: {fuel}")
      let xs ← inputs.mapM parseInt
      pure (args ++ " -> " ++ showResult (callWord cells64 p f word ⟨xs.reverse, []⟩))
    | _ => throw (IO.userError s!"bad case: {line}")
  | _ => throw (IO.userError s!"bad case: {line}")

end ProgramIRRun

/-- `lean --run tests/reference/program-ir-run.lean CASES`: print every case
of the file CASES with the model's result; fail on the first bad line. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    for line in ← IO.FS.lines path do
      IO.println (← ProgramIRRun.evalCase line)
    return 0
  | _ => IO.eprintln "usage: lean --run tests/reference/program-ir-run.lean CASES"; return 1
