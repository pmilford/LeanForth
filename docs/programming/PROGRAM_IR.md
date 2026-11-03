# Program IR, version 0.1

**Status: implemented and untrusted (2026-11-02, tasks 2.5.2 and 2.5.3 of
the [plan draft](../project/PLAN_DRAFT.md)).** The IR's semantics is a Lean
model, checked by Lean, not by LeanForth. The reader that turns Forth
source into IR is ordinary, unverified Forth.

The verified-program track needs an exact, small description of what a
Forth word does, between its source text and the proof obligations about
it:

```text
Forth source ──reader──▶ IR ──(2.5.5) obligations──▶ proofs ──▶ receipt
 src/program/*.fs        text form, Lean model           checked by Lean now, LeanForth later
```

IR 0.1 covers straight-line words with `IF`/`ELSE`/`THEN`, `EXIT`, signed
cells, explicit failure and source locations, as planned, and also
`BEGIN`/`WHILE`/`REPEAT` loops, so that all six example words translate
(see "Loops" below).

## One example in four forms

`lf-clamp` from [`src/program/clamp.fs`](../../src/program/clamp.fs).

**Mathematics.** For integers v, l, u: if l ≤ u the word returns
r = min(max(v, l), u) and *true*, so l ≤ r ≤ u, r = v when l ≤ v ≤ u,
r = l when v < l and r = u when v > u; if l > u it returns *false*. Cells
below the three inputs are untouched.

**Forth** (lines 12–14):

```forth
: lf-clamp ( value lower upper -- result true | false )
  2dup > if 2drop drop false exit then
  >r max r> min true ;
```

**IR text**, as the reader writes it ([`tests/program/ir/clamp.ir`](../../tests/program/ir/clamp.ir));
`@line:column` is where each token stands in the source:

```text
lf-ir 0.1
source src/program/clamp.fs
word lf-clamp @12:1
  prim 2dup @13:3
  prim > @13:8
  if @13:10
    prim 2drop @13:13
    prim drop @13:19
    prim false @13:24
    exit @13:30
  then @13:35
  prim >r @14:3
  prim max @14:6
  prim r> @14:10
  prim min @14:13
  prim true @14:17
end @14:22
```

**Lean** ([`tests/reference/program-ir.lean`](../../tests/reference/program-ir.lean)):
the same word as a term, and the theorem about it. `clamp` is the reference
model of `tests/reference/clamp.lean`, copied verbatim.

```lean
def clampBody : List Instr :=
  [prim .twoDup, prim .gt, ifElse [prim .twoDrop, prim .drop, prim .false, exit] [],
   prim .toR, prim .max, prim .fromR, prim .min, prim .true]

theorem clamp_correct (c : Cells) (fuel : Nat) (lower upper value : Int) (tail rs : List Int)
    (enough : 1 ≤ fuel) :
    callWord c clampProgram fuel "lf-clamp" ⟨upper :: lower :: value :: tail, rs⟩ =
      .next ⟨(if lower > upper then [0] else [-1, clamp lower upper value]) ++ tail, rs⟩
```

Stacks are lists with the top first, so `upper :: lower :: value :: tail`
is `value lower upper` in Forth order. `make reference-program-ir` checks
that the IR Lean prints for `clampProgram` is the reader's output with the
locations removed, so the theorem is about the IR the reader produced from
the actual source.

## Abstract syntax

A **program** is the list of definitions of one source file, in order. A
**definition** is a *word* (`: name … ;`) or a *constant*
(`… constant name`), each with a body. A **body** is a list of
instructions:

| Instruction | Forth | Meaning |
| --- | --- | --- |
| `prim p` | one of the 38 primitives below | one step on the stacks |
| `lit n` | a decimal literal | push n (a value outside the cell is *unmodeled*) |
| `call name` | an earlier definition | run it (a constant pushes its value) |
| `if` *yes* `else` *no* `then` | `IF … ELSE … THEN` | pop a flag; nonzero runs *yes*, zero runs *no* (empty without `ELSE`) |
| `begin` *test* `while` *body* `repeat` | `BEGIN … WHILE … REPEAT` | run *test*, pop a flag, stop on zero, else run *body* and repeat |
| `exit` | `EXIT` | leave the current word |

Primitives, with Forth-2012 stack effects (the top is on the right):

| Group | Words |
| --- | --- |
| Stack | `dup drop swap over nip tuck rot 2dup 2drop` |
| Return stack | `>r r> r@` |
| Arithmetic (wraps) | `+ - * negate abs 1+ 1-` |
| Division | `/ mod` |
| Comparison (flags) | `= <> < > 0= 0<> 0< 0>` |
| Bits | `and or xor invert rshift` |
| Other | `max min true false` |

## Semantics

The normative definition is `ProgramIR.run` in
`tests/reference/program-ir.lean`. In words:

- **Cells.** A cell has w ≥ 2 bits (Forth-2012 requires at least 16; the
  model allows fewer so that small cases can be checked exhaustively). A
  value is an integer from −2^(w−1) to 2^(w−1) − 1. `+ - * negate abs 1+ 1-`
  wrap in two's complement, so on 64-bit cells max + 1 is min. Bitwise
  words act on the two's-complement bit pattern.
- **Flags.** Comparisons give −1 for true and 0 for false; `IF` and `WHILE`
  treat any nonzero cell as true.
- **Return stack.** A called word starts with an empty return stack of its
  own and must leave it empty. It cannot see its caller's return-stack
  items, which on a real host hold return addresses.
- **Constants.** A constant's body runs on empty stacks and must leave
  exactly one value.
- **Not modeled.** `/` and `MOD` are defined only for a dividend ≥ 0 and a
  divisor > 0, where Forth-2012's floored and symmetric division agree;
  `RSHIFT` only for a shift below the cell width. Everything else about them
  is the failure *unmodeled*, not a guess.
- **Failures** are explicit results, never success: *underflow* (a missing
  data or return-stack item), *unmodeled*, *unbalanced* (a word returned
  with return-stack items), *unknownWord*, *badConstant*, *outOfFuel*.
- **Literals** must fit in a cell; the semantics gives a literal that does
  not the failure *unmodeled*. The reader writes only literals that fit in
  32 bits, so on cells of 32 bits or more every literal it writes fits.
- **Fuel** bounds the nesting depth of calls and the repetitions of each
  loop: a called word runs with one unit less than its caller, which
  continues with its own fuel afterwards, and each repetition of a loop
  leaves one unit less for the repetitions after it. So every run ends; the
  theorems state how much fuel suffices.
- **Outside the IR:** memory (`@`, `!`, `ALLOT`), I/O, return addresses,
  stack capacity (overflow), floating point, `DO` loops, `CASE`,
  `RECURSE`, defining words, and every word not listed above.

### Loops

The plan put loops into IR version 1 (task 4.4.1, "loops with invariants").
IR 0.1 already *executes* `BEGIN … WHILE … REPEAT`, with fuel, because
`lf-factorial` and `lf-gcd` need it and the reader task asks for all six
words. What waits for version 1 is reasoning about loops through
*invariants* in generated obligations; the two loop words below are proved
by induction directly on the semantics instead.

## Text form

```text
program    = "lf-ir 0.1" NL "source " path NL { definition }
definition = ( "word " name | "constant " name ) [loc] NL { line } "end" [loc] NL
line       = indent ( "prim " word | "lit " integer | "call " name | "exit"
                    | "if" | "else" | "then" | "begin" | "while" | "repeat" ) [loc] NL
loc        = " @" line-number ":" column-number
integer    = [ "-" ] digit { digit }      (decimal)
```

An integer is read as the mathematical integer it denotes, so leading
zeros are allowed and change nothing (`-007` is −7). An integer outside
the cell is still well-formed text; running it is the failure
*unmodeled*. The reader itself always writes integers without leading
zeros.

Names (after `word`, `constant` and `call`) are written in lower case
whatever case the source uses, since Gforth finds names ignoring the case
of A–Z: `LF-CLAMP`, `Lf-Clamp` and `lf-clamp` are one word and give the
same IR. Indentation is two spaces per open structure: `else` and `while`
sit at the level of their `if` and `begin`, the lines they enclose one
level deeper. The reader writes a location on every line except the two header
lines: for `word` the location of `:`, for `constant` and its `end` that of
the constant's name, for `end` of a word that of `;`, otherwise the token's
own. Line and column count from 1. The Lean printer writes the same text
without locations. It writes `else` only when that branch is not empty,
while the reader writes it whenever the source has it, so `IF … ELSE THEN`
with an empty `ELSE` part prints differently but means the same.

## The reader

[`src/program/ir-reader.fs`](../../src/program/ir-reader.fs) translates a
source file into the text form:

```forth
' type-line s" src/program/clamp.fs" lf-ir-read-file  ( -- outcome )
```

`type-line ( c-addr u -- )` receives each output line. `lf-ir-start`,
`lf-ir-feed` and `lf-ir-finish` do the same for lines given one at a time,
and `lf-ir-reason` and `lf-ir-where` tell why and where it stopped. The
reader keeps its state in a record of the checker context
([per-task contexts](../development/FORTH_LIBRARY.md)), so each context
has its own reader; in a new context it is stopped until `lf-ir-start`:
`lf-ir-feed` then reads nothing and `lf-ir-finish` gives *invalid*
("reader not started").

It accepts colon definitions and constants made only of the IR's
primitives, control words, decimal literals and earlier definitions, with
`\` and `( )` comments and `DECIMAL`, in any mix of upper and lower case.
Everything else stops it with one diagnostic line such as

```text
unsupported @1:7: not a known word or 32-bit decimal: foo
```

and an outcome from `src/lib/outcome.fs`:

| Outcome | When |
| --- | --- |
| *unsupported* | an unknown word or a word outside IR 0.1 (`UNTIL`, `DO`, `@`, …); a literal of more than ten digits or beyond 2,147,483,647, or in any other number syntax (`$FF`, `#10`, `'a'`, `1.`, `1e`, `+5`, …); a control word or `>R`/`R>`/`R@` outside a definition, or `CONSTANT`/`DECIMAL` inside one; `/` or `MOD` before `CONSTANT`; a second `WHILE` in one loop; a recursive call; a redefinition of a word the reader knows (also in another case, such as `: Dup … ;`); a name over 31 characters; a `(` comment not closed on its line; a character outside printable ASCII, a space or a tab anywhere on a line, comments included (a CR just before an LF ends the line and is not part of it); tokens before `CONSTANT` that do not leave exactly one value, or take values the file did not give, `CONSTANT` with nothing before it included; values left outside a definition |
| *invalid* | unbalanced `IF`/`ELSE`/`THEN`/`BEGIN`/`WHILE`/`REPEAT`; `:` inside a definition; `:` or `CONSTANT` without its name on the same line; a definition not closed at the end; an unreadable file or a line of 128 characters or more, not counting its line end; `lf-ir-feed` or `lf-ir-finish` before `lf-ir-start` |
| *full* | more than 32 definitions, 8 open structures or 8 tokens before `CONSTANT`, or an output line over 96 characters (a `source` path of 90 characters or more does not fit its header line) |

Lines written before a diagnostic are incomplete and must not be used.
If the output word throws, the exception passes to the caller; a file
being read is closed first. `lf-ir-feed` copies each line before reading
it, so the line may be in a transient buffer.

**It accepts less than Gforth, never more,** and gives what it accepts
Gforth's meaning (checked on Gforth 1.0.0 and 0.7.3):

- *Lines and tokens.* The reader splits a file into lines itself, at LF
  only: it opens the file as binary and reads it in blocks with
  `READ-FILE`, not with the host's `READ-LINE`, drops one CR just before
  an LF (both hosts drop it) and reads a last line without LF too. It
  splits each line into tokens at
  spaces and tabs, as both hosts do. The hosts also split at some other
  control characters (form feed, vertical tab) but not at others (DEL),
  end a line at a lone carriage return, and may treat bytes of 128 or
  more as parts of characters. To depend on none of that, a line holding
  any character other than printable ASCII (`!` to `~`), a space or a tab
  is refused, comments included, and the diagnostic never contains the
  character; so is any CR not just before an LF (a lone CR, CR CR LF, a
  CR at the end of the file). A line of 128 characters or more, not
  counting its LF and that CR, is refused. Nothing is handed to Gforth's
  interpreter: no source token is ever executed, whatever the caller's
  `STATE`, `BASE` or search order (tests feed it `bye`, and `[ 1 throw ]`
  from inside a definition being compiled).
- *Names* are found ignoring the case of A–Z, and only of A–Z, as Gforth
  finds them, so `DUP`, `Dup` and `dup` are the primitive `dup` and a word
  defined as `Clamp` is found as `clamp` or `CLAMP`. A definition or
  constant whose name, so folded, the reader already knows (an IR word,
  one of the other standard words it lists, such as `DO` or `@`, or an
  earlier definition of the file) is refused as a redefinition:
  `: True 0 ;` would otherwise change what a later `TRUE` means to Gforth
  but not to the IR. A word is not visible inside its own definition
  (Gforth hides it until `;`), so a recursive call is refused. A name
  that reads as a number, such as `5`, `-0`, `1e` or `$10`, is a name like
  any other: a token the file defined is a call (Gforth, too, finds a
  name before it reads a number), any other token a literal or refused.
- *Host words.* Other names the host defines, such as `.` or `DEPTH`, may
  be defined by the file. Its IR is unaffected, since the reader refuses
  every use of a word it does not know, but Gforth then uses the file's
  definition in anything compiled after the file in the same session. So
  the file must be loaded last: code compiled after it, such as a test
  harness, must use no name the file defines other than the words under
  test. Receipts state this in their `trusted-reader` assumption. Refusing
  every name the reading Gforth already defines (with `SEARCH-WORDLIST`)
  was rejected: it would refuse names the reading session itself defines,
  such as `lf-clamp` in `tests/program/ir-run-table.fs`, which loads the
  examples before reading them, and names such as `g`, which Gforth 1.0
  defines and 0.7.3 does not, so the same file would be accepted on one
  host and refused on the other; and it still could not see the words of
  the other Gforth version.
- *Literals* are an optional minus sign and one to ten decimal digits, at
  most 2,147,483,647 in size, so the same source suits 32-bit cells and a
  long literal cannot wrap to a small value. No other number syntax is
  accepted. Neither host defines a word whose name reads as such a
  literal, which Gforth would find before the number: `make test` checks
  every name of the default search order on the Gforth it runs
  (`tests/program/ir-reader.fs`; on a fresh Gforth that is 6,959 names on
  1.0.0 and 3,699 on 0.7.3, a word list that appears twice in the order
  counted twice).
- *Constants.* The tokens before `CONSTANT` must leave exactly one value,
  counted with each primitive's stack effect, and take none that the file
  did not give; Gforth would silently leave or take the rest. `>R`, `R>`
  and `R@` are refused outside definitions, and so are `/` and `MOD`:
  Gforth runs the tokens before `CONSTANT` while it loads the file, and a
  division by zero, or of the smallest cell by −1, stops the load there
  (`THROW` −10 or −11 on both hosts, so later definitions do not exist),
  whereas the IR runs a constant's body only when the constant is called.
  No other primitive can stop the load: shifts by any count and wrapping
  arithmetic give a value on both hosts (where the IR leaves that value
  unmodeled, calling the constant fails in the model, so nothing about it
  can be proved), and the counting above rules out underflow.
- *Structure.* `:` and `CONSTANT` must have their name on the same line,
  as Gforth requires, and a loop has at most one `WHILE` (Forth-2012 allows
  more, each closed by a `THEN` after `REPEAT`).

Nothing in the reader can check how Gforth is started: the source must be
loaded with `BASE` ten, Gforth's default search order and compilation word
list, and Gforth's own definitions of the standard words, as Gforth has
them when it starts, and last (see *Host words*). The IR's numbers are
written in decimal whatever `BASE` is.

How this is tested: every source the reader tests accept is also loaded by
Gforth itself, which must neither throw nor leave values (the fed lines
evaluated one by one, the three golden fixtures with `INCLUDE-FILE`, each
into a word list of its own), and the words that read as numbers return
on the host what their IR says. `tests/program/ir_reader_files.py` writes
files with every kind of line end (LF, CRLF, a lone CR, CR CR LF, a CR at
the end, no final LF, lines of 127 and 128 characters, a CR at the end of
the reader's first block), runs the reader on each, and has a fresh Gforth
load every accepted file and the fixtures: the IR of a CRLF file equals
that of its LF twin, and the host gives each word the value its IR gives.
It also records why three files are refused: Gforth ends a line at a lone
CR, and stops loading at `1 0 /` (−10) and at the smallest cell divided by
−1 (−11) before `CONSTANT`.

The reader is trusted for the translation: nothing proves that the IR means
what the source means on the host. Receipts list it as the assumption
`trusted-reader` ([program receipts](PROGRAM_RECEIPTS.md)).

## What is proved, and what is not

In `tests/reference/program-ir.lean`, for every cell width w ≥ 2, every
stack below the inputs and every caller's return stack, given the fuel
shown, the IR of each word returns exactly the result of its existing
reference model, copied verbatim from that model's file:

| Word | Theorem | Reference model | Inputs | Fuel |
| --- | --- | --- | --- | --- |
| `lf-clamp` | `clamp_correct`, `clamp_matches_stack_model` | `clamp` (clamp.lean), `execute clampCode` (stack-clamp.lean) | any integers | 1 |
| `lf-checked-add` | `checkedAdd_correct` | `CheckedAddReference.checkedAdd` | fit in a cell | 5 |
| `lf-checked-abs` | `checkedAbs_correct` | `ProgramExamplesReference.checkedAbs` | fits in a cell | 3 |
| `lf-in-range` | `inRange_correct` | `ProgramExamplesReference.inRange` | any integers | 2 |
| `lf-gcd` | `gcd_correct` | `GcdReference.checked` | any integers | b + 3 |
| `lf-factorial` | `factorial_correct` | `FactorialReference.checked` with the largest cell as limit | fits in a cell | n + 4 |

These say more than the reference models alone: the IR's arithmetic wraps,
so `checkedAdd_correct` and `factorial_correct` also prove that no addition
or multiplication the words perform overflows, and that `lf-factorial`'s
descending product with its division test equals the ascending reference
product.

The file also proves that every failure outcome is reachable (underflow,
unmodeled division by zero and an unmodeled literal outside the cell, out
of fuel, unbalanced return stack, bad constant, unknown word), and refutes two deliberately wrong programs: clamp
with `MAX` and `MIN` exchanged, and checked add without its overflow test,
which on 64-bit cells wraps max + 1 to min. `make check-lean-sources`
forbids `sorry`, `native_decide` and axioms in the file, and
`make reference-program-ir` accepts each theorem only if it uses no axioms
beyond Lean's `propext`, `Classical.choice` and `Quot.sound` (all nine
report exactly these three).

`make test` checks that the copies of the reference models are verbatim.

Not established: that Gforth executes these words as the IR semantics says
(task 2.5.4 tests it, without proving it: an IR interpreter, the host and
Lean's evaluation of the model agree on 5,152 cases, see
[the IR interpreter](PROGRAM_IR_RUN.md)); that the reader's translation is
faithful (it is tested on the six words, every primitive, every
diagnostic and line ends of every kind, and the host loads everything the
tests accept, not proved); anything about stack overflow, the compiler or
other hosts; and anything checked by LeanForth.
The theorems are checked by Lean 4.35.0 and labelled *checked by the Lean
reference, not by LeanForth*.

What links the reader to the Lean model: `make reference-program-ir`
compares the IR Lean prints for the six words and for
[`tests/program/ir/all-primitives.fs`](../../tests/program/ir/all-primitives.fs),
which uses every primitive once, with the reader's golden output; and
`make test` checks that the reader's table of the 38 primitives spells
them as Lean's `Prim.word` does, in the order of `Prim`, each with the
data-stack effect Lean's `step` gives it.

## Versioning

The version string `0.1` appears in the text form's first line, in the
reader's output and in receipts (`program.ir.version`). Any change to the
syntax, the primitives or the semantics gives a new version; the Lean
model, the reader, its golden files and the receipt schema change together.

## Running the checks

```sh
make test-program-ir        # receipts, verbatim copies, reader tests and files (Gforth, Python)
make reference-program-ir   # the Lean model, its axioms, its IR against the reader's
```

Both are part of `make test` and `make check` respectively. Measured on
2026-11-02 (Ryzen 5 7600X, WSL2): `make reference-program-ir` takes about
4.7 s with Lean 4.35.0; the reader tests pass on Gforth 1.0.0 and 0.7.3.

Files: [`tests/reference/program-ir.lean`](../../tests/reference/program-ir.lean)
(model and proofs), [`src/program/ir-reader.fs`](../../src/program/ir-reader.fs)
(reader), [`tests/program/ir-reader.fs`](../../tests/program/ir-reader.fs)
(reader tests),
[`tests/program/ir_reader_files.py`](../../tests/program/ir_reader_files.py)
(files with every kind of line end, loaded by the host too),
[`tests/program/ir/`](../../tests/program/ir/) (golden IR, and the
all-primitives source),
[`tests/program/check_program_ir.py`](../../tests/program/check_program_ir.py)
(copies, axioms, the primitive table, Lean-versus-reader comparison).
