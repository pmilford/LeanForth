# One symbol, three places: `+`

The owner asked (2026-11-04): "we are going to end up with 3 definitions of
`+` ... it is a bit concerning". This page shows the three, side by side, in
mathematics, in LeanForth's Forth syntax and in Lean; what each one does at
the edge of a cell; and the theorem that connects them. It is accurate to
the files named below on the day it was written; nothing here is new
behaviour.

The short answer: the three `+` never share a name, and the one theorem
that says when they agree is checked. **Forth's `+` wraps around at the
cell size. The program track's model of it wraps the same way. Lean's
mathematical `+` never wraps.** A program is verified against a stated
contract about its *Forth* `+`, so an overflow shows up as a failed
contract, not as a silent change of meaning.

Words used here: a *cell* is the unit a Forth stack holds (64 bits on the
development host, Gforth 1.0 on Linux); *wrapping* means that a result too
large for the cell comes back around, so that the largest cell plus 1 is
the smallest cell (two's complement); the *program track* is the part of
LeanForth that checks Forth programs against Lean models of them (the
[program IR](../programming/PROGRAM_IR.md), [ADR 0019](../adr/0019-program-words-two-modes.md)).

## The three, in three forms

| | Mathematics | LeanForth / Forth syntax | Lean |
| --- | --- | --- | --- |
| **1. Forth's `+`**, the host word that programs run | $a \oplus b = ((a + b - m) \bmod 2^{n}) + m$ for a cell of $n$ bits, $m = -2^{n-1}$ | `9223372036854775807 1 + .` prints `-9223372036854775808` on this host | (Lean never runs the host: see 2) |
| **2. The program track's model of it**, the meaning the verifier gives the word `+` | the same $a \oplus b$ | the program words `: add ( a b -- sum ) + ;` read as IR `add` | `.add, ⟨b :: a :: d, r⟩ => .next ⟨c.wrap (a + b) :: d, r⟩` (never a bare `a + b`) |
| **3. Lean's mathematical `+`**, `HAdd.hAdd`, what a theorem says | $n + m$ in $\mathbb{N}$ or $\mathbb{Z}$: no cell, no bound | `HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $ instHAdd 0 ^ Nat $ instAddNat $ $ n $ m $` | `n + m` (the term `@HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) n m`) |

Where each comes from:

1. **The host.** `+` is the standard Forth word. On the host used for
   development, cells are 64 bits, and Forth does not check for overflow:
   the example in the table is the whole story of the largest cell plus 1.
2. **The model.** In
   [`tests/reference/program-ir.lean`](../../tests/reference/program-ir.lean)
   the cell is a record `Cells` (a bit width of at least two), and
   ```lean
   def wrap (x : Int) : Int := (x - c.min) % c.modulus + c.min
   ```
   is the cell value congruent to `x`. The IR primitive `add` (like `sub`,
   `mul`, `negate`, `abs`, `1+` and `1-`) is defined with `wrap`: it is
   `c.wrap (a + b)`, never a bare `a + b`. The `+` inside `wrap (a + b)` is
   place 3, Lean's addition of integers; the model is a Lean *function*
   that uses the mathematical sum and then folds it into the cell. That the
   model is the right one is evidence, not proof: the IR interpreter and the
   host's own execution of the example words are compared on every case
   (`tests/program/ir-run-table.fs`; with Lean, `tests/program/ir_run_differential.py
   --lean` gives the Lean model the same cases, and its evaluation must
   print the same lines).
3. **The mathematics.** `HAdd.hAdd` is Lean's generic addition; for `Nat`
   or `Int` it is exact. The statement `n + m = m + n` is the pinned
   authoring example
   [`tests/author/07-add-comm.lf`](../../tests/author/07-add-comm.lf), checked
   against Lean's own term by `make check`. The printer shows the kernel
   term as `Eq (HAdd.hAdd n m) (HAdd.hAdd m n)` today; showing it as
   `n + m` is notation, plan task 4.4.3 ([the term printer](TERM_PRINTER.md)).

## What happens at the edge

For a cell of $n$ bits with smallest value $m = -2^{n-1}$ and largest
$M = 2^{n-1} - 1$:

| Place | `M + 1` | `2 + 3` |
| --- | --- | --- |
| 1. Forth `+` | $m$ (wraps) | `5` |
| 2. the model `c.wrap (a + b)` | $m$ (wraps) | `5` |
| 3. Lean `+` on `Int` | $M + 1$ (exact, not in the cell) | `5` |

A program that must not overflow therefore *says so in its contract*. The
checked-add example ([`lf-checked-add`](../programming/PROGRAM_EXAMPLES.md),
reference
[`checked-add.lean`](../../tests/reference/checked-add.lean)) returns the
sum only when the exact sum fits the cell and otherwise returns no result;
the same word without its overflow test is *refuted* in Lean
(`unchecked_add_refuted`: on 64-bit cells it wraps `max + 1` to `min`).

## The bridge: when the three agree

The program track's theorem
`wrap_of_fits` (in `tests/reference/program-ir.lean`) says that wrapping
changes nothing when the value already fits:

| Mathematics | LeanForth / Forth | Lean |
| --- | --- | --- |
| if $m \le x \le M$ then $x$ wrapped is $x$; so if $m \le a + b \le M$, then $a \oplus b = a + b$ | `2 3 + .` prints `5`, the same number as $2 + 3$ | `theorem wrap_of_fits {x : Int} (h : c.Fits x) : c.wrap x = x` |

Every proof that a word's IR equals its reference model (for example
`checkedAdd_correct`: "the IR `lf-checked-add` equals `checkedAdd` for all
inputs that fit in a cell, and its additions never wrap") uses it at the
spot where a `+` of the program meets a `+` of the mathematics. The
conclusion for a reader: **when the exact sum of two cells fits a cell,
Forth's `+` computes the mathematical sum; when it does not, only the
program track's model, `wrap`, says what Forth does.**

## Why no word is shared

[ADR 0017 §16](../adr/0017-leanforth-syntax.md#16-forth-words-keep-their-forth-meaning)
decided that no LeanForth word reuses the name of a Forth-2012 word with
another meaning: `+`, `-`, `*`, `=`, `<`, `max` and the rest keep Forth's
meaning, and mathematics is written by its Lean names (`HAdd.hAdd`, `Eq`).
The reasons, in short:

- *The two meanings differ exactly where programs fail.* If one token
  meant both, a verified program's overflow cases would hide in the
  ambiguity.
- *A reader would need the search order to understand a token.* A line
  must mean the same wherever it is read.
- *It can be added later; it could not be taken back.* A `+` for
  mathematics in a theorem is a job for notation (the printer will show
  `n + m`, [plan task 4.4.3](../project/PLAN_DRAFT.md); today it prints
  `HAdd.hAdd n m`) and for editors, not for the grammar.

What is *not* done yet: the program track checks Forth programs against
contracts about their wrapping `+`, but a mathematical statement about a
program's result (a theorem stated with Lean's `+`) is connected to the
program by the model and `wrap_of_fits` as above, by hand for each program;
a general way to state and prove such a bridge for any word is later work
on the program track.
