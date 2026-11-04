# Program IR, version 0.1

**Status: implemented and untrusted (2026-11-02, tasks 2.5.2 and 2.5.3 of
the [plan draft](../project/PLAN_DRAFT.md)).** The IR's semantics is a Lean
model, checked by Lean, not by LeanForth. What turns Forth source into IR
is ordinary, unverified Forth: since 2026-11-03 the
[program words](#the-program-words-correctness-mode) of ADR 0019, which run
the source file in correctness mode, with today's [reader](#the-reader)
kept beside them as their test oracle until the [parser] gate. IR 0.2
is [planned](#planned-for-ir-02), not implemented.

The verified-program track needs an exact, small description of what a
Forth word does, between its source text and the proof obligations about
it:

```text
Forth source ──program words──▶ IR ──(2.5.5) obligations──▶ proofs ──▶ receipt
 src/program/*.fs (correctness   text form, Lean model           checked by Lean now,
 mode; run mode: include FILE)                                    LeanForth later
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

**IR text**, as the program words and the reader write it ([`tests/program/ir/clamp.ir`](../../tests/program/ir/clamp.ir));
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
*invariants* in generated obligations. In Lean, the two loop words are
proved both by induction directly on the semantics and through stated
loop invariants and a general loop rule
([contracts](#contracts-of-the-five-other-words) below).

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

## The program words: correctness mode

**Status: implemented and untrusted (2026-11-03), before the [parser]
gate**, following [ADR 0019](../adr/0019-program-words-two-modes.md) and the
owner's answers to it: one source file, two ways to load it. *Run mode* is
ordinary Forth, `include clamp.fs`. *Correctness mode* runs the same file,
unchanged, through Forth's own text interpreter, and each Forth word, instead
of running, performs its *verification semantics*: `DUP` writes `prim dup`,
`:` reads its name as Forth's `:` does and writes `word NAME`, `IF` writes
`if`, a word of the file writes `call NAME`, a plain decimal `lit n`.

```forth
s" src/program/clamp.fs" lf-verify-file   ( -- outcome )  \ the mode shift
s" src/program/clamp.fs" lf-alias-file    ( -- outcome )  \ the separate vocabulary
```

Each writes the clamp's IR above, byte for byte, one line at a time through
the output word `lf-verify-to ( xt -- )` chose (each line is typed by
default), and gives an outcome; `lf-verify-text ( c-addr u c-addr2 u2 --
outcome )` and `lf-alias-text` run lines of text named c-addr2 u2 in the
header, and `lf-verify-reason`, `lf-verify-where` and `lf-verify-message`
tell why and where the last run stopped. A diagnostic has the reader's form
(below) and its reason numbers, plus four: 27 "the host read a literal
differently from its text" (the separate vocabulary only), 28 "run while
Forth is compiling", 29 "a standard word redefined before the run" (the
mode shift only) and 30 "a name that reads as a number".

| Module | What it is |
| --- | --- |
| [`src/lib/text-run.fs`](../../src/lib/text-run.fs) | General library (helpers private, ADR 0010): the search order, compilation word list and `BASE` saved and restored, a whole file read as bytes into a buffer (full when it fills it), lines split at LF, the plain-text rule |
| [`src/program/verify-report.fs`](../../src/program/verify-report.fs) | The run record, the reasons (in the authoring layer's message format, `src/author/errors.fs`), output lines and diagnostics |
| [`src/program/verify-semantics.fs`](../../src/program/verify-semantics.fs) | The verification semantics: one table keyed by name, the actions of `:`, `;`, `CONSTANT`, `IF` … and the 38 primitives, definitions, frames, literals |
| [`src/program/verify-runner.fs`](../../src/program/verify-runner.fs) | The runner both designs share: lines, files read a block at a time, isolation, exceptions |
| [`src/program/verify.fs`](../../src/program/verify.fs) | **The mode shift** (ADR 0019 §9 (b2), the owner's primary design) |
| [`src/program/verify-alias.fs`](../../src/program/verify-alias.fs) | The separate vocabulary, kept working beside it with the same actions |

**The mode shift.** The words are Forth's own: `DUP` is `FORTH-WORDLIST`'s
`DUP`, and its verification semantics sit in a table beside it. The runner
evaluates each line behind one entry word, the only word visible, which
runs Forth-2012's text interpreter with a third state: take the next name
with `PARSE-NAME`; find it with `SEARCH-WORDLIST`, the file's own words
first, then `FORTH-WORDLIST`; perform its verification semantics; a name
not found must be a plain decimal, which the words read themselves. A host
word is known by its *identity*, the execution token its name had when the
words loaded, together with the name: so a standard word redefined after
the program words loaded and before the run is refused at that word. This
covers only the verifying session, and has two known limits, both tested:
a word redefined before the program words load is not noticed, and on
Gforth 0.7.3, which gives every compile-only word (`IF`, `THEN`, `;` …)
one shared token, neither is a compile-only word redefined after. Run mode
is another Forth, so a tampered host stays an assumption in any case. No
host word ever runs, and the host converts no number.

**The separate vocabulary.** LeanForth's own words named `dup`, `if`, `:`
… live in a word list of their own; with only that list and the file's
words in the search order, Forth's interpreter finds and runs them, and
each performs the same action. Forth also reads the numbers, and Gforth
1.0's recognizers read more forms (`"x"`, `->x`, `` `dup ``, `1e`), so each
word first checks the text since the previous one (the *gap*): only plain
decimals, each written as `lit n`, and the data stack grown by exactly
their values. It cannot see a standard word redefined before the run, nor
a host word named like a decimal, which the mode shift refuses.

**What they accept** is what the reader accepts (below): colon definitions
and constants made of IR 0.1's primitives, control words, plain decimals
and earlier definitions, with `\` and `( )` comments and `DECIMAL`, in any
case of letters; the same lines and characters and the same capacities,
with a file read a block at a time and no limit on its size. They differ
from the reader on purpose in four ways, from the owner's answers and ADR
0019 §2-§3:

- *Forth-2012's Core and Core Ext words are reserved:* one outside IR 0.1
  (`CELLS`, `S"`, `EVALUATE`, `HEX` …) is refused as "a Forth word outside
  IR 0.1" where the reader says "not a known word", and none may be
  defined by the file (`: . drop ;`, `: depth 0 ;`), which narrows the
  reader's caveat that the file must be loaded last to Gforth's own words.
- *Names that read as numbers are refused* (answer 4) in `:` and
  `CONSTANT`. After any leading signs and base prefixes (`+ - # $ % &`):
  a digit; Gforth 1.0's digit separator `_`; a quote and one more
  character (`'a'`, `-'a'`); after a prefix, a hexadecimal letter (`$10`,
  `-a`) or any letter before a digit or a point (`-k1`, `+M5`, which Gforth
  1.0 reads as floats with an SI prefix for the point); or a point before
  a digit, `_` or a prefixed hexadecimal letter (`.5`, `._`, `$.a`).
  `->x`, `"x"`, `x:dup` and `-rot` are names. A test checks the rule
  against the running Gforth: no token of one to three printable
  characters (all but `"`, `{` and `}`, which Gforth 1.0 reads as strings
  and environment names) that the host reads by itself in an empty search
  order may pass it; Gforth 1.0 reads 11,769 such tokens and 0.7.3 3,171.
- *A run started while Forth compiles is refused* before any line runs,
  where the reader, which runs nothing, did not care.
- *The mode shift refuses a standard word redefined before the run*, with
  the limits above.

**Isolation** (ADR 0019 §3). The caller's search order, compilation word
list and `BASE` are saved and given back however a run ends (a search
order of more than 16 word lists is refused as *full* before anything
changes); `BASE` is ten throughout; after each line `STATE` must be zero
and the data stack as deep as before (defence in depth: no input reaches
either check). Every `THROW` is caught: a run is the authoring program's
top level (ADR 0018) and gives only an outcome. A token that Forth's
interpreter cannot read (the separate vocabulary) is refused as unknown at
the first token after the checked text that is no plain decimal. An output
word that throws or leaves a cell fails the run as *invalid* ("output word
failed"); a run started by the output word in its own context aborts
(`THROW` −2) and changes nothing. One run at a time in each context.

**Not in the checker.** Correctness mode runs source text and grows the
dictionary (a word list per run, a word per definition), so like the
authoring layer it belongs in the authoring program (plan 8.2.1) and
`src/main.fs` does not load it. It shares the authoring layer's message
records and its reading of the invoking token back from `>IN`.

**Evidence** (`make test-program-verify`, Gforth 1.0.0 and 0.7.3,
2026-11-04, after review rvPW): the three golden files byte for byte in
both designs; 287 inputs through the reader and both designs (108 cases of
the reader's tests, 151 hostile inputs, 28 files: every kind of line end,
a file of 65,536 bytes ending in an LF with a redefinition after it,
which is refused, a file of about 400,000 bytes, and the golden sources),
on which the two designs write the same lines and give the same outcome,
reason, line and column on all 287, and differ from the reader only by the
four rules above (66 inputs), the 58 accepted ones loaded by plain Gforth
too; a round trip of the golden IR and of IR with awkward names (`->x`,
`"x"`, `forth:dup`, `-rot`, `a(b)`, 31 characters) printed back as Forth in
another layout; 400 random programs from a seed, a fifth with a planted
mistake, identical in all three but for one number name; the number-name
rule against the host's own reading of every short token; eight and nine
open structures; a search order too deep; the source file closed after an
accepted, a refused and an interrupted run; a context left free when a
run's preparation throws; each word with verification semantics redefined
in turn before a run, refused by the mode shift at that word; a
compile-only `IF` redefined after loading (refused on 1.0, the known limit
on 0.7.3); a host word named `7`; and 29 planted faults
(`tests/mutants/faults.toml`): 27 caught, and 2 listed as equivalent (the
`STATE` and depth checks after each line, which no input reaches). Review
rvPW's second round also compared the block reader with today's reader on
2,874 files whose features cross block edges, on both hosts: identical.
The clamp receipt's IR is now written by the mode shift
([receipts](PROGRAM_RECEIPTS.md)); recording its evidence hashes the source
before and after the run and keeps that hash, which the receipt's
`program.source.sha256` must equal.

## The reader

[`src/program/ir-reader.fs`](../../src/program/ir-reader.fs), today's
reader, is kept unchanged as the program words' test oracle until they
pass the [parser] gate (ADR 0019 §8), and then retires. It translates a
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
| *unsupported* | an unknown word or a word outside IR 0.1 (`UNTIL`, `DO`, `@`, …); a literal of more than ten digits or beyond 2,147,483,647, or in any other number syntax (`$FF`, `#10`, `'a'`, `1.`, `1e`, `+5`, …); a control word or `>R`/`R>`/`R@` outside a definition, or `CONSTANT`/`DECIMAL` inside one; `/` or `MOD` before `CONSTANT`; a second `WHILE` in one loop; a recursive call; a redefinition of a word the reader knows (also in another case, such as `: Dup … ;`); a name over 31 characters; a `(` comment not closed on its line; a character other than printable ASCII, a space or a tab anywhere on a line, comments included (a CR just before an LF ends the line and is not part of it); tokens before `CONSTANT` that do not leave exactly one value, or take values the file did not give, `CONSTANT` with nothing before it included; values left outside a definition |
| *invalid* | unbalanced `IF`/`ELSE`/`THEN`/`BEGIN`/`WHILE`/`REPEAT`; `:` inside a definition; `:` or `CONSTANT` without its name on the same line; a definition not closed at the end; an unreadable file (a directory, for example) or a line of 128 characters or more, not counting its line end; `lf-ir-feed` or `lf-ir-finish` before `lf-ir-start`; a line fed after `lf-ir-finish` ("reader already finished"); an output word that throws, calls a reader word in its own context, or returns with the data stack at another depth ("output word failed"); an exception that stops a reader word ("read stopped by an exception") |
| *full* | more than 32 definitions, 8 open structures or 8 tokens before `CONSTANT`, or an output line over 96 characters (a `source` path of 90 characters or more does not fit its header line) |

Lines written before a diagnostic or an exception are incomplete and must
not be used. `lf-ir-finish` ends a read: finishing again gives the same
outcome, and a line fed after it stops the reader as *invalid* and writes
nothing. `lf-ir-feed` copies each line before reading it, and
`lf-ir-start` and `lf-ir-read-file` copy the path before the output word
first runs, so a line or a path may be in a transient buffer, such as the
pictured-numeric one that an output word numbering its lines with `<# #>`
reuses. A fed line's length is unsigned, and a line of 128 characters or
more is refused without being copied or read, whatever its address.

The four *reader words*, `lf-ir-start`, `lf-ir-feed`, `lf-ir-finish` and
`lf-ir-read-file`, keep the reader of their context *busy* while they
run, and so while the output word runs; `lf-ir-reason` then gives "reader
busy". A reader word called while the reader of its context is busy
refuses: it aborts (`THROW` −2) and changes nothing but a count of calls.
So the output word must not use the reader of its own context (it may
use another context's), and must return normally, in the context it was
called in, having taken its two arguments and left nothing. If it
throws, calls a reader word in its own context (refused, whether or not
it catches the refusal), or returns with the data stack at another depth,
the read stops as *invalid* ("output word failed"); a change of depth
also aborts (`THROW` −2), and any exception passes on. If it returns in
another context, the reader aborts (`THROW` −2) at once, touching no
context's record, not even to switch back, since the output word may have
freed the context it left; the reader of that context stays busy for
good.

An exception that stops a reader word, such as `THROW` −28 from Ctrl-C
during a blocked `OPEN-FILE` or `READ-FILE`, stops the read as *invalid*
("read stopped by an exception") and passes on to the caller; a file
whose lines were being read is closed first. Should the exception come
just after the reader word made the reader busy but before its handler
is set up, or just after its work threw but before the handler has run,
the reader stays busy for good instead. A reader that stays busy refuses
every reader word in its context, so its read never ends; that context
must be freed (`context-free`), or for the main context Gforth
restarted, before it can read again.

**Threat model.** The reader defends against hostile *source files*:
whatever a file holds, the reader refuses it or gives IR that means what
Gforth does with the file (the rule below). Its caller and the output
word are *trusted* harness code, such as the receipt generator and the
tests, relied on to use the reader as this section says. Even so, the
reader enforces the following on them, and this is the whole list:

- *A busy reader refuses.* While a reader word runs, and so while its
  output word runs, every reader word called in the same context refuses
  (`THROW` −2), changing nothing but a count of calls. A single check at
  the start of every reader word does this.
- *A misbehaving output word fails the read.* The read ends *invalid*,
  never *ok*, if the output word throws, calls a reader word in its own
  context, or returns with the data stack at another depth. If it returns
  in another context, the reader of the context it was called in stays
  busy for good, so that read never ends.
- *An exception fails the read.* An exception that comes while a reader
  word runs ends the read *invalid*; or leaves the reader busy for good,
  if it comes after the word made the reader busy but before its handler
  is set up, or after its work threw but before the handler has run; or,
  if it comes during the entry check or once the work has made the
  reader idle again, leaves the read as if it had come before or after
  the call (the call counted). So a read never ends *ok* if an exception
  cut its work short or came before its reader went idle again.
  Every exception passes on, closing first a file whose lines were being
  read.
- *Lines out of turn fail the read:* a line fed before `lf-ir-start` or
  after `lf-ir-finish`.
- *A fed line's length is unsigned:* a negative one is too long, and the
  line is refused unread: neither copied nor read, whatever its address.

Other misuse is not detected and is outside what the reader defends
against: an output word that writes into the reader's record or other
memory (should it clear the busy flag, the count of calls still fails the
read if it then calls a reader word in its context: a second guard),
changes data-stack cells below its arguments without changing the depth,
unbalances the return stack, or frees its context and makes a new one at
the same address; a caller that sets `lf-context` to anything but a live
context, ignores the outcome, or uses lines written before a diagnostic
or an exception; and a caller or output word that calls an internal word
of the reader, any but the four reader words, `lf-ir-reason` and
`lf-ir-where`. `ir-feed`, for one, does the work of `lf-ir-feed` without
the entry check, so an output word that calls it changes the read, which
can still end *ok* with IR that does not mean what Gforth does with the
file ([ADR 0010](../adr/0010-wordlists.md), only proposed, would hide such
words in a private word list). An exception between `OPEN-FILE` and the
reading of the file's lines, or during `CLOSE-FILE`, can leave the file
open; the read still fails. A review judges the reader against this
model: an accepted file whose IR does not mean what Gforth does with it
is a soundness bug; caller misuse is a bug only where the list above
says the reader detects it.

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
  counting its LF and that CR, is refused, as soon as a block of the file
  shows it too long, so a file without LF is not read to its end (nor is
  `/dev/zero`, which never ends). Nothing is handed to Gforth's
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
the reader's first block, a long file without LF), runs the reader on
each, and has a fresh Gforth load every accepted file and the fixtures:
the IR of a CRLF file equals that of its LF twin, and the host gives each
word the value its IR gives. It also records why three files are refused:
Gforth ends a line at a lone CR, and stops loading at `1 0 /` (−10) and at
the smallest cell divided by −1 (−11) before `CONSTANT`. The Forth tests
count the files opened, closed and read: a directory opens but cannot be
read, `/dev/zero` is refused after two blocks, and every file is closed.
They also give the reader output words that throw; that call each reader
word, catching the refusal or not; that start a read whose own output
word would leave a cell (the case that once ended *ok* with wrong IR);
that clear the busy flag and then start a read (the count of calls must
still fail it); that use another context's reader, and through it come
back to their own context and feed a line there (refused, and the read
fails); that return in another context, while lines are fed and while a
file is read; that leave or take a cell; and that reuse the
pictured-numeric buffer holding the path, read from a file or not. They
interrupt with `THROW` −28, as Ctrl-C would, the opening of a file, its
first read, a fed line, the `CATCH` with which `lf-ir-feed` or
`lf-ir-finish` sets up its handler, the reader's going idle after its
work returned, and the handler's after the work threw. Each must stop the
read as *invalid* or leave its reader busy for good, refusing every
reader word; a switch of context must leave the other context's read
untouched and close the file. They also feed lines after `lf-ir-finish`,
and lines of length −1 or 128 at address 0, which must be refused unread.

The translation is trusted, whether the reader's or the program words':
nothing proves that the IR means what the source means on the host.
Receipts list it as the assumption `trusted-reader`, which since
2026-11-03 names the program words ([program receipts](PROGRAM_RECEIPTS.md)).

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
`make reference-program-ir` accepts each of the 35 theorems it lists (the
nine above, the eighteen of the contracts below and the eight of
well-formedness) only if it uses no axioms beyond Lean's `propext`,
`Classical.choice` and `Quot.sound`: 26 report exactly these three,
`FactorialReference.checked_contract` reports `propext` and `Quot.sound`,
and the eight of well-formedness `propext` alone.

**Well-formedness** (Part 6, ADR 0019 test plan 4, MiniForth's linker
idea): `WellFormed p` is a decidable check of a program as the program
words write it, each name new, every call of an earlier definition (so no
recursion and no forward call), and a constant's body straight-line
instructions that call only earlier constants. `decide` proves it of
`clampProgram`, `examplesProgram` and `allPrimitivesProgram`, and refutes
it for a forward call, recursion, a redefinition, a constant calling a
word and a constant with an `IF`. The theorem that a well-formed program
never fails with *unknownWord*, which would let contracts drop that failure
formally, is not proved yet (a follow-up of ADR 0019).

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

## Contracts of the five other words

Plan task 1.5.3 (roadmap P2.3) gives the five example words other than
clamp formal contracts in the style of `ClampContract`
([`clamp.lean`](../../tests/reference/clamp.lean)): a Lean predicate that
says, clause by clause, what a right answer is, without restating the
algorithm. Each contract lives in its word's reference file, which proves
that the reference model meets it and refutes deliberately wrong models.
Part 5 of `program-ir.lean` copies the contracts verbatim (`make test`
checks the copies), proves that each word's **IR** meets the same clauses
for every cell width of at least two bits, every stack below the inputs
and every caller's return stack, and refutes a deliberately wrong **IR
program** for each word. Everything is checked by Lean 4.35.0: *checked by
the Lean reference, not by LeanForth*.

### One contract in three forms: `lf-gcd`

**Mathematics.** For integers a and b: if a < 0 or b < 0 the word returns
*false*; otherwise it returns g and *true*, where g ≥ 0 divides a and b and
every common divisor of a and b divides g. So g = gcd(a, b), and
gcd(0, 0) = 0. Euclid's loop works on a pair x, y (y on top) with the
**invariant** x ≥ 0, y ≥ 0 and gcd(x, y) = gcd(a, b); each repetition
replaces (x, y) by (y, x mod y), so y, the **measure**, decreases, and when
y = 0 the answer is x = gcd(x, 0).

**Forth** ([`src/program/examples.fs`](../../src/program/examples.fs)):

```forth
: lf-euclid ( a b -- gcd ) begin dup 0<> while tuck mod repeat drop ;
: lf-gcd ( a b -- gcd true | false )
  2dup 0< swap 0< or if 2drop false else lf-euclid true then ;
```

**Lean.** The contract, in
[`gcd-reference.lean`](../../tests/reference/gcd-reference.lean), with the
proof that the reference model `checked` meets it:

```lean
def GcdSpec (a b : Int) (r : Option Nat) : Prop :=
  (a < 0 ∨ b < 0 → r = none) ∧
  (0 ≤ a → 0 ≤ b → ∃ g : Nat, r = some g ∧ (g : Int) ∣ a ∧ (g : Int) ∣ b ∧
    ∀ d : Int, d ∣ a → d ∣ b → d ∣ (g : Int))

def GcdContract (f : Int → Int → Option Nat) : Prop :=
  ∀ a b : Int, GcdSpec a b (f a b)

theorem checked_contract : GcdContract checked
```

The same clauses for the IR, in `program-ir.lean`. `Meets` says that the
word returns normally, keeps the cells below its inputs and the caller's
return stack, and leaves the encoding of a result `r` (here `g true` or
`false`) that satisfies the clauses; a failure never meets a contract.

```lean
def GcdWordContract (p : Program) : Prop :=
  ∀ (c : Cells) (fuel : Nat) (a b : Int), b.toNat + 3 ≤ fuel →
    Meets c p fuel "lf-gcd" [b, a] encodeNat (GcdReference.GcdSpec a b)

theorem gcd_meets_contract : GcdWordContract examplesProgram
theorem gcd_top_only_violates_contract : ¬ GcdWordContract gcdTopOnlyProgram

def euclidInv (a0 b0 : Nat) (d r : List Int) (s : State) : Prop :=
  ∃ a b : Nat, s = ⟨(b : Int) :: (a : Int) :: d, r⟩ ∧ Nat.gcd a b = Nat.gcd a0 b0
```

### The five contracts

Fuel is the least the IR theorem asks for; "fits" means the inputs fit in a
cell.

| Word | Contract | Model meets it | IR meets it | Wrong models refuted | Wrong IR program refuted |
| --- | --- | --- | --- | --- | --- |
| `lf-checked-add` | for a, b that fit: a + b and true if a + b fits, else false (`CheckedAddSpec`) | `CheckedAddReference.checkedAdd_contract` | `checkedAdd_meets_contract`, fuel 5 | off by one at the upper or lower threshold (rejects 6 + 1 and 0 + (−8) on 4 bits); wrapping without a check (7 + 1 gives −8) | `unchecked_add_violates_contract`: `+ TRUE` alone wraps max + 1 to min |
| `lf-checked-abs` | for n that fits: false for the smallest cell, else \|n\| and true, with 0 ≤ \|n\| ≤ max (`CheckedAbsSpec`) | `ProgramExamplesReference.checkedAbs_contract` | `checkedAbs_meets_contract`, fuel 3 | no test for the smallest cell (\|−8\| = 8 on 4 bits) | `plain_abs_violates_contract`: `ABS TRUE` alone gives min and true |
| `lf-in-range` | false for lower > upper; else true exactly when lower ≤ value ≤ upper and false exactly outside, then true (`InRangeSpec`) | `ProgramExamplesReference.inRange_contract` | `inRange_meets_contract`, fuel 2, any integers | exclusive upper bound; one-point interval rejected | `unguarded_in_range_violates_contract`: no test for reversed bounds |
| `lf-gcd` | false if a or b is negative, else a greatest common divisor g and true (`GcdSpec`, above) | `GcdReference.checked_contract` | `gcd_meets_contract`, fuel b + 3, through Euclid's invariant | rejecting only two negative inputs; the answer 1, a common divisor but not the greatest | `gcd_top_only_violates_contract`: testing only b, −4 6 reaches `-4 6 MOD`, which IR 0.1 does not model |
| `lf-factorial` | for n that fits, with max the largest cell: false for n < 0 or n! > max, else n! and true (`FactorialSpec`) | `FactorialReference.checked_contract` | `factorial_meets_contract`, fuel n + 3, through the loop's invariant | treating 0 as negative (0! = 1 must be returned) | `wrapping_factorial_violates_contract`: no overflow test; on 16-bit cells 8! wraps to −25216 |

Every contract determines the answer completely, and each refutation
exhibits one input on which one clause fails. Two variants show why a
clause is needed: the wrapping adder returns every sum that fits exactly
(`wrappingAdd_exact_when_fits`), so only the failure clause rejects it; and
1 divides any two numbers, so only the clause "every common divisor
divides g" rejects the answer 1. The earlier
contracts on the models (`SuccessContract` and `OrderedContract`) were
weaker: they would have accepted a checked add that reports overflow as
success with any other value, and an in-range test that gives no answer
for values outside the interval. They are replaced by the contracts above.

### Loop invariants

Generator v0 has no loop invariants ([verification
conditions](PROGRAM_VC.md)), so Part 5 states the two loops' invariants
in Lean and proves them against the IR semantics, as a later generator
would. `LoopInvariant c p test body rest inv measure need goal` says, for
`BEGIN test WHILE body REPEAT rest`: from every state satisfying `inv`, the
test leaves a flag; on zero, `rest` gives a result satisfying `goal`;
otherwise the body returns to a state satisfying `inv` with a smaller
`measure`, or stops (EXIT or a failure) with a result satisfying `goal`.
`loop_rule` proves that the whole block then gives a result satisfying
`goal`, with one unit of fuel per repetition.

| Loop | Invariant | Measure | Goal | Theorem |
| --- | --- | --- | --- | --- |
| `lf-euclid` | two naturals x, y (y on top) with gcd(x, y) = gcd(a, b) (`euclidInv`) | y | gcd(a, b) on the caller's cells | `euclid_by_invariant`, fuel b + 1 |
| `lf-factorial-from` | counter k on top of product q, 1 ≤ q ≤ max, k ≤ max, q · k! = the total (`factorialInv`) | k | the total and true if it fits, else false through `EXIT` (`factorialGoal`) | `factorialFrom_by_invariant`, fuel k + 1 |

`gcd_meets_contract` and `factorial_meets_contract` rest on these
theorems, not on the reference models or the inductive proofs of Part 3.
The invariant proof of `lf-factorial-from` also shows that none of its
multiplications or decrements wraps.

Not established here: anything about Gforth or the reader beyond what is
said above; and that the five words' contracts are those a user wants,
which is for the owner to judge. The generator still reports the two loop
words *unsupported* (see [what is missing](PROGRAM_VC.md#results-2026-11-02)).

## Planned for IR 0.2

**Proposed in [ADR 0019 Amendment 1](../adr/0019-program-words-two-modes.md#amendment-1-proposed-ir-02-redefinition-output-words-and-sha-2)
(2026-11-04); nothing below is implemented, and the [parser] gate decides
it first.** Everything on this page describes IR 0.1 as it is.

- **Redefinition with Forth's early binding** (the owner's request): a
  file may define its own words again; each use means the version visible
  where it is written, and each version has its own IR name (`lf-clamp`,
  `lf-clamp'1`, …), so a proof and a receipt name exactly one version.
  Redefining Forth-2012 standard words stays refused (recommended).
- **Output words as effects:** `.`, `U.`, `CR`, `EMIT`, `SPACE`, `SPACES`,
  `."`, `S" … " TYPE` and `.S` inside definitions, written `out .` and so
  on; for the stacks they only take their argument, and what they print
  goes to a list of events that a stack proof ignores (a planned Lean
  theorem says the stacks never depend on it). `dup .` for debugging is
  the main use.
- **For SHA-256's helper words** (plan stage SHA-2): the primitives
  `lshift` and `-rot`, and Forth-2012's prefixed numbers (`$`, `#`, `%`,
  `'c'`) with values from −2^31 to 2^32 − 1.
- **Versioning:** a file using none of the new instructions still gives
  today's IR, labelled `lf-ir 0.1`; receipts of IR 0.2 programs need
  receipt schema 0.3 ([format] gate).

Probes behind the design, on both Gforths and in Lean:
[IR 0.2 probes](../development/measurements/ir-0.2-probes-2026-11-04/README.md).

## Versioning

The version string `0.1` appears in the text form's first line, in the
reader's output and in receipts (`program.ir.version`). Any change to the
syntax, the primitives or the semantics gives a new version; the Lean
model, the reader, its golden files and the receipt schema change together.

## Running the checks

```sh
make test-program-ir        # receipts, verbatim copies, reader tests and files (Gforth, Python)
make test-program-verify    # the program words: both designs, cross-check, round trip
make reference-program-ir   # the Lean model, its axioms, its IR against the reader's
```

The first two are part of `make test`, the last of `make check`. Measured on
2026-11-02 (Ryzen 5 7600X, WSL2): `make reference-program-ir` takes about
4.7 s with Lean 4.35.0 (about 6 s with the contracts, 2026-11-03); the
reader tests pass on Gforth 1.0.0 and 0.7.3, and so, on 2026-11-03, do the
program words' (`make test-program-verify`, about 4 s).

Files: [`tests/reference/program-ir.lean`](../../tests/reference/program-ir.lean)
(model and proofs), [`src/program/ir-reader.fs`](../../src/program/ir-reader.fs)
(reader), [`tests/program/ir-reader.fs`](../../tests/program/ir-reader.fs)
(reader tests),
[`tests/program/ir_reader_files.py`](../../tests/program/ir_reader_files.py)
(files with every kind of line end, loaded by the host too),
[`tests/program/ir/`](../../tests/program/ir/) (golden IR, and the
all-primitives source),
[`tests/program/check_program_ir.py`](../../tests/program/check_program_ir.py)
(copies, axioms, the primitive tables of the reader and the program words,
Lean-versus-reader comparison); the program words'
[`tests/program/verify.fs`](../../tests/program/verify.fs) (golden files,
diagnostics and isolation in both designs, redefined standard words),
[`tests/program/verify_check.py`](../../tests/program/verify_check.py)
(both designs against each other and the reader, with Gforth loading what
they accept),
[`tests/program/verify_roundtrip.py`](../../tests/program/verify_roundtrip.py)
(round trip and random programs) and
[`tests/lib/text-run.fs`](../../tests/lib/text-run.fs) (their library).
