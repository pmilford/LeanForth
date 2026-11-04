# ADR 0019: program words in two modes — correctness mode and run mode

Status: **implementation approved [parser]** by the owner on 2026-11-04
([decisions](../project/OWNER_DECISIONS.md#program-words-and-run-records-approved-2026-11-04);
next: IR 0.2 with redefinition by early binding and output words, as the
owner asked, designed in [Amendment 1](#amendment-1-proposed-ir-02-redefinition-output-words-and-sha-2),
approved in design the same day and **implemented** the same day, before
its [parser] implementation gate). **Accepted in direction** by the owner on 2026-11-03
([answers below](#the-owners-answers-2026-11-03)): option 2, IR first,
today's reader kept as a cross-check and then retired, names that read as
numbers refused. The question of [§9](#9-mode-shift-or-a-separate-vocabulary)
was answered the same day: "If we have both already prototyped, Keep
working in both. With precidence on mode shift" — the portable mode shift
(b2) is built first and is the primary design; the separate vocabulary is
kept working beside it, sharing the words' actions, and both must give the
same IR. Proposed the same day, answering the owner's decision
"[Program correctness the Forth way: words in two modes](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)",
which paused the [parser] gate of today's program reader (plan task
2.5.3). It changes how Forth source becomes the [program IR](../programming/PROGRAM_IR.md);
it changes no typing or conversion rule, no IR 0.1 instruction and no Lean
semantics; [§10](#10-defining-words-and-loops-in-both-designs) designs
what IR v1 must gain. Nothing in `src/` is changed. Throwaway prototypes
ran every claim below on Gforth 1.0.0 and 0.7.3; they are kept, with their
output, in
[two-mode-prototype-2026-11-03](../development/measurements/two-mode-prototype-2026-11-03/README.md).
The design still passes the [parser] gate before any code relies on it.

**Implemented, 2026-11-03, before the [parser] gate** (first follow-up
below): both designs for IR 0.1 in `src/program/`, the mode shift
(`verify.fs`) primary and the separate vocabulary (`verify-alias.fs`)
beside it, sharing the run record and reasons (`verify-report.fs`), every
action (`verify-semantics.fs`) and the runner (`verify-runner.fs`), with
the general pieces in the library `src/lib/text-run.fs`; they use the
authoring layer's message records and its reading of the invoking token
from `>IN`. The clamp receipt's IR is now written by the mode shift
(`scripts/program_receipt.py record`); today's reader stays, unchanged, as
the test oracle. Evidence and the four intended differences from the
reader are in [program IR](../programming/PROGRAM_IR.md#the-program-words-correctness-mode).
Where the implementation settles what this record left open or departs
from it:

- **Reserved words** are every Forth-2012 Core and Core Ext name (§3),
  refused where used as "a Forth word outside IR 0.1" and not to be
  redefined; the mode shift knows the 51 words with verification
  semantics by identity (token and name) and the reserved ones by name
  alone, so `RECURSE`'s moving token (§9) needs no special case in IR 0.1.
- **Names that read as numbers** (answer 4): the rule of §2 also refuses
  chains of signs and prefixes (`$-1`, `-$10`), Gforth 1.0's digit
  separator (`_1`, `-_1`, `#_1`), a quote after a sign (`-'a'`, read by
  both Gforths), after a prefix a letter before a digit or a point (`-k1`,
  `+M5`: Gforth 1.0's floats with an SI prefix), and a point before a
  digit, `_` or a prefixed hexadecimal letter (`.5`, `._`, `$.a`). The
  first version missed `-'a'`, `-_1` and `#_1` (review rvPW, M1), the
  second the SI floats (N1); a test now checks the rule against the
  running Gforth, which must read no token of one to three printable
  characters in an empty search order that the rule lets through.
- **The gap check** (separate vocabulary) writes each `lit` as it checks
  it, and after a host `THROW` writes the literals before the token it
  refuses, so that the lines before a refusal are the reader's; the
  values' check is defence in depth, which no host reading with `BASE` ten
  triggers (a test drives it directly).
- **Mode shift lookup order:** the file's words, then `FORTH-WORDLIST`,
  then a plain decimal, so a host word named like a decimal is refused, as
  run mode would call it.
- **A run started by the output word** in its own context aborts and
  changes nothing; the run under way goes on.
- **Files** are read a block at a time, with no limit on their size, as
  the reader does. (The first version read them whole, at most 65,536
  bytes, and a file whose 65,536th byte was an LF was cut there without a
  word: review rvPW's blocking finding B1, fixed the same day.)
- **Identity** (§9): known by the token a name had when the program words
  loaded; see the corrected reason 2 of §9 for what it does not cover.
- **Well-formedness** in Lean: the decidable predicate is in
  `tests/reference/program-ir.lean` (Part 6), checked by `decide`; the
  *unknownWord* theorem is still a follow-up.

## The owner's answers (2026-11-03)

1. **Option 2:** "1 but also consider if there is a way to do it with a
   mode shift rather than an alias. Either case probably needs special
   handling of defining words and looping." Considered in
   [§9](#9-mode-shift-or-a-separate-vocabulary) (prototyped: it works on
   both Gforths) and [§10](#10-defining-words-and-loops-in-both-designs)
   (defining words and loops, prototyped in both designs).
2. **IR first, symbolic execution later**, as recommended (§4).
3. **Today's reader stays as a cross-check, then retires**, as
   recommended (§8).
4. **Names that read as numbers are refused** in correctness mode (§2), as
   recommended. The prototypes predate this answer and still accept them;
   the implementation refuses any name that Forth-2012 or Gforth could read
   as a number.

## Summary in plain words

You asked whether the program reader is "1) an ascii file read and
translation … or 2) a set of LeanForth words with the same names, that,
instead of running, output the IR (in correctness mode) and execute in run
mode", and said you much prefer 2. Today's reader is option 1: it splits
the file into tokens itself, looks each up in its own table and writes IR.
Nothing in the file runs.

This record designs option 2. **One source file, two ways to load it:**

- **Run mode** is ordinary Forth: `include clamp.fs`. `DUP` duplicates
  the top of the stack, `:` compiles a word, and the program runs.
- **Correctness mode** loads the *same file, unchanged*, through the same
  Forth interpreter, but with a LeanForth *vocabulary* in place of
  Forth's own words. Its words have the same names. When the interpreter
  reaches `DUP`, LeanForth's `DUP` runs and writes `prim dup` to the IR;
  `:` writes `word NAME`; `IF` writes `if`, and so on. Forth does the
  reading, the word lookup (with its own rules for upper and lower case)
  and the number reading, exactly as in run mode. This is how Forth cross
  compilers have long worked: the same source, a different vocabulary.

The prototype loaded the six example words' real source files, unchanged,
and wrote IR **byte for byte identical** to today's golden files, on both
Gforth versions. The same files ran in plain Forth (19 calls checked).
It replayed today's reader tests (106 cases at the time, 108 on today's main: same verdict, line and
column, and the same diagnostic text and IR where the tests check them),
86 hostile inputs (every one refused except the five meant to pass), an
IR → Forth → IR round trip with awkward names, and four deliberately
planted faults (all caught).

Three things make it safe, and they are the heart of the design:

1. **Only the vocabulary is visible.** While a file runs in correctness
   mode, Forth can find exactly two lists of words: LeanForth's vocabulary
   and the words the file itself defines. `BYE`, `IMMEDIATE`, `[`,
   `POSTPONE`, `HEX`, `EVALUATE` — none of them exists there, so a file
   that uses one is refused, and no word of the host Forth can run.
2. **A colon definition keeps the interpreter interpreting.** `:` does not
   switch Forth into compiling. Each word of the body runs as the
   interpreter reaches it and writes its instruction. `IF` cannot know its
   condition, and does not need to: it writes `if`, and because the
   interpreter reads the text once from left to right, both branches' words
   run once each and write their instructions in order.
3. **Every number is checked against its text.** Forth's interpreter reads
   numbers itself and puts them on the stack. Each LeanForth word, when it
   runs, looks at the text between the previous word and itself: it must be
   only plain decimal numbers, as many as the stack grew, with exactly the
   values written. Anything else — `$10`, `1.5`, Gforth 1.0's `"x"` or
   `->x` — is refused at that token. No number can ever stand for
   anything else, so the "numbers that forge values" hole found in the
   theorem words cannot occur here.

What is trusted does not grow: the IR, its Lean semantics and the proofs
stay exactly as they are; the correctness words are untrusted notation.
One assumption remains, as today: that each LeanForth word means what
Gforth's word of the same name does. It is tested by running the IR
interpreter, Gforth and Lean's model on the same inputs.

**My recommendations** (questions at the [end](#questions-for-the-owner)):
replace today's reader by these words; emit today's IR first and add
symbolic execution later as an untrusted helper whose results are checked
against the IR; keep today's reader only as a test oracle until the switch,
then retire it. (All accepted; see the answers above.)

**Mode shift** (added after the owner's answer). Forth already gives one
word two meanings: when it interprets, `IF` is refused; when it compiles,
`IF` compiles a branch. Forth-2012 describes every word by its
*interpretation semantics* and *compilation semantics*, and `STATE` says
which the interpreter performs. A mode shift adds a third: *verification
semantics* — `DUP` verifying writes `prim dup`. No second `DUP` exists:
the word is Forth's own `DUP`. The prototype did this two ways, both giving
byte-identical IR for `clamp.fs` and the other golden files: portably on
both Gforths, and on Gforth 1.0 with Gforth's own interpreter switched
into a third state. It also refused a file in a Forth where `MAX` had been
redefined, which the alias design cannot notice. My recommendation is the
portable mode shift ([§9](#9-mode-shift-or-a-separate-vocabulary)).

## One example in four forms

`lf-clamp` from [`src/program/clamp.fs`](../../src/program/clamp.fs).

**Mathematics.** For integers v, l, u: if l ≤ u the word returns
r = min(max(v, l), u) and *true*; if l > u it returns *false*.

**Forth** — the one file, for both modes (lines 12–14):

```forth
: lf-clamp ( value lower upper -- result true | false )
  2dup > if 2drop drop false exit then
  >r max r> min true ;
```

**Correctness mode, writing IR** (prototype output, identical to
[`tests/program/ir/clamp.ir`](../../tests/program/ir/clamp.ir); its
SHA-256 `651875025cec88f7…` is the one the existing clamp receipt records):

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

**Correctness mode, symbolic** (the prototype's demo of question 4(b);
inputs named from the stack comment):

```text
sym lf-clamp  (3 inputs)
  when (lower > upper):  false
  when not (lower > upper):  min(max(value, lower), upper) true
```

**Lean** ([`tests/reference/program-ir.lean`](../../tests/reference/program-ir.lean),
unchanged): `ProgramIR.clamp_correct` proves that this IR returns
`[0]` when `lower > upper` and `[-1, clamp lower upper value]` otherwise,
for every cell width and every stack below the inputs.

**Run mode:** `5 0 10 lf-clamp` leaves `5 -1`, `15 0 10 lf-clamp` leaves
`10 -1`, `5 10 0 lf-clamp` leaves `0`, in plain Gforth 1.0.0 and 0.7.3.

## Context

- **The owner** (2026-11-03): "I much prefer 2"; "option 1 for program
  correctness isn't a very Forth like way to operate"; "this is important
  and may need more design." The reader's [parser] gate is paused.
- **Today's reader** (`src/program/ir-reader.fs`, 742 lines, five review
  rounds; [program IR](../programming/PROGRAM_IR.md#the-reader)) reads
  lines itself, splits tokens, folds case and recognises decimals as Gforth
  would, and must match Gforth on each of those points; its threat model
  defends against hostile source files.
- **IR 0.1** and its Lean semantics (`ProgramIR.run`), the six theorems,
  the [receipts](../programming/PROGRAM_RECEIPTS.md) (assumption
  `trusted-reader`), the [verification conditions](../programming/PROGRAM_VC.md)
  written by untrusted Python and made safe by a Lean theorem about
  `callWord` itself, and the three-way comparison
  ([IR interpreter](../programming/PROGRAM_IR_RUN.md)).
- **ADR 0017** (accepted as the design basis): theorems are Forth words run
  by Forth's own interpreter with only LeanForth's word lists visible, in
  the separate authoring program (plan 8.2.1). Its implementation
  (`src/author/`) has a line-by-line runner, positions read back from
  `>IN`, and an error catalogue. Its review found that negative numbers
  forge earlier values, that Gforth 1.0's recognizers accept `"x"`, `$10`,
  `->x` and more, and that names that are numbers leave words behind.
- **The program track's goal** ([plan](../project/PLAN_DRAFT.md#program-track-goal-most-of-forth-2012-core-owner-2026-11-02)):
  most of Forth-2012 Core in stages G1–G5, and the flagship target, a proof
  that LeanForth's own SHA-256 computes FIPS 180-4.
- **The owner's product rule:** end users need only a Forth system and an
  NDJSON file — no Python and, ideally, no Lean on their path.
- **MiniForth** (Leonardo de Moura, <https://github.com/leodemoura/MiniForth>,
  commit `e8756e2`; reviewed for this record): a Forth-like teaching
  language in Lean. It has no licence, so ideas only, no code.

## Prior art

- **Forth cross compilers and metacompilers.** Gforth builds its own kernel
  with `cross.fs`, in which `:`, `IF` and the other words have *target*
  meanings; cross compilers commonly separate host and target scopes (the
  proposed Forth cross-compiler standard names HOST, INTERPRETER, COMPILER
  and TARGET). The same source text gets a different meaning from a
  different vocabulary — exactly option 2. *Taken.*
- **Forth assemblers** run in their own vocabulary, with words such as
  `IF` redefined to emit machine branches. *Taken:* structured control
  words that emit structure.
- **Stack-effect inference and typed Forths** (Pöial's stack-effect
  calculus; StrongForth) analyse a word by running a model of each word
  over abstract stack items. *Taken* for the symbolic demo; inputs are
  drawn from below the stack as a word needs them.
- **Symbolic execution** (King, 1976): run a program on symbols, split at
  branches, collect path conditions. The demo of question 4(b).
- **MiniForth** keeps syntax, linking and semantics as three stages with
  their own guarantees; binds its programs through a global dictionary
  that, as its README says, does not model Forth's successive
  redefinitions; proves its fuel-limited interpreter sound and complete
  against a semantics without fuel; keeps total, safe-partial and partial
  correctness apart; and generates verification conditions by rewriting
  with proved Lean rules plus a tactic, not with a separate generator.
  *Taken:* structured blocks, early binding, a well-formedness check and a
  round-trip test (below); the other three points shape the order proposed
  in [§4](#4-what-the-words-emit). *Avoided:* the late-bound dictionary,
  unbounded integers, Lean syntax quotations as the program form.

## Decision

### 1. Colon definitions: the interpreter keeps interpreting

In correctness mode `:` reads the name after it (as Forth's `:` does),
writes `word NAME @line:column`, defines NAME in the file's own word list,
and **leaves Forth interpreting** (`STATE` stays zero). The words of the
body then run one by one as the interpreter reaches them, each writing its
instruction. `;` writes `end`. Top-level tokens before `CONSTANT` are kept
and written as the constant's body, exactly as IR 0.1 defines it.

**Structure.** `IF`, `ELSE`, `THEN`, `BEGIN`, `WHILE` and `REPEAT` write
`if`, `else`, `then`, `begin`, `while` and `repeat` and keep a stack of open
frames — the same idea as Forth's compile-time control-flow stack, but in
the vocabulary's own memory, never on the data stack. They never evaluate
a condition: the interpreter reads the text once, left to right, so every
word of both branches and of a loop body runs exactly once and writes its
instruction in order. The result is nested blocks (IR 0.1's `ifElse` and
loop), not jumps, which is what the Lean semantics and a one-line branch
rule for proofs want. A wrong nesting is *invalid*; a second `WHILE` in
one loop *unsupported*, as today.

**Calls are bound early.** Each word the file defines is a word of the
file's word list; when the interpreter finds it, it writes `call NAME`.
Forth's own lookup found it, so the call is bound to the definition that
was visible at that point — Forth's rule, not a name looked up later. The
word's record holds the definition's identity (its number). IR 0.1 calls by
name, and that is exact because a redefinition is refused (in any case of
letters, as today), so a name means one definition. If redefinition is
ever admitted, the call will carry the identity instead; nothing else has
to change. A word is visible inside its own body but refuses (*recursive
call*, unsupported), as Gforth hides it until `;`; `RECURSE` (stage G1)
will write a call of the definition being compiled explicitly.

**Rejected: compile normally, then run the compiled word in an emit mode.**
(i) Running a compiled `IF` needs its condition's value, so one run sees
one path; a compiled `IF` that runs both branches is the interpreting
design in disguise. (ii) Compiling hands tokens to the host's compiler:
numbers become literals whose text and position are lost, and `IMMEDIATE`,
`POSTPONE`, `[` and `]` would run host code at compile time. (iii) What
runs later is the host's compiled code, which carries no source positions
for the IR. **Rejected: our own loop over the dictionary** (read each
token, look it up with `SEARCH-WORDLIST`, call it): that is a parser of
our own, option 1 again.

### 2. Literals: the gap check, portable without recognizers

Forth's interpreter reads numbers itself, as in run mode. To see them,
**every word of the vocabulary and every word of the file, when it runs,
first checks the text between the previous word and itself** (the *gap*):

- the gap holds only plain decimal literals — an optional minus sign and 1
  to 10 digits, at most 2,147,483,647 in size (IR 0.1's rule) — separated
  by spaces or tabs;
- the data stack grew by exactly that many cells since the run began
  (every word takes its literals off again), and each cell equals its
  token's value; the floating-point stack did not change.

The literals become `lit n` instructions, each with its own line and
column. At the end of each line the runner checks the rest of the line the
same way. When Forth throws (−13 for an unknown token; Gforth 1.0 throws
−21 for `->x` when `x` is a word of the file), the runner reports the
first token after the checked text that is not a plain literal, as
*unsupported*.

The word finds its own token by reading back from `>IN` over one delimiter
and the token (Forth-2012 leaves `>IN` just past it), as ADR 0017's words
do. The gap is therefore everything between two words of ours.

**Why this is portable.** It uses no recognizer and no number-conversion
hook, only `SOURCE`, `>IN`, `DEPTH` and `>NUMBER`. The hosts read odd
tokens very differently (probe `p01-recognizers.fs` in the prototype
folder: Gforth 1.0 reads `"x"`, `${HOME}`, `` `dup ``, `<dup>`, `2p`,
`1_000` and `.5` as values; 0.7.3 refuses all of these; both read `$10`,
`'a'` and `1.`, and wrap `18446744073709551616`), but the check decides
from the text, so all 86 hostile inputs gave **byte-identical diagnostics
on both hosts**.

**Numbers that forge values: closed by construction.** No word of the
vocabulary takes a value from the data stack except the gap check, which
compares it with its text. Control frames live in the vocabulary's own
stack (`: f 0 then ;` is *invalid*: a number cannot stand for a frame).
There are no handles on the stack for a negative number to imitate.

**Names that are numbers.** Forth's own lookup decides in both modes: a
word the file defines is found before a number on both hosts, so
`: 5 7 ;  : g 5 05 ;` gives `call 5` and `lit 5`, as today's reader does
(and Gforth 1.0 itself warns "defined literal 5 as word"). The file's word
list is new for every run, so a name never outlives its file; a name that
did outlive its run was the cause of the theorem words' version of this
hole. **Decided (owner, answer 4): such names are refused** — `:`,
`CONSTANT`, `CREATE`, `VARIABLE`, `VALUE` and every user defining word
refuse a name that Forth-2012 or Gforth could read as a number (a digit
first; a sign, `#`, `$`, `%` or `&` and then a digit or hex letter;
`'c'`). Refusing accepts less than Gforth, never more.

**Extending the literal syntax** (needed for SHA-256's constants, §6):
Forth-2012's own prefixes `$` (hex), `#` (decimal), `%` (binary) and the
character form `'c'` read identically on both hosts (probe `p01`); the gap
check's own parser can admit them, computing the value itself and still
requiring the host's cell to agree.

### 3. Isolation

- **Search order:** exactly two word lists, set with `SET-ORDER`: the
  vocabulary first, then the file's word list (new for each run). Not
  `FORTH-WORDLIST`, and not the root word list `ONLY` would add. The
  vocabulary is searched first, so even if a redefinition check failed,
  the file could not shadow a vocabulary word.
- **Compilation word list:** unchanged; the vocabulary's defining words set
  it to the file's word list only around their `CREATE`.
- **`BASE`:** set to ten for the run. No vocabulary word changes it
  (`HEX` and `BASE` do not exist there); `DECIMAL` is accepted outside
  definitions and does nothing.
- **`STATE`:** no vocabulary word changes it (no `]`, and `:` does not
  compile). The runner refuses to start while `STATE` is nonzero — an
  immediate word calling it during compilation would otherwise compile the
  file's words into its caller — and checks it after every line.
- **Restored:** the caller's search order, compilation word list and
  `BASE` are saved with `GET-ORDER`, `GET-CURRENT` and `BASE @` and
  restored after the run however it ends (the runner `CATCH`es every
  `THROW`, as the authoring runner does under ADR 0018).
- **Lines:** the runner reads the file itself, once, as bytes; splits at
  LF (dropping one CR before it); refuses any character other than
  printable ASCII, space and tab, and lines of 128 characters or more,
  exactly as today; and hands each line to `EVALUATE` as a string. So no
  construct can reach the next line: a `(` must close on its line, and
  Gforth 1.0's string recognizer can consume at most the rest of the line,
  which the gap check then examines.
- **Everything else is unsupported, fail-closed:** an undefined word, any
  host word, any host-specific token form. Standard words outside IR 0.1
  (`DO`, `@`, `RECURSE`, …) are *reserved* vocabulary words that refuse
  with "a Forth word outside IR 0.1" and cannot be redefined; the
  implementation reserves every Forth-2012 Core and Core-Ext name, and the
  stages of §6 turn them into real words one by one.

**The invariant**, in one sentence: every character of every line lies
either in a gap that the literal check examined, or in a token or text
that a vocabulary word read and validated; and no other word of the host
can run, because no other word can be found. Gforth 1.0's recognizers can
still act on an unknown token before it is refused (`${HOME}` reads an
environment variable, `->x` throws), but they find names only in the
search order (`forth:dup` and `forth:bye` give −13 on both hosts), so they
reach nothing outside the vocabulary. Limiting Gforth 1.0's recognizers to
names and numbers during a run is possible hardening, not needed for the
argument.

**Process.** Correctness mode runs source text, so it belongs in the
untrusted **authoring program** of plan 8.2.1, never in the checker's
process; it hands over IR text (and later symbolic results), which is
data. Run mode is an ordinary, separate Forth process.

### 4. What the words emit

**(a) IR 0.1 first.** The prototype shows the vocabulary can write today's
IR byte for byte, so everything downstream is kept: the Lean semantics and
the six theorems, the golden files, the three-way comparison, the
verification-condition generator and the receipts.

**(b) Symbolic execution.** The prototype's second vocabulary (`sym.fs`,
about 300 lines) runs the same files on a symbolic stack: `dup` on *x*
leaves *x x*, `>` on *a b* leaves the term *(a > b)*, `IF` splits the path
and `THEN` joins two arms with *if-then-else* terms (two arms that leave
different depths, as in `if 2drop false else + true then ;`, stay two
paths), `EXIT` ends a path, a call applies the callee's paths, and inputs
are drawn from below the stack as words need them. On the six examples it
gave the results of the four words without loops (checked add as two paths
with if-then-else conditions, where the Python generator splits it into
five) and refused the two loops ("needs an invariant"), as that generator
does:

```text
sym lf-checked-abs  (1 inputs)
  when not (n = lf-example-min):  abs(n) true
  when (n = lf-example-min):  false
sym lf-in-range  (3 inputs)
  when not (lower > upper):  (not (lower > value) and not (value > upper)) true
  when (lower > upper):  false
sym lf-euclid: unsupported: a loop: needs an invariant (plan 4.4.1)
```

It would let Forth, not Python, compute the paths on the user's path. But
if the symbolic words' results *were* the proof obligations, the symbolic
meaning of every word would become a second trusted semantics beside the
IR's. The design rule is therefore: **the IR stays the single meaning that
is proved; symbolic execution is an untrusted producer whose output is
checked against it**, as the Python generator's is today (its `contract`
theorem is about `ProgramIR.callWord` itself, so a wrong symbolic step
makes a proof fail, never a false theorem). MiniForth points the same way
from the other side: there, generating conditions *is* rewriting with
proved rules.

**Recommended order:**

1. **(a) now:** the vocabulary replaces the reader and writes IR 0.1.
2. **One run, two outputs:** the vocabulary's words call one small emitter
   interface (`prim`, `lit`, `call`, `if`, …), implemented by the IR writer
   and by the symbolic executor, so both see exactly the same instructions
   and the receipt hashes the IR they came from.
3. **(b) as a Forth port of the Python generator's path search**, cross-
   checked against `scripts/program_vc.py` on every contract (Python as a
   test oracle only), its obligations still proved by Lean.
4. **Proved rules** (plan 4.4.2, IR v1): weakest-precondition rules for
   each instruction, proved once in Lean; with MiniForth's lessons — a
   semantics without fuel and a proof that the fuel-limited `run` is sound
   and complete for it, and the kind of correctness (total, safe-partial,
   partial) named in receipts.
5. **Phase 5 onwards** (plan 5.5.1, 8.4.1): the symbolic executor writes
   the proof term that applies those rules, and LeanForth's own checker
   checks it. Then neither Python nor Lean is on the user's path.

### 5. Run mode and receipts

**Run mode is the same file, unchanged, in ordinary Forth** — `include`,
Forth's own words, `BASE` ten, on a Forth whose standard words have their
standard meaning, loaded last (the file's definitions of host names, such
as `.`, affect what is compiled after it; today's rule). The prototype
loaded `clamp.fs` and `examples.fs` with plain Gforth and checked 19 calls
on both hosts.

**What ties the two runs.** The receipt already records
`program.source.sha256` and `program.ir.sha256`. *As built (2026-11-04):*
the correctness runner reads the file a block at a time, every byte of it
and with no limit, as today's reader does (the first version read it once
into memory, which review rvPW found could cut a large file, B1). A hash
of exactly what it ran would therefore be taken over the blocks as they are
read (with the Forth SHA-256 of plan 3.2.6), not over a copy in memory;
that is not built yet. Today the tie is made when the receipt's evidence
is recorded: `scripts/program_receipt.py record` hashes the source file,
runs the mode shift on it, hashes it again and requires both hashes equal
and the IR written byte for byte the IR file's; the receipt's
`program.source.sha256` must then be that hash. A run-mode loader for
receipts would do the same — check the hash against the receipt, evaluate
those bytes with Forth's own words — so both modes provably ran the same
bytes. Plain `include` stays fine for users, with `sha256sum` to compare.

**What remains trusted** (the receipt's assumptions):

- *The vocabulary's meaning:* each correctness word writes the IR whose
  Lean semantics is what Gforth's word of the same name does. This is
  today's `trusted-reader` assumption, made smaller: Forth now does the
  tokenizing, the case folding and the number reading in both modes, so the
  vocabulary no longer imitates them. It stays tested three ways (IR
  interpreter, Gforth, Lean's model; 5,152 cases today) and by the golden
  files. Renaming the assumption kind (for example `trusted-vocabulary`)
  is a receipt-schema change for the [format] gate, later.
- *The runner's isolation* (§3): only the vocabulary ran, and the gap
  check saw every literal.
- *The host:* its interpreter splits tokens and reads plain decimals the
  same way in both modes (it is the same interpreter), and the runtime
  executes the compiled words as the IR semantics says (`trusted-runtime`,
  unchanged).

### 6. Growth path: stages G1–G5 and SHA-256

Every stage adds vocabulary words, IR instructions, their Lean semantics
and three-way tests together, as the plan says.

- **G1 — counted loops, `RECURSE`, double and unsigned words.** `DO`,
  `?DO`, `LOOP`, `+LOOP`, `LEAVE`, `I`, `J`, `UNLOOP` are structure words
  with frames (a `DO` frame collects its `LEAVE`s); the arithmetic words
  are primitives; `RECURSE` writes a call of the definition being compiled,
  whose identity the vocabulary holds.
- **G2 — memory.** `VARIABLE`, `CREATE`, `ALLOT`, `,` and `C,` at the top
  level **run**, on the vocabulary's model of data space: they declare
  named regions with sizes and initial contents. Inside definitions, a data
  word writes its region's address and `@ ! C@ C! +! MOVE FILL` write
  memory instructions with bounds and no-overlap obligations.
- **G3 — execution tokens.** `'` and `[']` read the next name, as Forth
  does, and write `xt NAME` for a known definition; `DEFER`/`IS` at the top
  level declare a known target; `CATCH`/`THROW` get IR instructions with
  stated exception semantics.
- **G4 — defining words and compile-time computation: where option 2
  shines.** Take `: table ( n -- ) create , does> @ ;` and later `5 table
  five`. In correctness mode the definition of `table` is written in two
  parts (what `CREATE` time does, what each child does). When the file
  *uses* `table` at the top level, the vocabulary does what Forth does: it
  runs the create part **concretely**, with the IR interpreter that already
  exists in Forth (`src/program/ir-run.fs`), on the model of data space,
  and declares `five` with its data and the does part as its behaviour.
  Likewise `[ 4 5 * ] literal`: `[` switches the vocabulary to concrete
  evaluation, `]` back, and `literal` writes `lit 20` — the value computed
  by the model, which the three-way tests check against Gforth. A text
  reader would need an evaluator of its own for all of this; option 2 is
  already running the code. `VALUE`/`TO` and `CONSTANT` as today.
- **G5 — strings and I/O.** `S"`, `."`, `CHAR` and `[CHAR]` read their text
  as Forth's do; strings become declared read-only data; `TYPE`, `EMIT`,
  `ACCEPT` and file words write effect instructions with their assumptions.
- **Always unsupported** inside verified words (plan): `IMMEDIATE`,
  `POSTPONE`, `[COMPILE]`, `EVALUATE`, `STATE` games, run-time dictionary
  changes. They are simply absent from the vocabulary.

**SHA-256** (stages SHA-2 to SHA-5): the helper words need `LSHIFT` and
32-bit constants written in hex (`$428A2F98`): the gap check admits
Forth-2012's `$` prefix (§2), and IR 0.2 states the cell-width condition
for literals above 2,147,483,647. The 64-round compression needs G1's
counted loops; the constant table `create k $428A2F98 , …` and the
message buffers are G2/G4's declared data; the proof checked by LeanForth
is SHA-5. Throughout, `src/lib/sha256.fs` itself runs unchanged in both
modes: the code the product uses is the code that is verified.

### 7. Sharing with the theorem words (`src/author`)

The program vocabulary and the theorem words (ADR 0017) are two
vocabularies on one mechanism. They should share code, not copy it:

- **One runner:** reading a file once, splitting lines, the character rule,
  `EVALUATE` per line, saving and restoring the search order, compilation
  word list and `BASE`, the `STATE` check, catching every `THROW`. Today's
  `src/author/runner.fs` generalised to take its word lists; written as a
  standalone library under the owner's reusable-library rule (it is useful
  to any Forth program that runs a little language in its own vocabulary).
- **One way to find positions:** `src/author/source.fs` (the invoking
  token read back from `>IN`, line and column) as it is.
- **One error record:** a stable code, an outcome (ADR 0008), the position
  and text of the token, and a second position where useful; each
  vocabulary has its own catalogue and code range, documented like
  [LeanForth words](../programming/LEANFORTH_WORDS.md).
- **The gap check, offered to the theorem words:** it closes two of the
  syntax review's findings there too — Gforth 1.0's recognizer tokens
  (refused from the text), and forged items (theorem text would allow only
  nonnegative plain decimals, so `-3` could never be read as a reference).
  That is a proposal for the theorem words' own fix, not decided here.
- **Different on purpose:** program names fold case as Forth does; theorem
  names are case-exact (ADR 0017 §5).

### 8. What happens to today's reader

**Keep it, unchanged, as a test oracle during the switch, then retire it.**
While the vocabulary is built, every file either accepts must give
byte-identical IR from both, and every file one refuses the other must
refuse too, or the difference is listed and justified; its 108 verdict
tests are replayed against the vocabulary, as the prototype did. Once the
vocabulary has passed the [parser] gate, the reader leaves `src/` and
`src/main.fs`; its test inputs and golden files stay as the vocabulary's
tests. Keeping two front ends would double the work at every stage of §6,
and the independent checks that remain are stronger than a second reader:
Lean prints the IR from its own terms and must match, the three-way
runtime comparison, the golden files, and the round trip below.

### 9. Mode shift or a separate vocabulary

The owner asked whether the words could get their second meaning by a
*mode shift* rather than an *alias*. The two differ in where the second
meaning lives:

- **The alias** (§§1–8): LeanForth's own words with Forth's names (`dup`,
  `if`, `:` …) in a separate word list; correctness mode puts that list,
  and nothing else, in the search order. Two words are called `DUP`.
- **A mode shift:** one word, Forth's own `DUP`, and an interpreter
  *state* that selects which of its meanings runs, as `STATE` selects
  between interpreting and compiling today.

Four ways to shift modes were weighed; two were prototyped.

**(a) Dual-mode words that test a flag** ("state-smart" words): LeanForth
replaces `DUP` by `: dup verifying @ if … emit … else dup then ;`, loaded
before the program in both modes. Run mode stops being plain Gforth: every
call of every word becomes a call of LeanForth's wrapper plus a test (and
Gforth can no longer inline `DUP` or combine it with its neighbours), and
the wrappers become part of the runtime the receipt must trust. Forth
programmers know state-smart words as a source of subtle bugs (`'` or
`POSTPONE` of such a word does the wrong thing). **Rejected.**

**(b1) A third state of Gforth 1.0's own interpreter.** Gforth 1.0's
recognizers return a *translation* per token, and `translate-method:`
adds a new action to every translation, selected with `set-state` — Gforth's
own tokenizer uses this. The prototype (`ms-gforth1.fs`, 45 lines) adds
`verifying`, gives it actions for a found word (its verification
semantics) and for a one-cell number (checked against its text), switches
the state, and lets Gforth's own `INTERPRET` read each line. Every other
translation (strings, floats, `->x`, `${NAME}` …) has no `verifying`
action, and Gforth throws −13 for it, so it is refused. One catch, found
by the hostile inputs: Gforth 1.0 also finds words through other token
forms (`forth:dup` is FORTH's `DUP`), which 0.7.3 does not read, so the
action must check that the token is the word's own name. *Gforth 1.0
only*, and the words are marked gforth-experimental.

**(b2) A portable third state.** Hosts without recognizers (0.7.3, plain
Forth-2012) have no hook into their interpreter, so the verification
state is a loop of our own — Forth-2012's text interpreter (§3.4 of the
standard) with a third state: take the next name with `PARSE-NAME`; find
it with `SEARCH-WORDLIST`, the file's words first, then Forth's word list;
if found, perform its verification semantics, else it must be a plain
decimal. The loop runs *inside* the line as Forth's input source (the line
is evaluated behind one entry word), so `PARSE-NAME`, `PARSE` and `>IN`
are Forth's own and parsing words (`:`, `(`, `CREATE`) work unchanged.
The verification semantics are a table keyed by the word's identity. The
prototype (`ms.fs`, about 120 lines) reuses the alias design's actions
unchanged. Two host quirks shaped the identity: Gforth 0.7.3 gives every
compile-only word (`IF`, `THEN`, `;` …) one shared execution token, and
Gforth 1.0 gives `RECURSE` a token that changes with every new
definition; so a word is known by its token *and* its name, and
`RECURSE` by its name (it must still be FORTH's).

**(c) Found while prototyping: "verify while loading."** The third state
could also do the word's normal compile or interpret action, so one load
both builds the program and writes its IR, with every call bound to the
definition the host really compiled. **Rejected for correctness mode:** the
file's top-level code would then run inside the verifier, and once memory
words arrive (G2) a hostile file could write into the verifier and change
the IR it writes. Running untrusted code is what the separate authoring
program contains; there the model runs it (§10), not the host. It may be
useful later as a listing for developers, never for receipts.

**What the prototype showed** (both Gforths unless marked; outputs in the
prototype folder, section 8 of `run.sh`):

| Check | Alias (cv) | Portable mode shift (ms) | Gforth 1.0's own third state (g1) |
| --- | --- | --- | --- |
| `clamp.fs`, `examples.fs`, `all-primitives.fs` against the golden IR | byte-identical | byte-identical | byte-identical (1.0 only) |
| Today's reader tests replayed (108 verdict cases on today's `main`, 21 checks of text and IR) | 0 differences | 0 differences | 0 differences |
| 86 hostile inputs | 81 refused, 5 meant to pass | the same, byte-identical diagnostics | the same, after the own-name check |
| `MAX` redefined (as `MIN`) before the run | **accepted** — it cannot see the host's `MAX` | refused: "a standard word redefined before the run: max" | refused, the same |
| Defining words and loops (§10) | 95-line IR v1 draft | identical | not tried |

**Comparison:**

| | (a) flag words | Alias | (b1) Gforth 1.0 state | (b2) portable state |
| --- | --- | --- | --- | --- |
| Gforth 0.7.3 | yes | yes | **no** | yes |
| Gforth 1.0 | yes | yes | yes (experimental words) | yes |
| Run mode | **not plain Gforth**: every word wrapped | exactly the file in plain Gforth | the same | the same |
| Speed of run mode | slower (a call and a test per word) | unchanged | unchanged | unchanged |
| Who reads tokens and numbers | Forth | Forth (numbers checked by the gap check; Gforth 1.0's recognizers act first) | Forth (its recognizers act first) | Forth's `PARSE-NAME` and `SEARCH-WORDLIST`; numbers only plain decimals, read by LeanForth; no recognizer runs |
| Tie between a word and its meaning | the wrapper itself (trusted at run time) | the name | the word's identity | the word's identity (token and name) |
| A standard word redefined after the program words loaded and before the run | runs the redefinition | **not noticed** | refused | refused, except a compile-only word on Gforth 0.7.3 (one shared token); tampering before they load is not noticed in any design |
| What is trusted | wrappers, in run mode too | each alias's meaning; isolation by visibility | each verification semantics; Gforth's dispatch | each verification semantics; a short loop of its own |
| How a user switches | a flag | `verify FILE` versus `include FILE` | `verify FILE` (inside: `verifying set-state`, then Gforth's own interpreter reads each line) | `verify FILE` versus `include FILE` |

**Recommendation: the mode shift, done portably (b2).** Reasons:

1. It is literally what you described: *one* word `DUP`, which in run mode
   duplicates and in correctness mode writes `prim dup`. Forth-2012
   already describes words by their semantics per interpreter state; a
   word's verification semantics sits next to them in its documentation.
2. It is somewhat stronger: it checks that every word the file uses is the
   word that had the standard name when the program words loaded (the
   `MAX` test), so a standard word redefined after they loaded and before
   the run is refused, which the alias design cannot see. *Corrected after
   review rvPW (M2):* the check covers only the verifying session; on
   Gforth 0.7.3, which gives every compile-only word one shared token, a
   compile-only word redefined after loading is not noticed; tampering
   before the program words load is not noticed either; and run mode is
   another Forth. So a tampered host stays an assumption in every design
   (see Risks); the check never bears on whether the IR matches run mode.
3. It is simpler to argue: the host converts no number and runs no
   recognizer; each token is a word with verification semantics, a plain
   decimal, or refused. The alias design's gap check is not needed.
4. It runs identically on Gforth 0.7.3 and 1.0 (the CI host and the
   development host), with no experimental words.
5. It costs nothing in run mode, and all the actions are the ones the
   alias design already has; only the dispatch differs (the prototype
   shares every action), so the choice stays cheap to revisit.

Its price: the verification-state loop is LeanForth's own (a few lines
using Forth's `PARSE-NAME` and `SEARCH-WORDLIST`), and identity needs care
per host (token and name; `RECURSE` by name). Gforth 1.0's own third
state (b1) gave the same IR and can serve later as a cross-check on 1.0;
it is not the reference because 0.7.3 lacks it.

How it reads for a user:

```text
gforth clamp.fs                   \ run mode: plain Forth, nothing of LeanForth loaded
leanforth verify clamp.fs         \ correctness mode: the same file, verification state
```

and, for a Forth programmer, inside LeanForth: `verify clamp.fs` loads
the file in verification state as `include clamp.fs` loads it
interpreting.

### 10. Defining words and loops, in both designs

The owner expected that "either case probably needs special handling of
defining words and looping". It does, and the handling is the same in
both designs: the words below were prototyped once (`v1.fs`) and given to
the alias vocabulary *and* to the portable mode shift, and both wrote the
same draft IR v1, byte for byte, on both Gforths. The draft text below is
a sketch of IR v1 (plan 4.4.1), not yet a format anything reads.

**Defining words.**

| Forth | Correctness mode writes | Notes |
| --- | --- | --- |
| `: NAME … ;` | `word NAME` … `end` | IR 0.1 |
| `… CONSTANT NAME` | `constant NAME` with the tokens before it as its body | IR 0.1: the body runs when the constant is called, so a value that depends on the cell width (`-1 1 rshift`) stays exact for every width |
| `VARIABLE NAME` | `created NAME` / `cell undefined` / `end` | Forth-2012 leaves a variable's first contents undefined; the model must not assume 0. Inside definitions `NAME` writes `addr NAME` |
| `CREATE NAME` then `n ,` … at the top level | `created NAME` / `cell n` per `,` / `end` | declared data; SHA-256's table `create k $428A2F98 , …` is this form. `C,` and `ALLOT` add bytes and undefined cells |
| `VALUE NAME`, `TO NAME` | `value NAME` with its first cell; `NAME` writes `value@ NAME`, `TO NAME` writes `to NAME` | `TO` reads the next name as Forth's does; not prototyped |
| `: W … CREATE … DOES> … ;` (a user-written defining word) | `word W` / its *create part* / `does` / its *does part* / `end` | e.g. `: holder create , does> @ ;` |
| `7 holder seven` (using W at the top level) | `created seven` / `cell 7` / `does holder` / `end` | correctness mode **runs** W's create part, concretely, on a model of data space, with the top-level literals as its stack; its `CREATE` reads the next name, as Forth's does while loading. Inside definitions `seven` writes `call seven` (push its address, run W's does part) |
| W used inside a definition | refused | creating words while the program runs is a run-time dictionary change (plan: always unsupported) |
| `[ … ] LITERAL` | `lit n`, with n computed by the model | `[` makes the interpreter *run* instructions on the model, `]` returns, `LITERAL` writes the value; not prototyped |

**Running at the top level is the special handling.** Forth runs a
defining word while it loads the file; so does correctness mode, but on
LeanForth's model — the IR interpreter that already exists in Forth
(`src/program/ir-run.fs`, extended to IR v1) — never on the host, so a
hostile create part can only change the model. What the model can run is
supported: any create part made of IR instructions with known inputs. A
create part that reads input, depends on host words or reaches outside its
own data is unsupported. The prototype ran literals, `CREATE` and `,`, and
refused a create part with anything else (`create dup , ,`).

**Loops.**

| Forth | Correctness mode writes | Notes |
| --- | --- | --- |
| `DO` / `?DO` … `LOOP` / `+LOOP` | a `do` or `?do` block closed by `loop` or `+loop` | nested blocks from the frame stack, like `if` … `then` |
| `I`, `J` | `i`, `j` | need one or two enclosing `do` blocks, else *invalid* |
| `LEAVE` | `leave` | a structured exit of the innermost `do` block, also from inside an `if` |
| `UNLOOP` | `unloop` | before `EXIT` inside a `do` block; IR v1 checks one per enclosing block |
| `BEGIN … UNTIL`, `BEGIN … AGAIN` | `begin` … `until` / `again` | `again` leaves only through `EXIT` |
| `BEGIN … WHILE … REPEAT` | as IR 0.1 | IR v1 should allow Forth-2012's further `WHILE`s, each closed by a `THEN` after `REPEAT` |
| `RECURSE` | `call NAME` of the definition being made | bound early to the current definition, the only call allowed before `;` |

The draft IR of the demo's loops (prototype output, `v1-demo.ir`):

```text
word sum-below @4:1
  lit 0 @4:26
  prim swap @4:28
  lit 0 @4:33
  ?do @4:35
    i @4:39
    prim + @4:41
  loop @4:43
end @4:48
```

**What IR v1 must gain** (plan 4.4.1 and 4.4.2), in the Lean model
first:

- **Counted loops** with Forth-2012's exact rules: the loop parameters as
  a frame on the return stack (so `>R`/`R>` in a loop body, `I` and `J`
  are checked against it), `+LOOP`'s crossing rule, `?DO` skipping an
  empty range, `LEAVE` and `UNLOOP`.
- **`until` and `again` loops, several `while`s, and recursion** (a call of
  the definition itself).
- **Memory and declared data:** named regions with sizes and first
  contents (`created`, `cell n`, `cell undefined`), addresses as region and
  offset, `@ ! C@ C! +! MOVE FILL`, `cells`, values, a created word's
  `does` part; with bounds and no-overlap obligations (stage G2).
- **A semantics without fuel** (MiniForth's point): a relation saying what
  a program does, with the fuel-limited `run` proved sound and complete
  for it, so that a loop that never ends and *partial* correctness can be
  stated; today fuel is part of the meaning.
- **Loop rules with invariants:** a proved rule per loop form — for a
  `do` loop the index range gives the measure, for `begin` loops a
  user-given measure for total correctness — and weakest-precondition
  rules per instruction, proved once; receipts name the kind of
  correctness proved (total, safe-partial, partial).

**What the prototype showed** (section 9 of `run.sh`): `v1-demo.fs` (counted
loops with `I`, `J` and `LEAVE`, `BEGIN … UNTIL`, `RECURSE`, a user
defining word and its use, a `CREATE` table, a `VARIABLE`) runs in plain
Gforth (8 calls checked) and gives a 95-line draft IR v1, identical in
the alias and the mode-shift designs on both Gforths; with these words
loaded, IR 0.1's golden files are still byte-identical; 20 edge inputs
(a `DO` without `LOOP`, `J` in one loop, a defining word used inside a
definition or without its value, a `,` at the top level without a
`CREATE` …) gave 17 refusals and 3 intended passes, with identical
diagnostics in both designs.

## The prototype and what it showed

[Folder](../development/measurements/two-mode-prototype-2026-11-03/), run
with `bash docs/development/measurements/two-mode-prototype-2026-11-03/run.sh GFORTH`
from the repository root; outputs `run-gforth-1.0.0.out` and
`run-gforth-0.7.3.out`, identical apart from the version line. `cv.fs`
(about 420 lines) is the IR vocabulary and runner, `sym.fs` (about 320) the
symbolic demo; the [folder's README](../development/measurements/two-mode-prototype-2026-11-03/README.md)
lists the rest. Throwaway code: global variables, not reviewed, not in
`src/`.

| Check | Result, Gforth 1.0.0 and 0.7.3 |
| --- | --- |
| Correctness mode on the real `clamp.fs`, `examples.fs` and `all-primitives.fs`, unchanged | IR byte-identical to all three golden files |
| Run mode: the same files in plain Gforth | 19 calls of the six words, 0 failures |
| Today's reader tests (`tests/program/ir-reader.fs`) replayed | 108 verdict cases on today's main (outcome, reason, line, column) and 21 checks of diagnostic text and IR: 0 differences. The 93 other test blocks test the reader's own interface (output words, busy flags, contexts, files) and do not apply |
| Hostile inputs (`adversarial.fs`): recognizer and number syntaxes, `IMMEDIATE`, `POSTPONE`, `[`, `]`, `'`, `[']`, `LITERAL`, `STATE`, `EVALUATE`, `HEX`, `BASE`, `BYE`, `INCLUDE`, forged structure, names of vocabulary words, comments, a run started while Forth compiles | 81 refused, each at the right token; 5 accepted as intended (`-1 if 1 then`, number names, `x:dup`, `: . drop ;`, a `\` comment). Output byte-identical on both hosts |
| Round trip: IR → Forth text (calls in upper case, a literal that equals a defined name written `05`) → correctness mode → IR, for the three golden files and `awkward.ir` (names `5`, `-0`, `1e`, `$10`, `'a'`, `->x`, `forth:dup`, `"x"`, `x:dup`, 31 characters) | 4 of 4 identical apart from locations; a vocabulary name, a forward call, recursion and a redefinition refused |
| Planted faults in a copy of the vocabulary: `ELSE` written as `then`; minus signs dropped; names not folded to lower case; the 31-character limit raised | 4 of 4 caught (golden files or replayed reader tests) |
| Symbolic demo on the six words | clamp, checked add, checked abs, in-range: their paths; factorial and gcd: refused (loops) |
| Mode shift (§9): the portable third state (`ms.fs`) and Gforth 1.0's own (`ms-gforth1.fs`) on the golden files, the reader tests, the hostile inputs and a redefined `MAX` | byte-identical IR, 0 differences, identical diagnostics; the redefined `MAX` refused (the alias accepts it) |
| Defining words and loops (§10, `v1.fs`, `v1-demo.fs`) in both designs | run mode 8 calls; the same 95-line draft IR v1 in both designs; golden IR 0.1 unchanged; 20 edge inputs: 17 refused, 3 intended passes |

Not shown by the prototype: the receipt hash tie (§5) and Gforth 1.0
recognizer hardening; nothing about speed (each file took well under a
second).

## Test plan for the implementation

1. Golden IR for every accepted source, byte-identical (today's three).
2. Today's reader corpus replayed: verdicts, positions, diagnostics, IR;
   then a differential against the old reader over generated programs
   (the IR interpreter's random programs printed as Forth) and over
   `tests/program/ir_reader_files.py`'s line-end files, until it retires.
3. Hostile inputs: the prototype's 86, the syntax review's probes, every
   Forth-2012 number syntax, Gforth 1.0's recognizer forms, and after
   every outcome the search order, compilation word list, `BASE`, `STATE`
   and both stack depths as before the run.
4. A **Lean well-formedness check** of every emitted IR (MiniForth's
   linker idea): a decidable predicate — names unique, calls only to
   earlier definitions, constants well formed — checked by `decide`, and a
   theorem that a well-formed program never fails with *unknownWord*, so
   contracts can drop that failure formally.
5. The round trip IR → Forth → correctness mode → identical IR, with names
   that collide with vocabulary words (refused), read as numbers, or differ
   only in case.
6. Run mode: Gforth loads every accepted file; the three-way comparison
   (5,152 cases) unchanged.
7. Planted faults in a copy of the vocabulary, each caught: the four above,
   the gap check removed, a primitive writing another primitive's name,
   a frame taken from the data stack.
8. Both hosts: Gforth 1.0.0 locally, `make test` on 0.7.3 in CI.
9. With the mode shift: a Forth in which each standard word in turn was
   redefined before the run must be refused at that word; and, on Gforth
   1.0, the same IR from its own third state (b1) as a cross-check.
10. IR v1 (§10): every loop form and defining word with its Lean semantics
    and three-way comparison; `+LOOP`'s crossing rule at the cell edges;
    a defining word whose create part the model cannot run, or that is used
    inside a definition, refused; `VARIABLE`'s undefined first contents
    never read as 0.

## Risks

- **The vocabulary's meaning is trusted.** A word that writes the wrong
  instruction gives a proof about the wrong program. Mitigated as today:
  three-way runtime tests, golden files, planted faults, and Lean printing
  the IR from its own terms.
- **Host dependence.** Token splitting and number reading are the host's,
  in both modes — which is the point, but the gap check's syntax must stay
  inside what every supported host reads identically (probed on both).
- **Recognizers act before refusal** on Gforth 1.0 (an environment
  variable read, a `THROW`); harmless, and hardening is available.
- **Reading the invoking token back from `>IN`** relies on standard
  interpreter behaviour, as ADR 0017's words do; a vocabulary word run any
  other way finds that `SOURCE` is not the runner's line and stops.
- **Dictionary growth:** a word list and one word per definition per run;
  a `MARKER` between files or one process per file.
- **Run mode on a polluted host** (a standard word redefined before the
  file is loaded) is outside what a receipt covers; receipts say "loaded on
  a fresh Forth, last". The mode shift refuses such a Forth when it is the
  one verifying (§9); the run-mode Forth stays an assumption.
- **Host identity quirks** (mode shift): Gforth 0.7.3 shares one token
  among compile-only words and Gforth 1.0 moves `RECURSE`'s token; a word
  is therefore known by token and name, and each new host needs the same
  probe.

## Rejected alternatives

- **Option 1, today's reader**, as the design going forward: a parser of
  its own that must imitate Forth's tokenizing, case folding and number
  reading; the owner prefers option 2.
- **Compile, then run in an emit mode** (§1).
- **Our own token loop over the dictionary** (§1): option 1 again.
- **Gforth recognizers for literals:** not Forth-2012, and the two hosts'
  recognizers differ (§2).
- **Tagged or signed stack values to tell literals from other values**
  (ADR 0017 §6's sign rule): unnecessary, since no word takes anything but
  literals from the stack, and the sign rule is what the syntax review
  found forgeable.
- **Symbolic results as the proof obligations themselves** (§4): a second
  trusted semantics, and the Lean model and its proofs would be thrown
  away.
- **A late-bound dictionary** (MiniForth's model): not Forth's; calls are
  bound when the interpreter finds them.
- **Running correctness mode in the checker's process:** it runs source
  text, so it belongs in the authoring program (8.2.1).
- **Restricting Gforth 1.0's recognizers as the main defence:** host-only;
  kept as optional hardening.
- **Dual-mode words that test a flag** (§9 (a)): run mode would no longer
  be plain Gforth, would be slower, and would run trusted wrappers.
- **Gforth 1.0's own third state as the reference** (§9 (b1)): not on
  0.7.3 and built on experimental words; kept as a cross-check on 1.0.
- **Verify while loading** (§9 (c)): the file's code would run inside
  the verifier.

## Questions for the owner

**Answered on 2026-11-03** (see [the answers](#the-owners-answers-2026-11-03)):
1 option 2, with the mode shift to consider; 2 IR first; 3 the reader as
a cross-check, then retired; 4 names that read as numbers refused. The
questions as they were asked:

1. **Adopt option 2 as designed here** — the same file loaded with a
   LeanForth vocabulary (correctness mode) or with ordinary Forth (run
   mode); `:` keeps Forth interpreting; numbers checked against their text;
   only the vocabulary visible. *Recommendation: yes, as the design basis
   for replacing the reader (plan 2.5.3).* It is what you asked for, it
   runs the real files on both Gforths with byte-identical IR, and Forth's
   own interpreter now does the reading that the old reader had to imitate.
2. **What the words emit, and in which order.** *Recommendation: IR 0.1
   first; symbolic execution later, as an untrusted helper that is checked
   against the IR, growing into the proof producer for LeanForth's own
   checker* (§4's five steps). This keeps every existing Lean proof and
   test, and takes Python off your users' path without making a second
   meaning of every word trusted.
3. **Today's reader.** *Recommendation: keep it only as a test oracle
   until the vocabulary passes the [parser] gate, then retire it, keeping
   its tests.* Two front ends would double the work at every stage, and
   stronger independent checks remain.
4. **Names that read as numbers** (`: 5 7 ;`). Forth allows them and finds
   the name first; today's reader and the prototype follow Forth.
   *Recommendation: refuse them in correctness mode* (any name that Forth-2012
   or Gforth could read as a number). No real program needs one, a reader
   of `5` should see five, and the theorem words will refuse such names
   after their review; refusing accepts less than Gforth, never more, so
   it is safe.

**Open:**

5. **Mode shift or a separate vocabulary** (§9). Should each Forth word
   get its correctness meaning as a third *mode* of the same word
   (verification semantics, chosen by the interpreter's state, as
   interpreting and compiling are), or from a LeanForth word of the same
   name in a separate vocabulary (the alias)? *Recommendation: the mode
   shift, done portably (b2).* It is one word in two modes, as you
   described; it refuses a Forth whose standard words were changed before
   loading, which the alias cannot see; the host converts no numbers and
   runs none of Gforth 1.0's extra token forms; it runs the same on both
   Gforths; run mode stays exactly the file in plain Gforth; and the
   words' actions are the same as the alias's, so the choice is cheap to
   change later.

## Follow-ups

- On the open question: the verification semantics (or the vocabulary)
  and the shared runner in `src/` (a new module set under `src/program/`,
  the runner as a library), replacing the reader in the receipt pipeline,
  with the test plan above; the [parser] gate on that code. *Done
  2026-11-03 except the gate* (see the status above): test plan items 1-3,
  5-7 and 9 (without Gforth 1.0's own third state as a cross-check) and
  8 locally on both hosts; item 4's predicate. Then the reader retires
  (§8), and `src/author/runner.fs` could move onto `src/lib/text-run.fs`.
- IR v1 (plan 4.4.1, 4.4.2) as [§10](#10-defining-words-and-loops-in-both-designs)
  designs it: loops, recursion, memory and declared data, a semantics
  without fuel, loop rules with invariants.
- The Lean well-formedness predicate (done, 2026-11-03) and its
  *unknownWord* theorem (open) (test 4).
- Receipt schema: the assumption kind for the vocabulary ([format] gate).
- The theorem words: consider the gap check for their review findings.
- Plan 4.4.2 (IR v1 conditions): proved rules, a semantics without fuel
  with an adequacy proof, and the correctness kind named in receipts.

## Reproduction

```sh
bash docs/development/measurements/two-mode-prototype-2026-11-03/run.sh .tools/gforth/bin/gforth
bash docs/development/measurements/two-mode-prototype-2026-11-03/run.sh GFORTH_0_7_3_WRAPPER
```

Hosts: Gforth 1.0.0 (`.tools/gforth`, amd64) and Gforth 0.7.3 (Ubuntu's
package, extracted locally, as CI uses), Linux under WSL2, 2026-11-03.
`run.sh` includes the mode-shift comparison (`modes.sh`) and the IR v1
checks (`v1.sh`). The probes `p01-recognizers.fs` and `p02-scope.fs` (how
each host reads odd tokens with only one word list visible),
`p03-translations.fs` (Gforth 1.0's translation tokens) and
`p04-recurse.fs` (`RECURSE`'s token on each host) run with `gforth FILE`
from the same folder.

## Amendment 1 (proposed): IR 0.2, redefinition, output words and SHA-2

**Status: approved in design by the owner on 2026-11-04 [parser];
implemented the same day, before its [parser] implementation gate (below).**
Answers: own words may be redefined, Forth's way (A1);
standard words stay refused for now; output words allowed as effects (A2);
`LSHIFT`, `-rot`, number prefixes and 32-bit literals approved (A3), with
the owner's condition "the non-standard words should have portability
implementations" (so `-rot` gets a portable definition, `: -rot rot rot ;`,
for a Forth that lacks it); versioning as A4. The owner also asked whether
this is "a forth friendly native approach - not like the previous program to
read ascii and process it": it is. Everything here extends the approved
program words (the portable mode shift of §9): Forth's own interpreter
reads the file, and each word's verification semantics, including `:` and
`;` for a redefinition, writes the IR; no separate text translator is
involved ([decisions](../project/OWNER_DECISIONS.md#ir-02-design-approved-2026-11-04)).
Proposed 2026-11-04. It answers the
owner's request when approving the program words
([decisions](../project/OWNER_DECISIONS.md#program-words-and-run-records-approved-2026-11-04)):
"reconsider the refusal of redefinintions - for example sometimes adding
a dup . into a word definition for debugging helps - surely they can nest
the names?", and designs the IR additions that plan stage SHA-2 needs
([plan](../project/PLAN_DRAFT.md#program-track-goal-most-of-forth-2012-core-owner-2026-11-02)).
The [parser] gate decides the design before any code; the receipt
schema change (A4) goes through the [format] gate when the first receipt
needs it. It changes no typing or conversion rule of the checker.
Evidence: [probes](../development/measurements/ir-0.2-probes-2026-11-04/README.md)
run on Gforth 1.0.0 and 0.7.3 (their standard output identical but for
three number forms outside Forth-2012), and two Lean checks.

**Implemented 2026-11-04, before its [parser] implementation gate**, in
both designs, as A1-A4 say; the [program IR](../programming/PROGRAM_IR.md#ir-02)
describes it and its evidence (A5), and Lean's Parts 7 and 8 of
`tests/reference/program-ir.lean` prove `runOut_result`, the debugging pair,
the clamp with `dup .`, and the SHA-2 stage's first words: `sha-rotr`,
`sha-ch`, `sha-maj` and `sha-big-sigma0` (`src/program/sha-words.fs`) equal
to FIPS 180-4's ROTR, Ch, Maj and Σ0 for all 32-bit inputs on every cell of
at least 33 bits. Where the implementation settles what this amendment
left open or departs from it:

- **The version line comes last.** Since it depends on every line, the
  program words keep the IR in a heap buffer during the run and send it,
  version line first, to the output word when the run ends (after the
  caller's settings are back, while the run is still under way), with no
  limit of their own; a run whose IR the heap cannot hold stops as *full*.
  The diagnostic line has a slot of its own, and a run that stops as *full*
  sends it alone, no IR line (review rvIR3, L1: the first version sent the
  IR held so far, with no diagnostic, when the heap was full). An output
  word that fails still fails the run as invalid ("output word failed").
- **A new reason 32**, "text not closed on its line", for `."` and `S"`
  without their closing quote on the line (A2 names no reason; reason 8's
  "comment not closed" would mislead); a tab in such a text is refused as
  reason 16, since IR text holds none.
- **`TYPE` after `S"`** is read by `S"`, as `:` reads its name, and checked
  by the design: the mode shift by identity (a `TYPE` redefined before the
  run is refused there, reason 29), the separate vocabulary by name, as it
  knows all its words.
- **Literals are doubles** while they are read, so a value up to 2^32 − 1 is
  written exactly on 32-bit hosts too.
- **`-rot` and `.S`** have verification semantics, so they must be words of
  the verifying Forth; `src/lib/portability.fs`, which the program words
  load, defines `-rot` as `rot rot` and `.S` as both Gforths print it on a
  Forth without them (review rvIR3, L9), and run mode needs it loaded
  first there.
- **The IR interpreter** (`src/program/ir-run.fs`) reads IR 0.2, refuses an
  IR 0.2 instruction under IR 0.1's version line, and prints what out lines
  print to a sink, `.S` as both Gforths print it; `Event.render` in Lean
  gives the other events' bytes.
- **Receipts:** the generator refuses an IR 0.2 program, and
  [PROGRAM_RECEIPTS.md](../programming/PROGRAM_RECEIPTS.md#schema-03-what-ir-02-receipts-need)
  states what schema 0.3 needs; `src/lib/sha256.fs` is unchanged (it does
  not load `src/program/sha-words.fs` yet).

### In plain words

- **Redefining your own words: yes, Forth's way.** When a file defines
  `lf-clamp` twice, both versions exist, as in Gforth. Every use means the
  version that existed where it was written; words written before the
  second version keep calling the first. In the IR each version has its
  own name: the first is `lf-clamp`, the second `lf-clamp'1`, the third
  `lf-clamp'2`. So the names nest: a second `lf-clamp` may call the first,
  for example to show the stack around it,
  `: lf-clamp .s lf-clamp .s ;`, whose IR is `word lf-clamp'1` holding
  `out .s`, `call lf-clamp`, `out .s`. A proof, and a receipt, is always
  about exactly one version, named in it. Both Gforths behave identically
  in all twelve probes of this (probe 1).
- **Redefining standard words** such as `: . drop ;`: my recommendation
  is to keep refusing them for now (question 2). They work in Forth, but a
  verified file is often a library loaded before other code (SHA-256 is),
  and its `.` would silently change every `.` loaded after it.
- **`dup .` for debugging: yes.** `.`, `U.`, `CR`, `EMIT`, `SPACE`,
  `SPACES`, `."`, `S" … " TYPE` and `.S` become *output effects*. In the
  IR, `.` is written `out .`; for the stacks it only takes one cell, and
  what it prints goes to a separate list of output events. A proof about
  the stacks never looks at that list, and Lean will prove once that the
  stacks never depend on it. Already checked on today's model, with `.`
  standing in as "take one cell": the clamp proof, unchanged, proves the
  clamp with a `dup .` added (probe 6). A receipt says that a
  word prints, and that printing is assumed to succeed: Gforth stops with
  an error when it cannot write, for example to a closed pipe (probe 8).
- **SHA-256's helper words** need two more primitives, `LSHIFT` and
  `-rot`, and Forth-2012's `$` hexadecimal numbers. ROTR stays plain
  Forth (`2dup rshift -rot 32 swap - lshift or sha-w32`); a first Lean
  check proves that these instructions compute the standard's ROTR on
  64-bit cells (probe 7).
- **Nothing approved changes.** A file that uses nothing new gives byte
  for byte today's IR, still labelled `lf-ir 0.1`, so the golden files
  and the clamp receipt's IR stay as they are, and so does the receipt
  format; only the receipt's sentence describing the program words is
  reworded. Receipts of programs that use the new instructions need
  receipt schema 0.3 (one field widened, one added), decided at the
  [format] gate when the first one is written.
- Five questions for you are at the [end](#a6-questions-for-the-owner).

### A1. Redefinition with Forth's early binding

**What Forth does.** Probe 1, identical on Gforth 1.0.0 and 0.7.3 (they
also print "redefined NAME" warnings, to standard error):

| Probe | Result |
| --- | --- |
| `: pf 1 ;  : pg pf ;  : pf 2 ;  : ph pf ;` | `pg` gives 1, `ph` and `pf` give 2: a use is bound where it is compiled |
| `: pk 10 ;  : pk pk 1+ ;  : pk pk 1+ ;` | `pk` gives 12: inside its own definition a name is the previous version, since a definition is hidden until its `;` |
| `: pq pq ;` with no earlier `pq` | THROW −13, undefined word |
| `: Cw 1 ;  : cw 2 ;  : CW 3 ;` | `cw` gives 3: one name in any case of letters |
| `1 constant kk … 2 constant kk`; `: wc 7 ; … 8 constant wc` | constants are redefined the same way, also a word by a constant |
| `: pr 100 ;  : pr dup 0> if 1- recurse then ;` | `3 pr` gives 0: `RECURSE` calls the version being defined |
| `: pt 100 ;  : pt dup 0> if drop pt then ;` | `3 pt` gives 100: the plain name calls the previous version |
| two headers of one name in one word list | `SEARCH-WORDLIST` finds the newer; the older's execution token still runs |
| `: . drop ;`, `: dup over ;` | code compiled before keeps the host's word, code compiled after calls the file's |

**The rule.** A definition (`:` or `CONSTANT`) may use a name that the
file defined before, in any case of letters. As in Forth:

1. The new version becomes visible at its `;` (a constant as soon as its
   name is read). Inside its own body the name means the previous
   version; with no previous version it is refused as today ("recursive
   call"), where Gforth throws −13.
2. Every use is bound when the interpreter reaches it, to the version
   visible there. Lines already written are never changed.
3. **Each version has its own IR name:** the first is the name, folded to
   lower case, as today; the k-th redefinition is the folded name followed
   by `'k` (`lf-clamp'1`, `lf-clamp'2`), whatever case of letters the
   source uses. Every `word`, `constant` and `call` line uses the
   version's IR name.
4. A definition whose IR name is already the IR name of an earlier
   definition is refused (new reason 31, *unsupported*, "a name the IR
   gives another version"): a file that defines `x` twice and also
   `x'1` is refused at whichever comes second. So IR names stay unique in
   a file.

Names that read as numbers, names of more than 31 characters and the
capacity of 32 definitions per file stay as today (each version counts as
a definition; the suffix may take an IR name past 31 characters, since
only source names are limited).

**Example: nested names** (probe 5). Suppose `src/program/clamp.fs`,
whose `lf-clamp` stands on lines 12–14, had on line 15 a second version
that shows the stack around the first:

```forth
: lf-clamp ( value lower upper -- result true | false ) .s lf-clamp .s ;
```

```text
word lf-clamp'1 @15:1
  out .s @15:57
  call lf-clamp @15:60
  out .s @15:69
end @15:72
```

Plain Gforth (both versions): `5 0 10 lf-clamp` prints
`<3> 5 0 10 <2> 5 -1 ` and leaves `5 -1`.

**Which version a proof and a receipt cover.**

- *The IR* names each version and where its `:` stands
  (`word lf-clamp'1 @15:1`), and each `call` names the version bound
  there.
- *Lean* states theorems about one IR name:
  `callWord c p fuel "lf-clamp'1" s = …`. `lookup` finds the first
  definition of a name, which is exact because IR names are unique (the
  well-formedness check of Part 6 already requires it).
- *The receipt* (schema 0.2, no change): `program.word` is the IR name,
  `"lf-clamp'1"` (its pattern, printable ASCII with letters in lower case,
  admits `'`), and `program.source.line` the line of that version's `:`.
- *After loading*, Forth finds the name's last version. A receipt about an
  earlier version is still useful (the words compiled before the
  redefinition call it) but is not about what the name means after
  loading; its `trusted-reader` assumption says so in words: "version 1 of
  lf-clamp, line 12; after loading, the name means version 2, line 15,
  which this receipt does not cover". The generator writes that sentence
  whenever the version is not the last.

**How the program words would do it.** The file's word list already gets
one header per definition, each holding its definition's index, and a
definition's record its name. The changes: (1) the name check stops
refusing names of the file's own words; (2) each record keeps its IR name
and the index of the version it replaces, if any; (3) a lookup that finds
the definition being compiled takes that previous version instead (none:
"recursive call", as today) — Forth's hiding, done by the program words
because their `:` makes the header at once; (4) the collision check of
rule 4. Both designs share these actions, as they share all others.

**Why the IR still matches what plain Gforth does.** Gforth binds each
use, at the moment it compiles it, to the newest visible header of that
name, ignoring the case of letters; hides a definition until its `;`;
and keeps older versions running (probe 1). The program words find a
word of the file with `SEARCH-WORDLIST` on the file's word list, which on
both hosts finds the newest header (probe 1); they do so at the same
point of the text, the token being read, and apply the same hiding rule;
and they write the found version's unique IR name. So every `call` in
the IR names the definition that Gforth's compiled call executes, and
Lean's `lookup` by that unique name finds that definition's body: the IR's
call graph is Gforth's. Words of the host are unaffected: they are found
only when the file's word list has no word of that name.

**The identity check, `RECURSE` and the reserved words.**

- *The identity check* (§9) is untouched. The file's words, every version,
  live in the file's own word list, never in `FORTH-WORDLIST`, so they can
  neither trigger the check nor hide a host whose standard word was
  replaced.
- *`RECURSE`* stays reserved in IR 0.2 (stage G1). When it comes, it
  writes a call of the version being defined (`call lf-clamp'1`), while
  the plain name inside that definition calls the previous version
  (probe 1, `pr` and `pt`). It stays known by its name, since Gforth 1.0
  moves its token.
- *The reserved words* keep both roles under the recommendation of
  question 2: refused where used, and not to be redefined. The list
  shrinks by the words that get verification semantics (A2, A3: `.`,
  `U.`, `CR`, `EMIT`, `SPACE`, `SPACES`, `TYPE`, `S"`, `."`, `LSHIFT`).
  The table gains `.S` and `-rot`, which are not Forth-2012 Core words but
  are words of both Gforths (probe 4); today a file may define its own
  `-rot` or `.s`, and IR 0.2 would refuse that as a redefinition.

**A redefined standard word, such as `: . drop ;`.** *Recommended
(question 2): still refused*, "name already defined", as today. Forth
allows it, but (1) the owner's case needs only output words and the
file's own words, (2) a verified file is often a library loaded before
other code (`src/lib/sha256.fs` is loaded by the importer), where its `.`
or `dup` would silently change all code compiled after it, which no
receipt about the file's own words can show, and (3) refusing accepts less
than Gforth, never more, so it can be relaxed later. Debug output can be
switched off Forth's other way, with a word of one's own:
`: ?. ( n -- n ) dup . ;` used while debugging, then redefined before its
users as `: ?. ( n -- n ) ;`.

*If you choose to allow it*, the program words would do what Gforth does
(probe 1): before `: . drop ;`, `.` writes `out .`; after it, `.` is the
file's word, written `call .` (its IR, `word .` with `prim drop`, is a
definition named `.`, as distinct from the instruction `out .` as
`call dup` is from `prim dup`). The separate vocabulary would then have
to search the file's words before its own (today it searches its own
first, as defence in depth), or after `: . drop ;` it would still find
its own `.`; the mode shift already searches the file's words first.
Receipts would list every standard name the file redefines, and test
harnesses would load programs into a word list of their own and call
words by execution token. Redefining the words that read the file or
make its structure (`:`, `;`, `(`, `\`, `CONSTANT`, `IF` …) would still be
refused: Gforth accepts them, but such a file is a mistake.

**Risks.**

- *A receipt for a shadowed version read as covering the name after
  loading.* Mitigated by the version's IR name in `program.word` and the
  sentence in the `trusted-reader` assumption.
- *Late binding by mistake.* Were calls written with the source name, a
  call would reach the oldest version in Lean (`lookup` takes the first)
  and the newest in Gforth: wrong either way. Planted faults (tests).
- *The hiding rule wrong.* Finding the new version inside its own body is
  refused as recursion (safe); taking the wrong predecessor is unsound.
  Planted fault and host-oracle tests.
- *Collision refusals* (rule 4) refuse a few legitimate files, such as one
  that defines `x`, `x` and `x'1`.
- *Dictionary growth:* one header per version, as today one per definition.

**Tests** (host oracle: plain Gforth decides).

1. Generated files with random redefinitions, one definition per line:
   names in several cases of letters, constants, words redefined as
   constants, bodies calling the previous version, words compiled between
   versions. Plain Gforth 1.0.0 and 0.7.3 load each file line by line into
   a word list of its own, keeping each definition's execution token right
   after its line; every version's token then runs on random inputs and
   must leave the stacks that the IR interpreter (`src/program/ir-run.fs`)
   gives for that version's IR name, and Lean's model on a sample. Zero
   differences.
2. Probe 1's cases as fixed tests in both designs, with their IR lines,
   for example `: pf 1 ; : pg pf ; : pf 2 ; : ph pf ;` giving
   `word pf'1`, `call pf` in `pg` and `call pf'1` in `ph`.
3. Refusals at the right token: `: pq pq ;`, the collisions of rule 4, and
   (under question 2's recommendation) every standard name.
4. Planted faults, each caught by tests 1–2: calls written with the source
   name; the hiding rule removed; versions counted without folding case;
   the collision check removed.
5. Lean: well-formedness of renamed programs by `decide`; a program whose
   call reaches a later version refuted.

### A2. Output words as effects

**The words.** Only inside definitions; at the top level they would run
while the file loads, as part of no word, and are refused ("not allowed
outside a definition"). What they print was probed on both Gforths
(probes 2 and 3), with `BASE` ten:

| Forth | IR 0.2 line | Stack | Event | What both Gforths print |
| --- | --- | --- | --- | --- |
| `.` | `out .` | `( n -- )` | number n | n in decimal, then a space |
| `U.` | `out u.` | `( u -- )` | the cell's bit pattern as a natural number | that number, then a space (`-1 U.` prints 18446744073709551615 on 64-bit cells) |
| `CR` | `out cr` | `( -- )` | newline | an LF |
| `EMIT` | `out emit` | `( x -- )` | character x | the byte x mod 256 (321 gives `A`, −1 the byte 255); Forth-2012 defines only graphic characters |
| `SPACE` | `out space` | `( -- )` | 1 blank | a space |
| `SPACES` | `out spaces` | `( n -- )` | max(n, 0) blanks | n spaces; nothing for 0 or −2 |
| `." text"` | `out ." text"` | `( -- )` | text | the text (one space after `."` is the delimiter; more are kept) |
| `S" text" TYPE` | `out ." text"` | `( -- )` | text | the same; `TYPE` must follow on the same line |
| `.S` | `out .s` | `( -- )` | the whole data stack | host-defined: `<depth> `, then at most the top nine cells, deepest first, each with a space (both Gforths) |

`."` must close on its line, as `(` must. `S"` anywhere but directly
before `TYPE`, `TYPE` alone, `S\"` and `.(` stay refused: a string's
address is memory, which IR 0.2 does not have, and `.(` prints while a
definition is compiled, not when it runs (probe 2). `TYPE` after `S"` must
be Forth's own, by identity, and not a word of the file. Like every word
with verification semantics, the output words are known by identity
(§9); on Gforth 0.7.3 `."` has a token of its own, not the one its
compile-only words share (probe 4), so §9's limit there does not reach
it. A `."` text too long for an IR line (96 characters) stops the run as
*full*, as any long IR line does.

**Text form.** One new line kind, `out`:

```text
line    = indent ( IR 0.1's lines | "out " outword | "out ." QUOTE " " text QUOTE ) [loc] NL
outword = "." | "u." | "cr" | "emit" | "space" | "spaces" | ".s"
text    = { printable ASCII character other than QUOTE, or space }
```

QUOTE is the character `"`. The text cannot contain one, so the first `"`
after `out ." ` ends it, whatever the text holds (even ` @1:2`).

**Lean semantics** (planned, in `tests/reference/program-ir.lean`):

```lean
inductive Out where
  | dot | uDot | cr | emit | space | spaces | dotS | text (s : String)
-- Instr gains: | out (o : Out)

inductive Event where
  | number (n : Int) | unsigned (u : Nat) | newline | char (x : Int)
  | blanks (n : Nat) | text (s : String) | stack (d : List Int)
```

- `run` gives `out o` its stack effect only: `.`, `U.`, `EMIT` and
  `SPACES` take one cell (*underflow* without one), the others nothing.
  `run` stays the one function every stack proof uses.
- `runOut c p fuel b s : Result × List Event` follows the same recursion
  and also collects the events in order; a callee's events come where it
  is called, and a run that fails keeps the events before the failure
  (the host printed them).
- **Theorem `runOut_result`:** `(runOut c p fuel b s).1 = run c p fuel b s`
  for every program, fuel, block and state.
- *The debugging pair:* `run c p fuel (.prim .dup :: .out .dot :: rest)
  ⟨x :: d, r⟩ = run c p fuel rest ⟨x :: d, r⟩`.
- `Event.render` gives the characters of each event as the table says;
  `.S` has none (Forth-2012 leaves its format to the system), and `EMIT`
  of a non-graphic character gives the byte the Gforths write.

**Why a proof that ignores output stays sound.**

1. *In the model:* a contract about the stacks is stated with `run`, as
   `Meets` is today. By `runOut_result`, the stacks and the failure of the
   run that prints are exactly `run`'s, so the contract is a true
   statement about the word whatever it prints. No instruction reads the
   events, so output can never change a stack.
2. *Against the host:* each output word's stack effect is Forth-2012's,
   and the hosts agree (probe 2: `7 8 tidy`, which prints with `.`, leaves
   7; `.S` leaves the stack as it was). The three-way tests check it on
   every program (tests below).
3. *What the IR cannot see* is stated in the receipt: output is assumed to
   succeed — with standard output closed both Gforths discard it
   silently, but with a pipe whose reader has gone, 100,000 `.`s stop with
   THROW −2049 on both (probe 8), an exception the model does not have; `.`
   and `U.` print in the `BASE` in force when the word runs (probe 2:
   `BASE` 16 prints hexadecimal), which matters only to a contract that
   describes output; and they may overwrite the pictured-numeric buffer
   (Forth-2012 lets them; the probe's Gforths left a `#>` string intact),
   which IR 0.2, having no memory, cannot observe.

**The primary case: `dup .` in a definition.** Mathematics: the clamp
and the value max(v, l), printed when l ≤ u. Forth (probe 5):

```forth
: lf-clamp ( value lower upper -- result true | false )
  2dup > if 2drop drop false exit then
  >r max dup . r> min true ;
```

IR 0.2, line 14 (lines 12 and 13 as today):

```text
  prim >r @14:3
  prim max @14:6
  prim dup @14:10
  out . @14:14
  prim r> @14:16
  prim min @14:19
  prim true @14:23
end @14:28
```

Lean: `clamp_correct`'s statement is unchanged, and so, it is expected,
is its proof. Probe 6 checked exactly that on today's model, with `.`
written as `prim .drop`, its stack effect: the proof of
`tests/reference/program-ir.lean`, copied with only the names changed,
proves the clamp with `dup .` added; with `.` planted as doing nothing,
Lean rejects it. A contract that also describes the output adds a clause
on `runOut`'s events, here `[.number (max value lower)]` when
lower ≤ upper and `[]` otherwise. Gforth, both versions:
`5 0 10 lf-clamp` prints `5 ` and leaves `5 -1`; `15 0 10` prints `15 `
and leaves `10 -1`; `5 10 0` prints nothing and leaves `0`.

**What a receipt says about output** (schema 0.3, A4): `program.output`
is true when the word or any word it calls has an `out` line, and then an
assumption of the new kind `output` is required (as `floatingPoint`
requires `floating-point` today), saying whether the contract describes
the output or only the stacks, that output is assumed to succeed, and the
`BASE` assumed. The `run` part compares stacks as today and, when the
contract describes output, the captured standard output with the rendered
events.

**Risks.**

- *Output fails on the host* (a broken pipe) where the model cannot fail:
  stated as an assumption; the word's stacks are then not what the proof
  says, because the word does not return.
- *`BASE` at run time* changes what `.` prints, never the stacks.
- *Host-defined formats* (`.S`, `EMIT` beyond ASCII): treated as events
  only; a contract describing them names the host.
- *A contract that describes output trusts `render`*, the characters of
  each event, tested against both hosts, not proved.
- *Trace length:* output inside a loop gives one event per repetition;
  only memory and time, no effect on the stacks.

**Tests.**

1. For each output word, plain Gforth 1.0.0 and 0.7.3 run as a separate
   process, their standard output captured: the bytes equal the rendered
   events of `runOut` (and of the IR interpreter, once it records events)
   for `.` and `U.` at 0, −1, the smallest and largest cell, `CR`, `EMIT`
   for 0 to 255 and beyond, `SPACE`, `SPACES` for positive, zero and
   negative counts, `."` with leading spaces and `S" … " TYPE`; `.S`
   compared as events plus the probed format. The stacks after each
   equal `run`'s.
2. Non-interference: the IR interpreter's random programs with `dup .`,
   `.s`, `cr` and `." x"` inserted at random points; on both hosts the
   stacks equal `run`'s, and equal the program's without the insertions
   wherever the inserted `dup` had a cell.
3. Lean: `runOut_result`; the debugging pair; the clamp with `dup .` as a
   theorem (probe 6, made real); the 35 existing theorems unchanged.
4. Refusals: output words at the top level, `S"` without `TYPE`, `."` not
   closed on its line, `TYPE` of the file's own definition.
5. Planted faults: `.` written without its `out` line, or as taking no
   cell; an event dropped in `runOut`.

### A3. What stage SHA-2 needs

The helper words of `src/lib/sha256.fs` against IR 0.1:

| Word | Forth, as in `sha256.fs` | IR 0.1? | Needs |
| --- | --- | --- | --- |
| `sha-mask` | `$10000 dup * 1- constant sha-mask` | the constant's body yes: `*` and `1-` wrap | the `$` prefix (or writing 65536) |
| `sha-w32` | `sha-mask and` | yes | — |
| `sha-shr` | `rshift` | yes (`RSHIFT` modelled for counts below the cell width) | — |
| `sha-rotr` | `2dup rshift -rot 32 swap - lshift or sha-w32` | no | `LSHIFT`, `-rot` |
| `sha-ch` | `tuck xor rot and xor` | yes | — |
| `sha-maj` | `>r 2dup and -rot or r> and or` | no | `-rot` |
| the four Σ and σ | `dup 2 sha-rotr over 13 sha-rotr xor swap 22 sha-rotr xor` and so on | yes, given `sha-rotr` | — |

`AND`, `OR`, `XOR`, `INVERT` and `RSHIFT` are IR 0.1 primitives already.
Today the program words refuse `LSHIFT` ("a Forth word outside IR 0.1"),
and `-rot`, `$10000` and `4294967295` ("not a known word or 32-bit
decimal").

**Findings.**

1. *No literal above 2,147,483,647 is needed by `sha256.fs` as written.*
   The mask is computed (`$10000 dup * 1-`, which wraps to all ones on
   32-bit cells and gives 2^32 − 1 on wider ones, exactly in IR 0.1's
   wrapping semantics), and the 64 constants are written in 16-bit halves.
   What is needed is the `$` prefix. Wider literals are still worth
   admitting (below), since 32-bit code is naturally written with them.
2. *`sha256.fs` cannot be read in correctness mode as it is* (`require`,
   the module words, `[if]`, `begin-structure`, `create` tables). Stage
   SHA-2 therefore moves the mask and the eight FIPS functions into a
   small plain file, for example `src/lib/sha256-words.fs`, which
   `sha256.fs` requires inside its public section, so that the code the
   product runs is the code verified.
3. *On 64-bit hosts the product's round and message schedule do not call
   these words:* `sha256.fs` writes them out there with each rotation done
   as one shift of a doubled word (`sha-doubling`). Proofs of the helper
   words cover the portable path and the words as such; stage SHA-3 must
   also prove the doubled round equal to them, or make the plain round the
   product's path.
4. *The verification-condition generator* (`scripts/program_vc.py`, v0)
   accepts only the literals −1, 0 and 1, which fit every cell width; the
   shift counts, 32 and 65536 need a cell-width hypothesis in the
   generated contract, or SHA-2's theorems are written in Lean by hand, as
   the six example words' are.

**`LSHIFT` and `-rot` in IR 0.2.** `LSHIFT ( x u -- x' )`: for
0 ≤ u < w, the bit pattern shifted left with the bits above the cell
dropped, in Lean `c.signed ((c.unsigned x <<< u) % 2 ^ c.bits)`; any other
count is *unmodeled*, as for `RSHIFT`. Forth-2012 makes such counts
ambiguous, and the hosts take the count modulo 64 (probe 4: `1 64 lshift`
gives 1, `1 65 lshift` 2, `1 -1 lshift` 2^63, on both). `-rot
( x1 x2 x3 -- x3 x1 x2 )` is `rot rot`. It is not a Forth-2012 word, but
both Gforths define it (probe 4), `src/lib/portability.fs` supplies it
elsewhere, and LeanForth's own code uses it widely; the alternative is
rewriting `sha256.fs` with `rot rot` (question 4).

**Literals.** The program words would read, besides plain decimals,
Forth-2012's prefixed forms: `#[-]digits`, `$[-]hexdigits` (either case),
`%[-]binary digits` and `'c'` for a printable character other than a
space, each with a value from −2^31 to 2^32 − 1, so that every 32-bit
word, signed or unsigned, can be written. Both hosts read each of these
forms identically (probe 4). Refused: `-$10`, which Forth-2012 does not
define (its sign must follow the prefix; the probe's "Gforth 1.0 refuses
it, 0.7.3 reads −16" was wrong: Gforth 1.0 keeps state from one number to
the next, refuses `-$10` right after `$-10`, as in the probe, and reads −16
otherwise, review rvIR3, L4); the forms on which the hosts differ, `1_000`
and `$1_0` (1.0 reads them, 0.7.3 refuses them); `0x10`, which both read
but Forth-2012 does not define; and double-cell numbers such as `1.`. The IR still
writes decimals (`lit 4294967295`). IR 0.1's semantics already makes a
literal outside the cell *unmodeled*, so a theorem that uses one must
assume cells of at least 33 bits, and Lean holds it to that. The separate
vocabulary compares the host's reading with the text; on a 32-bit host,
which reads `$FFFFFFFF` as −1, it would refuse where the mode shift writes
`lit 4294967295` (unmodeled there): a difference only on hosts nobody
supports today.

**32-bit masking on a 64-bit cell.** The IR keeps one kind of cell. A
32-bit word is a cell holding a number from 0 to 2^32 − 1, as
`sha256.fs` says, and masking is the program's own `and` with `sha-mask`,
never implicit. The theorem relates the cell to the specification's
`BitVec 32`: for every cell width w ≥ 33, every word x, every count
n < 32 and every stack below,

```lean
callWord c shaProgram fuel "sha-rotr" ⟨(n : Int) :: (x.toNat : Int) :: d, r⟩ =
  .next ⟨((ROTR n x).toNat : Int) :: d, r⟩
```

(32-bit cells, where `sha256.fs` also works, would encode a word as
`c.signed x.toNat` and come later.) An IR with a 32-bit mode that masks by
itself was rejected: no Forth host does that.

**How ROTR is proved.** Probe 7 checks the core in Lean today, on a copy
of IR 0.1's cell arithmetic with `LSHIFT` added as above:
`rotr_masked` proves that or'ing x >> n with (x << (32 − n)) cut to
w bits and masking with 2^32 − 1 is the standard's ROTR on every width
w ≥ 32, from the specification's own `ROTR_toNat` and Lean's lemmas on
`Nat` bits; `rotr_cells64` proves that the instructions of `sha-rotr` and
`sha-w32` leave ROTR on 64-bit cells; `unmasked_rotr_wrong` refutes the
word without its mask (x = 2^31, n = 1). All use only `propext`,
`Classical.choice` and `Quot.sound`. The real proof runs `ir_simp`
through the instructions in the model and then these lemmas, generalised
to every width w ≥ 33. Σ0 and the others follow by using ROTR's theorem
as a rewrite rule for the call and the specification's
`bigSigma0_toNat`; wrong variants (a rotation by the wrong count, a shift
for a rotation, `Ch` without its complement) are refuted, as
`SHA256_SPEC.md` plans.

### A4. Versioning

- **IR 0.2** is IR 0.1 plus three things: `prim lshift`, `prim -rot` and
  the `out` lines. Version names (`lf-clamp'1`) and wider literals are
  not new IR: names were always opaque tokens and integers of any size
  (outside the cell they are *unmodeled*). Only the program words change
  for them.
- **The lowest version that fits.** The program words write `lf-ir 0.2`
  only when the IR has one of the three new things, and otherwise
  `lf-ir 0.1` with today's bytes. So `clamp.ir`, `examples.ir`,
  `all-primitives.ir` and the clamp receipt's IR hash stay unchanged; a
  second golden file covers the new primitives and every output word.
- **Lean model:** `Prim` gains `lshift` and `negRot`, `Instr` gains `out`,
  `run` gains their cases; `runOut` and `runOut_result` are new; the
  printer writes the lowest version that fits; well-formedness also
  refuses `out` in a constant's body. All 35 existing theorems must check
  unchanged; that is part of the acceptance.
- **Today's reader** stays IR 0.1 and refuses every IR 0.2 input. It was
  the oracle until the [parser] gate, which passed on 2026-11-04, and is
  due to retire as §8 plans; IR 0.2's oracle is plain Gforth.
- **Receipts.** Schema 0.2 is unchanged for IR 0.1 programs, version names
  included. The `trusted-reader` assumption's text changes (today it says
  redefinitions are refused), so the clamp receipt is regenerated with the
  new text, still schema 0.2. A receipt whose IR is 0.2 cannot be written
  in schema 0.2, whose `program.ir.version` is the constant `"0.1"`: that
  field must change. **Schema 0.3** would make exactly two changes:
  `program.ir.version` is `"0.1"` or `"0.2"`; and `program.output`
  (boolean, required), with the assumption kind `output` required when it
  is true. The [format] gate decides it when the first IR 0.2 receipt (a
  SHA-2 helper word) is generated, not before; the pending renaming of
  `trusted-reader` could ride along. Until then the generator refuses to
  write a receipt for an IR 0.2 program.
- **Messages:** reason 2 becomes "a Forth word outside IR 0.2"; new reason
  31 (A1, rule 4).

### A5. Test and evidence plan

The tests of A1 and A2, plus:

1. `LSHIFT` and `-rot` in the three-way comparison (IR interpreter, both
   Gforths, Lean's model) at the edges: counts 0 and w − 1, values 0, −1,
   the smallest and largest cell; counts of w and more and negative ones
   *unmodeled* in the IR (the hosts' values recorded, not compared).
2. Literals: each Forth-2012 form against both hosts' reading of it
   (probe 4); the range edges −2^31 and 2^32 − 1 accepted, −2^31 − 1 and
   2^32 refused; the forms the hosts disagree on refused; the IR → Forth →
   IR round trip with prefixed forms.
3. Today's golden files, the 287-input cross-check and the 400 random
   programs: byte-identical, header `lf-ir 0.1`.
4. SHA-2 itself (the stage, after IR 0.2): each helper word's IR proved
   equal to its specification function for all inputs, wrong variants
   refuted, and the words run by plain Gforth on the NIST-derived values.
5. Both hosts locally (the change touches number reading), then CI.
6. An independent review of the implementation before its [parser] gate,
   as for IR 0.1's program words.

### A6. Questions for the owner

1. **Redefining your own words.** Should a file be allowed to define a
   name again, as Forth allows, with each use meaning the version where it
   was written and each version getting its own IR name (`lf-clamp`,
   `lf-clamp'1`)? *Recommendation: yes.* It is Forth's own rule, both
   Gforths behave identically (probe 1), it gives your nested names (a
   second `lf-clamp` calling the first), and proofs stay exact because
   every version has its own name and every receipt names one version. The
   only refusal it adds is a clash with a name the file also uses
   literally, such as `x'1`.
2. **Redefining standard words** such as `: . drop ;` or `: dup over ;`.
   *Recommendation: keep refusing them for now.* A verified file is often
   a library loaded before other code; its `.` would silently change every
   `.` compiled after it, which no receipt about the file can show.
   Refusing accepts less than Forth, never more, so it can be relaxed
   later; switching debug output off works with a word of your own (`?.`).
   If you prefer full Forth behaviour, the amendment says how it would
   work and what it costs.
3. **Output words as effects** (`.`, `U.`, `CR`, `EMIT`, `SPACE`,
   `SPACES`, `."`, `S" … " TYPE`, `.S`, inside definitions only).
   *Recommendation: yes.* It is the debugging you asked for; the stack
   proof is unaffected, by a Lean theorem planned with it, and probe 6
   showed the clamp's proof working unchanged with a `dup .` added (`.`
   standing in as "take one cell" on today's model). The
   price is honest receipts: a word that prints says so, and assumes its
   output can be written.
4. **What SHA-256 needs:** `LSHIFT` and `-rot` as primitives, and
   Forth-2012's number prefixes with 32-bit values. *Recommendation: yes,
   with `-rot`* rather than rewriting `sha256.fs` with `rot rot`: both
   Gforths have it, our code uses it widely, and keeping the library's
   source unchanged keeps "the code the product runs is the code
   verified" simple. Literals up to 2^32 − 1 make a theorem hold only on
   cells of at least 33 bits, which Lean enforces.
5. **Versioning.** Label the IR 0.1 whenever nothing new is used, so
   everything already approved stays byte for byte as it is, and bring
   receipt schema 0.3 (one field widened, one added) to the [format] gate
   only when the first receipt needs it. *Recommendation: yes*: no approved
   file changes without a reason, and the schema question is asked when
   there is a real receipt to judge it by.
