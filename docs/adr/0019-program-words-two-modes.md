# ADR 0019: program words in two modes — correctness mode and run mode

Status: **accepted in direction** by the owner on 2026-11-03
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
`program.source.sha256` and `program.ir.sha256`. The correctness runner
reads the file once into memory and runs exactly those bytes, so it can
hash exactly what it ran (with the Forth SHA-256 of plan 3.2.6). A run-mode
loader for receipts does the same — read once, check the hash against the
receipt, evaluate those bytes with Forth's own words — so both modes
provably ran the same bytes. Plain `include` stays fine for users, with
`sha256sum` to compare.

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
| A standard word redefined before the run | runs the redefinition | **not noticed** | refused | refused |
| What is trusted | wrappers, in run mode too | each alias's meaning; isolation by visibility | each verification semantics; Gforth's dispatch | each verification semantics; a short loop of its own |
| How a user switches | a flag | `verify FILE` versus `include FILE` | `verify FILE` (inside: `verifying set-state`, then Gforth's own interpreter reads each line) | `verify FILE` versus `include FILE` |

**Recommendation: the mode shift, done portably (b2).** Reasons:

1. It is literally what you described: *one* word `DUP`, which in run mode
   duplicates and in correctness mode writes `prim dup`. Forth-2012
   already describes words by their semantics per interpreter state; a
   word's verification semantics sits next to them in its documentation.
2. It is stronger where it matters: it checks that every word the file
   uses *is* Forth's standard word (the `MAX` test), so a Forth that was
   tampered with before loading is refused, which the alias design leaves
   as an assumption.
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
  with the test plan above; the [parser] gate on that code.
- IR v1 (plan 4.4.1, 4.4.2) as [§10](#10-defining-words-and-loops-in-both-designs)
  designs it: loops, recursion, memory and declared data, a semantics
  without fuel, loop rules with invariants.
- The Lean well-formedness predicate and its *unknownWord* theorem (test 4).
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
