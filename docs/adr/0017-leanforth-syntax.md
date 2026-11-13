# ADR 0017: LeanForth Forth syntax for theorems, definitions and proofs

Status: **accepted as the design basis** by the owner on 2026-11-02 (decisions 1–4 as recommended, see [owner decisions](../project/OWNER_DECISIONS.md)); proposed 2026-11-02 (plan task 8.1.1). **Implemented** 2026-11-03 in `src/author/` (its [parser] gate **approved by the owner on 2026-11-03**, after two clean review rounds) and the term printer's Forth mode (plan task 8.1.2; [programming reference](../programming/LEANFORTH_WORDS.md), [user page](../user/LEANFORTH_SYNTAX.md)); the implementation still passes the [parser] gate before anything relies on it. Two points of the implementation refine this record: while the stores hold 64 nodes, equal subterms share one node, which keeps the position where it was first written (a step with a label or note always has its own node); and the stand-in for imports is the word `import-stub` (the prototype's `stub` and `declare`). The independent review of the implementation (2026-11-03) corrected four points of this record, in §3, §6, §9 and §10; they are listed under [corrections after the review](#corrections-after-the-review-2026-11-03). Before that, a throwaway prototype (outside the
repository, see [Evidence](#evidence)) ran every example below as Forth
words through Forth's own interpreter, built the terms in LeanForth's
existing stores, printed them with the term printer, and ran its own
printed words again.

**[Amendment 1](#amendment-1-accepted-leanforth-text-run-by-forth-itself-at-the-prompt-from-files-and-inline)
(accepted by the owner on 2026-11-04, design gate [parser] and
[bypass]):** with LeanForth loaded, Forth's own interpreter runs
LeanForth text — at the prompt, from files, or from Forth programs with
values passed in — with only LeanForth's sealed word lists visible and a
library such as `Init` as a vocabulary that keeps upper and lower case
exact (A16); each declaration is built in the kernel's stores and checked
when it ends. Results where other Forth ran read *checked in this
session* until saved and re-checked by `leanforth check` in a fresh
process. It revises the owner's OQ-1 answer (a separate authoring
program); §2, §18 and the follow-up "8.2.1" below are updated. A short
word for Lean's `+`: "Not now".

**[Amendment 2](#amendment-2-leanforth-text-checked-by-the-kernel-2026-11-12)
(2026-11-12, built; gates [parser], [bypass] and [import] pending):**
`leanforth check [--env EXPORT | --snapshot FILE] FILE.lf` checks LeanForth
text with the kernel, the file's declarations handed over as export
records through the importer stage, a library's constants named by their
Lean names; the whole file is checked when it ends.

This revision follows the owner's requirement of 2026-11-02: *"I was hoping
we can encode the theorems and proofs in leanforth words, not strings that
are parsed."* An earlier draft of this record used a reader with its own
word lookup; it is withdrawn (see [rejected alternatives](#rejected-alternatives)).

## Summary in plain words

Today a theorem reaches LeanForth only from Lean: you write it in Lean, Lean
exports it, LeanForth checks it again. This record designs the other way in:
writing a theorem, a definition and its proof directly in LeanForth, as
Forth words.

**Every token is a Forth word, and Forth's own interpreter runs it.** There
is no separate parser and no grammar inside strings. Each word does its job
when it runs, the way every Forth programmer knows: the parts go on the
stack, then a word combines them. Lean writes `g (f value)` ("apply f to
value, then g to the result"); LeanForth writes `g f value $ $`, where `$`
is the word "apply the function below to the argument on top". When a
binder word such as `explicit:` runs, it defines a temporary word for its
variable — like `:` or `CONSTANT`, it reads the name that follows — and
that word, when it runs later, pushes the variable (as the right de Bruijn
index; the author never writes indices). Each declared theorem or
definition becomes a word too. A whole theorem (the pinned fixture
`composition`: if A implies B and B implies C, then A implies C):

```text
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $ $   fun
end composition
```

Line by line: A, B and C are propositions; f is a proof that A implies B;
g that B implies C; the claim (before `:=`) is that A implies C; the proof
(after `:=`) is the function that takes a proof `value` of A and returns
`g (f value)`.

What matters for trust:

- **The syntax decides nothing.** The words only build terms; whatever a
  person or an AI writes, only the checker can accept it. (This record
  first ran the words in an authoring program separate from the checker;
  since Amendment 1, accepted 2026-11-04, they run in the checker's own
  Gforth with only LeanForth's words visible.) The checked statement can be
  printed back, so a person can see what was really checked.
- **Every word has one meaning.** No bracket, no symbol and no Forth word is
  reused with a second meaning. Forth's own words are not even visible
  while a proof runs, so `+` cannot mean anything there; mathematical
  addition is written by its Lean name, and showing it as `a + b` is the
  job of the printer and of editors
  ([the `+` question](#16-forth-words-keep-their-forth-meaning)).
- **Names are exactly Lean's names**, upper and lower case distinct, even
  though Forth looks words up without regard to case: each LeanForth word
  checks the exact spelling it was called with (§5). Mathematicians write
  `x : X`, and Mathlib has 537 groups of names that differ only in case.
- **Notes stay with the proof.** Any step can carry a label and a note
  written by a person (`note"`) or by an AI (`ai-note"`), kept in the source
  next to the step it explains, never checked, and printed with the proof
  with who wrote it (your answer to OQ-11).
- **Errors point at the author's text**: line and column of the word, and of
  the place it refers to.

Lean words used here are explained in
[terms for new readers](../user/TERMS_FOR_NEW_READERS.md) and, with
examples, in [concepts in three forms](../user/CONCEPTS.md): *term*,
*binder*, *de Bruijn index*, *universe level*, *Sort*, *Prop*, *Type*,
*constant*, *declaration*. Two more: an **implicit argument** is one Lean
fills in by itself (written `{A}`); an **instance argument** (`[inst : C]`)
is one Lean finds by searching a table of instances, such as "how to add
natural numbers". A short user page shows the sketch:
[LeanForth syntax](../user/LEANFORTH_SYNTAX.md).

## Context

- **Owner rules.** "The canonical language is ordinary Forth tokens and
  words; mathematics is represented as typed AST/data. Mathematical
  brackets, subscripts and infix symbols belong to an external
  notation/editor/rendering layer" (`AGENTS.md`). "A bracket must never mean
  one thing in LeanForth source and something unrelated in embedded math
  grammar … Human-friendly structured Forth declaration words are allowed,
  provided they are still Forth words and do not create implicit competing
  punctuation grammars" ([handoff](../project/CODEX_HANDOFF.md) §0). And
  (2026-11-02) theorems and proofs are encoded as LeanForth words, not as
  strings that are parsed.
- **Trust boundary** (OQ-1, plan 8.2.1): the authoring words, the
  elaboration helpers (implicit arguments, unification, 8.3.1) and tactics
  (8.3.2) are untrusted and run in a separate authoring program; the
  checker receives serialized terms only. (Revised by Amendment 1: the
  words run in the checker's Gforth, sealed; see §2.)
- **OQ-11** ([owner decisions](../project/OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)):
  "templates first", *"but make very easy from the start for ai written -
  and also human written that can stick with the proof as it evolves."*
- **Source spans** for every term, so errors and receipts point at the
  author's text ([interface contracts](../programming/INTERFACE_CONTRACTS.md),
  `sourceSpan`; the proof-step source-ID rule of `AGENTS.md`).
- **Round trip** (plan 8.1.2): the printer's Forth mode prints words, and
  running them rebuilds the identical term.
- **Program track.** Names in Forth *program* source are case-independent
  ([owner decision](../project/OWNER_DECISIONS.md#progress-marks-and-program-reader-names-2026-11-02-night)),
  and program files contain `+` with its machine meaning. The theorem words
  must not collide with either.
- **Portability**: Forth-2012, Gforth 1.0 for development, Gforth 0.7.3 in
  CI; nothing Gforth-only in the canonical form.
- **What exists.** The term store (`src/core/terms.fs`) holds Sort, bound
  variable, application, λ, Π and constant nodes; levels and names have their
  own stores; the presentation side table records binder names and kinds,
  declared types and a source ID per node (`src/present/binder-table.fs`);
  the term printer prints Lean's notation ([printing terms](../user/TERM_PRINTER.md)).
  The store has no `let`, literal, projection or inductive nodes yet. The
  test helpers of `tests/present/build.fs` build terms with words but take
  names as strings (`s" proof" ex.`); the words here read names as tokens.

## Prior art, briefly

**Lean 4** has a large surface syntax (notation, macros, an extensible
parser whose tokens change with imports) that an elaborator turns into a
small kernel term, `Expr`: `bvar`, `sort`, `const` with universe levels,
`app`, `lam` and `forallE` with a binder name and kind, `letE`, `lit`,
`proj`, `mdata`. *Taken:* the canonical LeanForth form maps one-to-one onto
`Expr`, with Lean's names, levels and binder kinds. *Avoided:* notation and
an extensible grammar in the canonical form.

**Metamath** writes proofs in reverse Polish notation: a sequence of labels
that a tiny verifier executes on a stack. It shows that a postfix proof
language can be checked by very little code. *Avoided:* raw label sequences
are unreadable without tools; LeanForth keeps names, binders on their own
lines and step labels. **Metamath Zero** separates a human-readable
specification from a proof stream that a stack machine checks; LeanForth's
separation of authoring program and checker is the same split.

**OpenTheory articles** describe HOL theories as commands of a stack
machine (`varTerm`, `appTerm`, `absTerm`, `constTerm`, with a dictionary for
sharing). *Taken:* postfix construction of terms is a proven exchange form.
*Avoided:* articles are not meant to be written by hand.

**HOL Light and the LCF family** build terms with constructor functions of
the host language (`mk_comb`, `mk_abs`), and proofs are programs in it.
*Taken:* proofs are host-language words that build terms. *Avoided:* in LCF
the host language is trusted to protect theorems; LeanForth keeps the
checker in its own program and sends it data only.

**Concatenative languages** (Forth, Factor, Joy, Cat): words with stack
effects; defining words that read the next token (Forth's `:` and
`CONSTANT`, Factor's `TUPLE:`); vocabularies and a search order; Cat's
statically typed stacks. *Taken:* all of these, and Forth assemblers'
practice of running in their own vocabulary.

**S-expressions** (Lisp-style kernels and export formats): fully
parenthesized prefix terms. *Avoided:* parentheses are Forth comments, and
brackets belong to the notation layer. Lean's own NDJSON export is also a
postfix DAG (every node refers to earlier nodes by number); LeanForth reads
it already and remains the way to bring in existing Lean work.

## Decision

### 1. Three layers, one checker

1. **Kernel form** (this ADR, decided here): exactly a kernel term. Every
   argument and every universe argument is written; nothing is inferred.
   The printer's Forth mode writes this form, and running it gives the
   identical term. Implemented first (8.1.2).
2. **Authoring form** (sketched; 8.3.1): the kernel form plus holes `_` that
   an untrusted elaborator fills (implicit arguments, universe levels,
   instances), plus short names through `open`.
3. **Tactic form** (sketched; 8.3.2): a `by` block of untrusted tactic words
   that produce a kernel term.

All three end as kernel terms, checked by the same checker; nothing written
in any layer can make the checker accept a false statement.

### 2. Forth's interpreter is the only parser

A proof file is Forth text. LeanForth sets the search order to the
LeanForth wordlists (§3) and hands the file to Forth's text interpreter
line by line (`EVALUATE`, counting lines for messages). Each token is found
as a word and executed, or converted as a number; nothing else reads the
text. A few words read the token after them, exactly where Forth's own
defining words do: the words that introduce a name (`theorem NAME`,
`explicit: NAME`, `universe NAME`, `namespace NAME`, `end NAME`,
`label: NAME`), and `note" …"`, whose text is prose, never structure. No
string carries mathematics.

**Trust** (as revised by [Amendment 1](#amendment-1-accepted-leanforth-text-run-by-forth-itself-at-the-prompt-from-files-and-inline),
accepted 2026-11-04; this record first put the words in an authoring
program separate from the checker, the owner's 2026-11-02 answer to OQ-1).
The words run in the checker's own Gforth, with only LeanForth's sealed
word lists visible, so the text can run nothing but LeanForth's fixed
words (Amendment 1, A5): it is data, as an NDJSON export is. A word that
misbehaves can at worst build a wrong term, which the checker checks as it
is and the printer shows. Where other Forth code has run in the same
Gforth (the prompt, a user's program), results read *checked in this
session* until the text is saved and re-checked by `leanforth check` in a
fresh process (Amendment 1, A7).

### 3. Wordlists and the search order

While a proof runs, the search order holds only LeanForth's wordlists,
searched in this order:

1. **LF-WORDS**, the syntax words (tables below);
2. **LF-LOCALS**, the variables and universe parameters in scope;
3. **LF-CONST**, every declared or imported constant under its full name,
   and a word for each shorter name it can be written by.

(Corrected after the review: namespaces are not wordlists in the search
order; which constant a name means is decided as Lean decides it, §9.)

Forth's own wordlist is not in the order, so Forth's words (`+`, `CHAR`,
`AND`, `MAX` …) are invisible in proof text: Lean's `Char`, `And` and `Max`
cannot be mistaken for them. `\` and `(` are LeanForth words with their
Forth meanings, for comments.

**Rule R1.** *Every syntax word is either one of Lean's reserved keywords or
contains a character that no unquoted Lean identifier contains* (such as
`-`, `:`, `>`, `$`, `^`, `"` or `#`; `_` alone is Lean's hole keyword). So
no name an author can write in Lean equals a syntax word, and since LF-WORDS
is searched first, a name can never change what a syntax word does.
Checked with pinned Lean 4.35.0: all 21 keywords used here (`theorem def
axiom universe end namespace open fun forall Prop Type Sort let have by
where structure class inductive import _`) are refused as identifiers
(`def fun := 1` is a syntax error), while even Lean's tactic names `intro`,
`exact`, `apply`, `induction`, `cases`, `rw` and `simp` are ordinary
identifiers (`def exact := 1` is accepted). The plain words a postfix syntax
tempts one to choose are common names in Mathlib's kernel terms: as binder
names, `app` occurs 1,789 times, `proof` 1,337, `step` 1,984, `succ` 760,
`max` 247 (of 13,887,415 binder names; scan of the pinned export,
[Evidence](#evidence)). Our own fixture `identity` names its hypothesis
`proof`.

Kernel terms may contain any name, including ones Lean source can write
only with `«»` quotes: 515 Mathlib binder names equal a keyword above
(`namespace` 97, `class` 94, `fun` 83, `let` 76 …), and 26,344 are `_`. A
binder word reads such a name as a name (`explicit: fun` is fine); where a
variable must be referred to and its name is a syntax word, the printer
writes it as `n var#` (§9).

### 4. Names are words

- **A variable** is a word. A binder word reads the name after it and adds
  it to LF-LOCALS; when the name's word runs, it pushes a reference to the
  innermost variable of that name, as a de Bruijn index counted at that
  moment. When the binder closes, the binding is gone: the word passes the
  token on to the wordlists after LF-LOCALS (§5), so a constant of the same
  name becomes visible again. (A Forth dictionary cannot remove one word,
  only everything after a `MARKER`; the hand-over makes removal
  unnecessary, and a long-running authoring program can still reclaim the
  space with `MARKER` between files.)
- **A universe parameter** named by `universe u` is a word in LF-LOCALS for
  the declaration. If a variable has the same name, the word pushes a name
  that is both, and the word that takes it decides: `$` takes the
  variable, `^` and `Sort` take the universe parameter. (Lean keeps
  universe names and variable names apart in the same way.)
- **A constant** is a word in LF-CONST under its full name, and in the
  wordlist of its namespace under its short name (`Nat.add_comm` and, in
  namespace `Nat`, `add_comm`). `end NAME` defines it when a declaration
  closes; importing a library (`import`, with 8.2.1) defines the words of
  its constants. The word pushes the constant with no universe arguments;
  `^` adds them.

### 5. Case: each word checks the spelling it was called with

Forth-2012 lets a system find words without regard to case, and Gforth
does; Lean names are case-sensitive. LeanForth keeps one word for all names
that are equal apart from case — a *name group* — and that word holds the
exact spellings with their meanings. When it runs, it re-reads the token
that invoked it (the interpreter leaves `>IN` just past it in `SOURCE`,
both standard) and acts only on an exact match; otherwise it hands the
token to the wordlists searched after its own (`GET-ORDER`,
`SEARCH-WORDLIST`) and runs what it finds there, or stops with "unknown
name". So:

- `x : X` works: `X` and `x` are two spellings in one group, each found by
  its exact spelling.
- The constants `Id` and `id` both work.
- A variable named `prop` works, although Forth first finds the syntax word
  `Prop` for it: `Prop`'s word sees the spelling `prop` and passes it on to
  LF-LOCALS.
- The syntax words are case-sensitive too: `PROP` is an unknown name.

The result does not depend on the host: on a Forth whose wordlists respect
case, each spelling simply has its own group. The prototype gave
byte-identical output with Gforth's ordinary wordlists and with Gforth's
case-sensitive ones (`table`).

### 6. The stack and the term words

A LeanForth value on the Forth data stack — a term, a universe level, a
name, a constant waiting for its universe arguments — is one cell: a
reference to an item kept by the authoring program, always negative.
Forth's own number literals can be negative (`-3`) and come in other forms
(`$10`, `1.`, `'a'`, floats), so the authoring program reads only *plain
decimals*: one to nine digits, never negative. Every other number form is
refused at its token, the same on every Forth host. Lean has no negative
literals or levels either, so a word that accepts a level or a term tells
a number from a value by its sign. So `0` is the level 0 before `^`, and
the natural-number literal 0 before `$`. Each value is used once: the word
that takes it marks its item used, so a copy of a value can never stand
for a term twice, and a variable is used only while its binder is open.
(The first version of this record said Forth number literals are
nonnegative; that was wrong, and the review showed `-3` standing for an
earlier value.)

| Word | Stack effect | Builds (Lean `Expr`) | Lean source |
| --- | --- | --- | --- |
| `Prop` | `( -- t )` | `.sort 0` | `Prop` |
| `Type` | `( l -- t )` | `.sort (l+1)` | `Type l`; Lean's `Type` is `0 Type` |
| `Sort` | `( l -- t )` | `.sort l` | `Sort l` |
| a name's word | `( -- x )` | a variable `.bvar i`, a constant `.const`, or a universe parameter | `x`, `Nat.add` |
| `^` | `( c l -- c' )` | adds universe argument `l` to constant `c` | `Eq.{1}` is `Eq 1 ^` |
| `$` | `( f a -- t )` | `.app f a` | `f a` |
| `A B ->` | `( A B -- t )` | `.forallE` whose binder the body does not use | `A → B` |
| `explicit:` NAME | `( A -- )`, opens a binder | — | `(x : A)` |
| `implicit:` NAME | `( A -- )` | — | `{x : A}` |
| `strict-implicit:` NAME | `( A -- )` | — | `⦃x : A⦄` |
| `instance:` NAME | `( A -- )` | — | `[x : A]` |
| `fun` | `( body -- t )`, closes the innermost binder | `.lam` | `fun x => body` |
| `forall` | `( body -- t )`, closes the innermost binder | `.forallE` | `∀ x, body`, `(x : A) → body` |
| `n var#` | `( n -- t )` | `.bvar n` | (none; for a hidden name, §9) |
| `root:` NAME | `( -- c )` | the root constant `NAME`, even if a variable has the name | `_root_.NAME` |

How to write a Lean term: **write its parts in Lean's order, put `$` after
each argument, `^` after each universe argument, and the binder word after
the binder's type.** `f a b` is `f a $ b $`; `g (f value)` is
`g f value $ $`; `@fixtureId.{u} α x` is `fixtureId u ^ α $ x $`.

### 7. Binders and scopes

A binder word takes the binder's type from the stack, reads the name after
it and opens a scope. `fun` or `forall` takes the body and closes the
scope, building one λ or Π node. As with Forth's control-flow stack
(`begin … until`), a scope is a frame, checked with `DEPTH`: when it
closes, exactly one value must be on the stack above the point where it
opened, and no word inside may take values from below that point. A
mistake stops with both places named:

```text
error at line:col 8:37 (token `fun`): the body of the binder opened at the
place below must be exactly one term; see line:col 8:15
```

`A B ->` builds a Π whose variable `B` does not use; the word shifts the
bound variables of `B` by one, so no name is needed.

### 8. Declarations and universe levels

```text
theorem NAME  [universe u]…  [binders]…  TYPE  :=  VALUE  end NAME
def     NAME  [universe u]…  [binders]…  TYPE  :=  VALUE  end NAME
axiom   NAME  [universe u]…  [binders]…  TYPE              end NAME
```

The binders still open at `:=` are the declaration's **parameters**, as the
binders before the colon are in Lean: they become Π binders around the type
and λ binders around the value. `universe u` lists the declaration's
universe parameters in order (Lean's `.{u}`). `end NAME` closes the
declaration, must repeat its name, and defines the constant's words. An
`axiom` is representable but the first checker answers *unsupported* for
it (owner gate answer G3); the owner's axiom policy is unchanged. `opaque`,
`abbrev` and the attributes Lean attaches to declarations are left for
later.

A universe level is a number (`0`, `1` …), a universe parameter, or built
by `l n level+` (`l + n`), `a b level-max` (`max a b`) and `a b level-imax`
(`imax a b`). Lean's `Type (u + 1)` is `u 1 level+ Type`.

### 9. Namespaces, `open` and the printer's names

`namespace N … end N` puts the declarations inside under `N.`; `open N`
opens `N` until the enclosing namespace ends. Which constant a name means
is decided exactly as pinned Lean 4.35 decides it (its `resolveGlobalName`;
corrected after the review, which found `def N.foo … := bar` building the
root `bar` where Lean builds `N.bar`): the first of `P.name` for the current
namespace `P` and each namespace around it, innermost first; otherwise the
name at the root and `O.name` for each open namespace `O`, which must all
be the same constant. While a declaration is made its own name's prefix is
the current namespace (Lean reads `def N.foo` as `namespace N def foo
end N`). `namespace A.B` enters two scopes, which `end A.B` (or `end B`
then `end A`) leaves; `open N` opens `P.N` for the nearest namespace `P`
around that has it, or `N`, and `O.N` for each open `O`. Through a
namespace (`P.name`, `O.name`), a name of one part never finds a constant
declared `protected` (`protected def N.bar`). Where Lean would
choose between two candidates by their types, the authoring words, which
have no types, stop with "ambiguous name: write the full name". The
first version of this record put namespaces in the search order and added
its own ambiguity check; both are replaced by Lean's rule.

The printer writes every constant with its full name (so printed text needs
no `open`), `root: NAME` where a variable has the same name, and `n var#`
for a variable whose name an inner binder hides, that has no name, or whose
name is a syntax word or a number.

### 10. Source spans

The authoring program counts lines, and each word knows its column from
`SOURCE` and `>IN`; every node it builds records that position as a source
ID (`lf-pres-source!`, the presentation side table): for a name its token,
for `$` the `$`, for a binder its opening word. Errors print the position
(``error at line:col 8:27 (token `valeu`)``); proof steps and receipts
carry it as `sourceSpan`. A token that is no word at all never reaches a
LeanForth word: Forth reports it as an undefined word (`THROW` −13), and
the authoring program finds it as the first token after the last word that
ran that is no plain decimal (§6). The checker receives terms only and reports node numbers; the
authoring program maps them back to positions. Spans never affect a
verdict.

### 11. Proof steps, labels and notes (OQ-11)

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `label:` NAME | `( t -- t )` | gives the term on top a stable step ID, `THEOREM/NAME` |
| `note" text"` | `( t -- t )` | attaches a note written by a person |
| `ai-note" text"` | `( t -- t )` | attaches a note written by an AI |

Notes are presentation data: never checked, never part of the term, and
labelled with their author kind wherever they are shown (provenance
`author-supplied` and `llm-generated` in the proof-step record of
[interface contracts](../programming/INTERFACE_CONTRACTS.md)). They sit in
the source next to the step they explain, so an edit to a step and an edit
to its note are the same edit; the printer writes them back after the term
they annotate, so they survive the round trip. Labels give notes kept
elsewhere (an AI's explanation file, a receipt) a stable ID; a label used
twice in one declaration is an error, and a note outside the file that
names a label which no longer exists is reported as orphaned, never
silently dropped. A receipt can keep a hash of each labelled step's
statement, so that when a step changes, its notes are flagged "to review".
Template explanations (plan §7) stay the default; these are additions.

### 12. How a proof is written, edited and generated

**People** write one binder or one step per line, as in the examples; an
edit to a step is an edit to its line, and its label and note move with it
([example 10](#example-10-a-proof-that-evolves-with-notes)). Running the
file gives either the declaration or an error at a line and column.

**AI tools** emit word sequences, which is what they produce best: the
words have fixed stack effects, the translation from Lean is the
one-line rule of §6, and names are Lean's names unchanged. A tool writes a
draft, runs it in the authoring program, reads the errors (a code, the
position, the token, the place referred to), and corrects; once it runs,
the printer's form of the result is the normalised text to keep, with the
tool's `ai-note"`s on the steps it explains. The JSON interface (8.5.1)
takes the same word sequences. Nothing a tool writes is trusted: the
checker decides, and the receipt says which notes are an AI's.

### 13. The printer's Forth mode and the round trip

The term printer gets a Forth mode beside Unicode, ASCII and LaTeX (8.1.2).
It prints words: one declaration as `theorem NAME`, a line per `universe`,
a line per parameter (the longest run of binders that the type and the
value share with the same name, kind and type), the type, `:=`, the value,
`end NAME`; binders inside terms as in §7; `A B ->` for a default-kind
binder that the body does not use and whose name is anonymous or hygienic
(Lean's `a._@._internal._hyg.0`); labels and notes after their terms.
Layout carries no meaning.

**Round-trip property** (the 8.1.2 test over all corpus terms): running the
printed words gives an identical term — the same nodes, levels, constants,
universe arguments and literals — with the same binder kinds and names and
the same labels and notes; and printing that term again gives the same
text. One stated exception: a binder printed as `->` comes back with the
anonymous name, so a hygienic name there is not kept. Lean's kernel ignores
binder names, and Lean's printer does not show these.

**The round trip is not enough on its own.** A fault planted in the
prototype's spelling check (§5) made `X` mean `x`: the printer and the
words agreed with each other, so the round trip stayed identical, and only
the comparison of the printed statement with Lean's `#print` showed the
wrong term. 8.1.2 therefore keeps both tests.

### 14. Literals, `let` and projections (sketch: not in the term store yet)

| LeanForth | Builds | Lean prints (`pp.explicit`) |
| --- | --- | --- |
| `5` where a term is wanted | `.lit (.natVal 5)`, any size | `nat_lit 5` |
| `s" hello"` (Forth's own string word, same meaning) | `.lit (.strVal "hello")` | `"hello"` |
| `T v let: x  body  let` | `.letE x T v body` | `let x : T := v; body` |
| `T v let: x  body  have` | the same, marked non-dependent | `have x := v; body` |
| `p Prod 0 field-at` | `.proj Prod 0 p` (index from 0, as in the kernel) | `p.1` |

`s" hello"` is a string literal *value* (Lean's `String` data), not
mathematics carried in a string. Lean's `(0 : Nat)` is `@OfNat.ofNat Nat
(nat_lit 0) (instOfNatNat (nat_lit 0))`, so its kernel form is
`OfNat.ofNat 0 ^ Nat $ 0 $ instOfNatNat 0 $ $`. Lean 4.35.0 itself turned
the test `def letExample : Nat := let x : Nat := 2; x` into
`have x := …; x`, which is why both closers exist. Natural numbers beyond
the cell size need a big-number literal word (with OQ-6's module). Lean's
`mdata` nodes (annotations its kernel ignores): 8.1.2 decides between
keeping them through a word and a documented exclusion from the round trip.

### 15. Inductive types and structures (sketch)

The binders opened after `where` are a constructor's arguments, and
`constructor: NAME` takes the constructor's result type and closes them
around it; a structure's fields are its one constructor's explicit
binders, exactly as Lean's kernel sees them:

```text
inductive MyNat                        structure MyMonoid
  0 Type                                 universe u
where                                    u Type explicit: M
  MyNat  constructor: zero               u Type
  MyNat explicit: n  MyNat             where
         constructor: succ               M M M -> ->  explicit: mul
end MyNat                                M            explicit: one
                                         M explicit: a  Eq u 1 level+ ^ M $
                                           mul a $ one $ $  a $  forall
                                                      explicit: mul_one
                                         MyMonoid u ^ M $  constructor: mk
                                       end MyMonoid
```

The parameters (`M`) open before `where` become the inductive's parameters
and are closed around each constructor's type, as Lean does. `class` is
written like `structure`. The authoring program generates the recursor and
the projections as Lean does; the checker checks them (phase 5). The
constructor type above, written with the same binder words, ran in the
prototype and printed as Lean prints `MyMonoid.mk`, apart from one known
printer limit ([example 8](#example-8-a-structure-and-an-instance-argument)).

### 16. Forth words keep their Forth meaning

The plan asked whether a mathematics wordlist may reuse names like `+`.
**No.** No LeanForth word reuses the name of a Forth-2012 standard word
with a different meaning: `+ - * / = < > max min and or not 1+ @ ! , . : ;`
and `field:`/`end-structure` keep their Forth meanings (`s"`, `\` and `(`
are reused with their Forth meanings). Mathematical operations are written
by their Lean names (`HAdd.hAdd`, `Eq`), shortened by `open` and filled in
by the elaborator; showing them as `a + b` is the job of the printer's
planned notation (plan 4.4.3) and of editors.

Forth wordlists and the search order would make the reuse easy: a math
wordlist searched first makes `+` mean `HAdd.hAdd`, as Forth assemblers
redefine `AND` or `IF`. It is rejected because:

1. **The two meanings differ exactly where programs fail.** Forth's `+` is
   addition that wraps around at the cell size; mathematical `+` on
   integers does not. A verified program sits next to its contract; if one
   token meant both, a reader could not tell which from the text, and the
   overflow cases that verification exists to catch would hide in that
   ambiguity.
2. **A reader would need the search order to understand a token.** A person
   or an AI reading one line could not know what `+` means without
   tracking which wordlists are active there, which is the kind of
   context-dependent grammar the owner's bracket rule excludes.
3. **It can be added later; it could not be taken back.** Admitting `+`
   later breaks no file; removing it would break every file that used it.

### 17. Elaboration and tactics on top (sketch, untrusted)

**Holes.** `_` is a hole: `fixtureId _ ^ _ $ h $` asks the elaborator
(8.3.1) for the universe level and the type. Every hole must be filled and
the result is checked like any other term. `$` never inserts arguments by
itself; a convenience word that inserts holes for a constant's implicit
arguments gets its own spelling (decided in 8.3.1, under R1), so that `$`
keeps exactly one meaning.

**Tactics** (8.3.2) are words too, working on a stack of goals, which suits
Forth. A `by` block replaces the value; tactic words follow R1 with a `by-`
prefix (Lean's tactic names are ordinary identifiers):

```text
theorem composition_by_tactics
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:= by
  by-intro: value          \ goal: C, with value : A
  g f value $ $  by-exact  \ closes the goal with this term
end composition_by_tactics
```

Lean's version, `by intro value; exact g (f value)`, elaborates to the
same term as the raw proof (`#print` shows `fun {A B C} f g value ↦
g (f value)`, checked with pinned Lean). Tactic steps can carry labels and
notes like terms. Whether proof files may define their own helper words
(Forth `:` definitions) is [decision 2](#decisions-for-the-owner).

### 18. Portability, scale and the trusted base

**Portability.** The mechanism uses Forth-2012 words only: `EVALUATE`,
`SOURCE`, `>IN`, `PARSE-NAME`, `PARSE`, `CREATE … DOES>`, `WORDLIST`,
`GET-ORDER`, `SET-ORDER`, `GET-CURRENT`, `SET-CURRENT`, `SEARCH-WORDLIST`,
`DEPTH`, `CATCH`/`THROW`. The prototype (which itself uses Gforth's locals
for brevity) gave byte-identical output on Gforth 1.0, on Gforth 0.7.3 and
with case-sensitive wordlists. The canonical text uses spaces, line ends,
printable ASCII words and UTF-8 in names (Lean names are Unicode). One
host extension is used where it exists: on Gforth 1.0, whose interpreter
recognizes more than words and numbers, LeanForth limits the recognizer to
words and digits while a proof runs (`rec-forth`, guarded by
`[DEFINED]`); every host then refuses the same tokens. A second host
extension, behind a small adapter per host, makes a library's names
findable without a word per name (Amendment 1, A4: Gforth 1.0's
`wordlist-class`, 0.7.3's `mappedwordlist`), with a Forth-2012 fallback.

**Scale.** Every constant declared in a file is a Forth word (a name
group). A library's constants are not: since Amendment 1 (A4, the owner's
decision of 2026-11-04) a library is a vocabulary whose search looks names
up in the library's hash index, measured at about 1.5 µs a name over all
of `Init` on Gforth 1.0, with nothing made when it loads. The first version
of this section measured the alternative, a word per constant: in Gforth
1.0 a name group with its entry took 119 bytes of dictionary, 6 µs to
define and 0.4 µs to look up (100,000 words of Mathlib-like names); all
729,263 Mathlib constants under full and short names would take about
170 MB and 9 s. That alternative is kept for future consideration
(Amendment 1, A4).

**Trusted base.** None of this is trusted. A wrong word produces a
different term, which the checker checks as it is and the printer shows;
the defences are the round-trip test, comparison of the terms with
Lean's, term for term, and of printed statements with Lean's, and the
printed statement in every receipt. Running in the checker's process, the
words' memory safety matters as the NDJSON reader's does (Amendment 1, A5
row 12).

### Corrections after the review (2026-11-03)

The independent review of the implementation found that a file could
build a different term than its reader expects. The corrections, each
with tests and a planted fault that the tests catch
([programming reference](../programming/LEANFORTH_WORDS.md#tests)):

- **Numbers (§6).** Forth reads `-3` as a number, so a negative literal
  could stand for an earlier value; Gforth 1.0 also reads `$10`, `0x3`,
  `"x"`, `->x` and more, unlike Gforth 0.7.3. Now only plain decimals are
  numbers; every other form is refused at its token, identically on both
  hosts (on Gforth 1.0 the interpreter's recognizer is limited to words and
  digits while a proof runs). Each value is used once.
- **Names that are numbers.** `universe 1` made `1 Type` mean the universe
  parameter, and left a word `1` behind for later runs. No name of a
  universe, declaration or namespace may now be number-like; a binder may
  be, but then gets no word (`n var#` refers to it).
- **Namespaces (§3, §9).** Names resolve as Lean resolves them, including
  inside a declaration with a dotted name. The re-review found one rule
  missing: through a namespace, a name of one part never finds a
  *protected* constant (Lean's `resolveQualifiedName`), so inside
  `namespace N`, `bar` silently built `N.bar` where Lean builds the root
  `bar` when `N.bar` is protected. `protected` now comes before
  `theorem`, `def`, `axiom` and `import-stub`, as in Lean, and is
  honoured; `export`, whose aliases Lean's resolution also searches, stops
  as not supported yet.
- **Text that silently changed meaning.** A `(` comment without its `)`
  on the line, numeric name parts with leading zeros (`x.01` and `x.1` are
  one Lean name), and labels or notes that would print as live words are
  refused; a value left below a parameter's binder stops at `:=`.
- **Evidence.** The comparison with Lean now covers the terms themselves,
  not only their printed text, which hides universe arguments and implicit
  arguments: each example's Lean source is compiled by pinned Lean, and the
  words' terms must equal Lean's own, node for node, with every universe
  argument, binder name and binder kind (and the pinned exporter's, apart
  from binder names and kinds, which that exporter merges between
  declarations).

## Worked examples

Each example gives the mathematics, the LeanForth kernel form, the Lean
source, and what the prototype printed in Lean's notation with the existing
term printer. (Its printed Forth form differs from the input only in
layout, so it is not repeated.) Every LeanForth text in examples 1–11 ran
as words through Gforth's interpreter in the prototype; its printed words
ran again and gave the identical result (terms, binder names and kinds,
labels and notes), with identical text on a second print. Example 12 shows
the errors and example 13 lists what is only sketched. The Lean lines were
checked with pinned Lean 4.35.0 and `-DwarningAsError=true`, and every
Lean-notation line equals Lean's own `#print` output except where a note
says otherwise. The five pinned fixtures' lines also equal
`tests/present/fixtures.golden`.

### Example 1: identity (pinned fixture)

Mathematics: $\forall P : \mathrm{Prop},\ P \to P$ — every proposition
implies itself.

```text
theorem identity
  Prop implicit: P
  P explicit: proof
  P
:=
  proof
end identity
```

Lean: `theorem identity {P : Prop} (proof : P) : P := proof`. Printed:

```text
theorem identity : ∀ {P : Prop}, P → P :=
fun {P} proof ↦ proof
```

### Example 2: composition (pinned fixture)

Mathematics: $\forall A\ B\ C : \mathrm{Prop},\ (A \to B) \to (B \to C) \to
(A \to C)$. LeanForth: as in the [summary](#summary-in-plain-words).
Lean: `theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
fun value => g (f value)`. Printed:

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
```

The printer's Forth form of the value is `A explicit: value g f value $ $
fun`.

### Example 3: a predicate on a type (pinned fixture `type_identity`)

Mathematics: for every type $A$, property $P$ of elements of $A$ and
$x \in A$: $P(x) \to P(x)$.

```text
theorem type_identity
  0 Type implicit: A
  A Prop ->  implicit: P
  A implicit: x
  P x $  explicit: proof
  P x $
:=
  proof
end type_identity
```

Lean: `theorem type_identity {A : Type} {P : A → Prop} {x : A} (proof : P x)
: P x := proof`. Printed:

```text
theorem type_identity : ∀ {A : Type} {P : A → Prop} {x : A}, P x → P x :=
fun {A} {P} {x} proof ↦ proof
```

### Example 4: a universe parameter (pinned fixture `poly_identity`)

Mathematics: the same statement for $A : \mathrm{Sort}\ u$, a type in any
universe $u$.

```text
theorem poly_identity
  universe u
  u Sort implicit: A
  A Prop ->  implicit: P
  A implicit: x
  P x $  explicit: proof
  P x $
:=
  proof
end poly_identity
```

Lean: `universe u` and `theorem poly_identity {A : Sort u} {P : A → Prop}
{x : A} (proof : P x) : P x := proof`. Printed:

```text
theorem poly_identity.{u} : ∀ {A : Sort u} {P : A → Prop} {x : A}, P x → P x :=
fun {A} {P} {x} proof ↦ proof
```

### Example 5: constants with universe arguments (pinned constant fixture)

Mathematics: the identity function $\mathrm{id}_\alpha(x) = x$ for $\alpha$
in any universe $u$, used once at level $u$ and once at level $0$, where
it maps a proof $h$ of $P$ to $h$.

```text
def fixtureId
  universe u
  u Sort implicit: α
  α explicit: x
  α
:=
  x
end fixtureId

def fixturePoly
  universe u
  u Sort implicit: α
  α explicit: x
  α
:=
  fixtureId u ^ α $ x $      \ @fixtureId.{u} α x
end fixturePoly

theorem fixtureUse
  Prop implicit: P
  P explicit: h
  P
:=
  fixtureId 0 ^ P $ h $      \ @fixtureId.{0} P h
end fixtureUse
```

`end fixtureId` defines the word `fixtureId`, which the later declarations
run. Lean: `def fixtureId {α : Sort u} (x : α) : α := x`, `def fixturePoly
{α : Sort u} (x : α) : α := fixtureId x`, `theorem fixtureUse {P : Prop}
(h : P) : P := fixtureId h`. Printed (the implicit arguments hidden, as
Lean hides them, because the side table knows `fixtureId`'s type):

```text
def fixtureId.{u} : {α : Sort u} → α → α :=
fun {α} x ↦ x
def fixturePoly.{u} : {α : Sort u} → α → α :=
fun {α} x ↦ fixtureId x
theorem fixtureUse : ∀ {P : Prop}, P → P :=
fun {P} h ↦ fixtureId h
```

### Example 6: universe levels with `+`, `max` and `imax`

Mathematics: $\mathrm{Type}\ u : \mathrm{Type}\ (u+1)$, and
$\mathrm{Sort}\ (\max(u, v)) : \mathrm{Type}\ (\max(u, v))$, likewise with
$\mathrm{imax}$.

```text
def Big
  universe u
  u 1 level+ Type
:=
  u Type
end Big

def PairSort
  universe u  universe v
  u Sort explicit: _A
  v Sort explicit: _B
  u v level-max Type
:=
  u v level-max Sort
end PairSort
```

`ImaxSort` is the same with `level-imax`. Lean: `def Big : Type (u + 1) :=
Type u`, `def PairSort (_A : Sort u) (_B : Sort v) : Type (max u v) := Sort
(max u v)` (the unused arguments keep Lean's universe linter satisfied).
Printed:

```text
def Big.{u} : Type (u + 1) :=
Type u
def PairSort.{u, v} : Sort u → Sort v → Type (max u v) :=
fun _A _B ↦ Sort (max u v)
def ImaxSort.{u, v} : Sort u → Sort v → Type (imax u v) :=
fun _A _B ↦ Sort (imax u v)
```

### Example 7: `Nat.add_comm`, an instance argument and universe arguments

Mathematics: $\forall n\ m \in \mathbb{N},\ n + m = m + n$. In Lean's
kernel `n + m` is `@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat
instAddNat) n m`: generic addition at the type `Nat`, with the instance
"addition of naturals" as an argument. The kernel form writes it all:

```text
theorem add_comm'
  Nat explicit: n
  Nat explicit: m
  Eq 1 ^ Nat $
    HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $  instHAdd 0 ^ Nat $ instAddNat $  $  n $ m $
  $
    HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $  instHAdd 0 ^ Nat $ instAddNat $  $  m $ n $
  $
:=
  Nat.add_comm n $ m $
end add_comm'
```

Lean: `theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm n m`.
With `pp.explicit` and `pp.universes` Lean prints the statement as
`@Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat
instAddNat) n m) (…)`: the same constants, universe arguments and
arguments, in the same order, as the kernel form. Printed (Lean, with
`pp.notation false`, prints the same lines):

```text
theorem add_comm' : ∀ (n m : Nat), Eq (HAdd.hAdd n m) (HAdd.hAdd m n) :=
fun n m ↦ Nat.add_comm n m
```

The kernel form is long because it is the kernel term; the authoring form
would be `Eq _ ^ _ $ HAdd.hAdd _ ^ _ ^ _ ^ _ $ _ $ _ $ _ $ n $ m $ $ …` with
holes, or, once 8.3.1 provides it, a word that inserts the holes. The
printer shows `n + m` once it has notation (plan 4.4.3).

### Example 8: a structure and an instance argument

Mathematics: in every structure $M$ with a multiplication $\cdot$ and an
element $1$ for which $a \cdot 1 = a$ is a law: $\forall a \in M,\ a \cdot
1 = a$. The class is the [sketch above](#15-inductive-types-and-structures-sketch);
the theorem, inside the namespace, writes the class's constants by their
short names, found through the namespace's wordlist:

```text
namespace MyMonoid
theorem mul_one'
  universe u
  u Type implicit: M
  MyMonoid u ^ M $  instance: inst
  M explicit: a
  Eq u 1 level+ ^ M $  mul u ^ M $ inst $ a $  one u ^ M $ inst $  $  $  a $
:=
  mul_one u ^ M $ inst $ a $
end mul_one'
end MyMonoid
```

Lean: `class MyMonoid (M : Type u) where mul : M → M → M; one : M; mul_one :
∀ a : M, mul a one = a`, then in `namespace MyMonoid`: `theorem mul_one' {M
: Type u} [inst : MyMonoid M] (a : M) : mul a one = a := mul_one a`.
Printed (the class's constants were given to the prototype with their Lean
types):

```text
theorem MyMonoid.mul_one'.{u} : ∀ {M : Type u} [inst : MyMonoid M] (a : M), Eq (MyMonoid.mul a MyMonoid.one) a :=
fun {M} [inst : MyMonoid M] a ↦ MyMonoid.mul_one a
```

The first line equals Lean's. In the second, Lean prints `fun {M} [MyMonoid
M] a ↦ MyMonoid.mul_one a`: Lean omits the instance binder's name because
it does not appear in the printed body, while the term printer shows it
because it appears in the term. That is a difference in the existing term
printer, found by this example and left to the printer's maintenance; the
terms are the same.

The constructor type written with the structure sketch's binders,
`u Type implicit: M  M M M -> -> explicit: mul  M explicit: one  M
explicit: a … forall explicit: mul_one  MyMonoid u ^ M $`, printed as

```text
{M : Type u} → (mul : M → M → M) → (one : M) → ((a : M) → Eq (mul a one) a) → MyMonoid M
```

where Lean's `#print MyMonoid.mk` (with `pp.notation false`) shows
`(∀ (a : M), Eq (mul a one) a)`: the same term, and a known limit of the
printer, which cannot always tell that a Π is a proposition
([printing terms](../user/TERM_PRINTER.md#limits-and-differences-from-lean)).

### Example 9: the four binder kinds; a strict-implicit hypothesis

Mathematics: $(\forall x \in A,\ P(x)) \to \forall y \in A,\ P(y)$.

```text
theorem strict_example
  0 Type implicit: A
  A Prop ->  implicit: P
  A strict-implicit: x  P x $  forall  explicit: h
  A explicit: y
  P y $
:=
  h y $
end strict_example
```

Lean: `theorem strict_example {A : Type} {P : A → Prop} (h : ∀ ⦃x : A⦄, P x)
(y : A) : P y := @h y`. Printed:

```text
theorem strict_example : ∀ {A : Type} {P : A → Prop}, (∀ ⦃x : A⦄, P x) → ∀ (y : A), P y :=
fun {A} {P} h y ↦ h
```

Lean prints the proof as `h`, hiding the argument `y` that the term
contains; the kernel form shows it (`h y $`). The instance kind appears in
example 8, the other kinds in examples 1–7.

### Example 10: a proof that evolves, with notes

Mathematics: $(A \to B) \to (B \to C) \to (C \to D) \to (A \to D)$. An AI
writes the first draft and explains two steps; a person explains the
third:

```text
theorem chain
  Prop implicit: A   Prop implicit: B   Prop implicit: C   Prop implicit: D
  A B ->  explicit: f
  B C ->  explicit: g
  C D ->  explicit: h
  A D ->
:=
  A explicit: a
    h  g  f a $   label: to-B  ai-note" f turns the proof a of A into a proof of B"
          $       label: to-C  ai-note" g turns that into a proof of C"
       $          label: to-D  note" h finishes the chain: a proof of D"
  fun
end chain
```

Later a person replaces the first two steps by the earlier theorem
`composition` and rewrites the note at `to-C`; the step `to-D` and its note
are untouched:

```text
  A explicit: a
    h  composition A $ B $ C $ f $ g $ a $
              label: to-C  note" composition does the first two steps at once"
       $      label: to-D  note" h finishes the chain: a proof of D"
  fun
```

Lean: `fun a => h (g (f a))`, then `fun a => h (composition f g a)`.
Printed for the edited version, with its steps:

```text
theorem chain : ∀ {A B C D : Prop}, (A → B) → (B → C) → (C → D) → A → D :=
fun {A B C D} f g h a ↦ h (composition f g a)
  step chain/to-C (line 24), note by a person: composition does the first two steps at once
    on: composition A $ B $ C $ f $ g $ a $
  step chain/to-D (line 25), note by a person: h finishes the chain: a proof of D
    on: h composition A $ B $ C $ f $ g $ a $ $
```

The step `to-B` vanished with its code; a note about it kept outside the
file would now be reported as orphaned. The printer wrote both drafts back
as words with their labels and notes, and running those words gave the
same terms, labels and notes.

### Example 11: names that differ only in case

Mathematics: the identity on a type $X$, as $x : X$; the identity function
`id` applied in the type `Id Nat`; a variable called `prop`.

```text
def caseVar
  0 Type implicit: X
  X explicit: x
  X
:=
  x
end caseVar

def bothIds
  Id 0 ^ Nat $  explicit: f
  Id 0 ^ Nat $
:=
  id 1 ^  Id 0 ^ Nat $  $  f $
end bothIds

def propVar
  Prop explicit: prop
  Prop
:=
  prop
end propVar
```

On Gforth, `X` and `x` are one word, `Id` and `id` are one word, and the
token `prop` first finds the syntax word `Prop`; each picks its meaning by
the exact spelling (§5). Lean: `def caseVar {X : Type} (x : X) : X := x`,
`def bothIds (f : Id Nat) : Id Nat := id f`, `def propVar (prop : Prop) :
Prop := prop`. Printed, as Lean prints them:

```text
def caseVar : {X : Type} → X → X :=
fun {X} x ↦ x
def bothIds : Id Nat → Id Nat :=
fun f ↦ id f
def propVar : Prop → Prop :=
fun prop ↦ prop
```

### Example 12: mistakes, and where the errors point

Each mistake stops at the author's text (prototype output):

| Mistake | Message |
| --- | --- |
| a `$` missing: `g f value $ fun` | ``error at line:col 8:37 (token `fun`): the body of the binder opened at the place below must be exactly one term; see line:col 8:15`` |
| a misspelt variable: `g f valeu $ $` | ``error at line:col 8:27 (token `valeu`): unknown name: no syntax word, bound variable, universe parameter or constant has it`` |
| a universe argument missing: `fixtureId P $ h $` | ``error at line:col 16:15 (token `$`): wrong number of universe arguments for the constant below (write each with ^); see line:col 16:3`` |
| `p` written for the variable `P` | ``error at line:col 4:3 (token `p`): unknown name: …`` |

Lean reports the misspelling as ``Unknown identifier `valeu` ``. The first
mistake also happened for real while this record was written: a `$` was
missing in the structure example, and the words stopped at the `forall`
that closed the binder `a`, naming where `a` was opened.

### Example 13: sketches that do not run yet

Literals, `let`/`have`, projections ([§14](#14-literals-let-and-projections-sketch-not-in-the-term-store-yet)),
inductive types and structures ([§15](#15-inductive-types-and-structures-sketch))
and tactics ([§17](#17-elaboration-and-tactics-on-top-sketch-untrusted)) are
sketches: the term store has no such nodes, so the prototype's words stop
with a message naming this ADR. Their Lean forms were checked with pinned
Lean: `#print` of `(0 : Nat)` shows `@OfNat.ofNat Nat (nat_lit 0)
(instOfNatNat (nat_lit 0))`; of `Prod.fst`, `fun α β self ↦ self.1`; of
`MyNat`, the constructors `MyNat.zero : MyNat` and `MyNat.succ : MyNat →
MyNat`.

## Evidence

- **Prototype.** About 720 lines of throwaway Gforth code outside the
  repository: the words of §§3–11 in LeanForth wordlists, run by Gforth's
  text interpreter through `EVALUATE`, with name groups and exact-spelling
  dispatch; two stand-ins, `declare` and `stub`, define the words of
  constants an import would provide; a Forth-mode printer; a round-trip
  check. It builds terms in the existing stores through the helpers of
  `tests/present/build.fs` and prints with `src/present/term-printer.fs`.
  It shares identical nodes because the stores hold only 64 terms; the real
  words keep one node per occurrence, so each has its own span. 18 example
  files: 24 declarations round-tripped identically (none differed), and the
  4 mistakes stopped with the messages above. The output was byte-identical
  on Gforth 1.0, on Gforth 0.7.3, and with case-sensitive wordlists.
- **Planted faults.** Five deliberate bugs, each in a copy of the
  prototype, run on six examples: the printer losing the implicit kind (4
  round trips differ), the printer writing `->` for a used binder (1), `$`
  swapping function and argument (4, and 3 Lean-notation lines), the
  printer dropping universe arguments (2), and the spelling check ignored
  (0 round trips, 1 Lean-notation line: see §13). Every fault was caught;
  the last only by comparison with Lean. The second needed an extra
  example, a used binder with a hygienic name, so the 8.1.2 tests must
  include Lean-imported terms.
- **Lean.** Every Lean form above was checked with pinned Lean 4.35.0
  (`-DwarningAsError=true`). A script compared the term printer's lines
  with Lean's `#print` output: 17 declarations equal Lean's two lines
  exactly (the seven of the five fixtures, which also equal
  `fixtures.golden`; `Big`, `PairSort`, `ImaxSort`, `add_comm'`, both
  drafts of `chain`, `strict_example`, `caseVar`, `bothIds`, `propVar`);
  the two differences are the instance-binder name in example 8, explained
  there, and the Π in the constructor type, a documented printer limit.
- **Mathlib scan.** A read-only pass over the pinned export
  (`.tools/mathlib/mathlib.ndjson`, 110,895,826 lines, 1 min 31 s):
  729,263 declarations, 537 groups of names differing only in case,
  13,887,415 binder names (1,433,740 distinct), and the counts quoted in §3.
- **Cost of words** (§18): measured in Gforth 1.0 on 100,000 words.
- Nothing was added to `src/` or `tests/`; `make test` and
  `make check-lean-sources` pass with this record.

## Consequences

- 8.1.2 implements the kernel form: the LeanForth wordlists and words
  (name groups, exact-spelling dispatch, frames, spans, fail-closed errors
  with stable codes), the authoring program's line-by-line runner, the
  printer's Forth mode, and the round-trip and Lean-comparison tests over
  every corpus term, including Lean-imported ones (names that are syntax
  words, hygienic arrows, hidden names, names differing only in case).
- The term store needs `let`, literal and projection nodes (needed for
  Mathlib anyway) before §14 runs; inductive types wait for phase 5.
- User documentation can show the Forth form of every example, labelled
  *design sketch* until 8.1.2 lands; [the user page](../user/LEANFORTH_SYNTAX.md)
  starts that.
- The JSON interface (8.5.1) and the LLM guide reuse the same words and
  error codes, so an AI can write a proof as words, get errors with
  positions, and normalise its text by printing it.

## Risks

- **Verbosity of the kernel form.** Example 7 shows it. It is the exact
  term, meant to be printed and compared; people and AIs will write the
  authoring form once 8.3.1 exists. Until then, hand-written proofs over
  Mathlib are long.
- **A wrong word changes the claim.** Mitigated by the round trip, the
  comparison with Lean's printing (which caught the one fault the round
  trip missed), and the printed statement in receipts.
- **Re-reading the invoking token** relies on the interpreter's standard
  behaviour of `>IN`; a word run in another way (from inside a colon
  definition, say) has no token to re-read. The LeanForth name words are
  meant to be run by the interpreter only; 8.1.2 makes them refuse
  otherwise.
- **Dictionary size** for large libraries (§18).
- **Postfix is unfamiliar to Lean users.** Mitigated by the one-line rule
  of §6, by the printer, and by keeping the Lean names unchanged.
- **Case sensitivity differs from program source.** Documented in both
  places; the words themselves never clash.

## Rejected alternatives

- **A string-parsed surface syntax** (for example `s" ∀ x, …" parse`), or
  any grammar carried in strings. Rejected on the owner's preference
  (2026-11-02): theorems and proofs are LeanForth words, and Forth's
  interpreter is the only parser.
- **A reader with its own word lookup** (this record's first draft): a
  fixed-vocabulary reader that looked names up itself, never through
  Forth's interpreter. It made case sensitivity and scoping simple, but it
  is a parser of its own, which the owner's requirement excludes; the name
  groups of §5 give the same results with Forth's own lookup.
- **Relying on Gforth's case-sensitive wordlists** (`table`) or on
  recognizers (a hook for unknown tokens): both are Gforth-only, not
  Forth-2012.
- **Forbidding names that differ only in case** within a scope: `x : X` is
  ordinary mathematics, and Mathlib depends on such names.
- **One wordlist per binder**, pushed on the search order: Forth-2012
  promises only eight wordlists in the search order, while terms nest
  binders hundreds deep.
- **Plain-word connectives** (`app`, `apply`, `proof`, `qed`, `succ`, `max`,
  `lam`, `pi`): they are names authors write (`proof` in our own fixture;
  the Mathlib counts in §3), and a syntax word would hide them.
- **Brackets: S-expressions or Lean's own notation in the Forth text**:
  brackets already mean comments and compilation state in Forth, and a
  second grammar is what the owner's rule excludes.
- **Reusing `+`, `=`, `max`, `1+` in a math wordlist**: §16.
- **Forth's first match for namespaces without a check**: an added `open`
  could silently change existing text.
- **Application with an argument count** (`f a b 2 apply`): a miscount
  silently shifts arguments; `$` is exactly Lean's binary application.
- **Universe arguments taken by the constant itself** (each constant word
  popping as many levels as it has parameters): the same word would take
  levels in the kernel form and none in the authoring form, where levels
  are inferred.
- **Levels inside a token** (`Eq.{1}`, `foo.{max u v}`): a small grammar
  inside tokens.
- **Two-cell tagged values** on the stack: then Forth's one-cell number
  literals could not be told from values; the sign rule of §6 needs no tag.
- **`Type` without a level, meaning `Sort 1`**: then `Type u` needs another
  word; `0 Type` costs one token.
- **One word per binder kind and node** (`fun-implicit`, `forall-instance`
  …): eight words instead of six, and the kind would be far from the name.
- **A closing word per declaration kind** (`end-theorem`, `end-def`):
  `end NAME` is Lean's keyword, uniform, and checks the name.
- **Notes in a separate file keyed by line numbers**: every edit above a
  note would detach it.
- **A round trip only up to binder names**: weaker than needed for exact
  printing; only the names Lean itself hides are excepted.

## Decisions for the owner

1. **The overall shape.** Theorems are written as Forth words that Forth
   itself runs: parts first, then the word that combines them
   (`g f value $ $`); binders as `TYPE explicit: NAME … fun`, where
   `explicit:` defines a temporary word for the variable; declarations as
   `theorem NAME … := … end NAME`, which defines a word for the theorem.
   *Recommendation: approve it as the basis for task 8.1.2.* It is what you
   asked for, ran every example on both Gforth versions, maps one-to-one
   onto what the checker checks, and leaves readable notation to the
   printer.
2. **Helper words inside proof files.** Because proof files are Forth, they
   could also define their own words (`: my-step … ;`). *Recommendation:
   not in proof files for now; only LeanForth's words there, with helper
   and tactic words in separate libraries loaded by the authoring program
   (8.3).* A proof file then reads the same for every person and AI tool,
   the printer can reproduce it, and nothing in it has behaviour hidden in
   a definition elsewhere in the file.
3. **Names are case-sensitive in theorem files**, unlike names in Forth
   program files. *Recommendation: yes.* Lean is case-sensitive, Mathlib has
   537 groups of names that differ only in case (`AlgebraicClosure` and
   `algebraicClosure`), mathematicians write `x : X`, and the prototype
   shows that LeanForth's words can keep the cases apart on any standard
   Forth.
4. **No `+` (or other Forth word) with a mathematical meaning.**
   *Recommendation: no reuse, for now.* In a verified program, Forth's `+`
   wraps around and mathematical `+` does not; one token must not mean
   both. Short mathematical names can still be added later without breaking
   anything, and readable `a + b` belongs to the printer and editors.
5. **Notes.** Each step can carry a label and notes marked as written by a
   person (`note"`) or by an AI (`ai-note"`), stored in the proof file next
   to the step, never checked, and printed with the proof. *Recommendation:
   approve; tell us if this is not what you meant by "stick with the proof
   as it evolves".*

## Follow-ups

- **8.1.2**: the LeanForth wordlists and words (perhaps `src/author/`), the
  runner, the printer's Forth mode, the round-trip and Lean-comparison
  tests over every corpus term, error codes in the diagnostics catalogue,
  and this ADR's examples as checked documentation (`DOC_EXAMPLE_PAGES`).
- **Term store**: `let`, literal, projection and `mdata` nodes (also needed
  to import Mathlib).
- **8.2.1** (replaced by Amendment 1, A13): LeanForth run by Forth itself
  in the checker's Gforth — files, the prompt and Forth programs — with
  the sealed word lists, the library as a vocabulary and each declaration
  checked when its `end NAME` runs, in steps 8.2.1a–g. (First version: an
  authoring program in its own process, sending the checker serialized
  terms with a span side file.)
- **8.3.1 / 8.3.2**: holes and the hole-inserting application word;
  tactics as `by-` words; both re-checked, with adversarial wrong outputs.
- **Term printer**: the instance-binder name difference of example 8.
- **Receipts and proof outlines (2.4.4, 3.4)**: carry labels, notes with
  their provenance, spans, and a statement hash per labelled step.
- **Documents that still say the syntax is not designed**
  (`docs/user/TERM_PRINTER.md`, `CONCEPTS.md`, ADR 0003's sketch,
  `FIRST_CHECKER_EXPECTED.md`): point them here when the owner has
  answered.

## Reproduction

The prototype and logs are in the session scratch folder of 2026-11-02
(not in the repository): `proto2/core.fs`, `words.fs`, `syntax.fs`,
`print.fs`, the example files `proto2/ex/*.lf`, `run.sh`, `run073.sh`,
`faults.sh`, `measure.fs` and the outputs `proto2/all.out`,
`all-073.out`, `all-cs.out`; Lean files `lean/examples.lean`,
`chain-edit.lean`, `case.lean`, `structure.lean`, `sketches.lean`,
`reserved.lean`; the Mathlib scan `names_scan.py` and `collisions.py`.
Commands: `gforth -e "false constant cs-host" print.fs -e
's" ex/02-composition.lf" run bye'` with the pinned Gforth 1.0.0 (`true`
for case-sensitive wordlists), and
`.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -DwarningAsError=true examples.lean`.

## Amendment 1 (accepted): LeanForth text run by Forth itself, at the prompt, from files and inline

**Status: accepted by the owner on 2026-11-04** (design gate [parser] and
[bypass]; [decisions](../project/OWNER_DECISIONS.md#native-leanforth-where-theorems-run-inline-use-library-vocabularies-2026-11-04-late)):
question 1 *yes*, question 2 *yes*, question 3 *"Lets do 1, but carefully
document and leave for future consideration 2. Also concerned about the
case issues."* — the library as a vocabulary (A4), one Forth word per name
kept as a documented alternative (A4), and case handled and tested in
every layer (A16); the first version's question 4, a short word for
Lean's `+`: *"Not now"* (A10). Proposed and revised the same day (the
owner's questions on the first version are quoted below). Each
implementation step (A13) still passes its own gate before code is relied
on. It **revises the owner's OQ-1 answer of 2026-11-02** ("Checker
isolation: separate program. The checker runs as its own program and
receives proofs only as data",
[decisions](../project/OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)),
on which §2, §18 and the follow-up "8.2.1" above (now updated), ADR 0010
§9 (updated) and ADR 0019 §3 ("Process") rested. Under this amendment Gforth with LeanForth loaded runs
LeanForth text with Forth's own interpreter — typed at the prompt, loaded
from a file, or passed from a Forth program — and each finished
declaration goes straight to the kernel's check. The claims below were
probed on Gforth 1.0.0 and 0.7.3 (section A12); the Lean forms were
checked with pinned Lean 4.35.0. It changes no typing or conversion rule,
no axiom rule and no LeanForth word of §§3–11.

**The owner's words.** The request (2026-11-04): *"I think the sealed word
list is the correct approach, are there any downsides? does it use the
standard forth parser? I was before concerned about, for example, +, being
mixed up between forth + and Lean +, I guess using a sealed word list and
limited non-forth vocabulary, we don't have to worry. We should be able to
run it inline, not just as a external file that starts gforth and then
exits. An example might be to run with different numeric constants passed
in in a loop from Forth. or different trig functions or a different sized
matrix all passed in a loop from Forth. (In the example above, perhaps A
might be a passed in parameter.."*; earlier the same day: *"I think we
should end up with native LeanForth going straight to the solver... seems
more forth like"*. On the first version's questions (2026-11-04):

- *"I'm confused by this question. the forth interpreter should be running
  the leanforth program (after loading leanforth and its primitives) how
  do we first create the leanforth text? One way is with a normal editor
  the we would use for forth, perhaps even inline interactive? Another way
  is with a math notation -> leanforth editor/translator. (and another is
  Lean to LeanForth translator) I don't like the description of a checker
  reading a file -- is it reading the ascii in the file and checking it?
  or is the forth interpreter checking it? when is it executed by which?"*
  — answered in "In plain words" and A1–A3.
- *"are there concrete examples from the literature that would guide this?
  it looks good, but does it have enough flexility to pass in, for
  example, trig functions?"* — A7 and A8.
- *"Is it look ahead or does a unknown word search a new place, the
  leanforth library as well - perhaps it is a vocabulary already? I like a
  forth like solution if it can be done efficiently"* — A4.
- On a short word for Lean's `+`: **"Not now"** (recorded in A10).

### In plain words

**Who does what.** You start Gforth and load LeanForth: the checker (the
"kernel") and the LeanForth words. From then on, Forth's own interpreter
runs LeanForth text exactly as it runs any Forth text — word by word, left
to right. The text can be typed at the prompt, loaded from a file you
wrote in any editor, or produced by a program. Each word builds a piece of
the theorem in the kernel's memory: `explicit: f` makes a variable, `$`
applies a function, and so on. The word `end NAME` hands the finished
theorem to the kernel's check, and the verdict is printed — or, when a
Forth program asked, left on the stack. Nothing else reads the text: there
is no separate program that reads the file's characters and checks them.
The only difference from loading an ordinary Forth file is that, while
LeanForth text runs, Forth can see only LeanForth's own words (its
"sealed" word lists): `+`, `dup`, `bye` simply do not exist there.

`leanforth check proof.lf` is only a convenience: it starts Gforth, loads
LeanForth (and the library you name, such as Lean's `Init`), loads the file
with only LeanForth's words visible, prints each verdict, and exits.

**Three ways to write LeanForth text** (A2):

1. *By hand*, in any editor, or typed at the prompt. At the prompt,
   `lf-prompt` switches to LeanForth: every line you type runs at once, and
   each theorem's verdict appears when you type its `end NAME`.
2. *From mathematical notation*, through a translator (for example a
   MathLive editor writing LaTeX or MathJSON, turned into LeanForth words).
   It is planned as an untrusted add-on (the handoff's "Priority B",
   ticket LF-012, roadmap T10.4); it needs the helper that fills in hidden
   arguments (plan 8.3.1) first. Whatever it writes is checked like any
   other text.
3. *From Lean.* This exists in part already: Lean exports a theorem to an
   NDJSON file, `leanforth check` checks it, and `leanforth print` shows
   its statement in LeanForth words (and the printer can write any checked
   declaration, proof included, as LeanForth words). Missing: literals,
   `let` and projections as words (§14), data types as words (§15), a
   command that writes a whole Lean library as a LeanForth file, and Lean's
   tactic proofs as tactic words (8.3.2) — today a proof comes back as the
   full term Lean's tactics produced.

**Does it use the standard Forth parser? Yes.** Forth's own interpreter
reads every word. LeanForth adds small checks around each line: numbers
must be plain decimals (Forth itself would also read `-3`, `$10`, `1e`,
and Gforth 1.0 even `"x"`), invisible control characters are refused, and
Forth must not be in the middle of compiling. The file is handed to the
interpreter a line at a time, as `INCLUDE` does, so that these checks can
run after each line.

**Library names: a vocabulary, as you suggested** (A4). The names of a
library such as `Init` (59,349 theorems and definitions) are not made into
Forth words in advance. The library is one more word list in the search
order — a vocabulary — whose search, instead of walking a list of words,
looks the name up in the library's own index, a hash table. Forth's
interpreter finds `Nat.add_comm` there as it finds any word. Measured on
all of `Init`: about 1.5 µs per name through the interpreter on Gforth 1.0
(0.3 µs for the lookup itself; 3 µs on 0.7.3), the index built in 17 ms,
and upper and lower case kept exactly as Lean needs (`nat.add_comm` is not
found; `Init` has 31 pairs of names that differ only in case, such as `id`
and `Id`, which ordinary Forth words would mix up). Gforth 1.0 and 0.7.3
both let a program make such a word list (Gforth 0.7.3 makes its locals
and Gforth 1.0 its case-sensitive tables the same way); a small adapter
per host hides the difference.

**Inline: values passed in from Forth** (A7, A8). Inside a Forth word,
theorem text goes between `lf[` and `]lf`, and values from Forth come in
by name with `param:`. This works today, on both Gforths, with the real
checker (probe p06; `lf[`, `]lf` and `param:` are prototypes kept outside
`src/`):

```forth
: composition-at ( A -- outcome )
  >lf-param
  lf[ param: A
      example
        Prop implicit: B   Prop implicit: C
        A B ->  explicit: f
        B C ->  explicit: g
        A C ->
      :=
        A explicit: value   g f value $ $   fun
      end example ]lf ;

: five ( -- )  5 0 do  i A-of composition-at drop lf-verdict. cr  loop ;
```

`A-of` builds, in ordinary Forth, the statement A(i): A(0) is
∀ P : Prop, P → P ("every statement implies itself"), and A(i+1) is
∀ P : Prop, P → A(i). For each i the checker checks "if A implies B and B
implies C, then A implies C" at that A. All five were accepted; a copy with
a wrong proof was *rejected*; a misspelling stopped at its line and column.
(The probe wrote `theorem compAt` where the design writes `example`, which
is not built yet.) A parameter can be any term: a statement as here, a
function such as `Real.sin` or `Real.cos`, a number, or a type such as an
n × n matrix type. Probe p10 passes two *functions* in a Forth loop and the
checker accepts both instances; trig functions themselves wait for
Mathlib's real numbers (A8). This is the way the LCF family of provers
(HOL Light, Isabelle, HOL4) has always let a program produce theorems:
quote the theorem, mark the holes, fill them from the program — HOL Light
verified Intel's sine and cosine that way (A7).

**How much to trust each way.** A file loaded into a Gforth with nothing
else in it can run only LeanForth's words, so its results get today's
label, *accepted (experimental, not independently audited)*. At the prompt
or inside your own Forth program, other Forth code shares the memory and
could in principle change a result, so those results read **checked in
this session** — a development result, never a claim. For a claim you save
the theorems as a LeanForth file (`lf-save`, `lf-write`) and run
`leanforth check` on it. Lean does the same: its toolchain re-checks
compiled libraries with a separate checker, because programs running
inside Lean (its metaprograms) could build an inconsistent library (A7).

**`+` cannot be mixed up.** In proof text Forth's `+` does not exist, and
inline, proof text is only ever between `lf[` and `]lf`. Your answer "Not
now" to a short word for Lean's `+` is recorded (A10).

**Downsides** (A11): a proof file still cannot define its own words, loop
or compute — repetition is the job of the Forth program around it;
Gforth's interpreter becomes part of what we rely on (the defence: the
statement is always printed back in three forms and compared with Lean in
the tests); the LeanForth words now run in the checker's memory and must be
as carefully bounded as the NDJSON reader; three small gaps must be closed
first (refuse to start while Forth compiles, refuse invisible control
characters, stop before the dictionary is full); today's words need
growable tables before they meet Mathlib; each theorem is checked when its
`end NAME` runs only once the kernel's library can grow one theorem at a
time (a kernel change with its own gate, A3).

**Your answers** (2026-11-04) are recorded in A14: yes to where theorems
run and how far each way is trusted; yes to passing values in with
`param:`; the library as a vocabulary, with one Forth word per name kept
for future consideration (A4); and how case is handled in every layer,
with its tests, is in A16.

### A1. Who does what, in Forth's terms

A **session** is one Gforth process with LeanForth loaded: the kernel
(`src/main.fs`), the LeanForth words (`src/author/`) and, when asked, a
library such as `Init`, whose declarations are staged, fed and checked
once when it is loaded (as `leanforth check EXPORT` does today).

**Running LeanForth text** means: the search order is set to LeanForth's
sealed word lists (A5), `BASE` to ten, and each line of text is handed to
Forth's text interpreter with `EVALUATE`; after each line LeanForth checks
the line's numbers and `STATE`; afterwards the caller's search order,
`BASE` and recognizer are restored. That is what `INCLUDE` does for Forth
files, plus the per-line checks (standard `INCLUDE` has no hook after each
line, so LeanForth reads the lines itself; it already does, in
`src/author/runner.fs`). Text can come from:

| Source | How it runs | Verdict goes |
| --- | --- | --- |
| a file: `leanforth check [--env EXPORT] proof.lf`, or `s" proof.lf" lf-include` in a session | line by line, as above | printed, one line per declaration, with its statement in three forms (plan 8.6.2) |
| the keyboard: `lf-prompt` | each line as you type it; `lf-done` returns to Forth's `ok` | printed when each `end NAME` runs |
| a Forth program: `lf[ … ]lf` or `lf-run` | the text kept in the program, run when the program reaches it, with parameters (A7) | on the stack (an ADR 0008 outcome); query words print it |

**Each word builds; `end NAME` checks.** The LeanForth words of §§6–11
build the declaration's type and value in the kernel's stores (the same
term, level, name and reference stores the NDJSON importer fills).
`end NAME` closes the declaration, adds it to the kernel's input
(`lf-input-add`) and runs the kernel's check of that one declaration
against everything before it (`check-declaration` through the publisher);
the verdict is printed or returned. An accepted declaration becomes usable
by the text after it, as a Forth word is usable after its `;`. (That last
step needs the kernel change of A3; until it is built, a file's
declarations are checked together when the file ends, with the same
verdicts.)

**Trust follows what ran in the process**, not where the text came from:

| What ran in this Gforth besides LeanForth | Label |
| --- | --- |
| nothing: `leanforth check proof.lf` (a fresh process, sealed text only) | *accepted (experimental, not independently audited)* |
| anything typed or loaded at Forth's prompt, or a user's program | *accepted (checked in this session; experimental, not independently audited)* |

Sealed text can run only LeanForth's fixed words (A5), so a file is data
in the way an NDJSON export is — which the kernel's process already reads
with Forth words (untrusted [import] code, fail-closed). Forth code typed
or loaded by a person or a program is code: it shares the kernel's memory
(A7). The prompt counts as a session even if you typed only LeanForth: you
could have left `lf-prompt` and typed Forth in between. `lf-save FILE`
writes everything declared in the session as a LeanForth file, and
`leanforth check` on that file gives the first label.

Unchanged: only the kernel and the publisher decide; "accepted" is printed
only from a declaration's published slot (`lf-check-verdict.`); a wrong
word can only build a different term, which is checked as it is and
printed back; the review gates of `AGENTS.md`. ADR 0019 (program words) is
not changed here; its §3 "Process" paragraph can be revisited by the same
rule in its own amendment.

### A2. Three ways to write LeanForth text

1. **An editor, or the keyboard.** Any text editor writes `.lf` files;
   layout carries no meaning (§13). At the prompt:

   ```text
   ok lf-prompt
   theorem identity
     Prop implicit: P
     P explicit: proof
     P
   :=
     proof
   end identity
     identity: accepted (checked in this session; experimental, not independently audited)
   lf-done
   ok
   ```

   `lf-prompt` is a Forth word; it reads each line with Forth's `REFILL`
   and runs it as above. `lf-done` is a LeanForth word (it contains `-`, so
   R1 holds) that ends the loop. Mistakes are reported at the line and
   column of the word, and the prompt goes on.

2. **A mathematical-notation translator.** An untrusted front end turns
   notation into LeanForth words: the handoff's "Priority B"
   (`docs/project/CODEX_HANDOFF.md` §5: a MathLive editor writing LaTeX or
   MathJSON, mapped deterministically to LeanForth terms, failing when
   ambiguous), ticket LF-012 of `docs/project/IMPLEMENTATION_PLAN.md`, and
   roadmap T10.4 (notation adapters with semantic review and ambiguity
   tests). It needs the elaborator (8.3.1) first, because notation such as
   `a + b` leaves out the type and the instance that the words must name;
   the translator writes holes `_` and the elaborator fills them. Its output
   is LeanForth text, checked like any other; it can never make a theorem
   true. Not part of task 8.2.1.

3. **Lean → LeanForth.** What exists: Lean exports NDJSON;
   `leanforth check` checks it; the term printer's Forth mode writes any
   checked declaration — statement and proof — as LeanForth words, which
   the authoring words read back to the identical term (8.1.2); and since
   2026-11-04 `leanforth print` shows each statement in LeanForth words,
   Lean's notation and LaTeX (8.6.1, 8.6.2). What is missing: words for
   literals, `let`, projections and `mdata` (§14; plans 5.2.2, 5.2.3),
   data-type declarations as words (§15), escaped spellings for the few
   names a token cannot spell (14 of `Init`'s names have a dot inside a
   part, `Std.«term_..._»`, p09), a command that writes a whole export as
   one `.lf` file (plan task 8.6.3), and tactic proofs: Lean exports the
   term its tactics built, often much longer than the tactic script, and
   LeanForth's own tactic words are plan 8.3.2.

### A3. Checking each declaration when `end NAME` runs

The Forth way is incremental: `;` makes a word usable at once. For
LeanForth, `end NAME` should check the declaration and, when it is
accepted, make it usable by the next line. Today's kernel checks an
*input* that is sealed before its environment is made (ADR 0012: the
environment is bound to the input's fingerprint, taken when loading
ends). Two ways to bridge it:

- **Now (no kernel change):** each `end NAME` adds the declaration to the
  input; the input is checked when the file ends, or, at the prompt and
  inline, re-checked as a whole at each `end` (correct, and fast enough for
  hand-sized sessions: p08 measured under 1 ms per small check). An
  `example` inline is checked against a snapshot and never added (A7).
- **Later (kernel change, its own [kernel] gate):** an ADR 0012 amendment
  lets the input grow by one declaration after the environment exists —
  append-only, a new fingerprint chained to the old, the new slot checked
  against a snapshot of everything before it and published as today. Then
  `end NAME` checks exactly one declaration. Task 8.2.1g.

### A4. The library as a vocabulary (the owner's question 3)

**Design.** The session's library (an export it loaded) is one more word
list, `LF-LIB`, at the end of the search order: LF-WORDS, LF-LOCALS,
LF-CONST (the file's own constants), LF-LIB. Its *find* is LeanForth's:
given a token, it looks the exact spelling up in the library's name index
and, if a declaration has that name (or, through the current namespace and
`open`, a name that §9's resolution could choose), answers with **one
shared word**, `lfa-library-name`, made by `CREATE … DOES>`. When that word
runs, it re-reads the token that invoked it (as every name word does,
§5), resolves it as Lean does (§9) and pushes the constant. Nothing is made
per library name; nothing is looked ahead; an unknown name is still
refused by Forth at its own token (−13, error 1). Case is exact: the
index compares bytes, so `nat.add_comm` does not find `Nat.add_comm`,
which Forth's own word lists would (they ignore case).

**How each host makes such a word list.** Neither is Forth-2012; both are
how Gforth itself builds special word lists:

- *Gforth 1.0:* a word list is a recognizer object;
  `wordlist-class ( reveal-xt rec-xt -- wid )` (`search.fs`) makes one
  whose search method is our `rec-xt` (`( c-addr u wid -- nt
  translate-name | translate-none )`). Gforth's `table` and `cs-wordlist`
  are made the same way.
- *Gforth 0.7.3:* `mappedwordlist ( map -- wid )` with a map of four
  execution tokens whose first is `find-method ( c-addr u wid -- nt | 0 )`
  (`kernel/int.fs`). Gforth 0.7.3 builds its locals word list this way.

A small adapter per host, like `src/lib/task.fs`'s for tasks (allowed by
the owner's OQ-7 answer: Gforth features behind an adapter with a portable
path). The **portable path** for a Forth with neither: before each line is
evaluated, the runner makes a group word in LF-CONST for each token of the
line that is not number-like and has no word yet (the first version's
"look-ahead"); it decides nothing and costs about 48 bytes per distinct
spelling (p05). Kept only as that fallback.

**Measured** (p09: `Init`'s 59,349 declarations staged and fed as
`leanforth check` does, then every name of `Init` looked up; per token;
Gforth 1.0 with the `gforth` engine, two runs, and Gforth 0.7.3 with its
`gforth-fast` engine, whose plain engine would not stage `Init` within
the probe's five minutes):

| How a name is found | Gforth 1.0 | Gforth 0.7.3 | Notes |
| --- | --- | --- | --- |
| LF-LIB, index by whole name (one hash table, `src/lib/htab.fs`, keyed by the dotted name) | lookup 0.23–0.34 µs (hit), 0.26–0.40 µs (miss); through Forth's interpreter, including the shared word's re-read and second lookup, 1.45–1.49 µs | 0.67 and 1.08 µs; through the interpreter 3.0 µs | built in 14–17 ms (57 ms on 0.7.3); 2.1 MB of name text; exact case |
| LF-LIB, index part by part (the name tier's hashes, `name-seek-str`, then the input's name column) | lookup 3.3–3.6 µs; through the interpreter 8.0–8.7 µs | 9.4 µs; 18.9 µs | no extra memory |
| one ordinary Forth word per declaration, made up front | 0.56–0.64 µs through the interpreter | 0.58 µs | 4,254,680 bytes of dictionary on both, made in 79–83 ms (119 ms); **31 pairs of `Init`'s names differ only in case (`id` and `Id`, `String.Pos` and `String.pos`, `Prod.Lex` and `Prod.lex` …): both Gforths warned "redefined … with …", and each later word hid the earlier**, so name groups (§5) are needed on top; for Mathlib's 729,263 declarations, scaled, about 50 MB and 1 s at every start |

Through LF-LIB, on both hosts, every name of `Init` that a token can spell
was found, as the shared word (59,335 hits), and `nat.add_comm`,
`NAT.ADD_COMM`, `Nat..add`, `.Nat` and `dup` were −13. On 1.0 with
default recognizers `->Nat.add` threw −21 (the shared word is
`CREATE … DOES>`), while `` `Nat.add `` and `"Nat.add"` pushed cells that
the number check refuses; with the runner's restricted recognizer, and on
0.7.3, every one of these was −13. 14 names of `Init` were not found: each
has a dot inside one part (`Std.«term_...<_»`), which no single token can
spell (A2).

**Decision (owner, 2026-11-04: "Lets do 1"):** LF-LIB with the whole-name
index, on both Gforths through the adapter; the look-ahead only on a Forth
without a custom find. At 1.5 µs a name, a file of 10,000 names costs
15 ms; the remaining difference to ordinary words (0.6 µs) is mostly the
second lookup, which a one-entry cache between the find and the shared
word removes. A second library (a Mathlib slice, S4) is a second LF-LIB in
the order, or one index over both. How LF-LIB keeps case exact, and how
that is tested, is in A16.

**The alternative, kept for future consideration (the owner: "carefully
document and leave for future consideration 2").** *One Forth word per
library name*, made when the library loads, in an ordinary word list after
LF-CONST.

- *What it is:* for every declaration of the library, its full name and
  each shorter name it can be written by become words, as a file's own
  constants are today (§4, §5).
- *Measured* (p09, all of `Init`): 4,254,680 bytes of dictionary for
  59,349 plain words, made in 79–83 ms on Gforth 1.0 and 119 ms on 0.7.3;
  0.56–0.64 µs a name through the interpreter (against LF-LIB's 1.5 µs on
  1.0 and 3.0 µs on 0.7.3). §18's earlier measurement of name groups with
  their entries: 119 bytes and 6 µs a name; all of Mathlib under full and
  short names, about 170 MB and 9 s.
- *The case finding:* made as plain Forth words, **31 pairs of `Init`'s
  names that differ only in case collided on both Gforths** ("redefined
  `id` with `Id`" …): Forth's word lists ignore case, so the later word
  hid the earlier, and a token such as `id` would have run `Id`'s word.
  The alternative is therefore sound only with name groups (§5) for the
  library's names too — one word per case-folded spelling, holding the
  exact spellings — which is what §18 measured, at the larger cost.
- *What it would need:* name groups for every library name; a dictionary
  far beyond Gforth's default of about 8 MB (already 14 MB for `Init`
  with groups; `-m` at start-up); the same cost at every start, unless a
  saved Gforth image holds the words (a host feature to check per Gforth).
- *What it would give:* no host adapter (Forth-2012 only), lookups about
  2.5 times faster per name, and the library visible to `WORDS` and other
  tools that walk word lists.
- *When to reconsider:* if a host without a custom find must be supported
  and the look-ahead proves awkward there, or if name lookup ever shows up
  in measured checking time (today it is microseconds per name against
  milliseconds per check).

**`protected`.** Lean's exporter does not record it (a limit the owner
noted when approving 8.1.2). Until the export pipeline records which
constants are protected (task 8.2.1d), a one-part name that would reach a
*library* constant through a namespace stops with "write the full name" —
a temporary refusal where Lean decides, closed by 8.2.1d.

**`import-stub` retires.** A stub declares a constant without checking it;
with a library loaded it would be an unchecked assumption. It is refused
when a library is loaded, stays for runs without one (the printer tests and
documentation) until those move to small exports, and is then removed with
its tests (task 8.2.1d). `import NAME` stays *not supported yet*: Lean's
exports carry no module names, so the library is named by whoever starts
the session (`--env EXPORT`, `lf-session`), and the output records the
export's SHA-256 from its manifest.

### A5. Sealed text: what must be shut, and the probes

While LeanForth text runs, sealed text can build terms with the words of
§§6–9 (and `param:`, `example`), declare theorems, definitions and
examples, attach labels and notes, open namespaces, and comment. It cannot
define Forth words, loop, branch, compute a number, read or write a file
or the environment, print, change `BASE` or `STATE`, reach memory, or run
any Forth word: §2's "Forth's interpreter is the only parser" holds, and §16
and owner decision 2 (no `:` definitions in proof files) are unchanged.

The argument: every token of a line either (a) is found as a word of the
sealed lists, all made by `CREATE … DOES>`, whose actions only build
terms, declarations, labels and notes in the kernel's stores and make name
words (group words, §5); or (b) is converted by Forth as a number, which
every LeanForth word refuses unless it is a plain decimal before it acts
on anything (the check of §6 and of the corrections); or (c) is refused at
its token. Nothing else may act. The table lists each way text could
escape, what the probes showed on each host, and the rule. **No item failed
on either Gforth; four need a new rule** (marked *new*).

| # | What could escape | Gforth 1.0.0 | Gforth 0.7.3 | Rule |
| --- | --- | --- | --- | --- |
| 1 | Forth's own words | 31 Forth words and forms in a sealed order (`[ ] state base hex decimal here ! : ; immediate postpone evaluate included require execute catch throw abort quit \ ( s" ." char literal forth-wordlist only set-order dup bye`) all THROW −13, and so do the scoped forms `forth:dup`, `forth:bye`, `sealed:w` (p01) | the same, −13 (p01) | Search order exactly LF-WORDS, LF-LOCALS, LF-CONST and LF-LIB (no FORTH, no Root); restored after the run, also after a THROW (p03) |
| 2 | Gforth 1.0's `->`, `+>`, `'>` recognizers | **`5 ->v` stored into a VALUE and `5 ->d` re-pointed a DEFER that sat in the sealed list; `7 +>v` added to it; `'>v` pushed its address**; `->w` on a `CREATE … DOES>` word threw −21 (p01), as `->Nat.add` did through LF-LIB (p09) | no such recognizers: −13 | *Hardened:* the sealed lists, LF-LIB's shared word included, hold only `CREATE … DOES>` words, never a VALUE, DEFER or VARIABLE; a test runs `0 ->NAME` for every word of them on 1.0 and requires −21 (today's lists already comply) |
| 3 | Gforth 1.0's other recognizers | default: `"x"` and `"a b"` (reads past its token), `${HOME}` (reads the environment), `` `w `` and ``` ``w ``` (an execution token), `<w>`, `1_000`, `.5`, `0x10`, `10h`, `2p`, `3k`, `1M` (SI floats) are all converted; with the runner's restriction to names and digit strings (`lfa-recognize`) 83 of p01's 89 tokens throw −13, and only the sealed word (in two spellings) and four digit strings remain; LF-LIB's names are found through the restriction (p09) | none | Keep the restriction during every sealed run, restored after (p03); the number check of row 4 still decides alone, as on 0.7.3 |
| 4 | Numbers in other forms, `BASE` | converted (default): `-3 $10 #10 %10 &10 0x10 1. 1.5 .5 1e 1e3 -1e 'a' 'a ''` … | converted: `-3 $10 #10 %10 &10 0x10 1. 1.5 1e 'a' 'a ''` | Every converted token must be a plain decimal of 1–9 digits, checked before the next word acts and at the line's end: each form refused at its token with error 35 on both hosts (p03). `BASE` is ten during the run; no sealed word changes it (`hex`, `base`, `decimal` are −13); the caller's `BASE` (16 in p03) is restored |
| 5 | `STATE`: called while Forth compiles | the runner, called by an immediate word *during compilation*, compiled the LeanForth word `theorem` into the caller's definition (`see victim` shows it), reported only "unknown name", and running that definition later threw −4129 (p03) | the same (p03) | *New:* refuse to start unless `STATE` is 0, and check it after every line, as ADR 0019 §3 does; no sealed word can change `STATE` (`[` `]` are −13) |
| 6 | Parsing words | only LeanForth's read text: a name after a word, `\` to the line's end, `( … )`, `note" … "`; each to the end of its line at most; `(` and `note"` must close on their line (errors 42, 37) | the same | Unchanged; `param:` (A7) reads one name like `explicit:` |
| 7 | Bytes that split tokens | Forth splits at TAB, LF, VT, FF, CR and space only; NUL, the other control bytes, DEL and no-break space are part of a token (p07) | identical (p07) | *New:* refuse a line holding a control byte other than TAB (and a CR before its LF), or invalid UTF-8. The runner's own splitter (errors, the number check) treats every byte up to 32 as a blank, Forth does not; with such bytes refused, both split alike and what an editor shows as one token is one token |
| 8 | Nested `EVALUATE` | the only one is the runner's own: a group word is made by `EVALUATE` of `lfa-group: NAME`. Of 18 names tried as a constant and as a variable, `bye ] [ : ; postpone immediate evaluate lfa-group: abort" s" x"y \ α` and names of 200 and 239 characters became harmless words (`.(` was refused as a name; `s"` and `\` as variables then met the syntax words of the same spelling, as §5 says); nothing ran; the run went on (p04) | the same (p04) | *Hardened:* during that `EVALUATE` the search order holds a private list with only `lfa-group:`, so no later definition of that name (for example by an inline program) is picked up |
| 9 | What a THROW leaves | after 11 errors of different kinds the caller's search order, compilation word list, recognizer, `BASE`, `STATE` and stack depth were as before and no floats were left (p03) | the same (p03) | The runner catches every THROW (ADR 0018). A declaration whose text failed is not checked; its terms are scratch, rolled back to the input's marks; group words stay (they only dispatch) |
| 10 | The stacks | 60,000 plain decimals in one declaration overflowed the data stack: THROW −3, caught (error 41), and the next run in the session worked; the host turns data and return stack overflow into THROWs −3 and −5 in `gforth` and `gforth-fast` (p04, p04c) | the same, at an earlier line (smaller stack) (p04) | Unchanged. Floats are read only on 0.7.3 (1.0's restricted recognizer reads none) and are refused at the line's end; a line of at most 1,023 characters holds at most 512 tokens, below both hosts' float stack (2,048 and 4,096 per `FLOATING-STACK`, p00) |
| 11 | The dictionary | each new spelling the file's own declarations and variables use is a group word, about 48 bytes for a short name (p05); library names make none (A4). Filling a small dictionary (`-m 3M`): the run that hit the end failed with −8, caught; afterwards every new name failed. **The host lets `HERE` pass the end: `UNUSED` was −32 after `CREATE` filled it and `,` then wrote 8 more bytes without a THROW** (p05b) | 48 bytes; with `-m 1M`, −8 at the end, caught; `UNUSED` stops at 2 (p05, p05b) | *New:* make no group word when `UNUSED` is below a reserve (64 KB proposed): the run ends *full* (error 66) and sealed text never reaches the host's edge |
| 12 | The LeanForth words' own buffers | — | — | *New for this process:* in a separate program an overrun could only spoil that program; here it could reach the kernel. Every buffer the words write (the line of 1,024 bytes, texts of 256, spellings of 4,096, the definition text of 256, the error token of 64, the stores, LF-LIB's index) is bounds-checked; the [bypass] review checks each, and a randomized hostile-text test compares the dictionary laid down while loading (`tests/support/dictionary-check.fs`) and the checked environment before and after |
| 13 | DEFERs and VALUEs of the implementation (`lfa-const-run`, `lfa-shift` …) | in the implementation's own word list, never in a sealed list: text cannot name them | the same | A user's program can (outside the session label's promise, A7) |

Rows 5, 7, 11 and 12 are the new rules (task 8.2.1a); rows 2 and 8 are
hardening of what already holds. The kernel and LeanForth's words load
together silently on both hosts (p02: about 1.6 MB and 120 KB of
dictionary).

### A6. Checking a file

```text
leanforth check [--env EXPORT] proof.lf
```

starts Gforth, loads LeanForth, loads and checks the library export when
`--env` names one, runs the file (A1), prints each declaration's verdict
with the position of its declaration word and its statement in three
forms, and exits with the command line's exit codes. A declaration whose
text has an error is not checked; the error is printed at its line and
column (exit 4, malformed input, as for a malformed export).

**`example`** (a Lean keyword, so allowed by R1; pinned Lean refuses `def
example := 1`) is a theorem without a name: checked like one and never
added to the library, as in Lean, which elaborates and kernel-checks an
`example` and then restores the environment (`elabMutualDef`,
`withoutModifyingEnv`, `src/lean/Lean/Elab/MutualDef.lean` lines
1195–1205 of the toolchain). It closes with `end example`; no later
declaration can name it.

### A7. Inline use: the words, the prior art, and why the label

A Forth program loads LeanForth and calls it in its own session. Proposed
words (names open to the [parser] review; each reuses no Forth-2012 name,
§16):

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `lf-session` | `( c-addr u -- outcome )` | load the library export named (none for an empty string): stage, feed and check it once; afterwards it is only read |
| `lf-include` | `( c-addr u -- outcome )` | run a `.lf` file in this session (A1) |
| `lf-prompt` | `( -- )` | run typed lines as LeanForth until `lf-done` (A2) |
| `lf[` … `]lf` | compiling: `( "text" -- )`; running: `( -- outcome )` | immediate: at compile time it takes the LeanForth text up to `]lf`, across lines, keeps it (on the heap) and compiles its address, length and a call of `lf-run`. Outside a definition it runs the text at once |
| `lf-run` | `( c-addr u -- outcome )` | run text built at run time, with the parameters pushed since the last run; the outcome of its last declaration (ADR 0008) |
| `>lf-param` | `( term -- )` | push a term as the next parameter |
| `>lf-const` | `( c-addr u -- )` | push a constant of the session by its full name, e.g. `s" Real.sin"` (found through LF-LIB) |
| `>lf-nat` | `( u -- )` | push a natural-number literal (needs 5.2.3; a negative cell is refused: Lean has no negative literals) |
| `>lf-level` | `( u -- )` | push a universe level |
| `lf-term[` … `]lf` | running: `( -- term outcome )` | run sealed text that leaves exactly one closed term and no declaration, to build a parameter in LeanForth words |
| `lf-app` `lf-arrow` `lf-pi` `lf-lam` `lf-bvar` `lf-sort` `lf-const` `lf-nat` | small stack effects on terms | build terms in Forth, for terms a loop computes (a matrix of size n); untrusted like everything else |
| `lf-statement` | `( -- term )` | the last check's statement, to print or pass on |
| `lf-verdict.` | `( -- )` | the verdict with its label, the statement in three forms and the axioms |
| `lf-error.` | `( -- )` | the text's error (code, line, column, token) or the kernel's diagnostic |
| `lf-write` | `( fid -- outcome )` | write the last checked declaration as sealed text, an `example` with the parameters filled in |
| `lf-save` | `( c-addr u -- outcome )` | write every declaration of the session to the file named |

In the sealed text, one new word:

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `param:` NAME | `( -- )` | bind NAME to the next parameter, in the order the caller pushed them (like Forth's `{: a b :}`); each later use of NAME pushes it as a value; a parameter missing or left over is an error |

**Prior art.** The design follows three established ideas:

- **LCF: a programming language around a small kernel.** Edinburgh LCF
  made ML the "metalanguage" of a prover and theorems an abstract type
  `thm` whose values only the kernel's inference functions can construct;
  any ML program — loops included — may build terms and call the kernel,
  and ML's type system guarantees that it cannot forge a theorem (Gordon,
  Milner and Wadsworth, *Edinburgh LCF*, LNCS 78, 1979,
  doi:10.1007/3-540-09724-4; Gordon, "From LCF to HOL: a short history",
  in *Proof, Language, and Interaction*, MIT Press, 2000,
  <https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf>). HOL4,
  Isabelle (Isabelle/ML) and HOL Light (Harrison, "HOL Light: An
  Overview", TPHOLs 2009, LNCS 5674, doi:10.1007/978-3-642-03359-9_4) keep
  the design. Programs that generate and prove many instances are routine
  there: Harrison verified the floating-point sine and cosine of Intel's
  Itanium in HOL Light, with OCaml programs generating and proving the many
  case-specific facts the error analysis needs ("Formal verification of
  floating point trigonometric
  functions", FMCAD 2000, LNCS 1954, pp. 217–233,
  <https://www.cl.cam.ac.uk/~jrh13/papers/fmcad00.html>); the Flyspeck
  proof of the Kepler conjecture checked very many generated instances in
  HOL Light (Hales et al., "A formal proof of the Kepler conjecture",
  *Forum of Mathematics, Pi* 5, e2, 2017, doi:10.1017/fmp.2017.1).
- **Quotation with antiquotation.** The provers let a program write a term
  in the object language and mark the holes the program fills: HOL Light's
  backquoted terms `` `x + 1` `` read by its term parser
  (<https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/parse_term.html>),
  with ML values combined through `mk_comb` and friends; HOL4's quotations
  with `^` antiquotations; Isabelle/ML's `@{term "…"}` antiquotations
  (Wenzel, *The Isabelle/Isar Implementation*, Isabelle's manual,
  <https://isabelle.in.tum.de/doc/implementation.pdf>); Lean 4's syntax
  quotations `` `(term| … $x …) `` with `$x` antiquotations (Ullrich and de
  Moura, "Beyond Notations: Hygienic Macro Expansion for Theorem Proving
  Languages", IJCAR 2020 and LMCS 18(2), 2022,
  <https://arxiv.org/abs/2001.10490>) and, for typed kernel terms, the Qq
  library's `q(…)` (<https://github.com/leanprover-community/quote4>).
  `lf[ … ]lf` is such a quotation: its content is LeanForth text, run by
  the sealed reader; `param:` is its antiquotation.
- **Forth and Factor quotations.** Gforth's `[: … ;]` (the Forth-200x
  quotations proposal,
  <https://www.complang.tuwien.ac.at/forth/ansforth-cvs/quotations.txt>;
  in Gforth 1.0, not in 0.7.3) and Factor's `[ … ]`
  (<https://docs.factorcode.org/content/vocab-quotations.html>) keep
  *code* of the host language inside a definition, to run later.
  `lf[ … ]lf` borrows the shape — a block inside a colon definition, run
  when the definition runs — but keeps *text* of the sealed language and
  compiles nothing, so it needs only standard words (`REFILL`,
  `PARSE-NAME`, `ALLOCATE`, `2LITERAL`) and runs on 0.7.3 too (p06).

**Why LCF's trust argument does not carry over to Forth — and so the
label.** LCF's guarantee rests on ML's static types: `thm` is abstract, so
no ML code can make one without the kernel. Forth has no types: any word
can store any cell at any address with `!`, word lists hide names but not
memory (ADR 0010 §9), and a program in the session can store into the
environment's slots or the owner token, re-point an implementation DEFER,
change a parameter's term after its check, or print a verdict of its own.
Nothing inside the session can rule that out (ADR 0012's threat model,
items 15, 17 and 21, already names such undetected writes). So a verdict
made where any other Forth ran reads *checked in this session* and is never
counted as proved; the trusted label needs a process in which only
LeanForth's code and sealed text ran. Lean makes the same move for the same
reason: metaprograms run inside Lean could build an inconsistent
environment ("environment hacking"), so Lean's toolchain ships
`leanchecker`, and lean4checker replays a module's declarations through
the kernel (<https://github.com/leanprover/lean4checker>); Mathlib's CI
runs it.

**The way to a claim.** `lf-write` writes each instance as sealed text —
an `example` (or a named theorem), the parameters' terms written out in
words, labels and notes kept — and `leanforth check --env EXPORT
instances.lf` re-checks the file in a fresh Gforth that loads only
LeanForth, giving today's label and the axiom report. Probe p06b did this
with p06's five instances: five *accepted*, statements identical byte for
byte, on both hosts. This is also plan 8.6.2's round trip ("the LeanForth
form, read back by the authoring words, builds the identical statement
term"): one test serves both.

**Isolation between checks (ADR 0009).** A session holds one context: the
library's input, sealed and marked, and its checked environment. Each
inline check builds its terms above the input's marks, checks them against
a snapshot of the environment, reads the verdict and rolls the stores back
to the marks (`lf-input-rollback`), whatever the outcome, so check n + 1
sees exactly what check n saw. An `example` is never published; a named
theorem inline is added only once A3's kernel change exists. Inline runs
never run inside a job; parallel inline checks (one context per task) come
later. A THROW inside a run is caught; the caller gets the outcome. The
`STATE` rule of A5 refuses a run while Forth compiles.

**Results on the stack.** Each run leaves one outcome of ADR 0008 (*ok*
for accepted, *rejected*, *unknown*, *unsupported*, *invalid* for a text
error, *exhausted*, *full*); details come from the query words, so a loop
can branch with `ok?` and print only what it needs.

**Why text in `lf[ … ]lf`, not LeanForth words compiled into colon
definitions.** Compile-time LeanForth words (`: f theorem t … end t ;`
with names read at compile time) were weighed and rejected: the binder
words make their variables' words when they *run*, so a compiled body
would need a second, compile-time implementation of every scope, name
group and namespace rule (a second [parser] surface); words that act
differently when compiling are the state-smart words ADR 0019 §9 (a)
rejected; and any Forth word could sit between two LeanForth words, so the
sealed property is lost and no instance could be printed back as the text
that made it. Parameters are named in the text (`param: A`), so a reader
sees where each enters, and the printed instance shows the value in its
place; the caller's own stack items stay below the run's floor, out of
reach of every word (frames, §7; p06 ended balanced).

### A8. Passing functions, types and numbers: the trig example

`param:` passes any term: a statement (p06), a **constant such as a
function** (`Real.sin`, `Real.cos`), a **type** (`Matrix (Fin n) (Fin n)
ℝ`, written as a term), a number (`>lf-nat`, with literals, 5.2.3), or a
level.

**What runs today** (probe p10, both Gforths, the real checker): the
session defines two functions on propositions, `idP` (p ↦ p) and `twiceP`
(p ↦ (p → p)); a Forth loop passes each in turn to the template "for every
P, f P implies f P", and the checker accepts both instances. A wrong proof
(`P` for a proof of `f P`) gives *unknown*, where pinned Lean rejects it
("Type mismatch"): a temporary gap, closed by unfolding (4.2.2), since
deciding it means unfolding `idP P` to `P`.

**The trig example in three forms** (a design: `>lf-const`, `example` and
the holes `_` of §17 are not built; the holes are ℝ's `≤` and its `1`,
which the elaborator fills, 8.3.1):

Mathematics: for $f \in \{\sin, \cos\}$: $\forall x \in \mathbb{R},\ f(x) \le 1$.

LeanForth (the function and the lemma that bounds it are passed by name):

```forth
: at-most-one ( -- outcome )        \ f and its lemma h pushed before
  lf[ param: f  param: h
      example
        Real explicit: x
        LE.le 0 ^ Real $ _ $  f x $ $  OfNat.ofNat 0 ^ Real $ 1 $ _ $  $
      :=
        h x $
      end example ]lf ;

: both ( -- )
  s" Real.sin" >lf-const  s" Real.sin_le_one" >lf-const  at-most-one drop lf-verdict. cr
  s" Real.cos" >lf-const  s" Real.cos_le_one" >lf-const  at-most-one drop lf-verdict. cr ;
```

Lean (Mathlib; `Real.sin_le_one (x : ℝ) : Real.sin x ≤ 1` and
`Real.cos_le_one` are in `Mathlib/Analysis/Complex/Trigonometric.lean` of
the pinned Mathlib, and both names occur in the pinned Mathlib export; not
compiled here, as Mathlib is not built in this checkout):

```lean
example : ∀ x : ℝ, Real.sin x ≤ 1 := fun x => Real.sin_le_one x
example : ∀ x : ℝ, Real.cos x ≤ 1 := fun x => Real.cos_le_one x
```

**Lean's own alternative to the Forth loop: quantify over the function.**
One theorem covers every f, and each instance is an application:

```lean
theorem at_most_one {f : ℝ → ℝ} (h : ∀ x, f x ≤ 1) (x : ℝ) : f x ≤ 1 := h x
example := at_most_one Real.sin_le_one
example := at_most_one Real.cos_le_one
```

The same theorem for any type with `≤` and `1`, and p10's `keeps (f :
Prop → Prop) (P : Prop) (h : f P) : f P := h` with its instances `keeps
idP` and `keeps twiceP`, were checked with pinned Lean. In LeanForth the
quantified form is ordinary text — `Prop Prop -> explicit: f` is a binder
like any other — and runs today. Quantify when the statement is uniform
in the parameter; loop in Forth when the instances are computed (a table
of constants, a structure whose size depends on n) or when each instance
needs its own proof found by a program, as in Harrison's verification of
sine and cosine (A7).

**What the trig example waits for:** Mathlib's real numbers (a quotient of
Cauchy sequences: 5.2.4), the standard axioms (5.3.1), structures and
instances (5.2.2), literals (5.2.3), unfolding (4.2.2), the elaborator for
the holes (8.3.1), and a Mathlib slice containing
`Mathlib.Analysis.Complex.Trigonometric` (stage S4, then all of Mathlib,
S5). Matrices of size n add `Fin n` (literals, 5.2.3) and the matrix
library (S4/S5); `>lf-nat` passes n. One caution in either case: a loop
over n = 1 … 10 checks ten separate facts and proves nothing about n = 11;
a statement for every n is one theorem with a "for all n" and a proof by
induction (5.2.1b).

### A9. Realistic examples and the tasks they wait for

| The owner's example | What it needs | Plan tasks |
| --- | --- | --- |
| `A` passed in, propositions without a library | works today (p06: five accepted, a wrong proof rejected, a misspelling at its line and column) | 8.2.1a–f make it a product |
| functions passed in (propositions to propositions) | works today (p10: two accepted; a wrong proof *unknown* where Lean rejects, until 4.2.2) | 8.2.1a–f; 4.2.2 |
| propositions of `Init` passed in (`True`, `And`) | `Init`'s non-recursive data types, accepted today, and LF-LIB (A4) | 8.2.1d |
| numeric constants in a loop (`n + 0 = n`, `2 + 2 = 4` with the number passed in) | natural numbers, literals, structures, unfolding; a literal word (§14); the elaborator, or else `OfNat.ofNat 0 ^ Nat $ 2 $ instOfNatNat 2 $ $` for each 2 | 5.2.1b, 5.2.2, 5.2.3, 4.2.2b–e, 8.3.1 |
| different trig functions passed in by name | A8 | 5.2.4, 5.3.1, 5.2.2, 5.2.3, 4.2.2, 8.3.1, S4 (then S5) |
| matrices of different sizes | `Matrix (Fin n) (Fin n) R` and its instances; literals; term-building words for the entries | 5.2.3, S4/S5, 8.3.1 |

### A10. `+` and §16 when both vocabularies are near

- **The owner's answer of 2026-11-04 to the first version's question 4:
  "Not now"** — no short word for Lean's `+`. §16 is unchanged; readable
  `n + m` stays the printer's job (4.4.3, 8.6.2); the question can come
  back after the elaborator (8.3.1), and adding such a word later breaks
  nothing (§16, reason 3). The three `+` are set side by side in
  [one symbol, three places](../user/ONE_SYMBOL_THREE_PLACES.md).
- **In sealed text** no Forth word is visible, so `+` is an unknown name
  (`tests/author/author.fs`: `p p +` stops at the `+`, error 1), and Lean's
  addition is `HAdd.hAdd` with its arguments.
- **Inline**, one colon definition holds both. The boundary is lexical and
  visible: outside `lf[ … ]lf` every word is Forth's, inside every word is
  LeanForth's; no word runs on the other side, because the sealed run
  replaces the whole search order and restores it afterwards (A5, row 1).
  At the prompt, `lf-prompt` … `lf-done` is the same boundary.
- **Numbers cross only explicitly.** A Forth number (a loop index `i`)
  becomes a Lean number only through `>lf-nat`, which makes a literal of
  the cell's value. Arithmetic stays on its side: `i 1+ >lf-nat` adds in
  Forth, where it wraps at the cell size, and hands the value over; a sum
  in the theorem is Lean's, on unbounded natural numbers. This is §16's
  first reason, kept by construction.
- **The new words follow §16 and R1.** `lf[`, `]lf`, `lf-run`, `lf-prompt`,
  `>lf-param` and the others are Forth-side words with names no Forth-2012
  word has (Forth's `[` and `]` are distinct words); `param:` and `lf-done`
  contain a character no Lean identifier has (`param` alone is an ordinary
  Lean identifier: pinned Lean accepts `def param := 1`); `example` is a
  Lean keyword (pinned Lean refuses `def example := 1`).

### A11. Downsides

1. **No definitions, no loops in proof text** (owner decision 2 of this
   ADR). A file is a list of declarations; families of instances come from
   a Forth program around it (A7), or from one quantified theorem (A8),
   later from tactics (8.3.2).
2. **Gforth's interpreter joins what we rely on** to build the term the
   text says: splitting tokens, finding words regardless of case (the name
   groups of §5 and LF-LIB's exact index restore exact case), running them
   left to right, and handing each line over. A host fault there could
   build another term. Mitigations: the kernel checks the term as built,
   never the text; every verdict prints the statement back in three forms
   (8.6.2); the round trip (print, read back, identical term) and the
   comparison with pinned Lean's terms, node for node, as 8.1.2's tests do
   for 67 declarations, run on both hosts; and the probes of A5 become
   tests that fail if a host reads tokens differently.
3. **The words' memory safety now matters to the kernel** (A5, row 12),
   as the NDJSON reader's does.
4. **Two host adapters.** LF-LIB uses Gforth's own way of making a word
   list with its own search (A4), different on 1.0 and 0.7.3 and not
   Forth-2012; the look-ahead stays as the portable path.
5. **Speed.** Running LeanForth text is cheap: 63–74 µs for the
   composition text on Gforth 1.0 and 255–271 µs on 0.7.3; a whole inline
   check, with a fresh environment each time, 0.73–0.95 ms and 1.85–3.2 ms
   (p08); a library name 1.5 µs (p09). But today's words were built for
   stores of 64 nodes: they find shared nodes by scanning the whole store
   (`lfa-find`, quadratic in the file's size), shift terms by recursion on
   Forth's return stack (`lfa-shift`, against plan 6.2.0 (b)'s rule that
   no pass's depth depends on it), and keep fixed tables (512 values, 256
   names, 4,096 spelling bytes, 16 namespaces …, listed in plan 6.2.4; the
   binder store grows since 6.2.0 (b)). Task 8.2.1b removes all three
   before files meet `Init` or Mathlib. Loading `Init` stages, feeds and
   checks it (staging and feeding alone took 104–195 s with Gforth 1.0's
   `gforth` engine and 286 s with 0.7.3's `gforth-fast` on a shared machine
   in p09; the progress report's run, on the faster path, about 21 s for
   feed and check) until saved results (OQ-3, ADR 0012 E8) let a
   development session reuse them, labelled.
6. **Error messages.** Positions are the file's line and column; inline,
   the text's own, its first line counted 1 (the design adds the source
   file and line where `lf[` stood). A Forth exception inside a run (stack
   or dictionary full) is error 41 with the THROW code, and today an empty
   token (p04); 8.2.1a names the line instead.
7. **Printed instances lose sharing.** The printer writes a term as words
   without `let` (§14 is a sketch), so a parameter built by reusing a
   subterm prints much longer than it is: with A(i+1) = A(i) → A(i), the
   words for A(4) hold 16 copies of A(0) (the first p06 run). The term the
   kernel checks is shared; only the printed text grows.
8. **Checking at each `end NAME`** needs the kernel change of A3 to be
   exact; until then sessions re-check, and files are checked at their end.

### A12. Evidence: the probes

Throwaway probes outside `src/` and `tests/`, kept in the work folder
`.claude/work/AU2/` (not in the repository), each run under `ulimit -u
500; timeout -k 5 … setsid`, on the pinned Gforth 1.0.0 and on Gforth
0.7.3, with `</dev/null`:

| Probe | What it shows | Result |
| --- | --- | --- |
| p00 | the hosts: recognizer words, stack sizes, dictionary | 1.0 has `rec-forth` and the nine recognizers probed by name (`rec-name`, `rec-number`, `rec-float`, `rec-string`, `rec-to`, `rec-tick`, `rec-dtick`, `rec-env`, `rec-scope`), 0.7.3 none; dictionaries about 7.7 and 8.0 MB free at start |
| p01 | 89 tokens evaluated with only a sealed list in the order: Gforth 1.0 default, 1.0 restricted as the runner does, 0.7.3 | 1.0 default: 41 tokens converted or run, **three wrote a VALUE or DEFER of the sealed list**; 1.0 restricted: only the sealed word (two spellings) and four digit strings, 83 −13; 0.7.3: 24 converted or run, 65 −13; `BASE` and `STATE` unchanged in all |
| p02 | the kernel and the authoring words in one image | load silently on both; about 1.6 MB and 120 KB of dictionary (1.62 and 0.12 MB on 1.0, 1.65 and 0.12 MB on 0.7.3) |
| p03 | the real runner: 11 errors with `BASE` 16 before; the runner called while compiling | settings restored in every case on both; while compiling, `theorem` was compiled into the caller (needs the `STATE` rule) |
| p04, p04c | stack overflows; 60,000 decimals in a text; names that are Forth words | THROWs −3 and −5 caught (also `gforth-fast`); the session went on; 18 odd names harmless; outputs equal on both hosts except the line where the stack fills |
| p05, p05b | the dictionary filling | 48 bytes per name; −8 caught; Gforth 1.0 lets `HERE` pass the end (needs the reserve) |
| p06 | inline, end to end: `lf[ … ]lf`, `param:`, five instances checked by the real checker, a wrong proof, a misspelling | five accepted, one rejected, error 1 at 8:33; output identical on both hosts (80 lines) |
| p06b | the instances written as words and re-checked from a file in a fresh process | five accepted; statements identical to p06's; identical on both hosts |
| p07 | which bytes split tokens | TAB, LF, VT, FF, CR and space on both hosts, identical |
| p08 | speed of 1,000 inline checks | 0.73–0.95 ms each on 1.0 and 1.85–3.2 ms on 0.7.3 (the sealed run alone 63–74 and 255–271 µs), three runs, before and after merging plan 6.2.0 (b) |
| p09 | the library as a vocabulary over all of `Init` (A4), on 1.0 with default and restricted recognizers, and on 0.7.3 (`gforth-fast`) | the custom search works on both hosts (`wordlist-class` on 1.0, `mappedwordlist` on 0.7.3): 59,335 names found through Forth's interpreter, exact case; whole-name index 1.5 µs (1.0) and 3.0 µs (0.7.3) a name; up-front words 0.6 µs, 4.25 MB, and 31 case collisions among `Init`'s names |
| p10 | a function passed in, in a Forth loop (A8) | `idP` and `twiceP` accepted; the wrong proof *unknown* (Lean rejects; closed by 4.2.2); output identical on both hosts |
| p11 | case over all of `Init` (A16): every declaration name dumped, the case pairs found (`p11-pairs.py`), and a fixture of 62 exact spellings and 168 wrong-case spellings run through LF-LIB and Forth's interpreter | 31 pairs, all ASCII, none Unicode-only; on Gforth 1.0 (default and restricted recognizers) and 0.7.3: all 62 exact spellings resolved to their own declaration, all 168 wrong-case spellings were refused, 0 failures; a planted wrong expectation in a small fixture was reported as a failure |
| p12 | a case twin used in a file, end to end with the checker (A16) | `same` accepted; `Same` found as written and *rejected* (Lean: "Type mismatch"); `SAME` error 1 at its line and column (Lean: "Unknown identifier"); output identical on both hosts |
| p13 | which letters each Gforth's lookup folds | ASCII A–Z only on both hosts; α/Α, é/É, ǆ/ǅ/Ǆ not folded |
| Lean | `lean/forms.lean`, `reserved.lean`, `plain.lean`, `functions.lean`, `wrong.lean`, `case.lean`, `case-wrong.lean`, `case-none.lean` with pinned Lean 4.35.0, `-DwarningAsError=true` | the instances' statements equal Lean's `#print` (Lean wraps the longer one); the kernel forms of `2 + 2 = 4` and `n + 0 = n` as quoted; `example` refused as an identifier, `param` accepted; p10's instances and the quantified `keeps` and `at_most_one` accepted; p10's wrong proof rejected ("Type mismatch"); p12's `same`/`Same` accepted, `Same` for `same` rejected ("Type mismatch"), `SAME` an unknown identifier; `Id` and `id` resolve as written |

**Finding on soundness.** Nothing found makes the sealed approach unsound
on either Gforth: with the rules of A5, text can run only LeanForth's
words on both hosts, and every refusal is identical. Two host facts shape
the rules: Gforth 1.0's `->`-style recognizers can write a VALUE or DEFER
that is in the search order (so the sealed lists hold none, and the
recognizer stays restricted), and Gforth 1.0 lets `HERE` overrun the
dictionary's end by a few bytes when it fills (so LeanForth stops well
before it). Gforth 0.7.3 has no recognizers; there the number check alone
refuses every other number form, as it already does.

### A13. Plan tasks

**8.2.1, new wording** (replacing "Process separation: user Forth
(authoring, tactics) runs in its own Gforth process; the checker process
receives serialized terms only (OQ-1)"; now in `docs/project/PLAN_DRAFT.md`
with steps 8.2.1a–g and the new task 8.6.3):

> **8.2.1 LeanForth run by Forth itself** (ADR 0017 Amendment 1). In a
> Gforth session with LeanForth loaded, Forth's interpreter runs LeanForth
> text — from files (`leanforth check [--env EXPORT] FILE.lf`,
> `lf-include`), typed at the prompt (`lf-prompt`) or from Forth programs
> (`lf[ … ]lf`, `param:`, `example`) — with only LeanForth's sealed word
> lists visible (Amendment 1 A5) and the library as a vocabulary (A4);
> each declaration is built in the kernel's stores and checked by the
> kernel of `leanforth check`. Results where only LeanForth ran carry the
> standard label; others read *checked in this session* until saved and
> re-checked by `leanforth check` in a fresh process.
> *Acceptance:* the A5 probes as tests on both Gforths; a randomized
> hostile-text run leaves the dictionary laid down while loading and the
> checked environment unchanged; every example file of `tests/author`
> checked, with the three forms; inline and prompt verdicts equal
> fresh-process verdicts; tests reaching accepted, rejected and
> unsupported/unknown; every case pair of the library resolves exactly
> (A16). *Needs:* 3.4.1, 8.1.2. *Gates:* [parser], [bypass]
> (8.2.1g: [kernel]). *Size:* M, as seven S steps.

| Step | What | Gates | Tests (three forms where a theorem is shown: mathematics, LeanForth, Lean) |
| --- | --- | --- | --- |
| 8.2.1a | Runner rules for the kernel's process: the `STATE` rule, control bytes and UTF-8, the dictionary reserve, the private list for the defining `EVALUATE`, the sealed-list content test, a named line for Forth exceptions | [parser] | p01, p03, p04, p05, p07 as tests on both hosts, each refusal with a stable code; planted faults: no `STATE` rule, a VALUE in LF-WORDS (caught on 1.0), no reserve |
| 8.2.1b | Authoring words at the kernel's scale: shared nodes found through a hash table (`src/lib/htab.fs`) or not shared, `lfa-shift` on `src/lib/frame.fs` steps, every table growable in the heap (the authoring words' part of plan 6.2.4) | [parser] | today's tests unchanged; a text of 100,000 nodes; a term nested 1,221 deep (Mathlib's deepest); round trips |
| 8.2.1c | The words to the kernel: `end NAME` adds an input declaration and checks; `leanforth check FILE.lf` and `lf-include` without a library; `example`; verdict lines with the statement in three forms (8.6.2) | [bypass], [parser] | `tests/author`'s fixtures accepted with the three forms (Lean compiled with pinned Lean, statements equal to `#print`, terms equal node for node); mutated proofs *rejected*; an axiom *unsupported*; a declaration whose text failed is not checked (exit 4) |
| 8.2.1d | The library as a vocabulary: LF-LIB with the whole-name index and the host adapters (1.0, 0.7.3), the look-ahead as the portable path, library constants in §9's resolution, `protected` recorded by the export pipeline, `import-stub` refused with a library and then removed; the case-twin note (A16) | [bypass], [import] | p09 and p11 as tests; A16's case tests T1–T7 on both hosts (every one of `Init`'s 31 pairs exact, no wrong-case spelling resolving); a file using `True.intro` and `And.intro` checked against `Init`, verdicts equal to the same theorems' Lean export; names only in the file, only in `Init`, in both (N2, as Lean); a protected `Init` constant through a namespace |
| 8.2.1e | Sessions and inline words (A7): `lf-session`, `lf-prompt`/`lf-done`, `lf[ … ]lf`, `lf-run`, `param:`, the parameter, term-building and result words; scratch rolled back after each check; examples never published; the session label; line numbers restarting for each text (p12 counted on from the session file) | [parser], [bypass] | p06 and p10 as tests; one row each for accepted, rejected, unknown, unsupported; a parameter missing or left over; the `STATE` refusal; a scripted prompt session; a planted forgery by a user program, shown and documented as outside the label |
| 8.2.1f | Saving and re-checking: `lf-write`, `lf-save`; `leanforth check` on the file | [format] once a receipt carries it | p06b as a test: same verdicts, statements identical; shared with 8.6.2's round trip |
| 8.2.1g | The input grows one declaration at a time after the environment exists (ADR 0012 amendment), so `end NAME` checks and publishes exactly one declaration (A3) | [kernel] | the environment's tests and the failure-path suite with declarations added one by one; verdicts identical to a whole-input run |

**Progress.** 8.2.1a is implemented (2026-11-04, before its [parser]
gate): the rules are in `src/author/runner.fs`, `groups.fs`, `source.fs`
and `errors.fs` (codes 45 and 46), described in
[LeanForth words](../programming/LEANFORTH_WORDS.md#forth-interface),
tested by `tests/author/author.fs` on Gforth 1.0 and 0.7.3, with nine
planted faults in `tests/mutants/faults.toml`, all caught. It also makes
each text's lines count from 1 (the p12 finding, first recorded for
8.2.1e). Since 2026-11-12 `leanforth check FILE.lf` runs every text under
these rules (integrated), and 8.2.1c and 8.2.1d are built as
[Amendment 2](#amendment-2-leanforth-text-checked-by-the-kernel-2026-11-12)
records.

**Where 8.6.2 fits.** The statement in three forms is printed with every
verdict of 8.2.1c and by `lf-verdict.`, from the same printer (merged
2026-11-04); its round-trip acceptance is 8.2.1f's test.

**Not part of 8.2.1:** the notation translator (A2: handoff §5, LF-012,
T10.4, after 8.3.1); a command that writes a whole Lean export as one
`.lf` file (new plan task 8.6.3, beside 8.6.2); named theorems added
inline before 8.2.1g; `import NAME` once exports carry module names;
inline checks in parallel jobs (ADR 0009); saved results for the library
(OQ-3, ADR 0012 E8).

**Other text changed with the acceptance:** the Follow-ups entry "8.2.1",
the summary's trust bullet, the context's trust boundary, §2's trust
paragraph and §18 above; `docs/user/LEANFORTH_SYNTAX.md`'s status
paragraph; ADR 0010 §9's last sentence; `docs/project/PLAN_DRAFT.md`
(8.2.1 with 8.2.1a–g, 8.6.3). The owner's answers are in
`docs/project/OWNER_DECISIONS.md`.

### A14. Questions for the owner, and the answers

**Answered by the owner on 2026-11-04** (recorded in
[decisions](../project/OWNER_DECISIONS.md#native-leanforth-where-theorems-run-inline-use-library-vocabularies-2026-11-04-late)):

- **1: yes.**
- **2: yes.**
- **3:** *"Lets do 1, but carefully document and leave for future
  consideration 2. Also concerned about the case issues."* — the library
  as a vocabulary (A4, decided); one Forth word per name documented and
  kept for future consideration (A4); case in every layer, with its tests
  (A16).
- The first version's question 4 (a short word for Lean's `+`): *"Not
  now"* (A10).

The questions as they were asked:

1. **Where theorems run, and how far to trust each way.** With LeanForth
   loaded, Gforth's own interpreter runs theorem text, whether it comes
   from a file, from what you type at the prompt, or from a Forth program
   that passes values in. A file run by `leanforth check` in a fresh Gforth
   can only use LeanForth's own words, so its results get the normal label.
   When other Forth has run in the same Gforth — anything typed at the
   prompt or your own program — that code could in principle change a
   result, so those results say "checked in this session" until you save
   the theorems to a file and run `leanforth check` on it. Is this the
   arrangement you want? It replaces your earlier answer that the checker
   should be a separate program that only receives finished data.
   *Recommendation: yes.* It is the Forth way you described: the
   interpreter runs the words, at the prompt, from files and inline. A file
   can run nothing but LeanForth's words (tested on both Gforths), so it is
   as safe as the NDJSON files the checker already reads. The re-check in a
   fresh Gforth is one command, mirrors your two modes for saved results
   (development and final run), and is what Lean itself does with its
   separate checker (`leanchecker`).

2. **Passing values from a Forth program into a theorem.** Inside a Forth
   word, the theorem's text goes between `lf[` and `]lf`, written exactly
   as in a file, and values from Forth come in by name (`param: f`). A
   value can be a statement, a function such as `Real.sin`, a number, or a
   type such as an n × n matrix type. The answer comes back on the stack
   as one outcome (accepted, rejected, unknown …), with words to print it.
   Is this the shape you want? *Recommendation: yes.* It is how the
   established provers in the LCF family (HOL Light, Isabelle) and Lean let
   a program build theorems — write the theorem as text, mark the holes,
   fill them from the program — and HOL Light was used this way to verify
   Intel's sine and cosine. It reuses the words of files unchanged, every
   instance can be saved and re-checked, and it already ran with today's
   checker on both Gforths (statements and functions passed in a loop).
   Where one theorem "for every f" is possible, Lean's own way — quantify
   over f — works too, in the same text.

3. **How Forth finds a library's names.** Lean's `Init` has 59,349 named
   theorems and definitions, Mathlib 729,263. Recommended: the library is
   a vocabulary — one more Forth word list in the search order — whose
   search looks a name up in the library's own index (a hash table), so no
   Forth word is made in advance. It was measured on all of `Init`: about
   1.5 µs per name on Gforth 1.0 (3 µs on 0.7.3), the index built in
   0.02 s, with upper and lower case exact, as Lean needs. The alternative
   is one ordinary Forth word per library name, made when the library
   loads: 0.6 µs per name, 4 MB and 0.08 s for `Init`, but about 50 MB and
   a second for Mathlib at every start, and Forth's search ignores case:
   `Init` alone has 31 pairs of names such as `id` and `Id` that it mixed
   up in the test, so it would need extra checks.
   *Recommendation: the vocabulary.* It is the Forth-like solution you
   asked about, it costs nothing at load time and stays exact; it uses
   Gforth's own way of making such word lists (Gforth 0.7.3 makes its
   locals and Gforth 1.0 its case-sensitive tables the same way) behind a
   small adapter for each, and keeps a plain-Forth fallback (looking at
   each line's names first) for other Forth systems.

### A15. Rejected alternatives

- **The separate authoring process of OQ-1, kept**: a process boundary for
  data that can only run fixed words adds serialization and a second
  reader without adding protection; the protection that matters, against a
  user's own code, is the fresh-process re-check (A7).
- **Compile-time LeanForth words in colon definitions** (A7).
- **A word for every library constant up front** (A4; question 3): not
  rejected but kept for future consideration, as the owner asked; measured
  cheap for `Init`, but case-blind unless every library name gets a name
  group (31 collisions in `Init` as plain words), and large for Mathlib at
  every start.
- **The per-line look-ahead as the main design** (the first version):
  kept only as the portable fallback; LF-LIB is the Forth way.
- **Gforth 1.0's recognizers for library names** (a recognizer stage
  after `rec-name`): would work on 1.0 only; the word-list adapter works
  on both Gforths and keeps `SEARCH-WORDLIST` (used by the name groups'
  hand-over, §5) seeing the library.
- **Parameters taken from the caller's data stack** inside the text: the
  run's frames (§7) exist so that no word reaches below its floor; a named
  parameter is visible in the text and in the printed instance.
- **Treating session verdicts like file verdicts**: the surrounding Forth
  could forge them (A7).

### A16. Case: how every layer treats upper and lower case

The owner, answering question 3: *"Also concerned about the case issues."*

**The rule.** Lean's names are case-sensitive: `Id` (a type) and `id` (a
function) are two constants, and `Init` alone has 31 such pairs (appendix
below; Mathlib has 537 groups, §3). Forth's word lists are not: both
Gforths find a word whatever the case of its ASCII letters. LeanForth never
lets that decide a meaning. Wherever Forth finds a word regardless of
case, the word itself compares the exact bytes of the token that invoked
it and, when they differ, passes the token, as written, to the word lists
searched after its own; wherever LeanForth looks a name up itself, it
compares exact bytes. So **a spelling means exactly the name Lean would
give it, or it is refused at its line and column; it never silently means
its case twin.**

| Layer | What Forth does | What LeanForth does | Evidence |
| --- | --- | --- | --- |
| Forth's own word lists, Gforth 1.0 and 0.7.3 | fold ASCII `A`–`Z` only; `α`/`Α`, `é`/`É`, `ǆ`/`ǅ`/`Ǆ` are not folded; the two hosts agree (p13). Both also have case-sensitive lists (`table`; on 1.0 `cs-wordlist`), which LeanForth does not use | relies on neither folding nor its absence: every rule below gives the same result with case-blind and case-sensitive lists (§5; the prototype's output was byte-identical with Gforth's case-sensitive lists) | p13; §5 |
| LeanForth's syntax words (LF-WORDS) | `prop` and `PROP` find the word `Prop` | each word checks the spelling it was called with (§5): `Prop` is the sort; `prop` is passed on, so a variable or constant named `prop` works; `PROP` is an unknown name (error 1) | `tests/author/author.fs`; `14-case.lf` |
| Variables and universe parameters (LF-LOCALS) | `x` and `X` find one word | one *name group* per case-folded spelling, holding each exact spelling: `x : X` works; `p` written for `P` is error 1 at its token | `10d-case.lf`, `15-case-variables.lf` (whose planted fault, a spelling check that ignores case, only the comparison with Lean catches, §13) |
| The file's own constants (LF-CONST) | `id` and `Id` find one word | name groups as above: a file declaring both uses each exactly | `14-case.lf`, compared with Lean's terms by `tests/author/check_author.py` |
| The library (LF-LIB, A4) | calls LeanForth's search with the token as typed | the whole-name hash index compares bytes; nothing is folded | p09; p11 (below) |
| From one layer to the next | — | a word that sees a different spelling hands the token *as written* to the later lists through `SEARCH-WORDLIST`, which on LF-LIB calls the exact search: a local `id` does not hide the library's `Id`, and the syntax word `Prop` does not hide a constant `prop` | §5; test T4 |
| Other names the words read: `namespace`, `open`, `end NAME`, `label:`, `root:`, `param:` | — | compared exactly: `end foo` after `theorem Foo` is error 22; `open nat` with only `Nat` known is an unknown namespace | `src/author/namespaces.fs`, `declarations.fs` |
| Forth-side words: `lf[`, `lf-prompt`, `lf-include`, `>lf-param` … | ordinary Forth words, case-blind as every Forth word (`LF-PROMPT` works) | they never stand for a Lean name; the `]lf` that ends a captured text is matched exactly, in lower case | A7 |
| The prompt and files | — | the same runner and words: a line typed at `lf-prompt` behaves exactly as the same line in a file (T9). At Forth's own `ok` prompt, outside `lf-prompt`, the words are Forth's and no LeanForth text runs | A1, A2 |
| The printer and `leanforth print` | — | names are written byte for byte as Lean has them: in Lean's notation through Lean's `Name.toString`, with escapes only for characters that are not part of an identifier (letters are never changed, `src/cli/name-text.fs`); in Forth mode `root:` is written only when a variable or universe parameter has *exactly* the same spelling (`lf-pf-hides?`, `lf-pp-any?` compare bytes), so a variable `x` beside a constant `X` prints a plain `X`, which reads back as `X` | `14-case.lf` round trip; `src/present/print-forth.fs` |
| Errors | — | the token is shown as written, with its line and column | A5 |

**When text says `Id` but means `id`.** It does exactly what Lean does.
`Id` is a name, so the word resolves to `Id` — never to `id`, and without
an error at the name; the kernel then checks the declaration as written.
Probe p12 (both Gforths, the real checker): with `same : Prop → Prop` and
`Same : Prop → Prop → Prop` declared, `def pick Prop Prop -> := same end
pick` is accepted and the same with `Same` is *rejected*; pinned Lean
rejects the second with "Type mismatch … Same has type Prop → Prop → Prop
but is expected to have type Prop → Prop" (`lean/case-wrong.lean`). A
spelling no constant has, `SAME`, stops with error 1 at its line and
column (p12), where Lean reports "Unknown identifier `SAME`"
(`lean/case-none.lean`). The statement printed back with every verdict
shows `Same`, so a reader sees which constant was used. If the two twins
had the same type and the proof still checked, the declaration would be
accepted — about the constant written — exactly as in Lean.

**A case-twin note (design, task 8.2.1d).** Because the owner is
concerned: when a declaration uses a name that has a case twin (another
constant equal to it apart from case), its verdict line adds a note with
the line and column, for example `note 14:29: Same — a constant same also
exists`. It is untrusted presentation: it never changes a verdict (the
default stays Lean's), it is printed with every verdict (most useful next
to a rejection) and in the JSON output. An opt-in flag
(`--case-twin-errors`) makes it an error, for those who want that;
stricter behaviour only behind a flag, as the owner's rule requires.

**Test plan** (task 8.2.1d; every test on Gforth 1.0, with default and
restricted recognizers, and on Gforth 0.7.3):

- **T1, every pair of `Init`:** both spellings of each of the 31 pairs (62
  spellings) resolve, through LF-LIB and Forth's interpreter, to the
  declaration with exactly that name; 168 wrong-case spellings that are no
  name of `Init` (all lower case, all upper case, cases swapped, the first
  letter of a part swapped) are refused. Probe p11 ran this fixture over
  all of `Init` on Gforth 1.0 (default and restricted recognizers) and
  0.7.3: every exact spelling resolved to its own declaration, every
  wrong-case spelling was refused, no failure.
- **T2, through the real runner:** the same fixture once LF-LIB is wired
  into the sealed order: every refused spelling is error 1 with its line
  and column.
- **T3, with the kernel:** for each pair, where a short declaration tells
  the twins apart by type (`Id`/`id`, `Bool`/`bool`, `Repr`/`repr`,
  `String.Pos`/`String.pos` …), a declaration using each spelling, with
  verdicts equal to pinned Lean's on the same source.
- **T4, shadowing across layers:** a variable `id` with the library's `Id`
  used in the same body; a file constant `ID` beside the library's `Id` and
  `id`; a file or library constant spelled like a syntax word (`prop`).
- **T5, a file's own pairs:** today's `14-case.lf`, `15-case-variables.lf`
  and `author.fs` rows, compared with Lean's terms.
- **T6, the printer:** every pair printed in Forth mode and read back to the
  identical term; the Lean-notation lines equal Lean's `#print`.
- **T7, planted faults, each caught:** LF-LIB's search folding case before
  hashing (T1 fails); a name group ignoring its spelling check (T5's
  comparison with Lean fails, as §13 found); the hand-over passing a
  case-folded token (T4 fails).
- **T8, beyond ASCII:** `Init` has no pairs that only Unicode case folding
  would make (p11: none); a file pair `α`/`Α` resolves exactly on both
  hosts (Gforth folds only ASCII, p13).
- **T9, the prompt:** T1's fixture typed into `lf-prompt` (scripted input)
  gives the same results as `lf-include` of a file.
- **T10, Mathlib:** at stage S4/S5, the same fixture generated from the
  Mathlib export (537 case groups, §3), with the same generator.

**Fixture plan.** A script, kept beside the test, derives the fixture from
an export as `p11-pairs.py` does — every name grouped by ASCII case
folding (and by Unicode case folding, to report any extra group), each
spelling of each group as an *exact* line, and up to eight wrong-case
spellings per group that are no name of the export as *none* lines — and
records the export's SHA-256, so the fixture is regenerated, never edited,
when the pinned Lean or Mathlib changes. For `Init` (SHA-256
`c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179`) it
has 62 exact and 168 none lines.

**Appendix: `Init`'s 31 case pairs** (pinned Lean 4.35.0; found by p11
over all 59,349 declaration names; all differ in ASCII letters only):

| # | Pair | # | Pair |
| --- | --- | --- | --- |
| 1 | `Bool` / `bool` | 17 | `Std.PRange.Nat.toList_Rco_succ_succ` / `Std.PRange.Nat.toList_rco_succ_succ` |
| 2 | `IO.Process.Output` / `IO.Process.output` | 18 | `String.Pos` / `String.pos` |
| 3 | `Id` / `id` | 19 | `String.Pos.Down` / `String.Pos.down` |
| 4 | `InvImage` / `invImage` | 20 | `String.Pos.Raw.IsValid` / `String.Pos.Raw.isValid` |
| 5 | `Lean.Grind.NodeDefUnexpander` / `Lean.Grind.nodeDefUnexpander` | 21 | `String.Pos.Raw.IsValidForSlice` / `String.Pos.Raw.isValidForSlice` |
| 6 | `Lean.Syntax.Ident` / `Lean.Syntax.ident` | 22 | `String.Pos.Splits` / `String.Pos.splits` |
| 7 | `List.Lex` / `List.lex` | 23 | `String.Slice` / `String.slice` |
| 8 | `PSigma.Lex` / `PSigma.lex` | 24 | `String.Slice.Pos` / `String.Slice.pos` |
| 9 | `PSigma.RevLex` / `PSigma.revLex` | 25 | `String.Slice.Pos.Down` / `String.Slice.Pos.down` |
| 10 | `PSigma.SkipLeft` / `PSigma.skipLeft` | 26 | `String.Slice.Pos.Splits` / `String.Slice.Pos.splits` |
| 11 | `Prod.Lex` / `Prod.lex` | 27 | `String.Slice.Subslice` / `String.Slice.subslice` |
| 12 | `Prod.RProd` / `Prod.rprod` | 28 | `String.ToSlice` / `String.toSlice` |
| 13 | `Repr` / `repr` | 29 | `String.getUTF8Byte` / `String.getUtf8Byte` |
| 14 | `ShareCommonM` / `shareCommonM` | 30 | `System.Uri.UriEscape.letterA` / `System.Uri.UriEscape.lettera` |
| 15 | `Std.Iter.Step` / `Std.Iter.step` | 31 | `System.Uri.UriEscape.letterF` / `System.Uri.UriEscape.letterf` |
| 16 | `Std.IterM.Step` / `Std.IterM.step` | | |

## Progress note (2026-11-05): numeric name parts

The rule "no part of a name may be number-like" of the re-review is
narrowed to what it protects: no word is made for a number. A declaration,
universe or namespace name must not be number-like as a whole token; a part
after the first may be numeric (`Name.num`), such as the 0 in Lean's private
`_private.Init.Data.Nat.Basic.0.Nat.zero_add.match_1_1`, so `Nat.zero_add`
and its helper are written whole and read back to the same names. A shorter
form of a name that is number-like gets no word. A string part of digits is
written and read between guillemets (`N.«0».f`), distinct from the numeric
part (`N.0.f`). Untrusted authoring and presentation only; no checker change.

## Amendment 2: LeanForth text checked by the kernel (2026-11-12)

**Status: proposed and built 2026-11-12 (plan tasks 8.2.1c and 8.2.1d,
agent LF1, branch `lf-files`); integrated, not through its [parser],
[bypass] and [import] gates.** It records how
Amendment 1's A1, A3, A4 and A6 were built and where the build differs
from them. It changes no typing or conversion rule, no axiom rule and no
kernel module: the declarations reach the kernel through the importer
stage, exactly as an export's do.

**In plain words.** `leanforth check FILE.lf` now checks a file of
LeanForth text with the checker that checks Lean's exports, and prints
the same report. `leanforth check --env EXPORT FILE.lf` lets the file use
a Lean library's constants, such as `Init`'s `Nat`, `Eq.refl` or
`Nat.add_comm`, by their Lean names; `--snapshot FILE` takes the library
from a snapshot instead. A file whose text has a mistake is not checked
at all. Examples: `tests/author/19-add-zero.lf` proves $n + 0 = n$ by
`Eq.refl n` and `20-zero-add.lf` proves $0 + n = n$ by induction with
`Nat.rec`; both are accepted against an export of `Init`, their wrong
twins rejected, as pinned Lean accepts and refuses the same theorems
([the command line](../user/COMMAND_LINE.md#checking-leanforth-text),
[LeanForth syntax](../user/LEANFORTH_SYNTAX.md#checking-a-file)).

**B1. The text reaches the kernel as export records** (A1, A3). The words
build each declaration in the context's term, level, name and reference
stores, as before. When the file ends without an error,
`src/author/export.fs` writes the declarations as the records of an export
in lean4export's format 3.1.0 — its names, levels and expressions in store
order, then each theorem, definition (with Lean's height, getMaxHeight + 1)
and axiom — through `src/lib/json-write.fs`, under a metadata record naming
LeanForth as the exporter, and hands each line to the importer stage
(`stage-produce`, `src/import/stage.fs`), which reads it with the same
handlers and checks as a Lean export's lines. The stage is sealed, fed and
checked by `cli/check-run.fs`'s run, and `cli/leanforth.fs` prints the
verdicts from the published slots (`src/cli/check-lf.fs` is the loading
step). *Why records, not the input directly:* the feed, the checked
environment, the snapshots' import pass, `--jobs` and every report work
unchanged, with the stage's own refusals of malformed records in front of
the kernel; the alternative, adding declarations to a sealed input, is the
kernel change of 8.2.1g. *Difference from A1/A3:* the whole file is checked
when it ends ("Now", A3), not each declaration at its `end NAME`.

**B2. The library** (A4, A6). `--env EXPORT` reads the export into the
stage first (its manifest checked unless `--no-manifest`); `stage-extend`
then keeps its declarations while the text's records are read on into the
same tier, so constants resolve among both at sealing, and every library
declaration is checked before the text's. `--snapshot FILE` loads the
snapshot's tier as `check --snapshot FILE EXPORT` does, keeps its
declarations the same way, and the import pass (ADR 0020 D5) takes them
from the snapshot, so only the text's are checked; the run is a snapshot
run, labelled so (development and research only). The words find the
library's constants through a finder (`src/author/library.fs`): the full
name, looked up in the stage's names and declarations before sealing,
gives its number of universe parameters and its height; a constant named
for the first time gets a record of kind library, and resolves as the
file's own constants do (§9). *Difference from A4:* LF-LIB, a word list
with its own search on each host (`wordlist-class`, `mappedwordlist`), is
not built; the look-ahead A4 kept as the portable path is used on both
Gforths: before a line runs, each of its tokens up to a `\` comment,
outside the text of `( … )` comments and notes (B6), that
no word list of the run has and that is not number-like gets a group word
in LF-CONST, which decides nothing (an unknown name still stops as
unknown, error 1). It costs a group word (about 48 bytes) per distinct
spelling, within the dictionary reserve of A5 row 11.

**B3. Rules of a checked text.** (1) `import-stub` is refused (error 48,
invalid): a stub declares a constant no one checks; it remains for runs of
the words alone (the printer's tests, the documentation's examples). (2) A
text that declares nothing of its own is refused (error 49). (3) A
declaration may not take a library constant's name (error 28, Lean's
"already declared"). (4) Lean's export does not record `protected`, so a
one-part name that reaches a library constant through a namespace (P.T or
O.T) stops with error 55 (unsupported, "write the full name"): a temporary
refusal where Lean decides, until the export pipeline records protected
(A4, 8.2.1d). (5) A text that stops with an error is not checked at all,
the declarations before the error included; the error is printed at its
line and column and the exit status is its outcome's (4 invalid, 2
unsupported, 3 full). (6) An axiom is checked as an export's axiom is:
Lean's verdict, labelled NOT PROVED with what depends on it (owner,
2026-11-04). The stores get the room the heap has while the words run, and
their settings back after.

**B4. Evidence** (`tests/author/check_author.py`, `author.fs`,
`tests/core/stage.fs`). All 25 fixtures of `tests/author` run through
`leanforth check`: the 19 whose Lean source pinned Lean accepts are
accepted (`07-add-comm`, `14-case`, `19-add-zero` and `20-zero-add` against
`tests/author/init-slice.ndjson`, 59 declarations of `Init` exported by
pinned Lean with `scripts/export.sh`; `08-monoid` against the class alone,
`monoid-slice.ndjson`, exported from its Lean source; both reproduced byte
for byte in `make check`), and the other 6 stop before any check (4 text
errors, the structure sketch's stub, a line too long); four wrong twins
in `tests/author/wrong/` are rejected, and pinned Lean refuses their Lean
sources; the words' terms equal Lean's, node for node, for every fixture
with a Lean source, literals included; 19 command cases reach every
outcome and misuse (accepted, rejected, NOT PROVED with and without
`--strict-axioms`, exhausted, unsupported, text errors, a library name
taken, a short name, wrong case, stubs, `--jobs 2`, a missing library,
`--json`, `--env` without a text). Nine planted faults in
`tests/mutants/faults.toml` (`lf-…`) are caught, among them a failed text
still checked and a stub accepted with a library. Against all of `Init`
(measured once, 2026-11-12, not in the test suites): `check --jobs 2
--save-snapshot` of the pinned `Init` export accepted its 59,349
declarations (one NOT PROVED) in 708 s; with that snapshot, `07-add-comm`,
`19-add-zero` and `20-zero-add` were accepted and the wrong twins of 07
and 19 rejected, 16 to 19 s and 0.6 GB a run.

**B5. What is left.** 8.2.1b (the words at the kernel's scale: their
node sharing searches the store), 8.2.1e (prompt and inline use), 8.2.1f
(saving and re-checking), 8.2.1g (a check at each `end NAME`, a kernel
change), LF-LIB with its host adapters (a speed-up over the look-ahead),
`protected` in the export pipeline, `open` of a namespace only the library
has (error 26 now: a namespace is known once the text enters it or
declares a name in it; a temporary gap where Lean decides, with
`protected`, in 8.2.1d's follow-ups), `--json` for a text, and the term
printer's types for library constants (a library constant prints with
all its arguments, `@Eq Nat …`, where Lean hides the implicit ones; the
terms are the same).

**B6. After the Forth and gate review of 2026-11-12**
([report](../development/forth-reviews/2026-11-12-lf-files.md); agent LF2,
branch `lf-files-2`). (1) *The records are compared* (H1):
`tests/author/report.fs` prints the records `export.fs` writes, and
`check_author.py` reads them as an export and compares every declaration
with the terms the words built (`make test`) and its whole record — kind,
name, `all`, `levelParams`, hints, safety, type and value — with pinned
Lean's export of the fixture's Lean source (`make check`); fixture
`06-universes` gained `PairOf` (a constant with two different universe
arguments) and `21-numeric-name` a name with a numeric part (a private
theorem); the reviewer's five writer faults are planted and caught.
(2) *Same format, not the same bytes* (L1, S7): each record has the
pinned exporter's form, key order (sorted; the JSON writer's sorted mode
refuses any other) and string escapes (Lean's `Json.compress`), but the
numbering differs — lean4export writes names, levels and expressions as
it first meets them, declaration by declaration, one record for equal
nodes; `export.fs` writes them store by store, and nodes the term store
keeps apart (binders) get records of their own; the metadata names
LeanForth as the exporter with no Lean build (`"githash": "none"`). A
declaration means what Lean's export of the same source means; the file
is not byte for byte Lean's. (3) *Fails closed earlier*: a projection
leaf anywhere but as the function of `$` stops the run (error 56, M2) and
the writer refuses a reference to one or a level of an unknown tag (S6);
the look-ahead skips the text of `( … )`, `note"` and `ai-note"` (M1); a
text whose records are refused before the check says so of the text
(L4). (4) Not changed: the typing and conversion rules, the axiom rules
and every kernel module.
