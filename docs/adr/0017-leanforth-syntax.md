# ADR 0017: LeanForth Forth syntax for theorems, definitions and proofs

Status: **accepted as the design basis** by the owner on 2026-11-02 (decisions 1–4 as recommended, see [owner decisions](../project/OWNER_DECISIONS.md)); proposed 2026-11-02 (plan task 8.1.1). **Implemented** 2026-11-03 in `src/author/` (its [parser] gate **approved by the owner on 2026-11-03**, after two clean review rounds) and the term printer's Forth mode (plan task 8.1.2; [programming reference](../programming/LEANFORTH_WORDS.md), [user page](../user/LEANFORTH_SYNTAX.md)); the implementation still passes the [parser] gate before anything relies on it. Two points of the implementation refine this record: while the stores hold 64 nodes, equal subterms share one node, which keeps the position where it was first written (a step with a label or note always has its own node); and the stand-in for imports is the word `import-stub` (the prototype's `stub` and `declare`). The independent review of the implementation (2026-11-03) corrected four points of this record, in §3, §6, §9 and §10; they are listed under [corrections after the review](#corrections-after-the-review-2026-11-03). Before that, a throwaway prototype (outside the
repository, see [Evidence](#evidence)) ran every example below as Forth
words through Forth's own interpreter, built the terms in LeanForth's
existing stores, printed them with the term printer, and ran its own
printed words again.

**[Amendment 1](#amendment-1-proposed-leanforth-text-checked-natively-and-inline-from-forth-programs)
(proposed 2026-11-04, for the owner's [parser] and [bypass] design
gate):** LeanForth text checked natively in the checker's process, with
only LeanForth's sealed word lists visible, straight into the checker's
stores; and inline checks from Forth programs, labelled *checked in this
session*, re-checked in a fresh process for a claim. It revises the
owner's OQ-1 answer (a separate authoring program), on which §2, §18 and
the follow-up "8.2.1" below rest.

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

- **The syntax decides nothing.** The words run in an authoring program
  that is separate from the checker (your answer to OQ-1), and it hands the
  checker only finished terms. Running an author's words there is safe for
  the checker: whatever a person or an AI writes, only the checker can
  accept it. The checked statement can be printed back, so a person can see
  what was really checked.
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
  checker receives serialized terms only.
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

A proof file is Forth text. The authoring program sets the search order to
the LeanForth wordlists (§3) and hands the file to Forth's text interpreter
line by line (`EVALUATE`, counting lines for messages). Each token is found
as a word and executed, or converted as a number; nothing else reads the
text. A few words read the token after them, exactly where Forth's own
defining words do: the words that introduce a name (`theorem NAME`,
`explicit: NAME`, `universe NAME`, `namespace NAME`, `end NAME`,
`label: NAME`), and `note" …"`, whose text is prose, never structure. No
string carries mathematics.

**Trust.** Running the author's words is acceptable because it happens in
the authoring program, which is untrusted and separate from the checker
(OQ-1); the checker receives serialized terms only. A word that misbehaves
can at worst build a wrong term, which the checker checks as it is and the
printer shows.

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
recognizes more than words and numbers, the authoring program limits the
recognizer to words and digits while a proof runs (`rec-forth`, guarded by
`[DEFINED]`); every host then refuses the same tokens.

**Scale.** Every constant an author can name is a Forth word. In Gforth 1.0
a name group with its entry took 119 bytes of dictionary, 6 µs to define
and 0.4 µs to look up (100,000 words of Mathlib-like names, measured). All
729,263 Mathlib constants, under full and short names, would take about
170 MB and 9 s in the authoring program; 8.2.1 can define only the words of
the modules a file imports. The checker is not affected.

**Trusted base.** None of this is trusted. A wrong word produces a
different term, which the checker checks as it is and the printer shows;
the defences are the round-trip test, comparison of the terms with
Lean's, term for term, and of printed statements with Lean's, and the
printed statement in every receipt.

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
- **8.2.1**: the authoring program in its own process, defining the words
  of imported constants and sending the checker serialized terms with a
  span side file.
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

## Amendment 1 (proposed): LeanForth text checked natively, and inline from Forth programs

**Status: proposed 2026-11-04 for the owner's [parser] and [bypass]
design gate. Nothing in `src/` or `tests/` is changed.** It answers the
owner's request of 2026-11-04 and **revises the owner's OQ-1 answer of
2026-11-02** ("Checker isolation: separate program. The checker runs as
its own program and receives proofs only as data",
[decisions](../project/OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)),
which §2, §18, the follow-up "8.2.1" above, ADR 0010 §9 and ADR 0019 §3
("Process") rely on. Under this amendment a LeanForth file is read *in the
checker's own process*, by Forth's own interpreter with only LeanForth's
sealed word lists visible, and goes straight to the checker; and a Forth
program can call the checker inline, with an honest, weaker label. The
claims below were probed on Gforth 1.0.0 and 0.7.3 (section A9); the Lean
forms were checked with pinned Lean 4.35.0. It changes no typing or
conversion rule, no axiom rule and no LeanForth word of §§3–11.

The owner's words (2026-11-04): *"I think the sealed word list is the
correct approach, are there any downsides? does it use the standard forth
parser? I was before concerned about, for example, +, being mixed up
between forth + and Lean +, I guess using a sealed word list and limited
non-forth vocabulary, we don't have to worry. We should be able to run it
inline, not just as a external file that starts gforth and then exits. An
example might be to run with different numeric constants passed in in a
loop from Forth. or different trig functions or a different sized matrix
all passed in a loop from Forth. (In the example above, perhaps A might be
a passed in parameter.."*; earlier the same day: *"I think we should end up
with native LeanForth going straight to the solver... seems more forth
like"*.

### In plain words

**What changes.** Until now the plan was: LeanForth words run in a separate
"authoring" program, which writes the finished terms to a file, which the
checker program reads (your OQ-1 answer). This amendment drops that
separate program. `leanforth check proof.lf` would read the LeanForth file
itself and check it, the same way it already reads Lean's NDJSON files;
and a Forth program could check theorems inline, many times in a loop, in
the same Gforth session. (A design: built after your answers, in the steps
of section A10.)

**Does it use the standard Forth parser? Yes.** The file is read by
Gforth's own text interpreter — the one that reads every Forth file —
handed the file one line at a time with `EVALUATE`, as today's authoring
words already do. While it reads, Forth's search order holds only
LeanForth's three word lists, so every word the file can run is a
LeanForth word: `dup`, `+`, `:`, `[`, `bye`, `evaluate` and every other
Forth word simply do not exist there (they stop with "unknown name" at
their line and column). LeanForth adds two checks *around* Forth's reading,
not a parser of its own: each number must be a plain decimal (Forth itself
would also read `-3`, `$10`, `1e`, `'a'`, and Gforth 1.0 even `"x"` and
`${HOME}`), and before Forth reads a line LeanForth makes sure each name
in it has a word, so that the names of a library such as `Init` are found
without first making a Forth word for each of its 59,349 declarations
(question 3).

**`+` cannot be mixed up.** In proof text Forth's `+` is not visible at
all: `p p +` in a proof stops at the `+` with "unknown name" (an existing
test, `tests/author/author.fs`). Lean's
addition is written by its Lean name (`HAdd.hAdd`) and *printed* as
`n + m`. Inline, Forth code and proof text sit in the same colon
definition, but proof text is only ever between `lf[` and `]lf`, and only
that text runs with the sealed list: outside it `+` is Forth's `+`, inside
it does not exist. Nothing in §16 changes.

**Inline, with `A` passed in.** This runs today, on both Gforths, with the
real checker (probe p06; the words `lf[`, `]lf` and `param:` are
prototypes kept outside `src/`):

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
implies C, then A implies C" at that A, for all statements B and C.
All five were accepted; a copy with a wrong proof (`f value $` in place of
`g f value $ $`) was *rejected*; a misspelt `valeu` stopped at line 8,
column 33 of the text. (The probe wrote `theorem compAt` where the design
writes `example`, which is not built yet.) Mathematics for i = 0:
$((\forall P.\,P\to P)\to B)\to(B\to C)\to(\forall P.\,P\to P)\to C$. Lean,
checked with pinned Lean: `theorem compAt_0 {B C : Prop} (f : (∀ P : Prop,
P → P) → B) (g : B → C) : (∀ P : Prop, P → P) → C := fun value => g (f
value)`, whose `#print` statement is character for character the one
LeanForth's checker printed.

**How much to trust an inline result.** A Forth program that calls the
checker shares its memory, so in principle it could change a verdict
after the fact. Inline results are therefore labelled **checked in this
session** — like your "development mode" for saved results (OQ-3): good
for exploring, never a claim. For a claim, the program writes each
instance out as LeanForth text (the printer already does this) and
`leanforth check` re-checks that file in a fresh Gforth with nothing of
yours loaded, giving today's label *accepted (experimental, not
independently audited)*. Probe p06b did exactly this with the five
instances: same verdicts, statements identical byte for byte. A plain
`leanforth check proof.lf` gets the normal label directly, because the
file can only run LeanForth's fixed words — it is data, like an NDJSON
file.

**Your other examples, honestly.**

- *Numeric constants in a loop* (`2 + 2 = 4` with the 2 passed in): needs
  natural numbers as a data type (task 5.2.1b), number literals (5.2.3),
  structures (5.2.2, because Lean's `+` is looked up in a table of
  "instances", here "how to add natural numbers") and unfolding of
  definitions (4.2.2); to avoid writing every hidden argument by hand, also
  the elaborator (8.3.1, the helper that fills them in). The full form the
  checker checks for `2 + 2 = 4` uses seven constants, 18 times, with eight
  universe arguments and six raw literals (checked with pinned Lean).
- *Different trig functions* (`Real.sin`, `Real.cos` passed in by name):
  Mathlib's real numbers, so quotients (5.2.4, the way Mathlib builds the
  reals), the three standard axioms (5.3.1) and a Mathlib slice (stage S4,
  then all of Mathlib, S5).
- *Different-sized matrices*: Mathlib's `Matrix (Fin n) (Fin n) R` (S4/S5),
  number literals (5.2.3) and the elaborator for its instances (8.3.1); a
  matrix built entry by entry in a Forth loop uses the small set of
  term-building words of section A6.
- One caution: a loop over n = 1 … 10 checks ten separate facts. It proves
  nothing about n = 11. A statement for *every* n is one theorem with a
  "for all n" and a proof by induction (5.2.1b).

**Downsides** (details in A5). A proof file still cannot define its own
Forth words, loop or compute — repetition is the job of the Forth program
around it (inline) or, later, of tactics. Gforth's interpreter becomes
part of what we rely on to build the term the text says; the defence is
that the checker checks the term as built and the statement is always
printed back (in LeanForth words, Lean notation and mathematics, plan
8.6.2) and compared with Lean in the tests. The LeanForth words now run
inside the checker's process, so they must be as carefully bounded as the
NDJSON reader. Three small gaps were found and need fixing first (section
A4): the reader must refuse to start while Forth is compiling, must refuse
invisible control characters, and must stop before Gforth's dictionary is
full (Gforth 1.0 lets it overrun by a few bytes). Today's authoring words
were built for 64-node stores and need growable tables before they meet
Init or Mathlib (task 8.2.1b). An inline check takes under 1 ms on Gforth
1.0 (p08). Checking a file against `Init` re-checks all of `Init` each
run (about 21 s) until saved results exist.

**Four questions for you** are in section A11: (1) the trust change above;
(2) the inline words' shape (`lf[ … ]lf` with named parameters, results
on the stack, `example` first); (3) how library names reach a file; (4)
whether to add any short word for Lean's `+` (recommendation: not now).

### A1. What changes from OQ-1: code or data, not which process

OQ-1 put user Forth and authoring in one process and the checker in
another. This amendment draws the line between **code** and **data**
instead:

- **Sealed LeanForth text is data.** It is read by Forth's interpreter
  with only LeanForth's word lists in the search order, so it can run only
  LeanForth's fixed words, which only build terms, declarations, labels
  and notes in the checker's stores (section A4 lists everything else
  that had to be shut). That is the position of an NDJSON export, which
  the checker's process already reads with Forth words (untrusted [import]
  code, fail-closed). `leanforth check FILE.lf` therefore gives the usual
  label.
- **A user's Forth program is code.** Inline use (A6) puts the user's
  program in the checker's process. Its verdicts are labelled *checked in
  this session* and support no claim, like a development-mode run under
  OQ-3; the claim comes from re-checking the instances as sealed text in a
  fresh process (A7).
- **Tactics and elaboration helpers (8.3) are code** too: they run in an
  inline session, and what they produce reaches a claim only as sealed text
  or terms re-checked the same way.

Unchanged: only the checker and the publisher decide; "accepted" is
printed only from a declaration's published slot (`lf-check-verdict.`);
a wrong word can only build a different term, which is checked as it is
and printed back; the review gates of `AGENTS.md`. ADR 0019 (program
words) is not changed here: a program file defines Forth words and is not
sealed text in this sense; its §3 "Process" paragraph can be revisited by
the same rule in its own amendment.

### A2. Sealed checking of a file

```text
leanforth check [--env EXPORT] FILE.lf
```

1. With `--env`, the export is staged and fed as `leanforth check EXPORT`
   does (`src/cli/check-run.fs`: stage, feed, the stores grown to fit), but
   the input is not ended yet.
2. The file runs sealed (A4). Each `theorem`, `def` or `example` … `end`
   adds one declaration to the checker's input (`lf-input-add`), its type
   and value built by the words straight into the checker's term, level,
   name and reference stores; its presentation record (binder names,
   kinds, positions, labels and notes, §§10–11) is kept for printing. No
   NDJSON is written.
3. If the run ends with an authoring error, nothing is checked: the result
   is that error, with its line and column (exit 4, malformed input, as a
   malformed export is). Otherwise the input ends (`lf-input-end`) and
   every declaration is checked in input order — the export's first —
   with `check-declaration` through the publisher, exactly as `ck-check`
   does.
4. Each of the file's verdicts is printed with the position of its
   declaration word and its statement in three forms (plan 8.6.2):
   LeanForth words (the printer's Forth mode), Lean's notation and
   mathematics.

**`example`** (a Lean keyword, so allowed by R1; pinned Lean refuses `def
example := 1`) is a theorem without a name: checked like one and never
added to the library, as in Lean, which elaborates and kernel-checks an
`example` and then restores the environment (`elabMutualDef`,
`withoutModifyingEnv`, `src/lean/Lean/Elab/MutualDef.lean` lines
1195–1205 of the toolchain). It closes with `end example`. In a file its
slot is checked in input order but no later declaration can name it.

**Names of the library** (question 3). Today every constant is a Forth
word, made by `end NAME` or `import-stub`. With an environment of tens of
thousands of constants, the design keeps Forth's own lookup for every
token and adds one step: before each line is evaluated, the runner splits
it at blanks (the splitter it already uses for errors) and makes a
constant-group word in LF-CONST for every token that is not number-like
and has none. That decides nothing: when the word runs, it resolves the
name exactly as §9 says, now with the environment's constants (found
through the input's name index, ADR 0012 E5) as candidates beside the
file's own, and stops with "unknown name" (error 1, at the token) when
nothing matches — the same error as today. A word is made per distinct
spelling the file uses, comments and notes included (48 bytes each,
p05), within the dictionary reserve of A4. The alternative, a word for
every constant up front, costs about 119 bytes and 6 µs per name group
(§18): about 14 MB for `Init`'s full and short names, more than Gforth's
default dictionary of about 8 MB (p00), and about 170 MB and 9 s for
Mathlib, every run.

**`protected`.** Lean's exporter does not record it (a limit the owner
noted when approving 8.1.2). Until the export pipeline records which
constants are protected (task 8.2.1d), a one-part name that would reach
an *environment* constant through a namespace stops with "write the full
name" — a temporary refusal where Lean decides, closed by 8.2.1d.

**`import-stub` retires.** A stub declares a constant without checking it;
in a check run it would be an unchecked assumption. It is refused in check
runs ("name the library with --env"), stays for authoring-only runs (the
printer tests and documentation) until those move to small exports, and is
then removed with its tests (task 8.2.1d). `import NAME` stays *not
supported yet*: Lean's exports carry no module names, so the environment is
named by the caller (`--env`, or the session's, A6), and the output records
the export's SHA-256 from its manifest.

### A3. What sealed text can do

Build terms with the words of §§6–9 (and `param:`, `example`), declare
theorems, definitions and examples, attach labels and notes, open
namespaces, and comment. It cannot define Forth words, loop, branch,
compute a number, read or write a file or the environment, print, change
`BASE` or `STATE`, reach any memory, or run any Forth word: §2's "Forth's
interpreter is the only parser" holds, and §16 and owner decision 2 (no
`:` definitions in proof files) are unchanged.

### A4. What must be shut, and the probes

The argument: every token of a line either (a) is found as a word of the
three sealed lists, all made by `CREATE … DOES>`, whose actions only build
terms, declarations, labels and notes in the checker's stores and make
name words (group words, §5); or (b) is converted by Forth as a number, which every
LeanForth word refuses unless it is a plain decimal before it acts on
anything (the check of §6 and of the corrections); or (c) is refused at its
token. Nothing else may act. The table lists each way text could escape,
what the probes showed on each host, and the rule. **No item failed on
either Gforth; four need a new rule** (marked *new*).

| # | What could escape | Gforth 1.0.0 | Gforth 0.7.3 | Rule |
| --- | --- | --- | --- | --- |
| 1 | Forth's own words | 31 Forth words and forms in a sealed order (`[ ] state base hex decimal here ! : ; immediate postpone evaluate included require execute catch throw abort quit \ ( s" ." char literal forth-wordlist only set-order dup bye`) all THROW −13, and so do the scoped forms `forth:dup`, `forth:bye`, `sealed:w` (p01) | the same, −13 (p01) | Search order exactly LF-WORDS, LF-LOCALS, LF-CONST (no FORTH, no Root); restored after the run, also after a THROW (p03) |
| 2 | Gforth 1.0's `->`, `+>`, `'>` recognizers | **`5 ->v` stored into a VALUE and `5 ->d` re-pointed a DEFER that sat in the sealed list; `7 +>v` added to it; `'>v` pushed its address**; `->w` on a `CREATE … DOES>` word threw −21 (p01) | no such recognizers: −13 | *Hardened:* the sealed lists hold only `CREATE … DOES>` words, never a VALUE, DEFER or VARIABLE; a test runs `0 ->NAME` for every word of the three lists on 1.0 and requires −21 (today's lists already comply) |
| 3 | Gforth 1.0's other recognizers | default: `"x"` and `"a b"` (reads past its token), `${HOME}` (reads the environment), `` `w `` and ``` ``w ``` (an execution token), `<w>`, `1_000`, `.5`, `0x10`, `10h`, `2p`, `3k`, `1M` (SI floats) are all converted; with the runner's restriction to names and digit strings (`lfa-recognize`) 83 of p01's 89 tokens throw −13, and only the sealed word (in two spellings) and four digit strings remain | none | Keep the restriction during every sealed run, restored after (p03); the number check of row 4 still decides alone, as on 0.7.3 |
| 4 | Numbers in other forms, `BASE` | converted (default): `-3 $10 #10 %10 &10 0x10 1. 1.5 .5 1e 1e3 -1e 'a' 'a ''` … | converted: `-3 $10 #10 %10 &10 0x10 1. 1.5 1e 'a' 'a ''` | Every converted token must be a plain decimal of 1–9 digits, checked before the next word acts and at the line's end: each form refused at its token with error 35 on both hosts (p03). `BASE` is ten during the run; no sealed word changes it (`hex`, `base`, `decimal` are −13); the caller's `BASE` (16 in p03) is restored |
| 5 | `STATE`: called while Forth compiles | the runner, called by an immediate word *during compilation*, compiled the LeanForth word `theorem` into the caller's definition (`see victim` shows it), reported only "unknown name", and running that definition later threw −4129 (p03) | the same (p03) | *New:* refuse to start unless `STATE` is 0, and check it after every line, as ADR 0019 §3 does; no sealed word can change `STATE` (`[` `]` are −13) |
| 6 | Parsing words | only LeanForth's read text: a name after a word, `\` to the line's end, `( … )`, `note" … "`; each to the end of its line at most; `(` and `note"` must close on their line (errors 42, 37) | the same | Unchanged; `param:` (A6) reads one name like `explicit:` |
| 7 | Bytes that split tokens | Forth splits at TAB, LF, VT, FF, CR and space only; NUL, the other control bytes, DEL and no-break space are part of a token (p07) | identical (p07) | *New:* refuse a line holding a control byte other than TAB (and a CR before its LF), or invalid UTF-8. The runner's own splitter (errors, the number check) treats every byte up to 32 as a blank, Forth does not; with such bytes refused, both split alike and what an editor shows as one token is one token |
| 8 | Nested `EVALUATE` | the only one is the runner's own: a group word is made by `EVALUATE` of `lfa-group: NAME`. Of 18 names tried as a constant and as a variable, `bye ] [ : ; postpone immediate evaluate lfa-group: abort" s" x"y \ α` and names of 200 and 239 characters became harmless words (`.(` was refused as a name; `s"` and `\` as variables then met the syntax words of the same spelling, as §5 says); nothing ran; the run went on (p04) | the same (p04) | *Hardened:* during that `EVALUATE` the search order holds a private list with only `lfa-group:`, so no later definition of that name (for example by an inline program) is picked up |
| 9 | What a THROW leaves | after 11 errors of different kinds the caller's search order, compilation word list, recognizer, `BASE`, `STATE` and stack depth were as before and no floats were left (p03) | the same (p03) | The runner catches every THROW (ADR 0018). A failed run checks nothing (A2); its terms are scratch, emptied by the next run or rolled back to the input's marks; group words stay (they only dispatch) |
| 10 | The stacks | 60,000 plain decimals in one declaration overflowed the data stack: THROW −3, caught (error 41), and the next run in the session worked; the host turns data and return stack overflow into THROWs −3 and −5 in `gforth` and `gforth-fast` (p04, p04c) | the same, at an earlier line (smaller stack) (p04) | Unchanged. Floats are read only on 0.7.3 (1.0's restricted recognizer reads none) and are refused at the line's end; a line of at most 1,023 characters holds at most 512 tokens, below both hosts' float stack (2,048 and 4,096 per `FLOATING-STACK`, p00) |
| 11 | The dictionary | each new spelling is a group word, about 48 bytes for a short name (p05). Filling a small dictionary (`-m 3M`): the run that hit the end failed with −8, caught; afterwards every new name failed. **The host lets `HERE` pass the end: `UNUSED` was −32 after `CREATE` filled it and `,` then wrote 8 more bytes without a THROW** (p05b) | 48 bytes; with `-m 1M`, −8 at the end, caught; `UNUSED` stops at 2 (p05, p05b) | *New:* make no group word when `UNUSED` is below a reserve (64 KB proposed): the run ends *full* (error 66) and sealed text never reaches the host's edge |
| 12 | The LeanForth words' own buffers | — | — | *New for this process:* in a separate program an overrun could only spoil that program; here it could reach the checker. Every buffer the words write (the line of 1,024 bytes, texts of 256, spellings of 4,096, the definition text of 256, the error token of 64, the stores) is bounds-checked today; the [bypass] review checks each, and a randomized hostile-text test compares the dictionary laid down while loading (`tests/support/dictionary-check.fs`) and the checked environment before and after |
| 13 | DEFERs and VALUEs of the implementation (`lfa-const-run`, `lfa-shift` …) | in the implementation's own word list, never in a sealed list: text cannot name them | the same | An inline program can (outside the session label's promise, A7) |

Rows 5, 7, 11 and 12 are the new rules (task 8.2.1a); rows 2 and 8 are
hardening of what already holds. The checker and LeanForth's words load
together silently on both hosts (p02: about 1.6 MB and 120 KB of
dictionary).

### A5. Downsides

1. **No definitions, no loops in proof text** (owner decision 2 of this
   ADR). A file is a list of declarations; families of instances come from
   a Forth program around it (A6), later from tactics (8.3.2).
2. **Gforth's interpreter joins what we rely on** to build the term the
   text says: splitting tokens, finding words regardless of case (the name
   groups of §5 restore exact case), running them left to right, and
   handing each line over. A host fault there could build another term.
   Mitigations: the checker checks the term as built, never the text; every
   verdict prints the statement back in three forms (8.6.2); the round
   trip (print, read back, identical term) and the comparison with pinned
   Lean's terms, node for node, as 8.1.2's tests do for 67 declarations,
   run on both hosts; and the probes of A4 become tests that fail if a host
   reads tokens differently.
3. **The words' memory safety now matters to the checker** (row 12),
   as the NDJSON reader's does.
4. **Speed.** Reading is cheap: 63–74 µs for the composition text on
   Gforth 1.0 and 255–271 µs on 0.7.3; a whole inline check, with a fresh
   environment each time, 0.73–0.95 ms and 1.85–3.2 ms (p08, 1,000 runs
   each, before and after merging plan 6.2.0 (b), on a machine shared with
   other work). But today's words were built for stores of 64 nodes: they
   find shared nodes by scanning the whole store (`lfa-find`, quadratic in
   the file's size), shift terms by recursion on Forth's return stack
   (`lfa-shift`, against plan 6.2.0 (b)'s rule that no pass's depth depends
   on it), and keep fixed tables (512 values, 256 names, 4,096 spelling
   bytes, 16 namespaces …, listed in plan 6.2.4; the binder store grows
   since 6.2.0 (b)). Task 8.2.1b removes all three before files meet
   `Init` or Mathlib. A file checked
   against `Init` re-checks all of `Init` (about 21 s today) until saved
   results (OQ-3, ADR 0012 E8) let a development run reuse them, labelled.
5. **Error messages.** Positions are the file's line and column; inline,
   the text's own, its first line counted 1 (the design adds the source
   file and line where `lf[` stood). A Forth exception inside a run
   (stack or dictionary full) is error 41 with the THROW code, and today
   an empty token (p04); 8.2.1a names the line instead.
6. **Printed instances lose sharing.** The printer writes a term as words
   without `let` (§14 is a sketch), so a parameter built by reusing a
   subterm prints much longer than it is: with A(i+1) = A(i) → A(i), the
   words for A(4) hold 16 copies of A(0) (the first p06 run). The term the
   checker checks is shared; only the printed text grows.
7. **The names look-ahead** (A2) is a small pre-pass over each line's
   tokens. It decides no meaning, but it is code beside Forth's reading,
   which the owner may weigh (question 3).

### A6. Inline use: the words

A Forth program loads LeanForth (the checker and these words) and calls it
in its own session. Proposed words (names open to the [parser] review;
each reuses no Forth-2012 name, §16):

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `lf-session` | `( c-addr u -- outcome )` | make the session's environment: stage, feed and check the export named (or none for an empty string); afterwards it is sealed and only read |
| `lf[` … `]lf` | compiling: `( "text" -- )`; running: `( -- outcome )` | immediate: at compile time it takes the LeanForth text up to `]lf`, across lines, keeps it (on the heap) and compiles its address, length and a call of `lf-run`. Outside a definition it runs the text at once |
| `lf-run` | `( c-addr u -- outcome )` | run text built at run time: sealed (A4), with the parameters pushed since the last run; check its declarations against the session; the outcome of the last one (ADR 0008) |
| `>lf-param` | `( term -- )` | push a term as the next parameter |
| `>lf-nat` | `( u -- )` | push a natural-number literal (needs 5.2.3; a negative cell is refused: Lean has no negative literals) |
| `>lf-level` | `( u -- )` | push a universe level |
| `>lf-const` | `( c-addr u -- )` | push a constant of the session by its full name, e.g. `s" Real.sin"` |
| `lf-term[` … `]lf` | running: `( -- term outcome )` | run sealed text that leaves exactly one closed term and no declaration, to build a parameter in LeanForth words |
| `lf-app` `lf-arrow` `lf-pi` `lf-lam` `lf-bvar` `lf-sort` `lf-const` `lf-nat` | small stack effects on terms | build terms in Forth, for terms a loop computes (a matrix of size n); untrusted like everything else |
| `lf-statement` | `( -- term )` | the last check's statement, to print or pass on |
| `lf-verdict.` | `( -- )` | the verdict with the session label, the statement in three forms and the axioms |
| `lf-error.` | `( -- )` | the authoring error (code, line, column, token) or the checker's diagnostic |
| `lf-write` | `( fid -- outcome )` | write the last checked declaration as sealed text, an `example` with the parameters filled in (A7) |

In the sealed text, one new word:

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `param:` NAME | `( -- )` | bind NAME to the next parameter, in the order the caller pushed them (like Forth's `{: a b :}`); each later use of NAME pushes it as a value; a parameter missing or left over is an error |

**Why text in `lf[ … ]lf`, not LeanForth words compiled into colon
definitions.** Three ways were weighed:

- *(α) Compile-time LeanForth words* (`: f theorem t … end t ;` compiling
  calls with the names read at compile time). Rejected: the binder words
  make their variables' words when they *run*, so a compiled body would
  need a second, compile-time implementation of every scope, name group
  and namespace rule (a second [parser] surface); words that act
  differently when compiling are the state-smart words ADR 0019 §9 (a)
  rejected; and any Forth word could sit between two LeanForth words, so
  the sealed property (A4) is lost and no instance can be printed back as
  the text that made it.
- *(β) The text, captured, with named parameters* (chosen). The text in
  `lf[ … ]lf` is LeanForth exactly as in a file and runs through the same
  sealed reader, so there is one vocabulary and one reader. It is not "a
  string that is parsed" (the owner's objection of 2026-11-02): Forth's
  interpreter runs it as words, as `EVALUATE` and `INCLUDED` run Forth
  text. Parameters are named in the text (`param: A`), so a reader sees
  where each enters, and the printed instance shows the value in its
  place. The caller's own stack items stay below the run's floor, out of
  reach of every word (frames, §7; p06 ended balanced).
- *(γ) Forth term-building words* (kept, small): for terms computed
  structurally, such as an n × n matrix, a Forth loop is the right tool;
  `lf-app` and friends build such a term, which then goes in as a
  parameter.

**Results on the stack.** Each run leaves one outcome of ADR 0008 (*ok*
for accepted, *rejected*, *unknown*, *unsupported*, *invalid* for an
authoring error, *exhausted*, *full*); details come from the query words,
so a loop can branch with `ok?` and print only what it needs.

**Isolation between checks (ADR 0009).** A session holds one context:
the session's input, sealed and marked, and its checked environment. Each
inline check builds its terms above the input's marks, checks them
against a snapshot of the environment, reads the verdict and rolls the
stores back to the marks (`lf-input-rollback`), whatever the outcome, so
check n + 1 sees exactly what check n saw. An `example` is never
published. A named `theorem` inline is checked the same way and reported
"not added" until the input can grow after the environment is made — an
amendment of ADR 0012 for the [kernel] gate, a later task. Parameters
built for one check live in its scratch and are rebuilt for the next (or
kept in a session tier above the input, a design detail of 8.2.1e).
Inline runs never run inside a job; parallel inline checks (one context
per task) come later. A THROW inside a run is caught; the caller gets the
outcome. The `STATE` rule of A4 refuses a run while Forth compiles.

### A7. Trust: the session label and the way to a claim

**Label.** An inline verdict reads *accepted (checked in this session;
experimental, not independently audited)*. The surrounding Forth program
shares memory with the checker: it can store into the environment's slots
or the owner token, re-point an implementation DEFER, change a parameter's
term after its check, or print a verdict of its own. Nothing inside the
session can detect that (ADR 0012's threat model, items 15, 17 and 21,
already names such undetected writes). So an inline verdict is a
development-mode result in the sense of OQ-3: never counted as proved in a
report or receipt.

**The way to a claim.** `lf-write` writes each instance as sealed text —
an `example` (or a named theorem), the parameters' terms written out in
words, labels and notes kept — and

```text
leanforth check --env EXPORT instances.lf
```

re-checks the file in a fresh Gforth that loads only LeanForth, giving
today's label *accepted (experimental, not independently audited)* and the
axiom report. Probe p06b: the five instances of p06, written by the
printer's Forth mode, read from a file by the sealed reader in a fresh
process and checked: five *accepted*, statements identical to p06's byte
for byte, on both hosts. This is also plan 8.6.2's round trip ("the
LeanForth form, read back by the authoring words, builds the identical
statement term"): one test serves both.

**Realistic examples.**

| The owner's example | What it needs | Plan tasks |
| --- | --- | --- |
| `A` passed in, propositions without a library | works today (p06: five accepted, a wrong proof rejected, a misspelling at 8:33) | 8.2.1a–f make it a product |
| propositions of `Init` passed in (`True`, `And`) | `Init`'s non-recursive data types, accepted today, and library names (A2) | 8.2.1d |
| numeric constants in a loop (`n + 0 = n`, `2 + 2 = 4` with the number passed in) | natural numbers, literals, structures, unfolding; a literal word (§14); the elaborator, or else `OfNat.ofNat 0 ^ Nat $ 2 $ instOfNatNat 2 $ $` for each 2 | 5.2.1b, 5.2.2, 5.2.3, 4.2.2b–e, 8.3.1 |
| different trig functions passed in by name | Mathlib's reals: quotients, the standard axioms, a Mathlib slice | 5.2.4, 5.3.1, S4 (then S5) |
| matrices of different sizes | `Matrix (Fin n) (Fin n) R` and its instances; literals; term-building words for the entries | 5.2.3, S4/S5, 8.3.1 |

### A8. `+` and §16 when both vocabularies are near

- **In sealed text** nothing changes: no Forth word is visible, so `+` is
  an unknown name (`tests/author/author.fs`: `p p +` stops at the `+`,
  error 1), and Lean's addition is `HAdd.hAdd` with its arguments, shown
  as `n + m` by the printer (4.4.3, 8.6.2).
- **Inline**, one colon definition holds both. The boundary is lexical and
  visible: outside `lf[ … ]lf` every word is Forth's, inside every word is
  LeanForth's; no word runs on the other side, because the sealed run
  replaces the whole search order and restores it afterwards (A4, row 1).
- **Numbers cross only explicitly.** A Forth number (a loop index `i`)
  becomes a Lean number only through `>lf-nat`, which makes a literal of the
  cell's value. Arithmetic stays on its side: `i 1+ >lf-nat` adds in Forth,
  where it wraps at the cell size, and then hands the value over; a sum in
  the theorem is Lean's, on unbounded natural numbers. This is §16's first
  reason, kept by construction.
- **The new words follow §16 and R1.** `lf[`, `]lf`, `lf-run`, `>lf-param`
  and the others are Forth-side words with names no Forth-2012 word has
  (Forth's `[` and `]` are distinct words); `param:` contains a colon, which
  no Lean identifier has (`param` alone is an ordinary Lean identifier:
  pinned Lean accepts `def param := 1`); `example` is a Lean keyword (pinned
  Lean refuses `def example := 1`).
- A short word for Lean's addition is not proposed; question 4 asks.

### A9. Evidence: the probes

Throwaway probes outside `src/` and `tests/`, kept in the work folder
`.claude/work/AU2/` of agent AU2's worktree (not in the repository), each
run under `ulimit -u 500; timeout -k 5 … setsid`, on the pinned Gforth
1.0.0 and on Gforth 0.7.3, with `</dev/null`:

| Probe | What it shows | Result |
| --- | --- | --- |
| p00 | the hosts: recognizer words, stack sizes, dictionary | 1.0 has `rec-forth` and the nine recognizers probed by name (`rec-name`, `rec-number`, `rec-float`, `rec-string`, `rec-to`, `rec-tick`, `rec-dtick`, `rec-env`, `rec-scope`), 0.7.3 none; dictionaries about 7.7 and 8.0 MB free at start |
| p01 | 89 tokens evaluated with only a sealed list in the order: Gforth 1.0 default, 1.0 restricted as the runner does, 0.7.3 | 1.0 default: 41 tokens converted or run, **three wrote a VALUE or DEFER of the sealed list**; 1.0 restricted: only the sealed word (two spellings) and four digit strings, 83 −13; 0.7.3: 24 converted or run, 65 −13; `BASE` and `STATE` unchanged in all |
| p02 | the checker and the authoring words in one image | load silently on both; about 1.6 MB and 120 KB of dictionary (1.62 and 0.12 MB on 1.0, 1.65 and 0.12 MB on 0.7.3) |
| p03 | the real runner: 11 errors with `BASE` 16 before; the runner called while compiling | settings restored in every case on both; while compiling, `theorem` was compiled into the caller (needs the `STATE` rule) |
| p04, p04c | stack overflows; 60,000 decimals in a text; names that are Forth words | THROWs −3 and −5 caught (also `gforth-fast`); the session went on; 18 odd names harmless; outputs equal on both hosts except the line where the stack fills |
| p05, p05b | the dictionary filling | 48 bytes per name; −8 caught; Gforth 1.0 lets `HERE` pass the end (needs the reserve) |
| p06 | inline, end to end: `lf[ … ]lf`, `param:`, five instances checked by the real checker, a wrong proof, a misspelling | five accepted, one rejected, error 1 at 8:33; output identical on both hosts (80 lines) |
| p06b | the instances written as words and re-checked from a file in a fresh process | five accepted; statements identical to p06's; identical on both hosts |
| p07 | which bytes split tokens | TAB, LF, VT, FF, CR and space on both hosts, identical |
| p08 | speed of 1,000 inline checks | 0.73–0.95 ms each on 1.0 and 1.85–3.2 ms on 0.7.3 (the sealed run alone 63–74 and 255–271 µs), three runs, before and after merging plan 6.2.0 (b) |
| Lean | `lean/forms.lean`, `reserved.lean`, `plain.lean` with pinned Lean 4.35.0, `-DwarningAsError=true` | the instances' statements equal Lean's `#print` (Lean wraps the longer one); the kernel forms of `2 + 2 = 4` and `n + 0 = n` as quoted; `example` refused as an identifier, `param` accepted |

**Finding on soundness.** Nothing found makes the sealed approach unsound
on either Gforth: with the rules of A4, text can run only LeanForth's
words on both hosts, and every refusal is identical. Two host facts shape
the rules: Gforth 1.0's `->`-style recognizers can write a VALUE or DEFER
that is in the search order (so the sealed lists hold none, and the
recognizer stays restricted), and Gforth 1.0 lets `HERE` overrun the
dictionary's end by a few bytes when it fills (so LeanForth stops well
before it). Gforth 0.7.3 has no recognizers; there the number check alone
refuses every other number form, as it already does.

### A10. Plan tasks

**8.2.1, new wording** (replacing "Process separation: user Forth
(authoring, tactics) runs in its own Gforth process; the checker process
receives serialized terms only (OQ-1)"):

> **8.2.1 LeanForth checked natively** (ADR 0017 Amendment 1).
> `leanforth check [--env EXPORT] FILE.lf` reads sealed LeanForth text in
> the checker's process — only LeanForth's word lists visible, the rules
> of Amendment 1 A4 — builds each declaration straight into the checker's
> input and checks it with the checker of `leanforth check`. Forth
> programs check inline (`lf[ … ]lf`, `param:`, `example`), labelled
> *checked in this session*, and write instances out as sealed text that
> `leanforth check` re-checks in a fresh process for the standard label.
> *Acceptance:* the A4 probes as tests on both Gforths; a randomized
> hostile-text run leaves the dictionary laid down while loading and the
> checked environment unchanged; every example file of `tests/author`
> checked, with the three forms; inline verdicts equal fresh-process
> verdicts; tests reaching accepted, rejected and unsupported/unknown.
> *Needs:* 3.4.1, 8.1.2. *Gates:* [parser], [bypass]. *Size:* M, as six S
> steps.

| Step | What | Gates | Tests (three forms where a theorem is shown: mathematics, LeanForth, Lean) |
| --- | --- | --- | --- |
| 8.2.1a | Runner rules for the checker's process: the `STATE` rule, control bytes and UTF-8, the dictionary reserve, the private list for the defining `EVALUATE`, the sealed-list content test, a named line for Forth exceptions | [parser] | p01, p03, p04, p05, p07 as tests on both hosts, each refusal with a stable code; planted faults: no `STATE` rule, a VALUE in LF-WORDS (caught on 1.0), no reserve |
| 8.2.1b | Authoring words at the checker's scale: shared nodes found through a hash table (`src/lib/htab.fs`) or not shared, `lfa-shift` on `src/lib/frame.fs` steps, every table growable in the heap (the authoring words' part of plan 6.2.4) | [parser] | today's tests unchanged; a text of 100,000 nodes; a term nested 1,221 deep (Mathlib's deepest); round trips |
| 8.2.1c | The words to the checker: `end NAME` adds an input declaration; `leanforth check FILE.lf` for files without a library; `example`; verdict lines with the statement in three forms (8.6.2) | [bypass], [parser] | `tests/author`'s fixtures accepted with the three forms (Lean compiled with pinned Lean, statements equal to `#print`, terms equal node for node); mutated proofs *rejected*; an axiom *unsupported*; a failed run checks nothing (exit 4) |
| 8.2.1d | Against a library: `--env EXPORT`, the names look-ahead, the environment's constants in §9's resolution, `protected` recorded by the export pipeline, `import-stub` refused in check runs and then removed | [bypass], [import] | a file using `True.intro` and `And.intro` checked against `Init`, verdicts equal to the same theorems' Lean export; names only in the file, only in `Init`, in both (N2, as Lean); a protected `Init` constant through a namespace |
| 8.2.1e | Inline words (A6): `lf-session`, `lf[ … ]lf`, `lf-run`, `param:`, the parameter, term-building and result words; scratch rolled back after each check; examples never published; the session label | [parser], [bypass] | p06 as a test (five accepted, one rejected, the misspelling's position); one row each for accepted, rejected, unknown, unsupported; a parameter missing or left over; the `STATE` refusal; a planted forgery by a user program, shown and documented as outside the label |
| 8.2.1f | Writing instances out and re-checking them: `lf-write`; `leanforth check` on the file | [format] once a receipt carries it | p06b as a test: same verdicts, statements identical; shared with 8.6.2's round trip |

**Where 8.6.2 fits.** The statement in three forms is printed with every
verdict of 8.2.1c and by `lf-verdict.`, from the same printer; its
round-trip acceptance is 8.2.1f's test. 8.6.2 can land first (it only
prints); 8.2.1c then uses it.

**Later, not part of 8.2.1:** named theorems added to the library inline
(the input grows after the environment exists: ADR 0012 amendment,
[kernel]); `import NAME` once exports carry module names; inline checks in
parallel jobs (ADR 0009); saved results for the library (OQ-3, ADR 0012
E8), so a development run does not re-check `Init` each time.

**Other plan text to change after approval** (the coordinator's, outside
this ADR): the Follow-ups entry "8.2.1" and §2's and §18's "separate
authoring program" sentences above, `docs/user/LEANFORTH_SYNTAX.md`'s
status paragraph, ADR 0010 §9's last sentence, and the OQ-1 line of
`docs/project/OWNER_DECISIONS.md` (with the owner's answer).

### A11. Questions for the owner

1. **Trust: may the checker read LeanForth files itself, and Forth
   programs call it?** This changes your OQ-1 answer ("the checker runs as
   its own program and receives proofs only as data"). `leanforth check
   proof.lf` would read the file in the checker's program with only
   LeanForth's sealed words visible to it; a Forth program could call the
   checker directly, with those results labelled *checked in this
   session*, which become full results only when the instances are written
   out and re-checked by `leanforth check` in a fresh program.
   *Recommendation: yes.* It is what you asked for (native, Forth-like,
   inline); the probes show that sealed text can run only LeanForth's
   words on both Gforths, which makes a file data, like the NDJSON files the
   checker already reads; the only thing that can share the checker's
   memory and misbehave is your own program, whose results are labelled and
   re-checkable with one command — the same two modes as your answer on
   saved results (OQ-3).
2. **The shape of inline checks.** Proof text inside a Forth word goes
   between `lf[` and `]lf`, exactly as in a file; values from Forth come in
   by name (`param: A`), in the order pushed; the answer is an outcome on
   the stack, with words to print it; the unit is Lean's `example`
   (checked, not added to the library), with named theorems added inline
   later. The alternative is LeanForth words compiled straight into colon
   definitions. *Recommendation: the captured text.* One vocabulary and
   one reader for files and programs; every instance can be printed as a
   file and re-checked; a LeanForth word never changes meaning between
   compiling and running; and a few Forth term-building words cover terms
   that loops compute (matrices).
3. **How a file finds a library's names.** `Init` has 59,349 declarations,
   Mathlib 729,263. (a) Before Forth reads each line, LeanForth looks at its
   words and makes a Forth word only for names the file uses; Forth's
   interpreter still reads and runs every word, and an unknown name still
   stops at its place. (b) Make a Forth word for every constant of the
   library first. *Recommendation: (a).* It costs a few kilobytes per file
   instead of about 14 MB for `Init` (more than Gforth's default
   dictionary) and about 170 MB and 9 s for Mathlib on every run; the
   look-ahead only splits at spaces and decides nothing.
4. **A short word for Lean's `+`?** Inside proof text Forth's `+` cannot
   run, so there is no mix-up to prevent. A short word for Lean's addition
   (spelt so it cannot be mistaken for Forth's, as §16 requires) would only
   make writing shorter. *Recommendation: not now; ask again when the
   elaborator (8.3.1) exists.* Such a word must also supply the hidden type
   and instance (`Nat`, `instHAdd`), which only the elaborator can fill in;
   readable `n + m` is already the printer's job (8.6.2, 4.4.3); and adding
   it later breaks nothing (§16, reason 3).

### A12. Rejected alternatives

- **The separate authoring process of OQ-1, kept**: a process boundary
  for data that can only run fixed words adds serialization and a second
  reader without adding protection; the protection that matters, against a
  user's own code, is the fresh-process re-check (A7).
- **Compile-time LeanForth words in colon definitions** (A6, α).
- **A word for every library constant up front** (A2; question 3).
- **Gforth 1.0's recognizers for unknown names** (a recognizer that looks
  names up in the environment): Gforth-only; 0.7.3 has none (p00).
- **Gforth's own wordlist methods** (a custom `find` on the environment's
  name index): host internals, not Forth-2012.
- **Parameters taken from the caller's data stack** inside the text: the
  run's frames (§7) exist so that no word reaches below its floor; a named
  parameter is visible in the text and in the printed instance.
- **Treating inline verdicts like file verdicts**: the surrounding program
  could forge them (A7).
