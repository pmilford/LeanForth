# ADR 0017: LeanForth Forth syntax for theorems, definitions and proofs

Status: **accepted as the design basis** by the owner on 2026-11-02 (decisions 1–4 as recommended, see [owner decisions](../project/OWNER_DECISIONS.md)); proposed 2026-11-02 (plan task 8.1.1). **Implemented** 2026-11-03 in `src/author/` and the term printer's Forth mode (plan task 8.1.2; [programming reference](../programming/LEANFORTH_WORDS.md), [user page](../user/LEANFORTH_SYNTAX.md)); the implementation still passes the [parser] gate before anything relies on it. Two points of the implementation refine this record: while the stores hold 64 nodes, equal subterms share one node, which keeps the position where it was first written (a step with a label or note always has its own node); and the stand-in for imports is the word `import-stub` (the prototype's `stub` and `declare`). Before that, a throwaway prototype (outside the
repository, see [Evidence](#evidence)) ran every example below as Forth
words through Forth's own interpreter, built the terms in LeanForth's
existing stores, printed them with the term printer, and ran its own
printed words again.

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
3. the namespaces entered with `namespace` and opened with `open`, newest
   first;
4. **LF-CONST**, every declared or imported constant under its full name.

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
reference to an item kept by the authoring program, always negative. Forth
number literals are nonnegative, and Lean has no negative literals or
levels, so a word that accepts a level or a term tells a number from a
value by its sign. So `0` is the level 0 before `^`, and the natural-number
literal 0 before `$`.

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

`namespace N … end N` puts the declarations inside under `N.` and puts
`N`'s wordlist in the search order; `open N` adds `N`'s wordlist until the
enclosing namespace ends. Forth stops at the first match in the search
order; LeanForth adds one check, because an added `open` must not silently
change the meaning of text further down: a constant's word found under its
short name looks for the same spelling in the other visible namespaces and
at the root, and stops with "ambiguous name: write the full name" if there
is one. Forth-2012 promises at least eight wordlists in the search order,
which leaves room for five namespaces at once on the smallest system.

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
the authoring program finds it as the first non-number after the last word
that ran. The checker receives terms only and reports node numbers; the
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
printable ASCII words and UTF-8 in names (Lean names are Unicode).

**Scale.** Every constant an author can name is a Forth word. In Gforth 1.0
a name group with its entry took 119 bytes of dictionary, 6 µs to define
and 0.4 µs to look up (100,000 words of Mathlib-like names, measured). All
729,263 Mathlib constants, under full and short names, would take about
170 MB and 9 s in the authoring program; 8.2.1 can define only the words of
the modules a file imports. The checker is not affected.

**Trusted base.** None of this is trusted. A wrong word produces a
different term, which the checker checks as it is and the printer shows;
the defences are the round-trip test, comparison of printed statements
with Lean's, and the printed statement in every receipt.

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
