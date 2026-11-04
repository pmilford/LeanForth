# LeanForth words: programming reference

Status: implemented 2026-11-03 in `src/author/` and `src/present/`
(plan task 8.1.2, [ADR 0017](../adr/0017-leanforth-syntax.md)); untrusted;
the [parser] review gate of `AGENTS.md` is still open. The user's view,
with examples in three forms, is [LeanForth syntax](../user/LEANFORTH_SYNTAX.md).
This page lists the modules, every word a proof file may use, the Forth
interface for running and printing, every error code, and the limits.

## Trust and layering

The authoring words build terms in LeanForth's stores; they decide
nothing. Only the checker can accept a theorem, and nothing here is part
of a verdict. The checker never loads `src/author/`: `make test` checks
that no module `src/main.fs`, `src/core/` or `src/kernel/` loads reaches
it (`tests/author/check_author.py`). Running proof text executes the
author's words in the same Forth image as the stores; the separate
authoring process that will hand the checker serialized terms only is
plan task 8.2.1 and is not built.

## Modules

| File | Holds | State (context members, ADR 0009) |
| --- | --- | --- |
| `src/author/source.fs` | the line being run and the current token; positions; token text: dots in names, plain decimals | `lfa-source` |
| `src/author/errors.fs` | error codes, the catalogue, the error record, `lfa-fail` | `lfa-error` |
| `src/author/build.fs` | nodes in the term, level and reference stores, shared by content; `->`'s shift | `lfa-sought`, `lfa-sought-ref` (lookup keys) |
| `src/author/scopes.fs` | open binders and stack frames | `lfa-binders`, `lfa-scope` |
| `src/author/constants.fs` | the declarations of a run | `lfa-decls` |
| `src/author/values.fs` | LeanForth values on the data stack, each used once | `lfa-items` |
| `src/author/groups.fs` | the wordlists, syntax words, name groups and their entries; the numbers check | `lfa-entries`, `lfa-groups` |
| `src/author/namespaces.fs` | namespaces, `open`, and which constant a name means (Lean's resolution) | `lfa-spaces`, `lfa-knowns` |
| `src/author/declarations.fs` | declarations, universes, binders | `lfa-current` |
| `src/author/words.fs` | the vocabulary (LF-WORDS) | none |
| `src/author/runner.fs` | running text and files; the public interface | `lfa-run` |
| `src/present/note-table.fs` | labels and notes per term | `lf-notes` |
| `src/present/print-forth.fs` | the term printer's Forth mode | `lf-pforth` (and the printer's) |

The wordlists, syntax words and name-group words are in the dictionary
and shared; their entries (which spelling means which variable, universe
or constant) are in the context, so another context sees the same words
but none of the names. Group words are made while a proof runs, for a
name spelt in no earlier run, by `EVALUATE` of a defining word; that is
the authoring program's only dictionary growth.

## The vocabulary

While a proof runs, the search order is LF-WORDS (`lf-words`), LF-LOCALS
(`lf-locals`) and LF-CONST (`lf-consts`); BASE is decimal. The only
numbers are plain decimals: one to nine digits. Values: *t* a term, *l* a
universe level or a number, *c* a constant waiting for universe arguments,
*n* a number. Each value is used once, by the word that takes it.

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `theorem` NAME, `def` NAME, `axiom` NAME | `( -- )` | start a declaration (empty stack) |
| `import-stub` NAME | `( -- )` | a constant an import would provide; an optional statement |
| `universe` NAME | `( -- )` | a universe parameter, right after the name |
| `:=` | `( t -- )` | the statement; open binders become the parameters |
| `end` NAME | `( t -- )` or `( -- )` | close the declaration (proof, or an axiom's statement) or a namespace |
| `namespace` NAME, `open` NAME | `( -- )` | outside declarations |
| `explicit:` `implicit:` `strict-implicit:` `instance:` NAME | `( t -- )` | open a binder of that kind |
| `fun`, `forall` | `( t -- t )` | close the innermost binder (λ, Π) |
| `->` | `( t t -- t )` | Π with an anonymous, unused binder |
| `$` | `( t t -- t )` | application |
| `^` | `( c l -- c )` | one more universe argument |
| `Prop`; `Type`, `Sort` | `( -- t )`; `( l -- t )` | Sort 0; Sort (l + 1), Sort l |
| `level+`; `level-max`, `level-imax` | `( l n -- l )`; `( l l -- l )` | l + n; max, imax |
| `var#` | `( n -- t )` | bound variable n (de Bruijn index) |
| `root:` NAME | `( -- c )` | the constant NAME in LF-CONST, whatever else has the name |
| `label:` NAME | `( t -- t )` | a step label, unique in the declaration |
| `note"` text`"`, `ai-note"` text`"` | `( t -- t )` | a note by a person, by an AI |
| `\`, `(` | `( -- )` | comments, as in Forth, on one line |
| `_`, `let:`, `let`, `have`, `field-at`, `by`, `s"`, `import` | — | not supported yet |

A name's word pushes a variable and/or a universe parameter (LF-LOCALS)
or a constant. Names are case-sensitive: one Forth word stands for every
spelling equal apart from case and acts on the exact spelling it was
called with, or passes the token on to the wordlists searched after its
own. A constant has an entry under its full name in LF-CONST, and each
shorter name it can be written by (what follows a dot of its name) has a
word there too. Which constant a name means is pinned Lean 4.35's rule
(`resolveGlobalName`): the first of `P.name` for the current namespace
`P` and each namespace around it, innermost first; otherwise the name at
the root and `O.name` for each open namespace `O`, which must all be the
same constant, or it is ambiguous (error 27; Lean would try each against
the expected type). Inside a declaration the current namespace is its own
name's prefix (`def N.foo` resolves in `N`). `namespace A.B` enters two
scopes; `end NAME` leaves one per part, each part naming its scope;
`open N` opens `P.N` for the nearest namespace `P` around that has it, or
`N`, and `O.N` for each open `O`. A namespace is known once entered or
once it is a prefix of a declared name.

No name of a declaration, universe or namespace, and no part of one, may
be number-like (a digit first, or one of `- + # $ % & '` and more after
it; error 30), so no word ever stands where a number is meant; a binder
may have such a name but gets no word (`n var#` refers to it). Numeric
name parts (`x.1`) have no leading zero. Each syntax word is a Lean
keyword or contains a character no unquoted Lean identifier has (ADR
0017, rule R1), and must be in the printer's list of the words it writes
(checked when `words.fs` loads).

## Forth interface

`require src/author/runner.fs` loads everything. Outcomes are those of
[ADR 0008](../adr/0008-outcome-vocabulary.md).

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `lf-author-begin` | `( -- )` | a new run: empty stores, tables and namespaces |
| `lf-author-text` | `( c-addr u -- outcome )` | run lines of text (LF or CR LF) |
| `lf-author-file` | `( c-addr u -- outcome )` | run the named file |
| `lf-author-count` | `( -- n )` | declarations made |
| `lf-author-decl` | `( i -- decl )` | declaration i, a `/lf-fdecl` record |
| `lf-author-notes` | `( i -- first end )` | indices of its labels and notes in the note table |
| `lf-author-print` | `( fuel -- outcome )` | every declaration as words, through the printer's sink |
| `lf-author-code` | `( -- code )` | the first error's code, 0 if none |
| `lf-author-error.` | `( -- )` | print it: code, line:col, token, message, a second place |
| `lf-author-message`, `lf-author-outcome` | `( code -- c-addr u )`, `( code -- outcome )` | a code's message and outcome |
| `lf-print-forth-term` | `( term fuel -- outcome )` | a closed term as words |
| `lf-print-forth-decl` | `( decl fuel -- outcome )` | a `/lf-fdecl` record as words |
| `lf-note-add` | `( c-addr u kind term -- i outcome )` | a label or note on a term (`note-table.fs`) |

A run's outcome is ok, or that of its first error: invalid (a mistake),
unsupported (a form not built yet) or full (out of room). An error stops
the run; begin a new one. The runner restores the caller's search order,
compilation wordlist and BASE, also after an error. Its `THROW` code for
an authoring error is −4129 (`lf-author-throw`), in the range ADR 0018
reserves for LeanForth; only the runner catches it, as the authoring
program's top level.

Numbers are refused the same way on every host. Forth's interpreter
converts a token that no word has as a number, in whatever forms its host
reads (Gforth 0.7.3: `-3`, `$10`, `%11`, `#1`, `'a'`, `1.`, floats;
Gforth 1.0 also `0x3`, `"x"`, `->x`, `${NAME}` and more, some of which act
at once). So: on Gforth 1.0 the runner limits the recognizer (`rec-forth`)
to words and digit strings while a proof runs, and restores it after; on
every host each LeanForth word, before it acts, checks the tokens of its
line between the last token a word read and its own, which are the
numbers, and the runner checks the rest of each line. The first token
that is no plain decimal stops the run at itself: error 35 if it is
number-like, otherwise error 1. Gforth's −13 (a token no word has and no
number) is reported the same way, at the first such token after the last
one a word read.

The printer's Forth mode returns ok; invalid for a malformed term or a
variable bound by an arrow; unsupported for a name it cannot spell (a
part with a dot, a space or only digits, or a universe parameter named
like a syntax word) and for a label or note that would not read back as
itself (a label that is empty or has a blank or control character, a
note with `"` or a line end), which it never prints as live words;
exhausted and full as the term printer. On a failure the text printed so
far is incomplete. Running the printed words gives the identical term,
names, binder kinds, labels and notes; a Pi printed as `->` comes back
with the anonymous name.

## Errors

Codes are stable; tests pin them, never the wording.
`tests/author/check_author.py` checks that this table and
`src/author/errors.fs` agree. Unless the message names another, the
position is the word that found the mistake (for codes 1 and 35, the
refused token itself; for 39, the long line's first token); codes 11, 12,
18 and 21 also give a second place (where the constant was written, where
the binder was opened; for 18, the parameter's binder with a value left
below it).

| Code | Outcome | Message |
| --- | --- | --- |
| 1 | invalid | unknown name: no syntax word, bound variable, universe parameter or constant has it |
| 2 | invalid | a name must follow on the same line |
| 3 | invalid | missing value: this word would use the stack below its binder or declaration |
| 4 | invalid | terms belong inside a declaration |
| 5 | invalid | a term is needed here, not a universe level |
| 6 | invalid | a universe level is needed here, not a term |
| 7 | invalid | a universe parameter is not a term (write root: NAME for a constant) |
| 8 | invalid | a universe parameter is needed here, not a variable |
| 9 | invalid | universe arguments attach only to a constant |
| 10 | invalid | too many universe arguments (at most 8) |
| 11 | invalid | wrong number of universe arguments for the constant (write each with ^) |
| 12 | invalid | the body of the binder must be exactly one term |
| 13 | invalid | no binder of this term is open here |
| 14 | invalid | declarations do not nest |
| 15 | invalid | a declaration starts with an empty stack |
| 16 | invalid | universe comes right after the declaration's name |
| 17 | invalid | := is not expected here |
| 18 | invalid | the statement before := must be exactly one term |
| 19 | invalid | := is missing |
| 20 | invalid | the proof after := must be exactly one term |
| 21 | invalid | a binder of the proof is still open |
| 22 | invalid | end names another declaration or namespace |
| 23 | invalid | end names no open namespace |
| 24 | invalid | namespace and open belong outside declarations |
| 25 | full | too many namespaces open |
| 26 | invalid | unknown namespace |
| 27 | invalid | ambiguous name: write the full name |
| 28 | invalid | already declared |
| 29 | invalid | label used twice in this declaration |
| 30 | invalid | not a name: an empty part, a part like a number, or a leading zero |
| 31 | invalid | var# index outside the binders |
| 32 | invalid | a count (a number) is needed here |
| 33 | invalid | the text ends inside a declaration or with values left |
| 34 | invalid | not a live LeanForth value: each value is used once |
| 35 | invalid | not a LeanForth word or number: numbers are plain decimals of at most 9 digits |
| 36 | invalid | a LeanForth word must be run by the text interpreter |
| 37 | invalid | a note must end with " on the same line |
| 38 | invalid | unknown constant |
| 39 | full | line too long |
| 40 | invalid | the file cannot be opened or read |
| 41 | invalid | a Forth exception, with its THROW code |
| 42 | invalid | a ( comment must end with ) on the same line |
| 50 | unsupported | not supported yet: natural-number literals need literal nodes (ADR 0017 section 14) |
| 51 | unsupported | not supported yet: designed in ADR 0017 but not built yet |
| 52 | unsupported | not supported yet: holes are filled by the elaborator (plan task 8.3.1) |
| 53 | unsupported | not supported yet: _root_ in a declaration's name |
| 60 | full | out of room: the term store is full |
| 61 | full | out of room: the level store is full or the level too large |
| 62 | full | out of room: the name store is full or the name too long |
| 63 | full | out of room: the constant-reference store is full |
| 64 | full | out of room: too many values in one declaration |
| 65 | full | out of room: too many binders open |
| 66 | full | out of room: too many names, namespaces or declarations |
| 67 | full | out of room: too many labels and notes |

The tests reach every code: `tests/author/author.fs` all but 39, which
the example file `17-long-line.lf` reaches (a line of 1024 characters or
more in a file). Proof text cannot reach 34, since it cannot write a
negative number and each value is used once; the unit tests reach it by
calling the words with a used value and with a variable outside its
binder. Code 41 is reachable: very many numbers overflow Forth's data
stack (−3, on Gforth 1.0 and 0.7.3 alike). Before the review of
2026-11-03 this page said no Forth exception other than −13 was
reachable; on Gforth 1.0, `->x` then threw −21.

## Limits

Measured on Gforth 1.0 and 0.7.3, which give byte-identical results.
Per run: the term store's 64 nodes (equal subterms share a node, except a
step with a label or note), 64 levels, 64 names in 2,048 bytes, 32
constant references, 32 declarations, 256 name entries in 4,096 bytes,
64 open binders, 512 values per declaration, 64 labels and notes in
4,096 bytes, 16 namespace scopes and open namespaces at once, 32 known
namespaces in 1,024 bytes, 8 universe parameters per declaration and 8
universe arguments per constant, numbers of at most 9 digits, lines of
at most 1,023 characters in a file. A source position is the line times
65,536 plus the column; on a 32-bit host lines beyond 32,767 wrap.

## Tests

`make test` (target `test-author`): `tests/author/author.fs` (every
reachable error code with its line and column, case sensitivity, Forth's
words invisible, numbers in every host form, values used once, names
that are numbers, namespaces and which constant a name means, `var#`,
`root:`, positions, labels and notes, the runner's restoring, the note
table, the Forth mode on its own and the labels and notes it refuses) and
`tests/author/check_author.py` (21 example files against
`fixtures.golden`, which records each declaration's terms as a tree dump,
with a round trip each; this table; the layering check; round trips over
the term printer's 50 cases and the five Lean exports); the syntax page's
examples. Run the unit tests with Gforth 0.7.3 too when the runner
changes: the numbers check is host-sensitive.

`make check` (target `reference-author`) compares with Lean, for the 15
example files with a Lean source (`tests/reference/author-*.lean`):

- **Terms, term for term** (`tests/author/lean_terms.py`). Pinned Lean
  compiles the source; a Lean metaprogram writes each declaration as Lean
  holds it, in the tree-dump format, and every theorem, definition and
  axiom must equal the words' terms exactly: every node, de Bruijn index,
  constant, universe argument, level, binder name and binder kind; each
  import stub must have Lean's universe parameters and, when it states a
  type, Lean's type. The pinned exporter (`leanexport`, lean4export 3.1.0)
  exports the same declarations, which must also agree, apart from binder
  names and kinds: that exporter shares nodes that differ only in binder
  names or kinds, so a later declaration can come out with an earlier
  one's (checked with three alpha-equivalent theorems). One binder name is
  a listed difference, with its reason (`12-hygienic-used.lf` names a
  binder with a hygienic name Lean's source cannot write). The example file
  `16-namespaces.lf` puts Lean's name resolution under this comparison.
- **Text**: pinned Lean's `#print` of every declaration against the
  example's `lean:` lines, one known printer difference listed with its
  reason.
- **Planted faults**: 22, each caught. Seven are faults in the printer and
  the words; fifteen each undo one fix of the review of 2026-11-03. The
  spelling check disabled, "every universe argument is 0" and the two name
  resolution faults must be caught by the comparison with Lean (the round
  trip and the printed text cannot see them).
