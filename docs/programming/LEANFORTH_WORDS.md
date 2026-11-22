# LeanForth words: programming reference

See also the [language reference](../user/LANGUAGE_REFERENCE.md) (owner's important page: every word by part, implemented or designed).

Status: implemented 2026-11-03 in `src/author/` and `src/present/`
(plan task 8.1.2, [ADR 0017](../adr/0017-leanforth-syntax.md)); untrusted;
the [parser] review gate of `AGENTS.md` is still open. The user's view,
with examples in three forms, is [LeanForth syntax](../user/LEANFORTH_SYNTAX.md).
This page lists the modules, every word a proof file may use, the Forth
interface for running and printing, every error code, and the limits.

## Trust and layering

The authoring words build terms in LeanForth's stores; they decide
nothing. Only the checker can accept a theorem, and nothing here is part
of a verdict. The kernel never loads `src/author/`: `make test` checks
that no module of `src/core/`, `src/kernel/` or `src/import/` reaches it
(`tests/author/check_author.py`). Since plan task 8.2.1c the command line
does (`src/cli/check-lf.fs`, so `src/main.fs` too): `leanforth check
FILE.lf` runs the text in the checker's Gforth, sealed (ADR 0017
Amendment 1, A5), and hands the declarations it made to the kernel as
export records through the importer stage ([checking text](#checking-text-the-export-and-the-library),
[ADR 0017 Amendment 2](../adr/0017-leanforth-syntax.md#amendment-2-leanforth-text-checked-by-the-kernel-2026-11-12)).

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
| `src/author/library.fs` | a library's constants, found through a finder (8.2.1d); checked runs refuse stubs | `lfa-library` |
| `src/author/form.fs` | the run's form, natural (the default) or kernel (`kernel-form`); the numerals' positions; the pending `'` | `lfa-form`, `lfa-numerals` |
| `src/author/words.fs` | the vocabulary (LF-WORDS) | none |
| `src/front/syntax.fs` | the syntax store: Lean-shaped trees of natural text, with positions (FE1a) | `syn-store` |
| `src/front/reader.fs` | the natural meanings of the words (FE1a) | `lfn-decl` |
| `src/front/tactic-syntax.fs` | tactic proofs read: the tactic words' natural meanings, block shapes, hypotheses' names, the record of steps (FE1g-2) | `tac-read`, `tac-steps`, `tac-args` |
| `src/front/dag-walk.fs`, `src/front/mvars.fs`, `src/core/mvar-leaves.fs` | the metavariable context and its walks (FE1b); metavariable leaves | `mctx`, `mv-exprs`, `mv-levels`, `mv-fvars` |
| `src/author/export.fs` | a run's declarations as export records, to a sink (8.2.1c) | `lfx` |
| `src/author/runner.fs` | running text and files; the look-ahead for a library; the public interface | `lfa-run` |
| `src/cli/check-lf.fs` | `leanforth check FILE.lf`: the library, the text and its records into the stage | `lfc` (and check-run.fs's) |
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
| `protected` KIND NAME | `( -- )` | a protected declaration (KIND is `theorem`, `def`, `axiom` or `import-stub`), as Lean's `protected`; it must be in a namespace |
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
| `lit#` | `( n -- t )` | the natural-number literal n (Lean's `Expr.lit (.natVal n)`; a number of one cell, at most 2^63 - 1). `OfNat.ofNat 0 ^ Nat $ 0 lit# $ instOfNatNat 0 lit# $ $ $` is Lean's `(0 : Nat)` |
| `proj#` NAME | `( i -- t )` | the projection leaf of field i (from 0) of the structure NAME, a full name of a declared constant; `$` applies it to e, which makes Lean's `Expr.proj S i e`: `0 proj# Prod p $` is `p.1`. The leaf is a term only as the function of `$`; anywhere else (an argument, a statement, a proof, a binder's type, a label) the run stops with error 56 |
| `label:` NAME | `( t -- t )` | a step label, unique in the declaration |
| `note"` text`"`, `ai-note"` text`"` | `( t -- t )` | a note by a person, by an AI |
| `\`, `(` | `( -- )` | comments, as in Forth, on one line |
| `_`, `let:`, `let`, `have`, `field-at`, `by`, `s"`, `import`, `export` | — | not supported yet |

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
the expected type). Through a namespace (`P.name` or `O.name`), a name of
one part never finds a protected constant: inside `namespace Nat`,
`add_comm` is not `Nat.add_comm` (which Lean's core library protects),
while `Nat.add_comm` is. Lean also searches aliases made by `export` and
private names; the words make neither (`export` stops with error 54), so
here there are none. An import stub must say `protected` where Lean's
constant is (`make check` compares this with Lean for every example).
Inside a declaration the current namespace is its own
name's prefix (`def N.foo` resolves in `N`). `namespace A.B` enters two
scopes; `end NAME` leaves one per part, each part naming its scope;
`open N` opens `P.N` for the nearest namespace `P` around that has it, or
`N`, and `O.N` for each open `O`. A namespace is known once entered or
once it is a prefix of a declared name.

No name of a declaration, universe or namespace may be number-like as a
whole token (a digit first, or one of `- + # $ % & '` and more after it;
error 30), so no word ever stands where a number is meant; a binder may
have such a name but gets no word (`n var#` refers to it). A part after the
first may be a number: `Nat.zero_add.match_1.0.x` has the numeric part
(Lean's `Name.num`) 0, read and written as the digits; no word is made for a
part, only for the whole name and its shorter forms, and a shorter form that
is number-like (`0.x` of `N.0.x`) gets none. A numeric part has no leading
zero (`x.01` is refused, `x.1` and `x.10` are numeric parts). A string part
of digits stays a string by guillemets: `N.«0».f` is `N` `"0"` `f`, distinct
from `N.0.f` (the printer writes it so; the guillemets hold digits only).
A name whose first part is numeric cannot be written (the token would be a
number). Each syntax word is a Lean
keyword or contains a character no unquoted Lean identifier has (ADR
0017, rule R1), and must be in the printer's list of the words it writes
(checked when `words.fs` loads).

### Natural LeanForth and the kernel form (plan FE1a)

Since 2026-11-12 every word has a meaning in each of two forms
([ADR 0021](../adr/0021-front-end.md) D8; owner decisions 1-4 of
2026-11-12). A run starts in **natural** form; `kernel-form`, outside any
declaration, switches it to the **kernel form** of the table above for the
rest of the run (error 57 inside a declaration). In natural form the words
build a syntax tree (`src/front/syntax.fs`), not kernel terms, and nothing
is elaborated yet:

| Word | Stack effect | Meaning in natural form |
| --- | --- | --- |
| a name | `( a1 .. ak -- t )` | the application of the constant or variable to as many values as its type has explicit binders (a library constant's from its type's telescope, a variable's from its binder's type as written); 73 when that count depends on unfolding a definition |
| a number | `( -- n )` | a numeral (Lean's `OfNat`), at its own line and column |
| `' NAME` | `( -- t )` | the function NAME, applied to nothing (59 when no name follows on the line) |
| `$` | `( f a -- t )` | one more argument: an application made by a name takes it as its next one |
| `+`, `-`, `*`, `/`, `%` | `( a b -- t )` | Lean's `binop% HAdd.hAdd a b`, and the same of `HSub.hSub`, `HMul.hMul`, `HDiv.hDiv`, `HMod.hMod` |
| `^` | `( a n -- t )` | Lean's `rightact% HPow.hPow a n` (slice S3a-ops C4): the exponent is elaborated apart, analyze and applyCoe never see it (`src/front/elab-term.fs`) |
| `=`, `≠`, `<`, `>`, `≤`, `≥`, and typed `<=`, `>=` | `( a b -- t )` | Lean's `binrel% Eq a b`, and the same of `Ne`, `LT.lt`, `GT.gt`, `LE.le`, `GE.ge` |
| `¬`, `∧`, `∨`, `↔`, `∣`, and typed `/\`, `\/`, `<->` | `( p -- t )`, `( a b -- t )` | Lean's notations for the root constants `Not`, `And`, `Or`, `Iff`, `Dvd.dvd`, applied as their names are (38 when the library lacks one) |
| registering a notation word | | `src/front/reader.fs`: `s" HSub.hSub" syn-k-binop lfn-operator: -`, `s" And" lfn-notation-name: ∧`, one line each, the notation table's Unicode or ASCII row checked while loading; the word itself is made and reserved by `src/author/words.fs`'s `lfa-natural-words` |
| `explicit:` and the other binder words | `( t -- )` | a binder whose type is the tree as written |
| `:=` | `( t -- )` | the statement, as in the kernel form |
| `by` | `( -- )` | right after `:=`: a tactic proof follows (69 elsewhere or twice), read by `src/front/tactic-syntax.fs` |
| `end NAME` | `( t -- )` | checks the declaration's shape (errors 19, 20, 22) and keeps the proof's tree, then elaborates it, which stops today: elaborating is plan FE1e (71, unsupported). Once FE1e gives the type and value, the hand-over (`src/front/handover.fs`, plan FE1f) instantiates every assigned metavariable, stops at a hole still reachable (74, invalid) or at a universe parameter of the declaration that is unused (75, invalid, as Lean's "unused universe parameter": a theorem's or axiom's counted in its statement alone, a definition's in its statement and value), refuses malformed terms (76, invalid: a term that is no node, a theorem or definition without a value, an axiom with one) and an instantiation step not ported yet (77, unsupported), and records the declaration; its records reach the kernel as a kernel-form text's do. After `:= by`: every block closed (82) and no value left (86), then the statement is elaborated (until plan FE1e, 71) and the tactics run (`src/front/tactic-run.fs`): each tactic not ported yet stops the run (80, unsupported, with its plan step), `by-sorry` closes the main goal, a goal left at the end is 89 at `by` (Lean's "unsolved goals"), and the value goes to the hand-over |
| `t by-exact`, `t by-induction`, `t by-induction-with` | `( t -- )` | a tactic step with its term; `by-induction-with` opens a block of alternatives up to `by-end` |
| `by-rfl`, `by-intro: NAME` | `( -- )` | a tactic step; `by-intro:`'s name (or `_`) is a hypothesis until its block ends |
| `by-sorry` | `( -- )` | Lean's `sorry` tactic: closes the main goal with `sorryAx` (an open part; the declaration is NOT PROVED); 90 when no goal is left |
| `t by-apply`, `by-assumption`, `by-constructor` | `( t -- )`, `( -- )`, `( -- )` | ports of Lean's `apply`, `assumption` and `constructor` (tactic plug-in design, slice a2-iii; `src/front/tactics/`, on the goal layer `src/front/meta-tactic/`): 380 no argument count makes t's conclusion fit, 125 an instance not found, 384 an instance found but not fitting, 381 no hypothesis has the goal's type, 382 the goal is no inductive type, 383 no constructor applies, 99 a case not ported |
| `by-decide`, `by-native-decide` | `( -- )`, `( -- )` | ports of Lean's `decide` and `native_decide` (plan row S3, slice S3a; `src/front/tactics/decide.fs`): 250 the statement is false, 251 the goal has a free variable, 252 a metavariable, 253 the evaluation is stuck, 122 no `Decidable` instance (synthInstance), 93 an exponent above 256 or a let variable (not supported yet); `by-native-decide` is always 254 (not supported: `Lean.ofReduceBool`) |
| `by-left`, `by-right`, `by-exfalso`, `by-intros`, `t by-clear` | `( -- )`, `( -- )`, `( -- )`, `( -- )`, `( t -- )` | ports of Lean's `left`, `right`, `exfalso`, `intros` and `clear t` (tactic batch 1, plan row TB1; `src/front/tactics/`, on the goal layer `src/front/meta-tactic/`): 385 and 387 the goal is no inductive type, 386 and 388 it has not two constructors, 380 the constructor does not fit; `by-exfalso` none of its own; `by-intros` introduction's 99 (a `let`, an instance binder) and 93; 389 t is no single hypothesis, 441 another hypothesis depends on it, 442 the goal does, 440 a variable of no context of the goal's (no text reaches it) |
| `T by-change`, `T by-show`, `by-swap`, `t by-specialize`, `h by-revert`, `f by-delta`, `by-contradiction`, `by-trivial`, `h by-absurd` | `( T -- )`, `( T -- )`, `( -- )`, `( t -- )`, `( h -- )`, `( f -- )`, `( -- )`, `( -- )`, `( h -- )` | ports of Lean's `change T`, `show T`, Batteries' `swap`, `specialize t`, `revert h`, `delta f`, `contradiction`, `trivial` and Batteries' `absurd h` (tactic batch 1, plan row TB2; `src/front/tactics/`, on the goal layer `src/front/meta-tactic/`): 443 change's pattern not definitionally equal to the goal, 444 show's (one goal), 445 show's (no goal fits), 96 a pattern that is no proposition, 446 swap with fewer than two goals, 447 specialize's term no hypothesis applied, 389 revert's term no hypothesis, 448 delta found nothing to unfold, 449 contradiction found no contradiction, 381 every rule of trivial failed (assumption's), 99 a case not ported (contradiction's cases, noConfusion, `Nat.hasNotBit`; delta of no constant; trivial nested past 32), 93 a type with an open metavariable, a `let` reverted, delta of a theorem or of f applied to f with too few arguments (Lean unfolds it again where it lands) |
| `T e by-have: NAME`, `e by-have`, `T e by-let: NAME`, `T e by-suffices: NAME`, `T by-have-goal: NAME`, `T e by-replace: NAME` | `( T e -- )`, `( e -- )`, `( T e -- )`, `( T e -- )`, `( T -- )`, `( T e -- )` | ports of Lean's `have NAME : T := e`, `have := e` (NAME `this`), `let NAME : T := e`, `suffices NAME : T from e`, Mathlib's `have NAME : T` and Lean's `replace NAME : T := e` (tactic batch 2a, plan row TB2; `src/front/tactics/have.fs`, `replace.fs`, on `src/front/meta-tactic/assert.fs`); NAME read after the word on its line (2 when missing, 84 a word): no codes of their own: 96 e not of type T (or not of the goal's, suffices), 130 T no type, 99 NAME `_` or a value naming a hypothesis the goal no longer has, 93 a type or value leaving a metavariable open |
| `by-intro: NAME`, `t by-exact`, `by-rfl`, run | | as Lean's `intro`, `exact` and `rfl` (plan FE1g-4, `src/front/tactics/intro.fs`, `exact.fs`, `rfl.fs`): 94 no binder to introduce, 95 a metavariable left unassigned, 96 a type mismatch, 97 two sides not definitionally equal, 98 a term the goal cannot take, 99 a case not supported yet (`intro rfl`, a `let`, a binder of no known kind, an instance binder; implicit and strict-implicit binders are introduced, plan row TB1), 93 a step of the Meta layer not ported yet |
| `\| TAG NAMES… =>`, `by-case: TAG NAMES… =>` | `( -- )` | an alternative of the `by-induction-with` it is right inside (up to the next `\|` or `by-end`), a case block (up to its `by-end`); the header on one line, its names hypotheses of the block |
| `by-end` | `( -- )` | closes the innermost `by-induction-with` or `by-case:` |
| `by-rw[`, `by-rewrite[` … `]` | `( -- )`, `( r1 .. rn -- )` | the values built between the brackets are the rules, in order; a hypothesis there takes no values (applied with `$`: `ih k $`) |
| `t by-induction`, `t by-induction-with`, `\|`, run | | as Lean's `induction t` and `induction t with \| …` (plan S2, `src/front/tactics/induction.fs` on the tactic library's `meta-tactic/elim.fs` and `tactic-alts.fs`, since plan 9.4.8l I): `t` a variable of an inductive type, the eliminator the data's (`Nat.recAux`) or `T.rec`; each alternative takes its case's goal, names its explicit fields and runs as a block; 205 no inductive type, 206 a name of no case, 207 a case not written, 208 too many names, 209 a mutual or nested type, 212 the motive's type, 213 a name written twice, 99 a form not ported (a target that is no variable, hypotheses that depend on it, index targets, instance binders); `by-case:` stays 80 (plan S2 merge B) |
| `by-rewrite[ r … ]`, `by-rw[ r … ]`, run | | as Lean's `rewrite [r, …]` and `rw [r, …]` (plan S2, `src/front/tactics/rewrite.fs` on the tactic library's `meta-tactic/rewrite.fs`, `lf-goal-rewrite`, since plan 9.4.8l I; on `kabstract.fs` and `meta-check.fs`): each rule a hypothesis or a theorem, its equation's left side abstracted wherever it occurs (`kabstract` at reducible transparency), the motive type-checked, `Eq.mpr` and `congrArg` as Lean builds them; `by-rw[` then tries `rfl` at reducible transparency; 215 no occurrence, 216 a motive not type correct, 217 a dependent motive, 218 no equation, 219 a metavariable pattern, 220 the occurs check, 99 a form not ported (a definition as a rule, `Iff`, an instance binder, a rule's argument left to a new goal) |
| `=>` | | ends a header; alone, error 84 |
| the tactic words in kernel-form text | | not supported (72) |
| the other kernel-form words (`Prop`, `fun`, `var#`, `^`, ...) | | not supported yet in natural form (70) |
| `'` and the notation words (`+`, `∧`, `<=`, ...; not `^`) in kernel-form text | | refused (58) |

Each operator word is checked against the printer's notation table while
the reader loads (`present/notation-table.fs`: the row of the constant
must spell the word). The Forth interface adds `lf-author-kernel ( -- )`
(the marker, for a caller that runs kernel-form text without it),
`lf-front-statement ( -- node )`, `lf-front-by ( -- pos )` and
`lf-front-proof ( -- node )`, the syntax store's words
(`src/front/syntax.fs`), the elaborator's hook `lf-front-elaborate ( --
type value )` and the hand-over `lf-handover ( decl type value -- outcome
)` (`src/front/handover.fs`), and the tactic record of
the declaration being read (`src/front/tactic-syntax.fs`, whose header
documents its format, `lf-tactic-format`, 1): `lf-tactic-proof? ( --
flag )`, `lf-tactic-count ( -- n )`, `lf-tactic-step ( i -- addr )` (the
fields `tac-kind`, `tac-parent`, `tac-at`, `tac-from`, `tac-to`,
`tac-arrow`, `tac-name`, `tac-first`, `tac-count`, `tac-inner`) and
`lf-tactic-arg ( j -- x pos )`; a hypothesis reads as a syntax node of
kind `syn-k-hyp`. The runner (`src/front/tactic-run.fs`, plan FE1g-3)
adds the statement's hook `lf-front-by-statement ( -- type )`, which plan
FE1e fills (the binders' locals pushed on the current view, the
statement's type in their context; until then error 71), the entry
`lf-tactic-by ( type -- goal )` (Lean's runTactic), the fuel words
`lf-tactic-fuel! ( n -- )` and `lf-tactic-fuel-default ( -- )`, the row
setter `lf-tactic-action! ( xt kind -- )` that later steps use while
loading, the words a tactic's action uses (`lf-tac-main`, `lf-tac-fail`,
`lf-tac-focus`, `lf-tac-unfocus`, `lf-tac-done`, `lf-tac-block`), the
saved states (`lf-tac-save`, `lf-tac-restore`, `lf-tac-commit`,
`lf-tac-try`, `lf-tac-forget`) and the open parts (`lf-open-parts`,
`lf-open-parts.`); the tactic library (`src/front/tactic-core.fs`) adds
`lf-tac-elab ( node expected -- term outcome )`, the term elaborator's
hook plan FE1e fills (Lean's `Tactic.elabTerm`), `lf-tac-defeq ( t s --
flag outcome )` (isDefEq as the tactics run it) and `lf-tac-holds? ( term
xt -- flag outcome )`. `leanforth print --lf` writes `kernel-form` as its
first line.

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
| `lf-author-export` | `( sink -- outcome )` | the run's theorems, definitions and axioms as export records, a line at a time to sink `( c-addr u -- outcome )` (`export.fs`) |
| `lf-author-library!` | `( finder\|0 -- )` | the library a run may name: finder `( name -- universes height true \| false )`, or none (`library.fs`) |
| `lf-author-checked!` | `( flag -- )` | true: a checked run, which refuses `import-stub` (error 48) |
| `lfc-library-open`, `lfc-library-close` | `( c-addr u checked? -- outcome )`, `( -- )` | an export as the library of later runs, outside `check` (`cli/check-lf.fs`) |

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

The runner's rules for running in the checker's own Gforth (plan task
8.2.1a; [ADR 0017 Amendment 1](../adr/0017-leanforth-syntax.md#amendment-1-accepted-leanforth-text-run-by-forth-itself-at-the-prompt-from-files-and-inline),
A5):

- **Forth must be interpreting.** A run started while Forth compiles (by
  an immediate word, say) is refused before anything runs, error 45 at
  line:col 0:0; otherwise the words would be compiled into the caller's
  definition. Every line must also end with Forth interpreting.
- **Characters.** A line may hold no control or format character (Unicode
  Cc and Cf: NUL, VT, FF, a CR inside a line, DEL, bidirectional controls,
  zero-width characters …), no line or paragraph separator and no bytes
  that are not UTF-8 (`src/lib/text-rule.fs`'s rule); TAB separates tokens
  as a space does. Such a line stops with error 46 at the character's
  column, before anything of the line runs; the token is left empty,
  since the character may be invisible or reorder the text around it.
  Forth splits tokens at TAB, LF, VT, FF, CR and space only, so with these
  characters refused a token is what an editor shows as one.
- **Lines.** Each text a run is given (`lf-author-text`, `lf-author-file`)
  counts its lines from 1.
- **Forth exceptions** (error 41, an internal fault, exit 5; error 300, full,
  exit 3, when a host stack, the dictionary or the heap ran out) name the last token a word read, or,
  when no word has read one on that line, the line's first token.
- **Group words** are made only while at least `lfa-dictionary-reserve`
  (65,536) address units of dictionary stay unused (else error 66, full),
  so a text never drives the dictionary to its end (Gforth 1.0 lets `HERE`
  pass the end by a few bytes there); and by an `EVALUATE` whose search
  order holds only a private word list with `lfa-group:`, so a word of
  that name defined later elsewhere is never run.
- **The three sealed word lists hold only `CREATE … DOES>` words**, never
  a `VALUE`, `DEFER` or `VARIABLE`: Gforth 1.0's `->` recognizer writes
  any of those it finds in the search order. A test checks every word of
  the three lists on Gforth 1.0.

### Checking text: the export and the library

`leanforth check [--env EXPORT | --snapshot FILE] FILE.lf`
([the command line](../user/COMMAND_LINE.md#checking-leanforth-text);
plan tasks 8.2.1c-d; ADR 0017 Amendment 2) runs in this order
(`src/cli/check-lf.fs`, `ck-lf-load`, in place of `ck-load`):

1. **The library.** With `--env`, the export is read into the importer
   stage (`stage-read`, its manifest checked unless `--no-manifest`) and
   not sealed; with `--snapshot`, the snapshot's tier is loaded as for
   `check --snapshot FILE EXPORT`. Without either, the stage is empty.
2. **The text**, a checked run (`lf-author-checked!`, so `import-stub`
   stops with error 48) with the finder `lfc-find`, which looks a name of
   the run up in the stage's names (`name-seek-str`, part by part) and
   declarations (one declaration of that name, its universe parameters and
   its height when it is a definition with regular hints). A constant
   named for the first time gets a record of kind `lfa-decl-library`
   (`constants.fs`): never printed, never exported. While a library is
   set, the runner's **look-ahead** gives every token of a line, up to a
   `\` comment, that no word list of the run has and that is not
   number-like, a group word in LF-CONST before the line runs, so that a
   library name reaches `lfa-const-run` and Lean's resolution (§9). Error
   55: a one-part name that reaches a library constant through a namespace
   (its export does not say whether it is protected); error 28: a
   declaration that takes a library constant's name. A run that declares
   nothing of its own stops with error 49. The stores get the room the heap
   has during the run (`lfc-rooms`), and their settings back after.
3. **The records.** `stage-extend` keeps the library's declarations and
   `stage-produce` reads the lines `lf-author-export` writes: a metadata
   record (exporter `leanforth`, read with `stage-any-version!`), every
   name of the name store in ID order, every level but zero and every term
   node but a projection's leaf in store order (the stores only append, so
   a record names earlier ones only), then each theorem, definition (hints
   regular, height one above the highest definition its value names) and
   axiom. Each line is a JSON text of `src/lib/json-write.fs`, its keys in
   Lean's sorted order (the writer's sorted mode) and its strings escaped
   as Lean's `Json.compress` escapes them: the same format as pinned Lean's
   export, not the same bytes (the numbering is store order, nodes are not
   merged as lean4export merges them, the metadata names LeanForth). A
   reference to a projection's leaf or a level of an unknown tag is
   refused (unsupported), never written. The stage is
   sealed and fed; the run goes on as an export's (`ck-check`, the import
   pass first for a snapshot), and `cli/leanforth.fs` prints the report.
   `make test` compares each fixture's records with the words' terms and
   `make check` with pinned Lean's export of its Lean source.
4. **A text that stops** (any error of the run) is not staged, sealed or
   checked: `lfc-failed?` is true and the command line prints the error
   (`lf-author-error.`) with its outcome's exit status. A text that ran
   but whose records the writer or the stage refused is not checked
   either: `lfc-refused?` is true and the error is said of the text. Each
   text's run starts with both flags cleared (`lfc-fresh`), and the
   stores' room and term sharing are given back after the words and the
   records, even after a THROW, which then passes on.

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
below it). The outcome *internal* (code 41) is none of the vocabulary: an
internal fault of LeanForth, exit 5 (review N1 of 2026-11-18).

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
| 41 | internal | a Forth exception, with its THROW code |
| 42 | invalid | a ( comment must end with ) on the same line |
| 43 | invalid | protected comes right before theorem, def, axiom or import-stub |
| 44 | invalid | protected declarations must be in a namespace |
| 45 | invalid | LeanForth text runs only while Forth interprets, never while it compiles |
| 46 | invalid | a character no line may hold (a control or format character, or no UTF-8) |
| 47 | full | out of room: the search order holds more wordlists than a run can save |
| 48 | invalid | import-stub is never checked: name the library with --env and use its constant |
| 49 | invalid | nothing to check: the text declares no theorem, definition or axiom |
| 50 | unsupported | not supported yet: natural-number literals need literal nodes (ADR 0017 section 14) |
| 51 | unsupported | not supported yet: designed in ADR 0017 but not built yet |
| 52 | unsupported | not supported yet: holes are filled by the elaborator (plan task 8.3.1) |
| 53 | unsupported | not supported yet: _root_ in a declaration's name |
| 54 | unsupported | not supported yet: export and the aliases it makes |
| 55 | unsupported | not supported yet: a library constant by a short name; write the full name |
| 56 | invalid | a projection leaf is no term: apply it with $ to the term it projects |
| 57 | invalid | kernel-form belongs outside declarations |
| 58 | invalid | a word of natural LeanForth: the text is in the kernel form (kernel-form) |
| 59 | invalid | ' takes the name right after it on the same line |
| 60 | full | out of room: the term store is full |
| 61 | full | out of room: the level store is full or the level too large |
| 62 | full | out of room: the name store is full or the name too long |
| 63 | full | out of room: the constant-reference store is full |
| 64 | full | out of room: too many values in one declaration |
| 65 | full | out of room: too many binders open |
| 66 | full | out of room: too many names, namespaces or declarations |
| 67 | full | out of room: too many labels and notes |
| 68 | full | out of room: the syntax store is full |
| 69 | invalid | by comes right after := and before the proof |
| 70 | unsupported | not supported yet in natural LeanForth (plan FE2); write kernel-form first |
| 71 | unsupported | not supported yet: elaborating natural LeanForth (plan FE1e-f) |
| 72 | unsupported | not supported yet: tactics (plan FE1g) |
| 73 | unsupported | not supported yet: how many arguments the name takes depends on unfolding its type |
| 74 | invalid | elaboration incomplete: a hole (metavariable) is left in the declaration |
| 75 | invalid | unused universe parameter: the statement (or a definition's value) must use it |
| 76 | invalid | malformed elaboration: a term that is no node, or a value unfit for the declaration |
| 77 | unsupported | not supported yet: this step of instantiating metavariables (plan FE1c) |
| 80 | unsupported | not supported yet: running this tactic |
| 81 | invalid | a tactic word belongs in a tactic proof, after := by |
| 82 | invalid | a block is still open: by-end closes by-induction-with and by-case:, ] closes by-rw[ |
| 83 | invalid | no block of this word's kind is open (\| belongs right inside by-induction-with) |
| 84 | invalid | a header is TAG NAMES... => on one line, after \| or by-case:; names are no words |
| 85 | invalid | an alternative or a by-case: block needs at least one tactic |
| 86 | invalid | wrong number of values: by-exact and by-induction take one, the others none |
| 87 | unsupported | not supported yet: how many values a hypothesis takes is known when tactics run |
| 88 | full | out of room: the tactic store is full |
| 89 | invalid | unsolved goals |
| 90 | invalid | No goals to be solved |
| 91 | exhausted | out of fuel: the tactic proof, or a reduction it ran, took more steps than its fuel |
| 92 | invalid | malformed tactic record or proof state: steps not nested as read, a bad goal list |
| 93 | unsupported | not supported yet: a type inference, reduction or let binder the tactic needs (FE1c) |
| 94 | invalid | Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce |
| 95 | invalid | don't know how to synthesize: the term leaves a metavariable it made unassigned |
| 96 | invalid | Type mismatch |
| 97 | invalid | Tactic `rfl` failed: The left-hand side |
| 98 | invalid | Tactic `exact` failed: attempting to close the goal using |
| 99 | unsupported | not supported yet: this case of the tactic (FE1G_TACTICS.md 5 names its step) |
| 100 | invalid | invalid universe level: not greater than 0 |
| 101 | invalid | AppBuilder failed: a term the tactic library builds does not fit (an equality proof expected, an application type mismatch, no instance found) |
| 110 | invalid | type class instance expected |
| 111 | invalid | type class resolution failed, insufficient number of arguments |
| 112 | invalid | elaboration data refused: an instance is recorded under a class its type is not of |
| 113 | invalid | elaboration data refused: an instance's recorded keys differ from its type's |
| 114 | unsupported | not supported yet: an instance's recorded keys are wider than its type's (no_index) |
| 115 | invalid | elaboration data refused: an instance is filed under another root key than its class |
| 116 | invalid | elaboration data refused: a default instance's type is not of its recorded class |
| 117 | unsupported | not supported yet: an instance problem whose type is a function type (plan FE1e5b) |
| 118 | unsupported | not supported yet: an instance answer that keeps the search's metavariables (FE1e5b) |
| 119 | unsupported | not supported yet: the search tries an instance the export left out |
| 120 | unsupported | not supported yet: the search tries an instance whose keys could not be checked (S2) |
| 121 | unsupported | not supported yet: Lean's check of an instance that holds metavariables (FE1e5b) |
| 122 | invalid | failed to synthesize |
| 125 | invalid | failed to synthesize instance of type class |
| 126 | invalid | typeclass instance problem is stuck |
| 127 | invalid | numerals are data in Lean, but the expected type is a proposition |
| 128 | invalid | numerals are data in Lean, but the expected type is universe polymorphic and may be a proposition |
| 129 | invalid | failed to assign synthesized type class instance |
| 130 | invalid | type expected |
| 131 | unsupported | not supported yet: a coercion (plan FE4) |
| 132 | unsupported | not supported yet: postponing an elaboration (plan FE2) |
| 133 | unsupported | not supported yet: an implicit lambda (plan FE2) |
| 134 | unsupported | not supported yet: an optParam, autoParam or eta argument (plan FE2) |
| 135 | unsupported | not supported yet: elaborating as an eliminator (plan FE5) |
| 136 | unsupported | not supported yet: a binder whose kind the declaration's type does not give (plan S5) |
| 137 | unsupported | not supported yet: #check of this form (plan FE2) |
| 138 | exhausted | out of fuel: the front end's work limit (--elab-fuel N gives more) |
| 139 | unsupported | not supported yet: an elaboration step (plans FE2-FE5, S2) |
| 140 | invalid | unexpected token '#check'; expected term |
| 141 | invalid | #check is a command: Lean would end the tactic block here; put it after end |
| 200 | unsupported | not supported yet: a smart-unfolding marker reached the declaration (plan S2) |
| 205 | invalid | Tactic `induction` failed: major premise type is not an inductive type |
| 206 | invalid | Invalid alternative name |
| 207 | invalid | Alternative |
| 208 | invalid | Too many variable names provided at alternative |
| 209 | invalid | The `induction` tactic does not support the type |
| 210 | invalid | Case tag |
| 211 | invalid | too many variable names provided |
| 212 | invalid | Type mismatch when assigning motive |
| 213 | invalid | Duplicate alternative name |
| 215 | invalid | Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| 216 | invalid | Tactic `rewrite` failed: motive is not type correct: |
| 217 | invalid | Tactic `rewrite` failed: Motive is dependent: |
| 218 | invalid | Invalid rewrite argument: Expected an equality or iff proof or definition name, but |
| 219 | invalid | Invalid rewrite argument: The pattern to be substituted is a metavariable |
| 220 | invalid | Occurs check failed: Expression |
| 300 | full | out of room: a Forth stack, the dictionary or the heap, with its THROW code |
| 440 | invalid | Tactic `clear` failed: unknown variable |
| 441 | invalid | Tactic `clear` failed: variable |
| 442 | invalid | Tactic `clear` failed: target depends on |
| 389 | invalid | Unexpected term |
| 380 | invalid | Tactic `apply` failed: could not unify the |
| 384 | invalid | Tactic `apply` failed: failed to assign synthesized instance |
| 381 | invalid | Tactic `assumption` failed |
| 382 | invalid | Tactic `constructor` failed: target is not an inductive datatype |
| 383 | invalid | Tactic `constructor` failed: no applicable constructor found |
| 443 | invalid | 'change' tactic failed, pattern |
| 444 | invalid | 'show' tactic failed, pattern |
| 445 | invalid | 'show' tactic failed, no goals unify with the given pattern. |
| 449 | invalid | Tactic `contradiction` failed |
| 250 | invalid | Tactic `decide` proved that the proposition |
| 251 | invalid | Expected type must not contain free variables |
| 252 | invalid | Expected type must not contain metavariables |
| 253 | invalid | Tactic `decide` failed to reduce |
| 254 | unsupported | `native_decide` is not supported: it trusts Lean's compiler (`Lean.ofReduceBool`), never accepted (ADR 0021 D7) |
| 448 | invalid | Tactic `delta` failed: did not delta reduce |
| 385 | invalid | Tactic `left` failed: target is not an inductive datatype |
| 386 | invalid | Tactic `left` failed: left tactic works for inductive types with exactly 2 constructors |
| 387 | invalid | Tactic `right` failed: target is not an inductive datatype |
| 388 | invalid | Tactic `right` failed: right tactic works for inductive types with exactly 2 constructors |
| 447 | invalid | 'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context |
| 446 | invalid | goal index `2` is out of bounds |

What follows the first line of eight of these messages (the table gives the first line, as `src/author/errors.fs` holds it):

- 122: Meta's synthInstance, the tactic library's: mkAppM's, mkAppOptM's and apply's instance binders, `by-decide`'s instance; the type indented and Lean's hint follow.
- 250: the proposition indented, then "is false".
- 251: the type indented, then Lean's `+revert` hint.
- 252: the type indented.
- 253: the decide term indented, then "to `true` or `false`.".
- 443 and 444: the pattern indented, "is not definitionally equal to target", the target indented.
- 445: a blank line, "In the first goal, the pattern", the pattern indented, "is not definitionally equal to the target", the target indented, "(Errors for other goals omitted)".
- 448: the names on the message's own line, ` [f]`, then the goal after a blank line.

Codes come in ranges (`src/author/errors.fs`): 1 to 73 the words, the
runner, the stores and natural text read (FE1a); 74 to 79 elaboration and
the hand-over (FE1c, FE1e, FE1f; 74 to 77 used); 80 to 99 tactic proofs
(FE1g; all used); 440 to 449 the tactics of batches TB1 and TB2
(`clear`'s 440 to 442 in `src/front/meta-tactic/goal.fs`; 443 to 445
`change` and `show`, `tactics/change.fs`; 446 `swap`; 447 `specialize`;
448 `delta`; 449 `contradiction`, `meta-tactic/contradiction.fs`);
250 to 254 `by-decide` and `by-native-decide`
(`src/front/tactics/decide.fs`, plan S3a; 255 to 269 kept for S3b); 122
Meta's synthInstance found none (the tactic library's "failed to
synthesize", with the type and Lean's hint: mkAppM's, mkAppOptM's,
apply's and decide's instances); 110 to 124 instances (S1: 110 and 112 to 116 are
the instance table's, `src/front/instances.fs`, plan FE1e3; 112, 113,
115 and 116 refuse the elaboration data at the first instance problem,
as FE1E_APPLICATIONS.md §4 says); 125 to 139 the elaborator's (S1,
`src/front/elab-*.fs`) and 140 and 141 `#check` inside a declaration, in
a term position (Lean's parser error) or in a tactic block (where Lean
would end the block before it; the first of FE2's command codes); 205 to
220 S2's induction and rewriting (`src/front/meta-tactic/elim.fs`, `tactic-alts.fs`,
`meta-tactic/rewrite.fs` and `tactics/rewrite.fs`: Lean's texts, the names they hold ending the
message's own line, as in "Invalid alternative name `suc`: Expected
`succ`"; 210 and 211 `by-case:`'s, `src/front/tactics/case.fs` and `meta-tactic/rename.fs`; 214
kept); the rest of 100 on free. Codes 81 to
88 are the reading of
tactic proofs (`src/front/tactic-syntax.fs`, plan FE1g-2): 82 names the
word and the open block's (by-induction-with for an alternative, by-rw[
for a word inside the brackets). Codes 80 and 89 to 93 are the runner's
(`src/front/tactic-run.fs`, plan FE1g-3): 80 names a tactic word not
ported yet and adds the plan step that ports it, `(plan FE1g-N)`; 89
names `by` (the proof) or a block's `=>`, where Lean reports unsolved
goals; 80, 89, 91 and 93 print the goals at that point on the lines after
the message, as Lean prints them under a tactic's error (when the heap
cannot hold them, a last line says the rest could not be shown). Codes
94 to 99 are the first tactics' (`src/front/tactics/`, plan
FE1g-4); 94, 96 and 97 continue with Lean's own lines (the goal after a
blank line; the term and its type and the type expected, with their
sorts when those differ; the two sides and the goal), so the message
and its lines read as pinned Lean's.

The tests reach every code: `tests/author/author.fs` all but 39 and the
natural form's (57 to 59 and 68 to 73, which `tests/front/front.fs`
reaches, 68 with the syntax store's limit lowered; 58 both; 74 to 77,
which `tests/front/handover.fs` reaches with an elaborator of its own, the
real one being plan FE1e; 80 to 88, which `tests/front/tactic-syntax.fs`
reaches, 88 with the tactic stores' limits lowered and with the heap
refusing; 80 again and 89 to 93, which `tests/front/tactic-run.fs`
reaches, and 94 to 99, which `tests/front/tactic-basic.fs` reaches, with
statements and terms built by stand-in elaborators until plan FE1e),
and 39 the
example file `17-long-line.lf` (a line of 1024 characters or more in a
file). Proof text cannot reach 34, since it cannot write a
negative number and each value is used once; the unit tests reach it by
calling the words with a used value and with a variable outside its
binder. Code 41 is reachable: very many numbers overflow Forth's data
stack (−3, on Gforth 1.0 and 0.7.3 alike). Before the review of
2026-11-03 this page said no Forth exception other than −13 was
reachable; on Gforth 1.0, `->x` then threw −21.

## Limits

Measured on Gforth 1.0 and 0.7.3, which give byte-identical results.
There are two kinds of limit.

The checker's stores (terms, levels, names, constant references) live in
the heap and grow up to a limit that each context sets
(`lf-term-capacity!`, `lf-level-capacity!`, `lf-name-capacity!`,
`lf-cref-capacity!`). A new context's limit is 64 terms (equal subterms
share a node, except a step with a label or note), 64 levels, 64 names and
32 constant references; `tests/author/terms.fs`, the harness the round
trips use, raises each to 1,000,000. Going over a limit is outcome full,
never accepted.

The authoring words' own tables are fixed per run, and making them
growable is plan task 8.2.1b: 1,024 declarations, 1,024 name entries in
65,536 bytes of spelling, 1,024 known namespaces in 32,768 bytes, 16
namespace scopes and open namespaces at once, names of at most 256 bytes
(a group name 240), values, numerals and open binders as many as the heap holds, 64 labels
and notes in 4,096 bytes, 8 universe parameters per declaration and 8
universe arguments per constant, a search order of at most 16 wordlists at
the start of a run (error 47), numbers of at most 9 digits (numeric parts
of names: 18 on a 64-bit host), lines of at most 1,023 characters in a
file. So a Lean export of more than 1,024 declarations does not read back
through `print --lf` text yet (error 66 at the declaration that overflows).
A source position is the line times 65,536 plus the column; on a 32-bit
host lines beyond 32,767 wrap. Group words leave at least 65,536 address
units of dictionary unused (a margin before the host's end, not a
capacity).

## Tests

`make test` (target `test-author`): `tests/author/author.fs` (every
reachable error code with its line and column, case sensitivity, Forth's
words invisible, numbers in every host form, values used once, names
that are numbers, namespaces and which constant a name means, `var#`,
`root:`, positions, labels and notes, the runner's restoring, the note
table, the Forth mode on its own and the labels and notes it refuses; and
the rules of task 8.2.1a above, from probes p01, p03, p04, p05 and p07 of
ADR 0017 Amendment 1: Forth's own words and more number forms refused,
a run while Forth compiles refused with nothing compiled, characters a
line may not hold, a Forth exception's token, lines counted per text,
Forth-word names as harmless groups, a later `lfa-group:` never run, the
dictionary reserve and, on Gforth 1.0, `0 ->NAME` throwing −21 for every
word of the sealed lists; the export's lines, heights, levels, literals
and binder kinds, a sink's refusal, a full line and an unsupported node;
a library's constant found by a finder, its record and height, errors 1,
28, 48 and 55; the look-ahead's group words, a comment and a number-like
token; the look-ahead stopping at the reserve), `tests/core/stage.fs`
(`stage-produce` and `stage-extend`: lines a producer hands over, a
refusal rolled back, an extended read keeping both reads' declarations)
and `tests/author/check_author.py` (25 example files against
`fixtures.golden`, which records each declaration's terms as a tree dump
and the export records the kernel is given, with a round trip each, the
five that name a library run with it through
`tests/author/report-library.fs`; the records against the terms; this
table; the layering check; round
trips over the term printer's 50 cases and the five Lean exports; and
`leanforth check` on every example file, 19 accepted and 6 stopped before
any check, each verdict found by its declaration's name, on the four wrong
twins in `tests/author/wrong/`, rejected, and
the command cases of every outcome and misuse); the syntax page's
examples. Run the unit tests with Gforth 0.7.3 too when the runner
changes: the numbers check is host-sensitive.

`make check` (target `reference-author`) compares with Lean, for the 19
example files with a Lean source (`tests/reference/author-*.lean`); pinned
Lean refuses the Lean sources of the four wrong twins
(`tests/reference/author-wrong-*.lean`); and `scripts/export.sh` reproduces
the two library exports byte for byte (`tests/author/init-slice.ndjson`,
59 declarations of `Init`, and `monoid-slice.ndjson`, the class of
`08-monoid.lf`):

- **Terms, term for term** (`tests/author/lean_terms.py`). Pinned Lean
  compiles the source; a Lean metaprogram writes each declaration as Lean
  holds it, in the tree-dump format, and every theorem, definition and
  axiom must equal the words' terms exactly: every node, de Bruijn index,
  constant, universe argument, level, binder name and binder kind; each
  import stub must have Lean's universe parameters and, when it states a
  type, Lean's type; and every declaration, import stubs included, must be
  protected exactly when Lean's is. The pinned exporter (`leanexport`,
  lean4export 3.1.0) exports the same declarations, which must also agree,
  apart from binder names and kinds (and protection, which the export
  does not carry): that exporter shares nodes that differ only in binder
  names or kinds, so a later declaration can come out with an earlier
  one's (checked with three alpha-equivalent theorems). One binder name is
  a listed difference, with its reason (`12-hygienic-used.lf` names a
  binder with a hygienic name Lean's source cannot write). The example
  files `16-namespaces.lf` and `18-protected.lf` put Lean's name resolution
  under this comparison, protected constants included.
- **Text**: pinned Lean's `#print` of every declaration against the
  example's `lean:` lines; for the five that name a library, Lean prints
  with `pp.explicit` and the lines are compared joined (Lean breaks long
  lines), without `@` and with `nat_lit n` read as `n`: the printer has no
  types for a library's constants, so it shows their every argument and
  marks each such application with `@`, where Lean marks only those with
  implicit arguments. Two listed differences, with their reason
  (`21-numeric-name.lf`'s private theorem, which Lean prints by its short
  name).
- **Records** (review of 2026-11-12, H1): the export records `export.fs`
  writes for each example (`report.fs`'s `record:` lines) must equal, for
  every theorem, definition and axiom, the words' terms (in `make test`)
  and pinned Lean's export of the Lean source: kind, name, `all`,
  `levelParams`, hints (Lean's height), safety, type and value (apart from
  binder names and kinds, which that exporter merges). `06-universes.lf`
  names a constant with two different universe arguments and
  `21-numeric-name.lf` declares a name with a numeric part. The writer's
  planted faults (`lf-export-…` in `tests/mutants/faults.toml`) are caught
  by `check_author.py --records`.
- **Planted faults**: 24, each caught. Seven are faults in the printer and
  the words; seventeen each undo one fix of the review of 2026-11-03 or of
  its re-review (protected constants). The spelling check disabled, "every
  universe argument is 0" and the three name-resolution faults must be
  caught by the comparison with Lean (the round trip and the printed text
  cannot see them); an example Lean accepts that the faulty words refuse
  counts.
