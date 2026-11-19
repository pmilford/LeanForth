# LeanForth syntax: theorems and proofs as Forth words

See also the [language reference](LANGUAGE_REFERENCE.md) (owner's important page: every word by part, implemented or designed).

**Status (2026-11-12): integrated; the [parser] review gate is
pending.** The words of [ADR 0017](../adr/0017-leanforth-syntax.md), which
the owner approved as the design, exist in `src/author/` (plan task
8.1.2): you write a theorem, a definition and its proof as Forth words,
run them, get your mistakes back with line and column, and print the
result back as words or in Lean's notation. Since 2026-11-12 (plan tasks
8.2.1c and 8.2.1d, [ADR 0017 Amendment 2](../adr/0017-leanforth-syntax.md#amendment-2-leanforth-text-checked-by-the-kernel-2026-11-12))
**`leanforth check FILE.lf` checks such a file with LeanForth's checker**,
and with `--env EXPORT` the file uses the constants of Lean's library
(such as `Nat`, `Eq.refl` and `Nat.add_comm` from `Init`) by their Lean
names: see [checking a file](#checking-a-file). The words have still to
pass the [parser] review gate of `AGENTS.md`. Not built yet (designed in
[ADR 0017 Amendment 1](../adr/0017-leanforth-syntax.md#amendment-1-accepted-leanforth-text-run-by-forth-itself-at-the-prompt-from-files-and-inline),
plan 8.2.1e–g): text typed at the prompt or passed in from a Forth
program, a check at each `end NAME` (today the whole file is checked when
it ends), a library found through a vocabulary of its own; helpers that
fill in implicit arguments or run tactics are plan 8.3. Theorems also
reach the checker from Lean exports ([workflows](WORKFLOWS.md#checking-a-theorem)).

**Trust.** The words decide nothing. They only build terms; only the
checker can accept a theorem, and the checked statement can always be
printed back for you to read. `leanforth check FILE.lf` runs the text in
the checker's own Gforth, with only LeanForth's words visible to it (ADR
0017 Amendment 1, A5), and hands the declarations to the kernel as export
records; the kernel's modules themselves never load `src/author/` (a test
checks it). A wrong word can only build a different term, which the
checker checks as it is. The words themselves do not type-check: a wrong
proof builds without error when the words run alone (the composition
demo's `g value $`, where a proof of B is needed), and `leanforth check`
rejects it ([checking a file](#checking-a-file)). Words such as *term*, *binder*
and *universe level* are explained in [terms for new readers](TERMS_FOR_NEW_READERS.md) and
[concepts in three forms](CONCEPTS.md). Every word, its stack effect and
every error code are in the
[programming reference](../programming/LEANFORTH_WORDS.md).

## Two forms: kernel form and natural LeanForth

This page describes the **kernel form**, in which you write the full
proof term with every hidden argument (the "assembly" form). Since
2026-11-12 (owner decision 4, [ADR 0021](../adr/0021-front-end.md) D8)
**natural LeanForth is the default**, so a file or text in the kernel form
starts with the word `kernel-form` (outside any declaration; the printer,
`leanforth print --lf`, writes it first), as every example file in
`tests/author` does:

```text
kernel-form \ Lean: theorem identity {P : Prop} (proof : P) : P := proof
theorem identity
  ...
```

Natural LeanForth is being built (plan FE1). Today its words are read
into a syntax tree and nothing more: in `0 n + n =` the numeral `0`, the
variable `n` and the words `+` and `=` (Lean's `+` and `=`, which in
theorem text are LeanForth words, never Forth's) build Lean's
`binrel% Eq (binop% HAdd.hAdd 0 n) n`; a name takes as many arguments as
its type has explicit binders (`n Eq.refl` is `Eq.refl n`), `' NAME` is
the function itself, and `f a $` applies once more. At `end NAME` the
elaborator (plan S1, branch `s1-elab`: written and tested alone; see
[the elaborator](ELABORATION.md)) builds the declaration's terms as
Lean's elaborator does, and the checker checks them. Given the library's
elaboration data (`--elab-data`; without it every natural declaration
stops with error 139), names, applications
with their hidden arguments, `=`, binders, term proofs and tactic proofs
([tactic proofs](#tactic-proofs-read-and-run-once-statements-are-elaborated))
work today; numerals and `+` stop with error 139 at the step that is not
there yet (instance search, plan FE1e5; unfolding, plan S2). A
kernel-form word used without the marker (such as `Prop`) stops with
error 70. Both are "not supported yet", and nothing is checked.

## Tactic proofs (read, and run once statements are elaborated)

**Status (2026-11-13): read (plan FE1g-2); the runner written and tested
alone (plan FE1g-3); it runs on statements the elaborator builds (plan
S1, branch `s1-elab`), which do not have numerals or `+` yet.** A proof can be a
list of instructions, *tactics*, as in Lean: `:= by` and then tactic
words, each named with the prefix `by-`. LeanForth reads such a proof
whole, checks its shape (every block closed, each word given the values
it takes, each case header well formed, every mistake at its line and
column) and keeps a record of the steps. At `end NAME` the runner
(plan FE1g-3) takes the statement the elaborator built and runs the
steps in order on its goal (`by-rfl` and `by-exact` on
`tests/front/s1-now.lf`, see [the elaborator](ELABORATION.md)); a
statement with numerals or `+`, as below, stops with error 139, "not
supported yet", and nothing is checked. A tactic never makes a theorem accepted,
now or later: only the checker's check of the term does.

*Mathematics:* $0 + n = n$ for every natural number $n$, by induction on
$n$: for $0$, $0 + 0 = 0$ by computation; for $k + 1$, assuming
$0 + k = k$, $0 + (k + 1) = (0 + k) + 1$ by the definition of $+$, which
is $k + 1$ by the induction hypothesis.

*LeanForth* (`tests/front/01-zero-add-rw.lf`): `n by-induction-with`
starts the induction on `n`, each `| TAG NAMES =>` line is one case with
the names of its new hypotheses, and `by-end` closes the group;
`by-rw[ … ]` rewrites with the rules built between its brackets, a
theorem written `' NAME`, a hypothesis by its name:

```text
theorem zero_add''
  Nat explicit: n
  0 n + n =
:= by
  n by-induction-with
  | zero =>       by-rfl
  | succ k ih =>  by-rw[ ' Nat.add_succ ih ]
  by-end
end zero_add''
```

*Lean*:

```lean
theorem zero_add'' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

What LeanForth says today, against S2's slice of `Init` (the declarations
the proof set uses) and its elaboration data (plan S2, integrated
2026-11-17):

```console
$ bin/leanforth check --env tests/front/s2-slice.ndjson --elab-data tests/front/s2-slice.elab.ndjson tests/front/01-zero-add-rw.lf | grep "^zero_add"
zero_add'': accepted; axioms: none
```

Without the elaboration data (`--elab-data`) the statement's numerals and
`+` cannot be elaborated, and the text stops at `end` (error 139, exit 2).

The words (the design is [FE1G_TACTICS.md](../design/FE1G_TACTICS.md));
all of them are read and run (see "Running" below):

| Word | Stack effect | Lean | Read as |
| --- | --- | --- | --- |
| `:= by` | `( -- )` | `:= by` | a tactic proof, up to `end NAME` |
| `t by-exact` | `( t -- )` | `exact t` | close the goal with the term `t` |
| `by-rfl` | `( -- )` | `rfl` | close the goal by computation |
| `by-intro: NAME` | `( -- )` | `intro NAME` | introduce one hypothesis, `_` for one without a name |
| `t by-induction` | `( t -- )` | `induction t` | induction on `t`, one goal per case |
| `t by-induction-with` | `( t -- )` | `induction t with` | the same, its cases written up to `by-end` |
| `\| TAG NAMES… =>` | `( -- )` | `\| tag names =>` | one case, up to the next `\|` or `by-end`; the names are its new hypotheses |
| `by-case: TAG NAMES… =>` | `( -- )` | `case tag names =>` | a block for one case, up to its `by-end` |
| `by-end` | `( -- )` | (Lean's indentation) | closes the innermost `by-induction-with` or `by-case:` |
| `by-rw[ r1 … ]` | `( -- )` | `rw [r1, …]` | rewrite with each rule in order (none is allowed, as in Lean); every value between the brackets is a rule, so a hypothesis applied to arguments is written with `$`: `ih k $` is Lean's `rw [ih k]` |
| `by-rewrite[ r1 … ]` | `( -- )` | `rewrite [r1, …]` | the same without closing by computation |
| `by-sorry` | `( -- )` | `sorry` | close the goal without a proof: an open part (below) |

The same proof by `case` and `exact` is `tests/front/01-zero-add.lf`
(`by-case: succ k ih =>  ' Nat.succ ih congrArg by-exact  by-end`); one
tactic alone, `tests/front/02-add-zero-rfl.lf` and
`tests/front/03-zero-add-exact.lf`. Blocks nest (a `by-case:` inside a
case, an induction inside an alternative, as in
`tests/front/04-nested-ih.lf`, whose inner `ih` hides the outer one) as
deep as memory allows.

**Mistakes in the shape** each stop at their word with a code (every code
is in the [programming reference](../programming/LEANFORTH_WORDS.md#errors)):
a tactic word outside a tactic proof, in the statement say (81); `end
NAME` with a block still open, or a tactic word inside `by-rw[ ]` (82,
with the block's place as the second place); `by-end`, `]` or `|` with no
block of its kind (83: `|` belongs right inside `by-induction-with`); a
header not of the form `TAG NAMES… =>` on one line, or a tag or name that
is a LeanForth word (84); an alternative or `by-case:` block with no
tactic (85, at the word that ends it, with its `=>` as the second place,
where Lean's parser refuses it too); a word given the wrong number
of values, or values left at a word that takes none or at `end NAME`
(86). An empty proof (`:= by end NAME`) and a `by-induction-with` with no
case are read: Lean parses both, and refuses them only when it runs them
("unsolved goals", "alternative not provided"), which is FE1g-3 onward.

**Running** (plan FE1g-3; tested with statements built by hand until plan
FE1e). The steps run in order on a list of goals, the statement's goal
first, as Lean runs them; LeanForth stops at the first error, Lean goes
on to report more. Today `by-sorry`, `by-intro:`, `by-exact` and `by-rfl`
run (plan FE1g-4: Lean's `intro`, `exact` and `rfl`, with Lean's error
texts for a goal with nothing to introduce, a term of another type and
two sides that are not equal), and so do `by-induction`,
`by-induction-with` with its `|` alternatives, `by-rw[ ]` and
`by-rewrite[ ]` (plan S2, integrated 2026-11-17: Lean's `induction`,
`rw` and `rewrite`) and `by-case:` (Lean's `case`: the goal of that tag,
its hidden hypotheses renamed; errors 210 and 211). A goal
left when the proof ends is Lean's "unsolved goals" at `by` (error 89),
the goals printed as Lean prints them; a tactic with no goal left is
Lean's "No goals to be solved" (error 90); each step spends one unit of
the run's own fuel (error 91 when none is left, exit 3).

**Open parts** (`by-sorry`, Lean's `sorry`; ADR 0021 Amendment 1). The
goal is closed with Lean's axiom `sorryAx`; the checker checks
everything else, and the theorem, when accepted, is NOT PROVED: it
depends on `sorryAx` and is never counted as proved. After the verdicts
the command line lists each open part with its declaration, its line and
column and its goal:

```text
zero_add_sorry: accepted; axioms: unlisted; NOT PROVED: depends on sorryAx
...
open part 1 of zero_add_sorry (by-sorry at line:col 17:3):
p : Prop
⊢ p
note: everything else in a declaration with open parts was checked by the kernel;
note: accepted, it holds if each of its open parts is true, and is NOT PROVED
```

(That run is `tests/front/tactic-run.fs`'s, with a statement built by
hand; the wording and a JSON form wait for the owner's decision.) Lean
names each `sorry` with a label made from its position; LeanForth's term
has no label yet (plan PD1), which changes no verdict.

**Not supported yet** (exit 2): Lean's `induction t with tac | …` (a
tactic before the first `|`), the wildcard `| _ =>`, `| @tag …`, several
tags `| a | b =>` and `by-case: _` (error 72; plan FE5); and, while
tactics are only read, more values than a word takes where a hypothesis
was read with values below it, which it might take: how many values a
hypothesis takes is known only once the tactic that introduces it runs
(error 87). So `k ih by-exact` answers 87, while `ih n by-exact`, with
`n` a variable, is a mistake (86: `ih` comes first and takes nothing
from `n`); inside `by-rw[ ]` no doubt arises, since there every value is
a rule.

**`k ih` reads two ways.** Inside `by-rw[ ]` it is two rules, `k` and
`ih` (Lean's `rw [k, ih]`); outside the brackets it is one term, `ih`
applied to `k` when `ih` takes an argument (Lean's `ih k`), as every name
takes its explicit arguments. To rewrite with `ih` applied to `k`, write
`by-rw[ ih k $ ]`. A hypothesis can be used until its
block ends (a `by-intro:`'s until the end of the block it is in); one
named like a variable hides the variable while it is in scope.

## How to read it

Every token is a Forth word, and Forth's own interpreter runs it; there is
no other parser and no mathematics inside strings. It is postfix, like all
Forth: the parts come first, then the word that combines them.

- `$` applies a function to an argument: Lean's `f a b` is `f a $ b $`, and
  `g (f value)` is `g f value $ $`.
- `TYPE explicit: NAME` starts a variable of that type (also `implicit:`,
  `strict-implicit:`, `instance:` for Lean's `{x}`, `⦃x⦄`, `[x]`). Like
  Forth's `:`, it reads the name after it; using the name pushes the
  variable. `fun` or `forall` ends the variable's scope, making a function
  or a "for all".
- `A B ->` is "A implies B" (or "functions from A to B").
- `Prop`, `l Type`, `l Sort` are the universes; `c l ^` gives the constant
  `c` the universe level `l` (Lean's `c.{l}`); `u 1 level+`, `u v level-max`
  and `u v level-imax` build levels. Numbers are plain decimals (`0`, `1`,
  `12`, at most nine digits); Forth's other number forms (`-3`, `$10`,
  `1.`, `'a'`) are refused.
- `theorem NAME … := … end NAME` (also `def` and `axiom`): the variables
  still open at `:=` are the hypotheses; before `:=` comes the statement,
  after it the proof. `universe u` right after the name adds a universe
  parameter. `end NAME` defines a word for the theorem, so later proofs can
  use it. `namespace N … end N` and `open N` work as in Lean, and a name
  means the constant Lean would pick: inside `namespace N`, or in a
  declaration named `N.foo`, `bar` means `N.bar` if there is one, unless
  `N.bar` is *protected* (`protected def N.bar …`, as in Lean): a protected
  constant is found only by a name with a dot, such as `N.bar`. Where
  Lean would choose between two open namespaces by type, LeanForth asks
  for the full name.
- Names are Lean's names, exactly, with upper and lower case distinct
  (`x : X` works), although Forth finds words regardless of case: each
  word checks the spelling it was called with. LeanForth's own words are
  either Lean keywords or contain a character no Lean name has (`-`, `:`,
  `$`, `^`), so they never clash with a name. The name of a theorem,
  universe or namespace may not look like a number (`1`, `N.1`, `-x`), so
  a name never hides a number. Forth's own words, such as `dup` or `+`,
  are not visible while a proof runs; `+`, `=`, `*` and `≤` are words of
  natural LeanForth (Lean's operators), refused in kernel-form text
  (error 58).
- Comments are Forth's: `\` to the end of the line, `( … )` within a line
  (a `(` must be closed on its line).

Lean's library is named on the command line, `leanforth check --env
EXPORT FILE.lf` (an export of `Init`, or of any Lean library): the file
then uses its constants by their Lean names, and a name means the
constant Lean would pick. Before that existed, files named such constants
with `import-stub NAME [universe u]… [TYPE] end NAME`, a stand-in that only
defines the constant's word; a stub declares a constant no one checks, so
`leanforth check` refuses it (error 48). Stubs remain for running the
words and the printer on their own (the examples below with the
`leanforth` helper), until those move to small exports.

## Running it

From Forth (`gforth`, in the repository):

```text
require src/author/runner.fs
lf-author-begin  s" proof.lf" lf-author-file   \ gives an outcome (0 = ok)
lf-author-error.                               \ the first error, if any
1000 lf-author-print                           \ every declaration as words
```

The examples on this page are run by `make test` through a small helper,
`leanforth`, that runs the rest of its block as LeanForth text and prints
each theorem and definition as Lean's `#print` shows it (or the error); it
is documentation only:

```forth
\ Documentation helpers, not part of LeanForth: leanforth runs the rest of
\ its block as LeanForth text (src/author/) and prints each theorem and
\ definition as Lean's #print shows it, then each note with its step, or
\ the error; leanforth-words prints the declarations back as words.
require ~+/src/author/runner.fs
create text 8192 allot  variable text#
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: line+ ( c-addr u -- ) text+ s"  " text+ 10 text text# @ 1- + c! ;
: rest ( -- c-addr u ) 0 text# ! begin refill while source line+ repeat text text# @ ;
: ok. ( outcome -- ) ok? 0= abort" print failed" ;
: .kind ( decl -- ) lf-fdecl-kind @ lf-decl-theorem = if ." theorem " else ." def " then ;
: .universes ( decl -- )
  dup lf-fdecl-universes @ ?dup 0= if drop exit then
  ." .{" 0 ?do i if ." , " then dup lf-fdecl-universe i cells + @ lf-print-name ok. loop
  drop ." }" ;
: .type ( decl -- )
  dup lf-fdecl-type @ 1000 rot lf-fdecl-kind @ lf-decl-theorem =
  if lf-print-statement else lf-print-term then ok. ;
: .decl ( decl -- )
  dup lf-fdecl-kind @ lf-decl-def > if drop exit then
  dup .kind dup lf-fdecl-name @ lf-print-name ok. dup .universes ."  : " dup .type ."  :=" cr
  lf-fdecl-value @ 1000 lf-print-term ok. cr ;
: label-of ( term -- c-addr u )
  lf-note-count 0 ?do dup i lf-note-on? i lf-note-kind@ lf-note-label = and
    if drop i lf-note-text@ unloop exit then loop drop s" -" ;
: .note ( decl i -- )
  ." step " swap lf-fdecl-name @ lf-print-name ok. ." /" dup lf-note-term@ label-of type
  ."  (line " dup lf-note-source@ lfa-pos> drop 0 .r ." ), note by "
  dup lf-note-kind@ lf-note-person = if ." a person: " else ." an AI: " then
  lf-note-text@ type cr ;
: .notes ( i -- )
  dup lf-author-decl swap lf-author-notes swap ?do
    i lf-note-kind@ lf-note-label <> if dup i .note then loop drop ;
: run-rest ( -- flag )
  lf-author-begin lf-author-kernel rest lf-author-text ok? dup 0= if lf-author-error. cr then ;
: leanforth ( -- )
  run-rest 0= if exit then
  lf-author-count 0 ?do i lf-author-decl .decl loop
  lf-author-count 0 ?do i .notes loop ;
: leanforth-words ( -- ) run-rest if 1000 lf-author-print ok. then ;
```

## Checking a file

`leanforth check FILE.lf` runs a file of LeanForth text and checks every
theorem, definition and axiom it declares with LeanForth's checker, the
one that checks Lean's exports; the report is the same as for an export
([the command line](COMMAND_LINE.md#checking-leanforth-text)):

```console
$ bin/leanforth check tests/author/01-identity.lf
identity: accepted; axioms: none
1 declaration: 1 accepted
accepted: 1; axioms: none
```

**A proof of your own, using Lean's library.** *Mathematics:* for every
natural number $n$, $n + 0 = n$, by computation: $n + 0$ reduces to $n$.
*LeanForth* (`tests/author/19-add-zero.lf`): `Nat`, `Eq`, `HAdd.hAdd`,
`OfNat.ofNat`, `Eq.refl` and the rest are `Init`'s, named by their Lean
names; the proof is `Eq.refl n`, which proves $n = n$, and the checker
must see that `n + 0` reduces to `n` (Lean's `0` is
`OfNat.ofNat Nat 0 (instOfNatNat 0)`, and `0 lit#` is the literal 0):

```text
theorem add_zero'
  Nat explicit: n
  Eq 1 ^ Nat $
    HAdd.hAdd 0 ^ 0 ^ 0 ^ Nat $ Nat $ Nat $  instHAdd 0 ^ Nat $ instAddNat $  $  n $
      OfNat.ofNat 0 ^ Nat $  0 lit# $  instOfNatNat 0 lit# $  $  $
  $
    n $
:=
  Eq.refl 1 ^ Nat $ n $
end add_zero'
```

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson tests/author/19-add-zero.lf | tail -3
add_zero': accepted; axioms: none
60 declarations: 60 accepted
accepted: 60; axioms: none
```

*Lean*, which accepts the same theorem with the same term (the tests
compare the terms node for node):

```lean
theorem add_zero' (n : Nat) : n + 0 = n := Eq.refl n
```

The export `tests/author/init-slice.ndjson` holds the 59 declarations of
`Init` these examples need; the first 59 lines of the report are theirs,
checked before the file's. With all of `Init`'s export, or a snapshot of
it (`--snapshot FILE`), the file is checked the same way.

**Induction.** *Mathematics:* $0 + n = n$ for every $n$ — but not by
computation, since $0 + n$ does not reduce while $n$ is unknown (the
checker rejects `Eq.refl n` here, as Lean does:
`tests/author/wrong/19-add-zero.lf`). By induction on $n$: $0 + 0 = 0$, and
from $0 + k = k$ follows $0 + (k + 1) = (0 + k) + 1 = k + 1$.
*LeanForth* (`tests/author/20-zero-add.lf`) writes the induction as Lean's
kernel term: the recursor `Nat.rec` with the motive $k \mapsto 0 + k = k$,
the case for zero and the step, `congrArg Nat.succ` applied to the
hypothesis `ih`. *Lean*:

```lean
theorem zero_add' (n : Nat) : 0 + n = n :=
  @Nat.rec (fun k => 0 + k = k) (@Eq.refl Nat 0)
    (fun k ih => @congrArg Nat Nat (0 + k) k Nat.succ ih) n
```

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson tests/author/20-zero-add.lf | tail -1
accepted: 60; axioms: none
```

**What happens to a file.** Forth's own interpreter runs it line by line
with only LeanForth's words visible, and before each line LeanForth makes
a word for every name in it that has none yet (not for the text of `( … )`
comments and notes, which is no name), so that a library name
such as `Nat.add_comm` runs as Lean resolves it (unknown names still stop
as unknown, error 1). When the file ends without an error, the
declarations it made are handed to the checker as export records, behind
the library's, and checked in file order. A file that stops with an error
is not checked at all; the error is printed with its line and column. In
the rare case that the text runs but its records are refused before the
check (no room for them, say), the error says so of the text, and nothing
is checked. Three limits for now, each a temporary gap where Lean
decides (plan task 8.2.1d's follow-ups): the library's export does not
say which constants are *protected*, so a library constant is written by
its full name inside a namespace (`MyMonoid.mul`, not `mul`; error 55
otherwise); `open` of a namespace that only the library has, such as
`open Nat`, stops with error 26 (unknown namespace: a namespace is known
once the text enters it or declares a name in it), so write the library's
names in full; and `import-stub` is refused (error 48). A projection leaf
(`0 proj# S`) is a term only as the function of `$`; anywhere else the run
stops with error 56.

## Example: identity

**Mathematics.** For every proposition $P$: $P \to P$.

**LeanForth**, and what the words built, printed as Lean prints it:

```forth
leanforth
theorem identity
  Prop implicit: P
  P explicit: proof
  P
:=
  proof
end identity
```

```text
theorem identity : ∀ {P : Prop}, P → P :=
fun {P} proof ↦ proof
```

**Lean**, and what Lean prints for it:

```lean
theorem identity {P : Prop} (proof : P) : P := proof
set_option pp.unicode.fun true in
#print identity
```

```text
theorem identity : ∀ {P : Prop}, P → P :=
fun {P} proof ↦ proof
```

## Example: composition

**Mathematics.** For all propositions $A, B, C$: if $A \to B$ and
$B \to C$, then $A \to C$.

**LeanForth**: `f` and `g` are the two hypotheses; the proof takes a proof
`value` of A and returns `g (f value)`.

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $ $   fun
end composition
```

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
```

**Lean**:

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
set_option pp.unicode.fun true in
#print composition
```

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
```

## Example: a universe parameter and a constant used at two levels

**Mathematics.** The identity function $\mathrm{id}_\alpha(x) = x$ for
$\alpha$ in any universe $u$; used at level $0$ it maps a proof $h$ of
$P$ to $h$.

**LeanForth**: `end fixtureId` defines the word `fixtureId`, which the
theorem then uses with the universe argument `0 ^`.

```forth
leanforth
def fixtureId
  universe u
  u Sort implicit: α
  α explicit: x
  α
:=
  x
end fixtureId

theorem fixtureUse
  Prop implicit: P
  P explicit: h
  P
:=
  fixtureId 0 ^ P $ h $      \ @fixtureId.{0} P h
end fixtureUse
```

```text
def fixtureId.{u} : {α : Sort u} → α → α :=
fun {α} x ↦ x
theorem fixtureUse : ∀ {P : Prop}, P → P :=
fun {P} h ↦ fixtureId h
```

**Lean**:

```lean
universe u
def fixtureId {α : Sort u} (x : α) : α := x
theorem fixtureUse {P : Prop} (h : P) : P := fixtureId h
set_option pp.unicode.fun true in
#print fixtureUse
```

```text
theorem fixtureUse : ∀ {P : Prop}, P → P :=
fun {P} h ↦ fixtureId h
```

## Example: commutativity of addition

**Mathematics.** For all natural numbers $n, m$: $n + m = m + n$.

**LeanForth.** This is the *kernel form*: the term as Lean's kernel
has it (this version, with import stubs, is only run by the words; `tests/author/07-add-comm.lf`, without them, is checked against Init),
with every hidden argument written out. Lean's `n + m` is generic
addition `HAdd.hAdd` at the type `Nat`, with "addition of naturals"
(`instHAdd 0 ^ Nat $ instAddNat $`) passed as an argument, and `0 ^` and
`1 ^` are universe levels. Shorter forms, where a helper fills in such
arguments, are planned (task 8.3.1); the `+` sign itself stays with the
printer and editors, because in Forth `+` means machine addition. Here,
run by the words alone, import stubs stand in for Lean's core library;
`tests/author/07-add-comm.lf` is the same theorem without them, checked
with `leanforth check --env tests/author/init-slice.ndjson`
([checking a file](#checking-a-file)):

```forth
leanforth
import-stub Nat end Nat
import-stub instAddNat end instAddNat
import-stub instHAdd  universe u_1  end instHAdd
import-stub HAdd  universe u  universe v  universe w  end HAdd
import-stub outParam  universe u  end outParam
protected import-stub Nat.add_comm end Nat.add_comm
import-stub Eq
  universe u_1
  u_1 Sort implicit: α
  α α Prop -> ->
end Eq
import-stub HAdd.hAdd
  universe u  universe v  universe w
  u Type implicit: α
  v Type implicit: β
  outParam w 2 level+ ^  w Type $  implicit: γ
  HAdd u ^ v ^ w ^  α $ β $ γ $  instance: self
  α β γ -> ->
end HAdd.hAdd

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

```text
theorem add_comm' : ∀ (n m : Nat), Eq (HAdd.hAdd n m) (HAdd.hAdd m n) :=
fun n m ↦ Nat.add_comm n m
```

**Lean**, printed without the `+` and `=` notation, as the term printer
prints it today:

```lean
theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm n m
set_option pp.unicode.fun true in
set_option pp.notation false in
#print add_comm'
```

```text
theorem add_comm' : ∀ (n m : Nat), Eq (HAdd.hAdd n m) (HAdd.hAdd m n) :=
fun n m ↦ Nat.add_comm n m
```

## Example: a proof with notes that evolves

**Mathematics.** From $A \to B$, $B \to C$ and $C \to D$ follows
$A \to D$.

**LeanForth.** Any step can get a label and a note. `note"` marks a note
written by a person, `ai-note"` one written by an AI. Notes are never
checked; they stay in the file next to their step, are printed with the
proof, and survive printing the proof back as words. Here a person has
replaced an AI's first two steps by the earlier theorem `composition` and
rewritten that note; the last step and its note did not change:

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $ $   fun
end composition

theorem chain
  Prop implicit: A   Prop implicit: B   Prop implicit: C   Prop implicit: D
  A B ->  explicit: f
  B C ->  explicit: g
  C D ->  explicit: h
  A D ->
:=
  A explicit: a
    h  composition A $ B $ C $ f $ g $ a $
              label: to-C  note" composition does the first two steps at once"
       $      label: to-D  note" h finishes the chain: a proof of D"
  fun
end chain
```

```text
theorem composition : ∀ {A B C : Prop}, (A → B) → (B → C) → A → C :=
fun {A B C} f g value ↦ g (f value)
theorem chain : ∀ {A B C D : Prop}, (A → B) → (B → C) → (C → D) → A → D :=
fun {A B C D} f g h a ↦ h (composition f g a)
step chain/to-C (line 19), note by a person: composition does the first two steps at once
step chain/to-D (line 20), note by a person: h finishes the chain: a proof of D
```

**Lean**:

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
theorem chain {A B C D : Prop} (f : A → B) (g : B → C) (h : C → D) : A → D :=
  fun a => h (composition f g a)
set_option pp.unicode.fun true in
#print chain
```

```text
theorem chain : ∀ {A B C D : Prop}, (A → B) → (B → C) → (C → D) → A → D :=
fun {A B C D} f g h a ↦ h (composition f g a)
```

## Example: names that differ only in case

**Mathematics.** The identity on a type $X$, written with an element
$x : X$.

**LeanForth.** Forth would find `X` and `x` as one word; LeanForth's
words tell them apart, as Lean does:

```forth
leanforth
def caseVar
  0 Type implicit: X
  X explicit: x
  X
:=
  x
end caseVar
```

```text
def caseVar : {X : Type} → X → X :=
fun {X} x ↦ x
```

**Lean**:

```lean
def caseVar {X : Type} (x : X) : X := x
set_option pp.unicode.fun true in
#print caseVar
```

```text
def caseVar : {X : Type} → X → X :=
fun {X} x ↦ x
```

## Printing a proof back as words

The printer's Forth mode writes a declaration as the words that build it,
with a line per universe parameter and per hypothesis; running those
words gives the identical term, with the same names, binder kinds, labels
and notes (the tests check this for every example file and for every term
of the term printer's tests). Layout carries no meaning, so this is also
the normal form of a file:

```forth
leanforth-words
theorem composition  Prop implicit: A  Prop implicit: B  Prop implicit: C
  A B -> explicit: f  B C -> explicit: g  A C ->  :=  A explicit: value g f value $ $ fun
end composition
```

```text
theorem composition
  Prop implicit: A
  Prop implicit: B
  Prop implicit: C
  A B -> explicit: f
  B C -> explicit: g
  A C ->
:=
  A explicit: value g f value $ $ fun
end composition
```

## Mistakes point at your text

A missing `$`, a misspelt name or a Forth word stops at the word, with its
line and column, a stable error code and, where it helps, a second place:
for a body with two values instead of one, the place where its variable
was opened.

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f value $   fun
end composition
```

```text
error 12 at line:col 7:37 (token `fun`): the body of the binder must be exactly one term; see line:col 7:5
```

```forth
leanforth
theorem composition
  Prop implicit: A   Prop implicit: B   Prop implicit: C
  A B ->  explicit: f
  B C ->  explicit: g
  A C ->
:=
  A explicit: value   g f valeu $ $   fun
end composition
```

```text
error 1 at line:col 7:27 (token `valeu`): unknown name: no syntax word, bound variable, universe parameter or constant has it
```

Lean reports the second one as ``Unknown identifier `valeu` ``. Forth's
own words are unknown names too: `A dup` in a proof stops at `dup`.

## Limits today

- **Store sizes.** A run on its own builds its terms in LeanForth's
  stores, which start with 64 terms, 64 levels, 64 names and 32 constant
  references; `leanforth check` gives them as much room as the heap has.
  Equal subterms share one node (which keeps the position where it was
  first written), found through a hash index of the store's nodes (since
  2026-11-18; before, a search through the whole store made a statement
  of 500 arrows take minutes); a step with a label or note always has a
  node of its own. A declaration may hold any number of values, as the
  heap allows. The authoring tables hold 1,024 declarations and 1,024
  names in scope.
- **Depth.** A statement nested very deeply stops with error 300 (out of
  room: a Forth stack; exit 3), never with another term: `P -> P -> … ->
  P` of 900 arrows is checked in about 3 s with `gforth-fast`, one of
  1,000 stops at once, because the words that build `A B ->` shift `B`'s
  variables recursively (planned: a walk on the heap instead).
- **Not supported yet** (each stops with a "not supported yet" error):
  string literals and natural-number literals above one cell, `let`/`have`,
  holes `_`, tactic blocks `by` in the kernel form (natural LeanForth
  reads them, [tactic proofs](#tactic-proofs-read-and-run-once-statements-are-elaborated),
  and runs them once their statements are elaborated), `import`, and `_root_` in a declaration's
  name. Inductive types and structures are sketched in ADR 0017 only: a
  file uses them from a library export (`tests/author/08-monoid.lf` uses a
  class that Lean declared). `n lit#` is the literal n, `i proj# NAME` a
  projection.
- **Checking.** `leanforth check FILE.lf` checks the whole file when it
  ends, not each declaration at its `end NAME` (plan 8.2.1g); the prompt
  and Forth programs (`lf-prompt`, `lf[ … ]lf`) are not built (8.2.1e);
  `--json` and run records do not take a text yet.
- **One line per word and name.** A word that reads a name, a note and a
  `( … )` comment must have it on the same line; lines are at most 1023
  characters in a file.
- **Where LeanForth is stricter than Lean.** Lean chooses between two
  constants a name could mean (from two open namespaces, or one open and
  the root) by their types; LeanForth has no types here and asks for the
  full name (error 27). A name Lean reads as a field of a variable or
  constant (`h.symm`) is an unknown name: projections are not supported
  yet. `_root_.x` is written `root: x`. `export`, which gives a constant a
  second name, is not supported yet (error 54); so a name that Lean finds
  only through such an alias in its library is an unknown name here.
- **Printing.** In Lean notation an instance argument's name is shown in
  `fun [inst : C]` where Lean writes `fun [C]` when the printed body does
  not show the name (ADR 0017, example 8); the terms are the same. A Pi
  printed as `A B ->` comes back with the anonymous binder name, so a
  hygienic name there is not kept; Lean does not show such names either.
