# LeanForth language reference: theorems, proofs and tactics

> **IMPORTANT: keep this page current.** The implementation is changing
> fast. Whoever changes, adds, renames or retires a LeanForth word updates
> this page **in the same branch** (owner, 2026-11-15; `AGENTS.md`).
>
> **Status date: 2026-11-15**, written against `main` at the commit that
> added it, and rewritten the same day from the words' definitions. It
> lists what the definitions in `src/author/` and `src/front/` do and what
> the checked files under `tests/front/` and `tests/author/` show. Where a
> point could not be settled from the code, the entry says "(unclear from
> the code)".

**Who this is for.** You know mathematics, or Forth, or both. You do not
need to know Lean. Every technical word is explained in the
[glossary of concepts](#glossary-of-concepts) the first time it matters, and
each explanation ends with the matching Lean spelling, for readers who
want to compare.

**What LeanForth is.** LeanForth lets you write a theorem and its proof as
ordinary Forth text, and then has a small checking program (the *kernel*)
confirm that the proof is correct. The theorem prover and its language come
from Lean, a system for checking mathematical proofs; LeanForth reads the
same mathematics in a postfix (Forth-style) spelling.

**Notation.** A word is **implemented** when its definition exists on
`main`; it carries no mark. A word marked **`**`** is *designed but not yet
implemented* (or implemented only in part, as the entry says), and the entry
cites its design document. A `**` word is never shown as running input
except in a block marked "(design, not run)". Sample blocks cite the
checked file they come from; a block I wrote that no test checks is marked
"(illustration, not run)". Stack comments are explained in
[Reading this reference](#reading-this-reference).

**Trust.** The words build mathematical expressions and tactic steps. They
decide nothing. Only the kernel's check of the finished proof accepts a
theorem (`bin/leanforth check`, [the checker](COMMAND_LINE.md)). LeanForth
today re-checks proofs written in LeanForth text and proofs that Lean
exported; it does not claim that "LeanForth proved" anything by itself.

**Other pages.** The same words are also described in
[LEANFORTH_SYNTAX.md](LEANFORTH_SYNTAX.md) (user view, kernel-form examples),
[LEANFORTH_WORDS.md](../programming/LEANFORTH_WORDS.md) (programming
reference, every error code) and [ELABORATION.md](ELABORATION.md) (what the
elaborator fills in). Where they differ from this page, the code and this
page's dated status decide; report the difference.

**Two forms.** A file is **natural LeanForth** by default (the form of this
page: `0 n + n =`; Lean's elaborator fills in the hidden arguments). A file
that starts with `kernel-form` is in the **kernel form**, in which every
hidden argument and universe level is written out (`tests/author/*.lf`).
See [natural form and kernel form](#natural-form-and-kernel-form). Natural
files need the library's elaboration data (`--elab-data`); without it the
elaborator stops with error 139. Most words below work in both forms; the
"Kind" and "Function" cells say where a word is of one form only.

| Part | Contents |
| --- | --- |
| [Two annotated examples](#two-annotated-examples) | a one-line theorem and a three-theorem file, every line labelled |
| [Reading this reference](#reading-this-reference) | how a file is read, postfix order, symbols and how to say them, placeholders, stack letters, what the words change |
| [Glossary of concepts](#glossary-of-concepts) | declaration, binder, statement, tactic, goal, level and the other ideas the words work on |
| [Errors](#errors) | what an error message shows |
| [A. Theorems](#a-theorems) | declarations, binders, statements, `#check` |
| [B. Proof outlines](#b-proof-outlines) | the outline of a checked proof; labels and notes |
| [C. Proofs](#c-proofs) | proof terms |
| [D. Tactics](#d-tactics) | `:= by ... end`, every `by-` word |
| [E. Vocabulary tools](#e-vocabulary-tools) | finding words and names |
| [F. File input](#f-file-input) | `bin/leanforth check FILE.lf` |
| [G. Pretty printing](#g-pretty-printing) | `print`, outlines, `--latex`, notation |

---

## Two annotated examples

Both files are checked by the test suite and accepted by the kernel. In
the tables, "part" says what each line is. The words used are defined
below; the examples are here first so that you can see the shape of a
file. Lines that start with `\` are comments and are left out.

### A theorem of one line: `0 + 0 = 0`

File: `tests/front/s1-rfl.lf`.

| Line | Text | Part | What it does |
| --- | --- | --- | --- |
| 1 | `theorem t` | start of the declaration, with its **name** `t` | begins a theorem called `t` |
| 2 | `  0 0 + 0 =` | **statement** | in postfix: push `0`, push `0`, `+` adds them, push `0`, `=` builds the claim "(0 + 0) equals 0" |
| 3 | `:= by` | `:=` then `by` | `:=` ends the statement ("is proved by"); `by` says the proof is a list of tactics |
| 4 | `  by-rfl` | **tactic** | closes the goal "0 + 0 = 0": both sides are the same number once `0 + 0` is computed |
| 5 | `end t` | **end** | finishes the declaration; repeats the name `t` |

There is no binder, because the statement mentions no variable.

- Mathematics: 0 + 0 = 0.
- LeanForth: `theorem t  0 0 + 0 =  := by  by-rfl  end t`
- Lean: `theorem t : 0 + 0 = 0 := by rfl`

### Three theorems, one using the others: addition commutes

File: `tests/front/ps-add-comm.lf` (the owner's proof set; Lean twin in
`tests/front/s2-proofs.lean`). Lines are the file's own line numbers.

| Line | Text | Part |
| --- | --- | --- |
| 8 | `theorem ps_zero_add` | start, **name** |
| 9 | `  Nat explicit: n` | **binder**: a parameter `n`, a natural number |
| 10 | `  0 n + n =` | **statement**: `0 + n = n` |
| 11 | `:= by` | `:=`, `by` |
| 12 | `  n by-induction-with` | **tactic**: induction on `n`; it opens a block of alternatives |
| 13 | `  \| zero =>       by-rfl` | **case alternative** for `n = 0`, with its tactic |
| 14 | `  \| succ k ih =>  by-rw[ ' Nat.add_succ ih ]` | **case alternative** for `n = k + 1`; `k` and the hypothesis `ih` are named here; the tactic rewrites with two rules |
| 15 | `  by-end` | closes the block of alternatives |
| 16 | `end ps_zero_add` | **end** |
| 17 | `theorem ps_succ_add` | start, **name** |
| 18 | `  Nat explicit: n  Nat explicit: m` | two **binders** |
| 19 | `  n Nat.succ m + n m + Nat.succ =` | **statement**: `succ n + m = succ (n + m)` |
| 20 | `:= by` | `:=`, `by` |
| 21 | `  m by-induction-with` | **tactic**: induction on `m` |
| 22 | `  \| zero =>       by-rfl` | **case alternative** (zero) |
| 23 | `  \| succ k ih =>  by-rw[ ' Nat.add_succ ih ' Nat.add_succ ]` | **case alternative** (successor) |
| 24 | `  by-end` | closes the alternatives |
| 25 | `end ps_succ_add` | **end** |
| 26 | `theorem ps_add_comm` | start, **name** |
| 27 | `  Nat explicit: n  Nat explicit: m` | two **binders** |
| 28 | `  n m + m n + =` | **statement**: `n + m = m + n` |
| 29 | `:= by` | `:=`, `by` |
| 30 | `  m by-induction-with` | **tactic**: induction on `m` |
| 31 | `  \| zero =>       by-rw[ ' ps_zero_add ] by-rfl` | **case alternative**; `ps_zero_add` is the theorem of lines 8-16, **used as a rewrite rule**; the second tactic, `by-rfl`, closes what is left |
| 32 | `  \| succ k ih =>  by-rw[ ' Nat.add_succ ih ' ps_succ_add ]` | **case alternative**; uses `ps_succ_add`, lines 17-25 |
| 33 | `  by-end` | closes the alternatives |
| 34 | `end ps_add_comm` | **end** |

Each statement in three forms:

| Theorem | Mathematics | LeanForth statement | Lean |
| --- | --- | --- | --- |
| `ps_zero_add` | for every natural n: 0 + n = n | `0 n + n =` | `theorem ps_zero_add (n : Nat) : 0 + n = n` |
| `ps_succ_add` | for all n, m: (n + 1) + m = (n + m) + 1 | `n Nat.succ m + n m + Nat.succ =` | `theorem ps_succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m)` |
| `ps_add_comm` | for all n, m: n + m = m + n | `n m + m n + =` | `theorem ps_add_comm (n m : Nat) : n + m = m + n` |

The Lean proof of `ps_add_comm`, for comparison:

```lean
theorem ps_add_comm (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => rw [ps_zero_add]; rfl
  | succ k ih => rw [Nat.add_succ, ih, ps_succ_add]
```

(`Nat.succ n` is "the successor of n", that is n + 1. The tick `'` before
a theorem's name, as in `' Nat.add_succ`, means "the theorem itself, as
a rewrite rule"; see [D.5](#d5-by-rw--by-rewrite-).)

---

## Reading this reference

### How a file is read

**A file is Forth text; LeanForth words are the only words Forth sees.**
The file is read by Forth's own text interpreter, one line at a time
(`lfa-eval-line`, `src/author/runner.fs:185`: the line goes to Forth's
`EVALUATE`). Before each line, the runner sets Forth's *search order*
(the list of wordlists in which Forth looks a token up) to exactly three
wordlists, searched in this order (`lfa-order!`, `src/author/groups.fs:52`):

1. `lf-words`: the fixed LeanForth words (`theorem`, `explicit:`, `by-rfl`,
   `+`, `=`, `:=`, `end`, ...);
2. `lf-locals`: the names the current declaration has introduced
   (its variables, universe parameters and hypotheses);
3. `lf-consts`: the names of constants (the declarations made so far in
   the file and, with `--env`, the library's).

The three are ordinary Forth wordlists, but they are *private*: the caller's
own search order is saved before the run and restored after it
(`lfa-save`, `lfa-restore`, `runner.fs:93-99`). **Ordinary Forth words are
not reachable.** `dup`, `+` (as Forth's addition), `:`, `.` and the like are
not in the search order, so a `.lf` file cannot call them or define a Forth
word; the `+` you write is LeanForth's `+`, which builds an addition, not
Forth's. A token that no one of the three lists has and that is not a plain
decimal number is an error (codes 1 and 35).

**When a word runs.** The interpreter is in *interpret state* (Forth's
default, as opposed to compiling a `:` definition). In that state the
interpreter takes each token, finds its word and runs it at once, left to
right. So a LeanForth word runs at the moment the interpreter reaches it
in the text. The words do not make a program and run it later; most of them
only record something (a value on the stack, a binder, a tactic step).
Natural form adds one delay: the words before `end NAME` only record, and the
real work (turning the record into mathematics and running the tactics)
happens when `end NAME` is read ([below](#when-things-happen)).

**"Immediate".** In Forth an *immediate* word is one that runs even while
Forth is compiling a definition. LeanForth words are not immediate and do
not need to be: the file is never read in compile state. A run started
while Forth is compiling is refused (error 45, `runner.fs:133,184`), and
every line must end with Forth still interpreting. This page does not use
"compile time" in any other sense.

**Other facts about the reading.** A token that is a plain decimal number of at
most nine digits is a number; any other token that is no word is an error
(codes 1, 35). Names are case-sensitive even though Forth is not
(`groups.fs:12-20`). A line must have fewer than 1024 characters (error 39).

### When things happen

The file runs from the top to the bottom. Between declarations the words
are `namespace`, `open`, `end` (of a namespace), `kernel-form`, comments,
and an expression followed by `#check`; a file that stops inside a
declaration or with values left is error 33. `theorem NAME` (or `def`,
`axiom`) opens a declaration; binders, statement, `:=` and proof follow;
`end NAME` closes it.

1. *While the lines are read*, each word acts at once: it takes values off
   the stack and leaves new ones, and adds binders and tactic steps.
2. *At `end NAME`*, in natural form, the elaborator turns the recorded
   syntax into complete mathematical expressions, the tactics run, and the
   result is handed over as a finished declaration (`lfn-end-declaration`,
   `reader.fs:192`; `lft-end-proof`, `tactic-syntax.fs:312`).
3. *After the whole file has run*, `bin/leanforth check` hands every
   finished declaration to the kernel (`src/cli/check-lf.fs:196`).

The first error ends the run; later text is not read.

### Natural form and kernel form

In **natural form** you write `0 n + n =` and the elaborator (see
[elaboration](#elaboration)) supplies what Lean would infer: which type
each number has, which `+` is meant, hidden arguments. In the **kernel
form** nothing is inferred: every hidden argument and universe level is
written out, and a few words (`^`, `Sort`, `fun`, `forall`, `->`) exist
only there. The kernel form is what the checker finally works with.

### Postfix order, and what the symbols mean

**Postfix order.** An argument is written before the word that uses it.
`0 n + n =` means: push `0`; push `n`; `+` takes those two and builds the
sum `0 + n`; push `n`; `=` takes the sum and `n` and builds the claim
"`0 + n` equals `n`". In Lean it is `0 + n = n`. A name takes as many values
from the stack as the thing it names has explicit arguments, so
`xs List.length` is Lean's `xs.length`.

**`=` is never assignment.** In LeanForth, `=` builds the *proposition*
"a equals b": a statement that may be true or false and is to be proved. It
stores nothing and compares nothing at run time. `0 1 =` is a perfectly good
statement (a false one, which no proof can establish).

| Symbol | Say it as | What it is |
| --- | --- | --- |
| `=` | "equals" | builds the proposition "a equals b" from two values; never assignment |
| `:=` | "is proved by" (after a theorem's statement), "is defined as" (in a definition) | ends the statement and starts the proof (or, for `def`, the value) |
| `=>` | "gives" or "then" | ends the header of a case: `\| zero =>` reads "in the case zero: ..." |
| `\|` | "case" (from "bar") | starts one case alternative of an induction |
| `'` | "tick" | `' NAME` means "the theorem or function NAME itself, not applied to anything"; used for rewrite rules |
| `#check` | "check" | prints the type of the value before it; asserts nothing |
| `rfl` (here `by-rfl`) | "reflexivity" | the tactic that closes `a = a`, also when the two sides only become the same after computing |
| `by` | "by" | says the proof that follows is a list of tactics |
| `⊢` | "proves" or "turnstile" | in a printed goal, separates the hypotheses (left) from what is still to prove (right) |
| `$` | "apply" | gives a function one more argument |
| `≤` | "is at most" | builds the proposition "a is at most b" |

### Stack comments, parsed text and placeholders

The *stack* column shows only the data stack, in Forth notation
`( before -- after )`: what the word takes from the stack and what it
leaves, the top of the stack rightmost. Text that a word reads *itself*
from the rest of the line (it is *parsed*, in Forth's term) is never on
the stack. It is written in capitals in the *word* column, after the word,
as you type it. Text a parsing word reads is not run as words: in
`theorem foo` the token `foo` is a name for the word to use, not a word to
run. A parsing word that finds no token left on its line stops the run with
error 2.

**Placeholders** (the capitals in the word column), each defined once:

| Placeholder | What you write there |
| --- | --- |
| `NAME` | one name token: the name of a declaration, a universe parameter, a namespace, a label, or a constant (see [name](#name)) |
| `VAR-NAME` | one name token that becomes a new variable (the parameter a binder adds) |
| `HYP-NAME` | one name token that becomes a new hypothesis or a case's variable, for example `k` and `ih` in `\| succ k ih =>`; or `_` for one you will not use |
| `CASE-TAG` | the name of one case of an induction, as the type defines it: `zero` or `succ` for `Nat`; `nil` or `cons` for `List` |
| `KIND` | one of the words `theorem`, `def`, `axiom`, `import-stub` |
| `TEXT` | free characters, up to the closer the entry names (the end of the line, a `)`, or a `"`) |
| `...` | zero or more further tokens of the same sort, up to the terminator the entry names (for example `=>`) |

Examples of how the entries use them:

| Written | Meaning |
| --- | --- |
| `universe NAME` with stack `( -- )` | the word parses the next token on its line (one name) and leaves nothing on the stack |
| `by-case: CASE-TAG HYP-NAME ... =>` | it parses the case tag, then any number of hypothesis names, up to and including the terminator `=>` |
| `note" TEXT"` | it parses the characters up to the next `"` on the same line |
| `explicit: VAR-NAME` with stack `( v -- )` | it takes a value from the stack (the variable's type) and also parses a name |
| `+` with stack `( t1 t2 -- t3 )` | an ordinary word: two values in, one out |

### The stack letters: what a value is

In stack comments `t` is a *term* (a mathematical expression: see
[term](#term)), `s` a *statement* (a term that is a proposition), `v` any
LeanForth value, `c` a constant waiting for universe levels, `l` a universe
level or a plain number, and `n` a plain number. Several others are one-off:
`f` a function, `a` and `b` operands, `r` a rewrite rule.

**What such a letter is in memory.** Every one of them, `t`, `s`, `v`, `c`
and a level, is *one Forth cell* on the data stack. For all but plain
numbers the cell is a **negative number** `-(k+1)`: `k` is an index into
LeanForth's item store, a table of records, one per value made in the
current declaration, a heap store that grows as values are made (`lfa-items`, `src/author/values.fs`).
The record says what the value is (kind: term, level, name, constant,
or in natural form a syntax node) and holds the index of the expression
node in the term store (`src/core/terms.fs`). A plain number `n` is an
ordinary non-negative cell; a level written as a number is read as that
level. Natural form works in two steps: the cell first stands for a syntax
node; the elaborator makes the real expression at `end NAME`.

**What you can do with a value:** pass it to a word that takes one
(`+`, `=`, `$`, `explicit:`, `by-exact`, ...). A value can be used **once**:
the word that takes it marks it used, and a second use is error 34. A value
can be used only in the declaration and binder that made it. There is nothing
to inspect: Forth's `@` and `.` are not even in reach.

**Why it is not a Forth address.** An address could be copied and used again,
and could point at memory that has since been reused; the cell is an
index that is checked every time (a number, a used or stale value stops the
run, error 34), so a copy of a value can never stand for an expression
twice or after its binder has closed. The checker never trusts the cell
itself anyway; it checks the finished expression.

**The value stack.** The values LeanForth builds live on Forth's data stack
(called "the stack" in the tables). A word that needs `n` values checks that
they are above the *frame*: the stack depth where the innermost open binder
or the declaration began (`lfa-args`, `src/author/scopes.fs:83`); too few
is error 3. So the stack of one declaration is empty when it starts (error
15) and holds exactly one value, the statement, when `:=` comes.

### What the words change

The tables' "What it changes" column names the following parts of the
author's working state. Each is defined here once and in plain words.

| Name in the tables | What it is |
| --- | --- |
| the declaration | the record of the declaration being built: its kind, name, universe parameters, statement, proof, protected flag (`lfa-current` and `lfa-decls`; `src/author/declarations.fs:54-60`, `constants.fs:22-29`). It exists from `theorem NAME` to `end NAME`. See [declaration](#declaration) |
| the binder list | the parameters opened so far, innermost last: for each its name, kind, type and where it began (`lfa-binders`, `src/author/scopes.fs:20-28`). See [binder](#binder) |
| the locals | the names in the wordlist `lf-locals`: one word for each variable, universe parameter and hypothesis, made as the name is introduced and removed when its binder or block ends (`groups.fs`; `declarations.fs:111,119`). See [locals](#locals) |
| the value stack | Forth's data stack, as above |
| the syntax record | in natural form, the recorded syntax of the statement and proof, kept until `end NAME` (`lfn-decl`, `src/front/reader.fs:46-51`) |
| the tactic steps | the list with one entry per tactic word read, in order (`tac-steps`, `tac-args`; `src/front/tactic-syntax.fs:96-124`) |
| the goal list | while tactics run (at `end NAME`), the goals still to prove (`src/front/goals.fs`, `lf-goals`) |
| the namespaces | the namespaces entered and opened (`lfa-spaces`, `src/author/namespaces.fs:104-113`) |

---

## Glossary of concepts

Each concept: one line in plain words, then a few sentences, an example,
and "Lean:" for the Lean spelling. They are in the order a beginner needs
them. For the sense of "term" see [term](#term).

### name

**Meaning:** the label of a declaration, variable, universe parameter or
namespace.

A name is a *token*, that is, text between blanks (space, TAB, line ends).
It may hold any characters a line may hold (letters of any language, digits,
`_`, `'`, `!`, `?`, ...), except control and formatting characters (error 46).
A dot separates the *parts* of a name: `Nat.add_succ` has the parts `Nat`
(a namespace) and `add_succ`. A name has no empty part (`.a`, `a.`, `a..b`
are error 30). For the name of a declaration, universe, namespace or
hypothesis, a first character that is a digit, or one of `+ - # $ % & '`
with more text after it, is refused (error 30; error 35 for such a token
that is no name at all). A binder's name may look like a number: it then
gets no word, and `n var#` refers to the binder. A part that is only digits
is a number part (no leading zero; at most 18 digits on a 64-bit host, 9 on
a 32-bit one); `«123»` (with the guillemets) is the string `123`. Names are
case-sensitive: `n` and `N` differ. A declaration's full name may be 256
characters (error 62). `[anonymous]` is the name of a binder that has none.
*Hygienic names* are Lean's invisible names made by macros (`HAdd.hAdd✝`);
you never write them. LeanForth uses them for its operator words: `+` means
the global constant `HAdd.hAdd`, whatever local variable or namespace is
around (`src/front/syntax.fs:19-21`). Example: `Nat.add_succ`. Lean:
identifiers (`Nat.add_succ`, `n`, `zero_add''`).

### declaration

**Meaning:** a named item added to the library: a theorem, definition or
axiom.

A declaration has a name, a type, and sometimes a value. A **theorem** has
a statement (its type, a proposition) and a proof (its value): once proved it
is a fact you can use by name. An **axiom** has a statement and no proof: it
is assumed, and every theorem that uses it reports it (`axioms: none` is the
good case). A **def** (definition) has a type and a value that is data or a
function. `import-stub` stands for a constant that a library would provide;
the checker refuses it. Example: `theorem ps_zero_add ... end ps_zero_add`.
Lean: `theorem`, `axiom`, `def double (n : Nat) : Nat := n + n`.

### binder

**Meaning:** a parameter: a variable, with its type, that the declaration
is stated for.

Before `:=`, the binders are the *parameters* of the declaration; a user of
the theorem supplies a value for each explicit one. In LeanForth a binder is
written as its type, a binder word and its name: `Nat explicit: n` adds the
parameter `n`, of type `Nat`, to the theorem being written. It is not a
definition of `Nat`. Example: `Nat explicit: n` in `ps_zero_add`. Lean:
`(n : Nat)`.

**Binder kinds.** *Explicit* (`explicit:`), Lean's `(x : T)`: the user of the
theorem supplies it. *Implicit* (`implicit:`), `{x : T}`: Lean infers it from
other arguments. *Strict implicit* (`strict-implicit:`), `⦃x : T⦄`: like
implicit, but filled in only once a later explicit argument is given.
*Instance* (`instance:`), `[x : T]`: Lean finds it by *instance search*
(looking up a registered fact such as "Nat can be added"). The kind decides
how many arguments a name takes from the stack: only the explicit ones
(`src/present/binder-table.fs:36-39`).

### locals

**Meaning:** the names that are valid only inside the declaration being
written.

When a binder is opened, a word with the binder's name is added to the
wordlist `lf-locals`, so that writing `n` in the statement or proof refers to
the parameter. The same happens for universe parameters and for the
hypotheses a tactic names. These words are removed when their binder or block
ends, or at `end NAME`; nothing outside the declaration sees them. A name
spelt like a number gets no word. Lean: the local context (`n : Nat` above
the turnstile).

### statement, statement tree

**Meaning:** the proposition a theorem asserts; the *statement tree* is
that proposition as the syntax recorded so far.

The statement is the one value left on the stack when `:=` is read: for
`0 n + n =` it is "0 + n = n". It is a *type*: the proof is a value of that
type. In natural form the statement is first kept as a *syntax tree* (a tree
of the words you wrote: the `=` with the `+` below it, and so on) in the
syntax record, until `end NAME` turns it into a full expression.
Example: line 10 of `ps-add-comm.lf`. Lean: the text between `:` and
`:=` in `theorem t : statement := ...`.

### term

**Meaning:** a mathematical expression the kernel can check, of any
kind.

*Term* in this page always has the mathematical (Lean) meaning: a number,
a variable, a function, an application `f a`, a proposition such as
`0 + n = n`, or a proof. Every term has a *type*: `n` has type `Nat`; a
proof has as its type the proposition it proves. A *proof term* is a term
whose type is a theorem's statement; the kernel checks proof terms. (The
words "value" and "cell" are used for what lies on the Forth stack, which
stands for a term; see [the stack letters](#the-stack-letters-what-a-value-is).)
Example: `0 + n = n` is a term of type `Prop`; `Nat.zero_add n` is a term
whose type is that proposition. Lean: terms, types, proof terms.

### natural form and kernel form

**Meaning:** the two spellings of LeanForth text.

Natural form is how people write: you give what Lean would write and
leave the hidden parts out. Kernel form is the complete version, in which
every hidden argument is spelt out; it is what the kernel finally checks.
Elaboration (below) turns the first into the second. The checker accepts
both file kinds; a file starts in natural form unless its first
declaration-level word is `kernel-form`. Example: natural
`theorem t  0 0 + 0 =  := by  by-rfl  end t` (`tests/front/s1-rfl.lf`);
kernel form `tests/author/01-identity.lf` (below, section A.2). Lean: the
source text versus the fully elaborated expression.

### goal, hypothesis

**Meaning:** a goal is something still to be proved; a hypothesis is
something assumed while proving it.

While tactics run, a *goal* is a statement still to be proved, together with
what may be assumed. A *hypothesis* is one of those assumptions: a variable
`n : Nat`, or an assumption `ih : 0 + k = k`. A tactic step changes the goal
list: it closes a goal, or replaces it by simpler ones. Lean prints a goal as
`n : Nat ⊢ 0 + n = n` (read: from the hypothesis `n : Nat`, it proves
`0 + n = n`).

### tactic, tactic step, alternative

**Meaning:** a tactic is a command that changes the goal list; a *tactic
step* is one use of a tactic in the file; an *alternative* is the part of an
induction that handles one case.

A tactic tells the system how to build the proof: `by-rfl` ("the two sides are
equal by computation"), `by-exact` ("this expression is the proof"),
`by-rw[ ... ]` ("rewrite with these equations"), `by-induction-with` ("prove
it for zero, and from `k` to `k + 1`"). Each tactic word read adds one *step*
to the step list; the steps run at `end NAME`. An *alternative* is
`| CASE-TAG HYP-NAME ... =>` followed by the tactics for that case, for
example `| succ k ih => ...`: the tag names the case, the names after it
name that case's variables and hypotheses. The tactics only build a proof
term; the kernel checks it. Lean: `rfl`, `exact`, `rw`, `induction ... with`.

### namespace

**Meaning:** a prefix that groups names.

`Nat.add_succ` lives in the namespace `Nat`; inside `namespace Nat`,
`add_succ` alone finds it. A *protected* declaration is not found by its short
name through a namespace: `protected theorem Nat.foo` can be written
`Nat.foo` even inside `namespace Nat`, but not `foo`. `private` (visible only
in its file) has no LeanForth word. Lean: `namespace`, `open`, `protected`,
`private`.

### Sort and universe level

**Meaning:** every expression that is a type has a *sort*, a kind of "size
class", given by a number called the *universe level*.

The worked example:

| Expression | Is | Sort it belongs to |
| --- | --- | --- |
| `0 + 0 = 0` | a proposition | `Prop`, which is `Sort 0` |
| `Nat` (the natural numbers) | an ordinary type | `Type`, which is `Sort 1` (so `Nat : Type`) |
| `Type` | a collection of types | `Type 1`, which is `Sort 2` (so `Type : Type 1`) |
| `Type 1` | a bigger collection | `Type 2`, which is `Sort 3` |

So `Sort l` is the sort at level `l`; `Prop = Sort 0`; `Type l = Sort (l + 1)`.
Each is one level up from what it contains. **Why levels exist:** if `Type`
held itself (`Type : Type`), one could build "the collection of all
collections that do not contain themselves", and the system would prove
false statements (Russell's paradox, in its type-theory form). Putting every
collection one level above its members avoids it. A *universe parameter*
is a level variable, `u`, that makes a declaration generic: `identity.{u}
{A : Sort u} (a : A) : A` holds for types of every level. `universe u`
after the declaration's name introduces one. In practice you need one only
when a statement is about an arbitrary type (`A : Sort u`, "for every type
A"); a statement about `Nat` or lists of `Nat` needs none. Lean: `Sort u`,
`Type u`, `Prop`, `universe u`.

### elaboration

**Meaning:** completing what you wrote into a full expression.

Lean's elaborator finds the type of each part, supplies hidden arguments,
finds instances and decides what a numeral like `0` means (here `OfNat Nat
0`, "the number 0 as a natural"). LeanForth's elaborator (`src/front/`) does
the same steps, at `end NAME` or at `#check`, as the pinned Lean does; see
[ELABORATION.md](ELABORATION.md). Lean: the elaborator.

### kernel

**Meaning:** the small program that checks proof terms.

The kernel accepts an expression only if its type is correct. Words,
elaborator and tactics are untrusted; only an accepted kernel check makes a
theorem true. After a theorem is accepted the checker lists the *axioms* its
proof depends on (`accepted; axioms: none`). A proof closed with `by-sorry`
depends on `sorryAx`: it is accepted but reported NOT PROVED. Lean: the
kernel (`Lean.Environment.addDecl`).

### motive

**Meaning:** the statement-valued function that an induction or a rewrite
works with.

Induction on `n` in `0 + n = n` uses the function `fun n => 0 + n = n`: the
zero case proves it at zero, the step case from `k` to `k + 1`. For a
rewrite with `a = b`, the motive is the goal with `a` replaced by a
variable. LeanForth builds it as Lean does and type-checks it (errors 212,
216, 217). Lean: the motive of `Nat.rec`; `Eq.mpr`.

### rewrite rule

**Meaning:** an equation `a = b` used to replace `a` by `b` in the goal.

A rule is a proof of an equation: a hypothesis written by name, or a
theorem written `' NAME`. Rewriting finds the left side of the equation in
the goal and replaces it by the right side. **Worked example.** The goal is
`0 + (k + 1) = k + 1`. The rule is `Nat.add_succ : n + succ m = succ (n + m)`
("adding a successor: n plus the successor of m is the successor of n plus
m"). The rule's left side, `n + succ m`, matches the goal's left side
`0 + succ k` (written `k + 1` above) with `n := 0` and `m := k`. Each match
is replaced by the right side, `succ (0 + k)`. The goal after the rewrite
is `succ (0 + k) = succ k`. A second rule, the hypothesis `ih : 0 + k = k`,
now matches `0 + k` and turns the goal into `succ k = succ k`, which `rfl`
closes. In LeanForth: `by-rw[ ' Nat.add_succ ih ]`. Lean: `rw [Nat.add_succ, ih]`.

---

## Errors

The first error stops the run. Every error prints:

- its **code**, a number that stays the same (`error 97`);
- the **position**, `line:col` (line and column of the place);
- the **token** where it stopped (the word or name being read);
- a **message in plain English**. For errors about the mathematics (a
  proof step that does not work), the message is Lean's own text; the goals
  are printed below it, as Lean prints them. Terms in the message name
  things as those goals do: a hypothesis that cannot be written (an
  inaccessible `n`) prints as `n✝`, a metavariable made for an unnamed
  binder as `?a✝` (`tests/front/s2w-case-under.lf`, `s2w-rw-lt.lf`).

Example, from the done-check `docs/development/done-checks/2026-11-14-s1.md`
(file `tests/front/s1-rfl-wrong.lf`, which claims `0 + 0 = 1` by `rfl`):

```text
error 97 at line:col 8:3 (token by-rfl): Tactic rfl failed:
  The left-hand side / 0 + 0 / is not definitionally equal to the right-hand side / 1 / ⊢ 0 + 0 = 1
```

(Printed on one line in the checker; wrapped here.) Read it: error 97, the
tactic `rfl` failed, at line 8, column 3, at the token `by-rfl`; the two sides
`0 + 0` and `1` are not the same once computed. The checker also exits
with a status: 2 not supported, 3 out of fuel, 4 refused ([F.2](#f2-the-commands)).
Tests pin the codes, never the wording. The catalogue of messages is
`src/author/errors.fs`; the codes with their causes are listed in
[the programming reference](../programming/LEANFORTH_WORDS.md#errors).

---

## A. Theorems

### A.1 Glossary

Errors named in the "Function" cells are codes of `src/author/errors.fs`.

| Word | Takes from the stack | How it reads the line | What it creates or changes | What it does |
| --- | --- | --- | --- | --- |
| `theorem NAME` | `( -- )` | reads one name from its line | opens a new [declaration](#declaration) of kind theorem, with no binders yet; the word NAME exists only after `end NAME` | Starts a theorem named NAME inside the current namespace; errors 2 no name, 14 inside a declaration, 15 values on the stack, 28 name already declared (also by the library), 30 bad name, 53 `_root_` in the name. |
| `def NAME` | `( -- )` | one name | as `theorem`, kind def | Starts a definition: the same, with a value instead of a proof. |
| `axiom NAME` | `( -- )` | one name | as `theorem`, kind axiom | Starts an axiom: binders and one statement, no `:=`; `end NAME` takes the statement. |
| `import-stub NAME` | `( -- )` | one name | as `theorem`, kind stub | Stands for a library constant; `bin/leanforth check` refuses it (error 48). |
| `protected KIND NAME` | `( -- )` | two names: first the kind word (`theorem`, `def`, `axiom` or `import-stub`), then the name | as that kind, and marks the declaration protected | Starts a declaration that short names cannot reach through a namespace; error 43 when the first token is no kind, 44 when the name has no namespace prefix. |
| `universe NAME` | `( -- )` | exactly one name; a second name is a new token to run | adds a [universe parameter](#sort-and-universe-level) called NAME to the declaration (at most 8): an entry NAME in the declaration's universe list, and a word NAME in the [locals](#locals) | Lets the declaration be generic over the sizes of types: Lean's `universe u` in `def identity.{u} {A : Sort u} (a : A) : A`. It must come right after the declaration's name, before any binder, value or `:=` (error 16), once per name (28), at most 8 (10). |
| `explicit: VAR-NAME` | `( v -- )`: the type of the new variable | one name | adds the **parameter** VAR-NAME of that type to the declaration being written: an entry in the declaration's binder list (name, kind explicit, type, position), and a word VAR-NAME in the locals that stands for the variable until the declaration ends (no word for `[anonymous]` or a number-like name). A user of the finished theorem supplies a value for it | Lean's `(name : T)`. `Nat explicit: n` reads "a parameter `n`, of type `Nat`". Errors 3 no type below, 2 no name, 65 too many binders. |
| `implicit: VAR-NAME` | `( v -- )` | one name | the same entry and word, with kind implicit | Lean's `{name : T}`: Lean infers the argument from the other ones. |
| `strict-implicit: VAR-NAME` | `( v -- )` | one name | as `implicit:`, kind strict implicit | Lean's `⦃name : T⦄`: inferred only once a later explicit argument is given. |
| `instance: VAR-NAME` | `( v -- )` | one name | as `implicit:`, kind instance | Lean's `[name : T]`: found by instance search. |
| `:=` | `( s -- )`: the statement | reads nothing; acts once per declaration | takes the statement off the stack and stores it in the declaration (in natural form as syntax, in kernel form as the finished type); the binders open now become the declaration's parameters | Ends the statement and starts the proof ("is proved by"; in a `def`, "is defined as"). Errors 17 not allowed here (outside a declaration, in an axiom, or a second `:=`), 18 the statement is not exactly one expression or a value sits between binders. |
| `end NAME` | `( -- )` | one name; inside a declaration it completes it, outside it leaves a namespace | completes the declaration: closes its binders around statement and proof, records its type and value, and makes the word NAME for later declarations; or leaves the namespaces | NAME must repeat the declaration's name (error 22) or name the namespaces to leave (22, 23). In natural form it runs the elaborator and the tactics (errors 19 `:=` missing, 20 proof not one expression, 21 binder still open, 82 block open, 86 value left over). |
| `namespace NAME` | `( -- )` | one name, may be dotted | enters one [namespace](#namespace) per part | Between declarations only (error 24); `namespace A.B` enters `A`, then `A.B`; more than 16 namespaces entered and opened together is error 25. |
| `open NAME` | `( -- )` | one name | marks the namespace opened (until the enclosing `end`) | Makes the names of namespace NAME findable by their short names; unknown namespace is error 26. |
| NAME of a constant or variable (a word you never define; the interpreter finds it) | `( v1 ... vk -- v )`: its k explicit arguments | none | takes its arguments, leaves one value | Applies the constant or variable to as many values as it has explicit arguments (k); errors 1 unknown, 27 ambiguous, 55 a short name of a library constant, 73 the count depends on unfolding a definition. |
| a numeral `0`, `2` | `( -- v )` | none (read by Forth, not a LeanForth word) | pushes a number and remembers where it was written | In natural form Lean's numeral, a plain decimal of at most nine digits; other number forms are error 35. |
| `' NAME` | `( -- v )` | reads the next token without consuming it; natural form only | the next name takes no arguments from the stack | The function or theorem NAME itself, applied to nothing ("tick NAME"); error 59 when no name follows on the line. |
| `$` | `( f a -- v )` | none | takes two values, leaves the application | One more argument: `f a $` is Lean's `f a`. |
| `+` `*` | `( a b -- v )` | none; natural form only (error 58 in kernel form) | takes two values, leaves the sum or product | Lean's `a + b` and `a * b`, as `binop%` of `HAdd.hAdd` and `HMul.hMul`. |
| `=` `≤` | `( a b -- v )` | none; natural form only | takes two values, leaves the *proposition* "a equals b" or "a is at most b" | Lean's `a = b` and `a ≤ b`, as `binrel%` of `Eq` and `LE.le`. `=` is never assignment. |
| `#check` | `( v -- )` | none; natural form; outside declarations only | counts the check; prints one line `EXPRESSION : TYPE`; adds no declaration | Elaborates the expression with no expected type and prints it with its type; inside a declaration it is error 140 (141 in a tactic block). |
| `kernel-form` | `( -- )` | none; acts outside declarations | switches the rest of the run to the kernel form | Error 57 inside a declaration. |
| `\ TEXT` | `( -- )` | the rest of the line | nothing | A comment to the end of the line. |
| `( TEXT)` | `( -- )` | text up to `)` on the same line | nothing | A comment; without `)` on its line it is error 42. |
| `->` | `( a b -- t )` | none; kernel form only | takes two types, leaves the function type | `A B ->` is Lean's `A → B`. |
| `fun` `forall` | `( v -- t )` | none; kernel form only | closes the innermost open binder around the one value above it | A λ (function) or a Π (for all) over that binder; errors 13 no binder open, 12 body not one expression. |
| `Prop` `Type` `Sort` `^` `var#` `lit#` `proj#` `level+` `level-max` `level-imax` `root:` | see [programming reference](../programming/LEANFORTH_WORDS.md#the-vocabulary) | kernel form only (natural form: error 70) | build kernel expressions and levels | Levels, de Bruijn variables, literals, projections and universe arguments written out. |
| `**` natural spellings `->`, `fun`, `forall`, `Prop`, `∃`, `_`, `let:`, `have:`, `show`, `⟨ ⟩`, `.NAME`, `@`, `++` and more | `( A B -- t )` etc. | designed: [FE2_TERMS.md §2.2](../design/FE2_TERMS.md) | n/a | Today error 70 in natural form; `_`, `let:`, `have`, `by` in kernel form are errors 51 and 52. |
| `**` `variable`, `section`, `set_option` | `( -- )` | designed: [FE2_TERMS.md §2.2](../design/FE2_TERMS.md) | n/a | Commands, not built. |

### A.2 The words

**Declarations.** `theorem`, `def` and `axiom` start a declaration on an
empty stack: they read one name from the line, make its record
(`lfa-declare`, `src/author/declarations.fs:90-92`: kind, full name = current
namespace plus NAME, no type, no value yet) and open its scope, in which
binders and values are counted from the current stack depth
(`lfa-open-scope`, line 83). The name becomes a word only at `end NAME`
(`lfa-register`, line 198), so a declaration cannot use itself. A theorem has
binders, then the statement (one term), then `:=`, then the proof (a term,
section C, or `by` and tactics, section D), then `end NAME`. A definition is
the same with a value; an axiom has no `:=`. Lean:
`theorem NAME (binders) : statement := proof`.

**`universe NAME`** reads exactly one token after it (`lfa-name-token`,
`src/author/namespaces.fs:34`), so `universe ALGEBRA geometry` declares one
parameter, `ALGEBRA`, and then runs `geometry` as the next word, which is an
unknown name (error 1) unless a constant is called that. A second parameter
needs its own `universe v`. The parameter is a word in the locals until the
declaration ends; in kernel form `u Sort implicit: A` uses it
(`tests/author/04-poly-identity.lf`). In natural form no word consumes a
universe name yet (`Sort`, `Type`, `^` are error 70 there; universe levels of
library constants are worked out by the elaborator), so a declared parameter
that the statement does not use is error 75 at `end` ("unused universe
parameter").

**`protected KIND NAME`** reads two tokens, the kind and the name; it is the
only word that reads another declaration word as text
(`lfa-w-protected`, `words.fs:39-41`). It sets the declaration's protected
flag (`lfa-protect`, `declarations.fs:96`). Lean: `protected theorem N.f`.

**`import-stub`** stands for a constant an import would provide;
`leanforth check` takes the library from `--env`, so the stub is error 48.

**`namespace`, `open`, `end`.** They work as in Lean, with Lean's name
resolution (`src/author/namespaces.fs`: innermost namespace first, protected
names hidden from one-part names, two candidates are error 27). A declaration
named `A.f` has its body resolved in namespace `A`, as Lean reads
`def A.f` as `namespace A def f end A`.

```text
\ tests/front/01-zero-add-rw.lf (statement and header; proof in D)
theorem zero_add''
  Nat explicit: n
  0 n + n =
:= by
  ...
end zero_add''
```

```text
\ tests/front/s1-now.lf: a statement with a bound variable, and a term proof
theorem self_eq
  Nat explicit: n
  n n =
:=
  n Eq.refl
end self_eq
```

Lean: `theorem self_eq (n : Nat) : n = n := Eq.refl n`.

**Binders.** `T explicit: x` takes the value T from the stack, reads the name
`x` and opens a binder `(x : T)` (`lfa-binder-open`, `declarations.fs:128`:
a record in the binders list with name, kind, type, start depth; a word `x`
in the locals). `Nat List explicit: xs` is `(xs : List Nat)`: the type is the
tree built before the binder word, here `Nat List`, the constant `List`
applied to `Nat`. Every binder before `:=` becomes a parameter of the
declaration (`lfa-params-tight`, `declarations.fs:149-152`: each parameter's
frame starts where the declaration's does, so no value stands between
binders). The words `implicit:`, `strict-implicit:` and `instance:` exist in
both forms; no checked natural-form file uses them (a binder kind the
elaboration does not give is error 136). The kernel form's `fun`, `forall` and
`->` close binders (`tests/author/01-identity.lf`, `02-composition.lf`).

```text
\ tests/front/ps-length-append.lf
theorem ps_length_append
  Nat List explicit: xs  Nat List explicit: ys
  xs ys HAppend.hAppend List.length  xs List.length ys List.length + =
:= by
  ...
end ps_length_append
```

```text
\ tests/author/01-identity.lf, kernel form (Lean: theorem identity {P : Prop} (proof : P) : P := proof)
kernel-form
theorem identity  Prop implicit: P  P explicit: proof  P  :=  proof  end identity
```

The second sample is a one-line reformatting of the first lines of
`tests/author/01-identity.lf` (illustration, not run; the file itself is
checked by `make test`).

**Statements in postfix form.** A statement is a term written in postfix:
`0 n + n =` is `0 + n = n`; the operator follows its two operands.
A name takes its explicit arguments from the stack, so `xs List.length` is
`xs.length` and `n Nat.succ` is `Nat.succ n`; the number of arguments comes
from the name's type (`lfn-const-arity`, `src/front/reader.fs:81`; for a
variable from its binder's type as written). `' NAME` pushes the function
unapplied (needed as a rewrite rule, section D) and `$` applies once more.
`+`, `*`, `=` and `≤` are Lean's `HAdd.hAdd`, `HMul.hMul`, `Eq` and
`LE.le`, in Lean's `binop%`/`binrel%` forms, so numerals and instances are
resolved as Lean does (default instances, instance search; see
[ELABORATION.md](ELABORATION.md)). Lean: `0 + n = n`.

```text
\ checked by tests/front/check_elab.py: 2 + 2 = 4, n + n = n + n, Nat.succ n = Nat.succ n
2 2 + 4 =
n n + n n + =
n Nat.succ n Nat.succ =
```

(Each line is a statement of `tests/front/s1-now.lf`: `two_add_two`,
`add_self`, `succ_eq`.) Other operator words (`<`, `∧`, `∨`, `¬`, ...), `→`, `∀` and `∃` are
**`**: natural spellings are designed in
[FE2_TERMS.md §2.2-2.3](../design/FE2_TERMS.md); natural-form `fun`,
`forall`, `Prop`, `->` stop with error 70 today.

**`#check`.** `EXPRESSION #check` (between declarations) elaborates the expression with no
expected type and prints `EXPRESSION : TYPE` (`edc-w-check`,
`src/front/elab-decl.fs:170`). It is never part of a verdict: a file of only
`#check` lines ends "nothing checked by the kernel", exit 0. Lean:
`#check 0 + 0 = 0`, which prints `0 + 0 = 0 : Prop`.

```text
\ tests/front/s1-check.lf (output: 0 + 0 = 0 : Prop)
0 0 + 0 = #check
```

```text
\ tests/front/s1-now.lf
Nat.zero Nat.zero = #check
Nat.zero Eq.refl #check
```

A bare constant (`Nat.zero #check`, Lean prints a signature) is error 137.

**`kernel-form`.** Outside a declaration it switches the file to the
kernel form of `tests/author/*.lf`; inside a declaration, error 57. See
[LEANFORTH_SYNTAX.md](LEANFORTH_SYNTAX.md) for the kernel-form examples.

**Comments.** `\ ...` discards the rest of the line (`lfa-w-backslash`,
`words.fs:18`); `( ... )` skips to `)`, which must be on the same line.

---

## B. Proof outlines

A *proof outline* is a printed, step-by-step reading of an accepted proof.
It is untrusted presentation: its sentences are not checked reasoning, and
each line names the checker steps behind it
([PROOF_OUTLINE.md](PROOF_OUTLINE.md)). Printing is section G; this
section is the words in the text that go into it.

### B.1 Glossary

| Word | Takes from the stack | How it reads the line | What it creates or changes | What it does |
| --- | --- | --- | --- | --- |
| `label: NAME` | `( v -- v' )` | parsing: one name; kernel form only (natural form: error 70) | gives the term its own node and adds a label entry to the note table (`src/present/note-table.fs`) | Names the step that built the value on top, so the printer can refer to it; a label repeated in one declaration is error 29, a missing name is 2. |
| `note" TEXT"` | `( v -- v' )` | parsing: the text up to the next `"` on its line; kernel form only | as `label:`, entry kind person | Attaches a note by a person; no closing `"` on the line is error 37. |
| `ai-note" TEXT"` | `( v -- v' )` | parsing: as `note"`; kernel form only | as `label:`, entry kind AI | Attaches a note tagged as written by an AI. |
| `**` English line per tactic step (plan 8.6.12) | | designed in [S2_INTERFACE.md](../design/S2_INTERFACE.md), `--steps` | n/a | Not on main. |

### B.2 The words

`label:` and the two note words attach a name or a sentence to the term on
the stack: each takes the value, makes a fresh node for the same term
(`lfa-step`, `src/author/words.fs:103`), records the label or note with its
source position in the note table (`lfa-note!`, line 104) and leaves a new
value. The printer shows them again; they exist in the kernel form
(`tests/author/09a-chain-draft.lf`, `09b-chain-edit.lf`). Notes never
change the term, so editing a note does not change a verdict. Too many
labels and notes is error 67. Lean has no equivalent; the nearest is a
comment.

```text
\ tests/author/09a-chain-draft.lf, kernel form (excerpt)
h  g  f a $   label: to-B  ai-note" f turns the proof a of A into a proof of B"
      $       label: to-C  ai-note" g turns that into a proof of C"
   $          label: to-D  note" h finishes the chain: a proof of D"
```

```text
\ (illustration, not run) a note on a natural-form term proof; label: and note" are
\ kernel-form words today, so this line stops with error 70 in natural form
n Nat.zero_add note" the library theorem 0 + n = n"
```

`**` Tactic steps do not yet carry notes. A printed English line per
tactic step ("explained proofs", plan 8.6.12) and `--steps` are designed in
[S2_INTERFACE.md](../design/S2_INTERFACE.md) and are not on main.

---

## C. Proofs

A proof of a theorem is either a term after `:=` (this section) or a tactic
block after `:= by` (section D). Whatever you write, the kernel checks the
term that results.

### C.1 Glossary

| Word | Takes from the stack | How it reads the line | What it creates or changes | What it does |
| --- | --- | --- | --- | --- |
| NAME of a theorem or constructor | `( a1 ... ak -- t )` | ordinary (resolved when run) | pops k values, pushes the application | Applies it to its explicit arguments: `n Eq.refl` is Lean's `Eq.refl n`; the elaborator supplies the hidden type and level. |
| `' NAME` | `( -- t )` | looks ahead; natural form | marks a pending tick | The constant itself, unapplied. |
| `$` | `( f a -- t )` | ordinary | pops two, pushes one | One more argument. |
| `Eq.refl`, `Nat.zero_add`, `congrArg`, ... | `( a -- t )` | ordinary names | as NAME | Any constant of the library named with `--env`; the count of values is its explicit arguments. |
| `^` | `( c l -- c' )` | ordinary; kernel form only | adds a universe argument to the constant | `Eq.refl 1 ^ Nat $ n $`: explicit universe levels with `^`, every argument with `$`. |
| `**` `fun`, `⟨ ⟩`, `show`, `▸`, `calc`, `let:` and `have:` in natural form | | designed: [FE2_TERMS.md §2.2](../design/FE2_TERMS.md) | n/a | Proof-term forms, not built. |

### C.2 The words

A proof term is a term whose type is the statement. Names are applied to
their explicit arguments exactly as in statements, so `n Eq.refl` builds
`Eq.refl n : n = n` and the elaborator supplies the hidden type and level.
At `end NAME` the proof is elaborated against the statement
(`edc-value`, `src/front/elab-decl.fs:132`; a mismatch is an elaboration error
with Lean's message, codes 125-139, and a hole left over is error 74).
Lean: `Eq.refl n`.

```text
\ tests/front/s1-now.lf: theorem self_eq, proof n Eq.refl
theorem self_eq
  Nat explicit: n
  n n =
:=
  n Eq.refl
end self_eq
```

```text
\ tests/front/s1-now.lf: theorem zero_eq_term, proof Nat.zero Eq.refl
theorem zero_eq_term
  Nat.zero Nat.zero =
:=
  Nat.zero Eq.refl
end zero_eq_term
```

A library theorem is used the same way. `n Nat.zero_add` is
`Nat.zero_add n : 0 + n = n`; the checked file
`tests/front/03-zero-add-exact.lf` uses it as the argument of `by-exact`
(section D), and the kernel-form `tests/author/07-add-comm.lf` uses
`Nat.add_comm n $ m $`.

```text
\ (illustration, not run) the same proof as a term, no tactics
theorem zero_add_term  Nat explicit: n   0 n + n =   :=   n Nat.zero_add   end zero_add_term
```

Lean: `theorem zero_add_term (n : Nat) : 0 + n = n := Nat.zero_add n`.
The kernel form's proof terms (`tests/author/19-add-zero.lf`,
`20-zero-add.lf`: `Nat.rec` with a motive, `congrArg Nat.succ ih`) are
the "assembly" form; see [LEANFORTH_SYNTAX.md](LEANFORTH_SYNTAX.md).
A proof that is wrong is stopped by the elaborator or the kernel:
`tests/author/wrong/19-add-zero.lf` (`Eq.refl n` for `0 + n = n`) is
rejected, as Lean rejects it.

---

## D. Tactics

A tactic proof is `:= by`, then tactic words, then `end NAME`. Each
tactic word starts with `by-` (the exceptions are the words that structure
the proof: `by`, `|`, `=>` and `]`). The words run in order on a list of
goals, the statement's goal first, as Lean runs them; LeanForth stops at the
first error, Lean goes on to report more. A tactic never makes a theorem
accepted: the term it builds is checked by the kernel.

**Two moments.** A tactic word *reads* when the file is run: it takes its
values from the stack, checks the shape (values, blocks, names) and appends a
**step** to the tactic step list (`tac-steps`, `src/front/tactic-syntax.fs`;
the values it took are kept as syntax trees in `tac-args`). Nothing is
proved yet. At **`end NAME`** the runner (`lfr-proof-end`,
`src/front/tactic-run.fs:511`) elaborates the statement, makes one goal for it,
and runs the steps in order against the goal list; each step closes or
replaces the first (main) goal and assigns the term that proves it. At the
end no goal may remain (error 89, "unsolved goals"). The tables name both:
"read" is the step recorded, "run" is what the step does to the goals.

**Hypotheses.** A name given at `by-intro: h` or in a header
`| succ k ih =>` becomes a word, a hypothesis, until the block that gave it
ends (`lft-entry!`, `tactic-syntax.fs:247`). Written alone it takes no
values; to apply it write `$` (`ih k $`).

**Apply, assumption, constructor.** These three words are ports of
Lean's tactics of the same names: they make the same choices, in the same
order, and build the same proof term (each is compared with pinned Lean
4.35.0 by `tests/front/tactics/*/check.py`).

- A *conclusion* is what a theorem says after its arguments. `Nat.le_succ`
  takes a number `n` and concludes `n ≤ n + 1`. `t by-apply` closes the main
  goal with `t` when `t`'s conclusion is the goal. Arguments the goal does
  not fix become new goals. Lean's order is kept: first the goals that no
  other new goal mentions, then the others. When there are several new
  goals, each is named after `t`'s argument (`case left`), put after the
  goal's own name inside an `induction ... with` alternative (`case
  zero.left`; `tests/front/tactics/apply/ap-tag-trans.lf`); a single new
  goal keeps the goal's name. No fit is error 380, with Lean's message; an
  instance argument that is found but differs from the one the goal fixes
  is error 384; a term still unknown after it is elaborated, which Lean
  would go on to work out, is not supported yet (error 99).
  Examples, from checked files: `' Nat.le_succ by-apply` proves
  `n ≤ n + 1` (`tests/front/tactics/apply/ap-le-succ.lf`); in
  `tests/front/tactics/apply/ap-and.lf`, `' And.intro by-apply` leaves the
  goals `case left` and `case right`. Mathematically: from n ≤ n + 1 for
  every n, conclude it for this n. Lean: `apply Nat.le_succ`. The goals
  it leaves may be closed by `by-exact` as well: after
  `' Nat.le_trans by-apply`, `' h1 by-exact` closes `a ≤ ?m` and so fixes
  `m`, and `' h2 by-exact` closes `?m ≤ c`
  (`tests/front/tactics/apply/ap-exact.lf`); `' h1 by-exact` on the
  second goal is Lean's Type mismatch, error 96, with `b ≤ c` as the type
  expected (`w-ap-exact.lf`).
- A *hypothesis* is a fact the theorem assumes, such as `h : a ≤ b`.
  `by-assumption` closes the main goal with the newest hypothesis whose
  statement is the goal, up to unfolding (definitional equality). None is
  error 381. Examples: `by-assumption` proves `a ≤ b` from `h : a ≤ b`
  (`tests/front/tactics/assumption/as-one.lf`) and `a ≤ a + 0` from
  `h : a ≤ a` (`as-defeq.lf`, since `a + 0` unfolds to `a`). Lean:
  `assumption`.
- An *inductive type* is a type made of listed *constructors*, the ways to
  build its values or proofs: `And` has one, `And.intro`; `Or` has two,
  `Or.inl` and `Or.inr`. `by-constructor` unfolds the goal until its head
  is an inductive type, then applies the first constructor that fits, as
  `by-apply` would. A goal that is no inductive type is error 382; no
  constructor that fits is error 383. When several fit, Lean also prints a
  warning; LeanForth prints none, and chooses the same one. Examples:
  `by-constructor` turns `a ≤ b ∧ b ≤ a` into the goals `case left` and
  `case right` (`tests/front/tactics/constructor/co-and.lf`), and proves
  `n ≤ n` by `Nat.le.refl` (`co-le.lf`). Lean: `constructor`.

**Left, right, exfalso, intros, clear.** Five more ports of Lean's tactics of
the same names (tactic batch 1, plan row TB1), compared with pinned Lean in
the same way (`tests/front/tactics/*/check.py`).

- `by-left` and `by-right` are `by-constructor` for an inductive type with
  exactly two constructors, taking the first or the second instead of the
  first that fits. Mathematically: to prove "P or Q", prove P (left) or
  prove Q (right). In LeanForth, with `h : a ≤ b`, the goal
  `a ≤ b ∨ b ≤ a` (written `a b ≤ b a ≤ Or`) becomes `a ≤ b` after
  `by-left` (the constructor `Or.inl`), which `' h by-exact` closes
  (`tests/front/tactics/left/le-or.lf`). In Lean: `left` then `exact h`.
  The goal is unfolded first: `a ≤ a + 1` unfolds to `Nat.le a (a + 1)`,
  whose constructors are `Nat.le.refl` and `Nat.le.step`, so `by-right`
  leaves `Nat.le a a` and `by-left` closes it
  (`tests/front/tactics/right/ri-le.lf`). A goal that is no inductive type
  is error 385 (`by-left`) or 387 (`by-right`); a type with another number
  of constructors (`And` has one) is 386 or 388; a constructor that does
  not fit the goal is apply's error 380, whose text names it "the term", as
  Lean's does.
- `False` is the proposition that has no proof: an inductive type with no
  constructor. From a proof of `False` anything follows (Lean's
  `False.elim`). `by-exfalso` replaces the goal, whatever it states, by
  `False`, keeping its name; the proof of `False` given afterwards proves
  the old goal through `False.elim`. Mathematically: a contradiction proves
  anything. In LeanForth, with `h : False`, `by-exfalso ' h by-exact`
  proves `a = b` (`tests/front/tactics/exfalso/ex-exact.lf`); in Lean,
  `exfalso` then `exact h`. After `' And.intro by-apply`, each new `False`
  goal keeps its name, `case left` and `case right`
  (`tests/front/tactics/exfalso/ex-tag.lf`). It has no error of its own.
- A *binder* is a `∀ x,` or an `A →` at the front of a goal: the goal
  `a ≤ b → a ≤ b` has one. `by-intros` makes every binder at the front of
  the goal a hypothesis. Each gets an *inaccessible* name, shown with a
  dagger (`a✝`): the text cannot write it, but `by-assumption` finds it.
  It unfolds nothing first, so `¬ a = b` (which unfolds to
  `a = b → False`) has no binder for it, and a goal with none is left as
  it is. In LeanForth, after `' Or.elim ' h $ by-apply` leaves the goals
  `a ≤ b → a ≤ b`, `by-intros by-assumption` closes each
  (`tests/front/tactics/intros/is-or.lf`); in Lean, `intros` then
  `assumption`. On `¬ a = b`, `by-intros` then `by-assumption` is
  assumption's error 381 (`tests/front/tactics/intros/w-is-not.lf`). A
  `let` or an instance binder `[x : C]` is not supported yet (99); naming
  the hypotheses, Lean's `intros x y`, is not either.
- `' h by-clear` removes the hypothesis or variable `h` from the goal's
  context. It is refused when another hypothesis mentions `h` (error 441,
  Lean's "variable 'h2' depends on 'h'"), when the goal does (442, "target
  depends on 'h'"), or when the term is no single hypothesis (389,
  "Unexpected term ...; expected single reference to variable"). In
  LeanForth, `' h2 by-clear` then `' h1 by-exact`
  (`tests/front/tactics/clear/cl-hyp.lf`); in Lean, `clear h2` then
  `exact h1`. `' a by-clear` with `h : a ≤ a` is error 441
  (`tests/front/tactics/clear/w-cl-dep.lf`). One hypothesis a word: Lean's
  `clear h1 h2` is two steps.

A statement's hypothesis is written with a tick when it stands alone,
`' h by-apply`, because its type is not unfolded to count its arguments
(error 73).

### D.1 Glossary

| Word | Takes from the stack | How it reads the line | What it creates or changes | What it does | Lean |
| --- | --- | --- | --- | --- | --- |
| `by` | `( -- )` | ordinary; right after `:=` only (error 69 elsewhere; natural form; error 51 in kernel form) | read: records the proof's position and opens the tactic block (step 0) | Marks that a tactic proof follows `:=`. | `:= by` |
| `by-rfl` | `( -- )` | ordinary | read: a step. Run: assigns the main goal `Eq.refl` and removes it from the goals | Closes the goal `a = b` when both sides are definitionally equal; otherwise error 97. | `rfl` |
| `by-exact` | `( t -- )` | ordinary | read: a step holding the term. Run: elaborates t against the goal, assigns it, removes the goal | Closes the goal with the term t; a goal named in either type may be assigned, as Lean's `exact` does; a type mismatch is error 96, a wrong number of values 86 or 87. | `exact t` |
| `by-intro: HYP-NAME` | `( -- )` | parsing: one name, or `_` | read: a step; HYP-NAME becomes a hypothesis word in the locals. Run: replaces the goal by one with the first binder introduced | Introduces one hypothesis HYP-NAME from the goal's first binder, of the binder's kind (explicit, implicit `{x}` or strict implicit `⦃x⦄`; an instance binder `[x]` is not supported yet, 99); `_` leaves it inaccessible (it cannot be written afterwards); error 94 when there is none, 84 when HYP-NAME is a LeanForth word. | `intro HYP-NAME` |
| `by-sorry` | `( -- )` | ordinary | read: a step. Run: assigns the goal `sorryAx T Bool.false`, records an open part | Closes the goal with an open part; the declaration is accepted but reported NOT PROVED. | `sorry` |
| `by-apply` | `( t -- )` | ordinary | read: a step holding t. Run: assigns the main goal t applied to new goals, which take its place | Closes the goal with t when t's conclusion fits it; t's arguments the goal does not fix become goals. No fit: error 380; an instance not found: 125; an instance found that differs from the one the goal fixes: 384; t still unknown after elaboration: 99 (not supported yet). | `apply t` |
| `by-assumption` | `( -- )` | ordinary | read: a step. Run: assigns the main goal the newest hypothesis whose type is the goal's, removes the goal | Closes the goal with a hypothesis; none fits: error 381. | `assumption` |
| `by-constructor` | `( -- )` | ordinary | read: a step. Run: as `by-apply` with the first constructor of the goal's inductive type that fits | Proves an `And`, `Or`, `True`, `≤`... goal by one of its constructors; the goal is no inductive type: 382; none fits: 383. | `constructor` |
| `by-left` | `( -- )` | ordinary | read: a step. Run: as `by-apply` with the first of the goal's two constructors | Proves an `Or`, `≤`... goal by its first constructor; the goal is no inductive type: 385; it has not two constructors: 386; the constructor does not fit: 380. | `left` |
| `by-right` | `( -- )` | ordinary | read: a step. Run: as `by-apply` with the second of the goal's two constructors | Proves an `Or`, `≤`... goal by its second constructor; the goal is no inductive type: 387; it has not two constructors: 388; the constructor does not fit: 380. | `right` |
| `by-exfalso` | `( -- )` | ordinary | read: a step. Run: assigns the main goal `False.elim` of a new goal `False`, which takes its place with its name | Turns any goal into `False`; no error of its own. | `exfalso` |
| `by-intros` | `( -- )` | ordinary | read: a step. Run: replaces the main goal by one with every leading binder introduced | Introduces all the goal's leading binders as inaccessible hypotheses, unfolding nothing; none leaves the goal as it is; a `let` or an instance binder: 99 (not supported yet). | `intros` |
| `by-clear` | `( t -- )` | ordinary | read: a step holding t. Run: replaces the main goal by one whose context lacks t | Removes the hypothesis t; t no hypothesis: 389; another hypothesis depends on it: 441; the goal does: 442. | `clear t` |
| `by-induction` | `( t -- )` | ordinary | read: a step holding t. Run: replaces the main goal by one goal per case | Induction on the variable t; the cases are left open (alone it ends in error 89). | `induction t` |
| `by-induction-with` | `( t -- )` | ordinary; opens a block that `by-end` closes | read: a block step holding t. Run: as `by-induction`, each case taken by an alternative | Induction on t with the cases written as alternatives. | `induction t with` |
| `\| CASE-TAG HYP-NAME ... =>` | `( -- )` | parsing: tokens of its line up to `=>`; only right inside `by-induction-with` (error 83 elsewhere) | read: an alternative block; the names become hypotheses until the alternative ends. Run: introduces the case's fields and runs the block | One alternative of an induction. CASE-TAG is the name of the case (`zero`, `succ`); each HYP-NAME becomes a new word for one of the case's variables or hypotheses (`k`, `ih` in `\| succ k ih =>`) until the alternative ends. The alternative ends at the next `\|` or at `by-end`. | `\| tag names =>` |
| `=>` | | read only by `\|` and `by-case:` as their terminator; run alone it is error 84 | none | Ends an alternative's header. | `=>` |
| `by-end` | `( -- )` | ordinary | read: closes the innermost `by-induction-with` or `by-case:` block | Closes the block; with none open, error 83. | indentation |
| `by-rw[` | `( -- )` | ordinary; opens a rule block that `]` closes | read: a block step. Run: rewrites the goal with each rule, then tries `by-rfl` | Starts a list of rewrite rules; every value built until `]` is a rule. | `rw [` |
| `by-rewrite[` | `( -- )` | ordinary; opens a rule block that `]` closes | read: as `by-rw[`. Run: rewrites with each rule, no `by-rfl` | The same without the closing `rfl`. | `rewrite [` |
| `]` | `( r1 ... rn -- )` | ordinary | read: the n values become the block's rules, in order; closes it | Ends the rule list of `by-rw[` or `by-rewrite[`; with none open, error 83. | `]` |
| `by-case: CASE-TAG HYP-NAME ...  =>` | `( -- )` | parsing: as `\|`; closed by `by-end` | read: a case block. Run: takes the goal of that tag (or whose tag ends or starts with it), renames its hidden hypotheses with the names, newest first | Works on one case after `by-induction`; errors 210 (no such tag), 211 (too many names), 89 (goal left at `=>`). | `case tag names =>` |
| `**` `by-decide` | `( -- )` | designed | n/a | Close a closed goal by evaluation. | `decide` |
| `**` `by-omega` | `( -- )` | designed | n/a | Linear arithmetic over `Nat` and `Int`. | `omega` |
| `**` `by-native-decide` | `( -- )` | designed; permanently unsupported (exit 2): it rests on `Lean.ofReduceBool` | n/a | n/a | `native_decide` |
| `**` `by-try`, `by-first`, `<;>` | | combinators; sketched in FE1G §4 and S2 §3 (the trail), no word fixed | n/a | n/a | `try`, `first`, `<;>` |
| `**` `by-alt: CASE-TAG HYP-NAME ... =>` | | an open question of the design: spelling alternatives without `\|` | n/a | n/a | `\| tag names =>` |
| `**` `by-refine`, `by-subst`, `by-cases` and others | | named in FE2 §3/FE5 as later tactics; no spelling is fixed | n/a | n/a | `refine`, `subst`, ... |

Designs: [FE1G_TACTICS.md](../design/FE1G_TACTICS.md) (the first tactics,
§3.2 words, §7 FE1i hook), [FE1I_AUTOMATION.md](../design/FE1I_AUTOMATION.md)
(§4 `by-decide`, §5 `by-omega`, stack table at line 266),
[S2_INTERFACE.md](../design/S2_INTERFACE.md) §4, §5 and appendix G
(induction and rewriting; it overrides FE1G where they differ).

### D.2 `by`, `by-end` and the block words

`by` must follow `:=` directly (`lfn-by-here?`, `src/front/reader.fs:177`: no
value, no binder opened since, not already seen; error 69 elsewhere) and, in
natural form, opens the first block, the proof (`lft-w-by`,
`tactic-syntax.fs:300`). At `end NAME` every block must be closed (82), and
no value may be left (86). `by-induction-with` opens a block of alternatives;
`by-end` closes it. Blocks nest. Mistakes in a shape each stop at their word
with a code, listed in the
[programming reference](../programming/LEANFORTH_WORDS.md#errors). A tactic
word outside a tactic proof is 81. An empty proof is read; it stops when run
with Lean's "unsolved goals" (89) at `by`.

```text
\ (illustration, not run; tests/front/05-unsolved.lf and s2w-rw-empty.lf are the checked cases)
theorem t   0 0 + 0 =   := by   end t
```

### D.3 `by-rfl`, `by-exact`, `by-intro:`, `by-sorry`

`by-rfl` is Lean's `rfl`: it closes `a = b` when both sides are
definitionally equal and builds `Eq.refl` (`src/front/tactics/rfl.fs`, on
the tactic library's `lf-goal-refl`). As in Lean, the goal may become an
equation only once a definition is unfolded: `a a = id`, Lean's
`id (a = a)`, is closed (`tests/front/s2-rfl-id.lf`). When the sides
differ, error 97 shows Lean's `apply_rfl` message, which unfolds only
reducible definitions first: for `a b = id` its sides are `Prop` and
`a = b`, the two arguments of `id` (`tests/front/s2w-rfl-id.lf`). `by-exact` takes a term from the
stack and closes the goal with it (`src/front/tactics/exact.fs`, on
`lf-close-main-goal-using`); a type mismatch is
error 96. `by-intro: HYP-NAME` reads NAME, makes it a hypothesis word and, when
run, introduces the goal's first binder as a hypothesis named NAME, usable
until the block ends, of the binder's own kind (explicit, implicit or strict
implicit, as Lean's `intro` since plan row TB1); with no binder left it is
error 94. `by-sorry` closes
the goal with `sorryAx`; the declaration is then accepted but reported NOT
PROVED, with each open part listed (`lfr-sorry`, `tactic-run.fs:391`).

```text
\ tests/front/s1-rfl.lf: accepted, term equal to Lean's node for node
theorem t
  0 0 + 0 =
:= by
  by-rfl
end t
```

```text
\ tests/front/03-zero-add-exact.lf (accepted on all of Init, done check 2026-11-14-s1)
theorem zero_add_ex Nat explicit: n   0 n + n =   := by  n Nat.zero_add by-exact   end zero_add_ex
```

```text
\ tests/front/s1-rfl-wrong.lf (reformatted here): stops at by-rfl with Lean's message (exit 4)
theorem t   0 0 + 1 =   := by   by-rfl   end t
```

Lean: `rfl`; `exact Nat.zero_add n`; the wrong twin gives Lean's
"Tactic `rfl` failed: The left-hand side 0 + 0 is not definitionally equal to the right-hand side 1". `by-intro:` is defined (`src/front/tactics/intro.fs`)
and run by that module's tests with a stand-in statement `p -> p`, because
natural `Prop` and `->` are still FE2; `tests/front/07-intro-exact.lf` shows
its form (not an end-to-end checked file today):

```text
\ tests/front/07-intro-exact.lf (the words as written; its statement is replaced in the unit test)
by-intro: h
h by-exact
```

```text
\ tests/front/06-sorry.lf: by-sorry (read; end-to-end run uses stand-in statements, see the file)
theorem zero_add_sorry   Nat explicit: n   0 n + n =   := by   by-sorry   end zero_add_sorry
```

### D.4 `by-induction`, `by-induction-with`, `|`, `by-end`

`n by-induction-with` is Lean's `induction n with`: `n` must be a variable
of an inductive type; the eliminator is the data's (`Nat.recAux`) or
`T.rec`. When run it replaces the main goal by one goal per case and builds
the motive from the goal. Each `| CASE-TAG HYP-NAME ... =>` alternative takes its
case's goal and names its explicit fields (`| succ k ih =>`: the number `k`
and the hypothesis `ih : 0 + k = k`). The header is on one line: `|` reads
the tag and the names up to `=>` (`lft-header`, `tactic-syntax.fs:276`);
a header whose line ends before `=>` is error 84, and the tag and names must not
be LeanForth words. Blocks nest; an inner `ih` hides the outer one. Errors:
205 no inductive type, 206 a name of no case (`suc`), 207 a case not written,
208 too many names, 209 mutual or nested types, 213 a name written twice, 99 a
form not ported (a target that is no variable, hypotheses depending on it,
index targets). Plain `n by-induction` is defined too: it makes one goal per
case and leaves them open, so alone it ends in error 89
(`tests/front/s2w-induction-plain.lf`); its cases are meant for `by-case:`
(D.6), or use `by-induction-with`.

```text
\ tests/front/01-zero-add-rw.lf: accepted by the kernel with the S2 slice, term equal to Lean's
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

```text
\ tests/front/04-nested-ih.lf: an induction inside an alternative
theorem zero_add_nested
  Nat explicit: n  Nat explicit: m
  0 n + n =
:= by
  n by-induction-with
  | zero =>       by-rfl
  | succ k ih =>
    m by-induction-with
    | zero =>       by-rw[ ' Nat.add_succ ih ]
    | succ j ih =>  ih by-exact
    by-end
  by-end
end zero_add_nested
```

Lean: `induction n with | zero => rfl | succ k ih => rw [Nat.add_succ, ih]`.
Wrong twins: `tests/front/s2w-alt-name.lf` (`| suc k ih =>`, error 206),
`s2w-alt-missing.lf` (a case left out, 207), `s2w-alt-names.lf` (too many
names, 208), `s2w-alt-twice.lf` (213), `s2w-induction-plain.lf` (89).

### D.5 `by-rw[ ]`, `by-rewrite[ ]`

In plain words: each rule is an equation `a = b`; the tactic finds `a` in the
goal and writes `b` in its place, one rule after the other, then closes
the goal by `rfl` if the two sides have become the same. A worked example
is under [rewrite rule](#rewrite-rule): with the rule `Nat.add_succ`, the goal
`0 + (k + 1) = k + 1` becomes `succ (0 + k) = succ k`.

`by-rw[ r1 r2 ... ]` is Lean's `rw [r1, r2, ...]`: each rule is a
hypothesis (written by name) or a theorem written `' NAME`; its equation's
left side is abstracted wherever it occurs in the goal (`kabstract` at
reducible transparency), the motive is type-checked, and the goal becomes
the rewritten one; then `rfl` is tried at reducible transparency
(`trw-w-rw`, `src/front/tactics/rewrite.fs`, on the tactic library's
`lf-goal-rewrite`, `src/front/meta-tactic/rewrite.fs`).
`by-rewrite[ ... ]` is `rewrite` and does not try `rfl` (`trw-rules`). The rules
are the values built between `by-rw[` and `]`; each stays on the stack until
`]` takes them, in order. Every value between the brackets is a rule, so an
applied hypothesis is written with `$`: `ih k $` is Lean's `ih k`. No tactic
word may stand inside the brackets (error 82). Errors: 215 no occurrence of
the pattern, 216 motive not type correct, 217 dependent motive, 218 no
equation, 219 a metavariable pattern, 220 the occurs check, 99 a form not
ported (a definition as a rule, `Iff`, an instance binder). An instance a
rule's term leaves open that none fills is Lean's own error, as for a
term anywhere: 125 "failed to synthesize instance of type class" with the
class below it, or 126 when the problem is stuck (`by-apply` and
`by-constructor` the same). Not yet (`**`, S2
merge B and later): `←`, `at h`, `using`, `generalizing`, and `++` as a word.

```text
\ tests/front/ps-succ-add.lf (the owner's proof set; accepted, term pinned to Lean's)
theorem ps_succ_add
  Nat explicit: n  Nat explicit: m
  n Nat.succ m + n m + Nat.succ =
:= by
  m by-induction-with
  | zero =>       by-rfl
  | succ k ih =>  by-rw[ ' Nat.add_succ ih ' Nat.add_succ ]
  by-end
end ps_succ_add
```

The zero case is closed by `by-rfl`: `Nat.succ n + 0` unfolds to
`Nat.succ n` and `Nat.succ (n + 0)` to `Nat.succ n`. `by-rfl` also closes
`n + (m + 0) = n + m + 0` (`ps-mul-add.lf`): `Nat.add n (m + 0)` does not
unfold (its match is stuck on `m`), the other side does, and the two then
agree, as in Lean.

```text
\ tests/front/ps-length-append.lf (excerpt: rewriting with earlier theorems)
  | nil =>           by-rw[ ' List.nil_append ' List.length_nil ' ps_zero_add ]
  | cons x t ih =>   by-rw[ ' List.cons_append ' List.length_cons ' List.length_cons ih ' ps_succ_add ]
```

The other files of the owner's set are `ps-add-comm.lf` and `ps-mul-add.lf`.
Wrong twins: `s2w-rw-empty.lf` (`by-rw[ ]` leaves the goal: 89),
`s2w-rw-definition.lf` (a definition as a rule, 99), and `s2w-rw-unsolved.lf`,
`s2w-not-eq.lf`, `s2w-pattern.lf`, each refused with Lean's first message.

### D.6 `by-case:`

`by-case: CASE-TAG HYP-NAME ... =>` ... `by-end` is Lean's `case CASE-TAG
HYP-NAME ... =>` (`src/front/tactics/case.fs`). It picks one open goal by
its case tag. It looks for the tag itself first, then for a tag that ends
with it (`zero` finds `succ.zero`), then for one that starts with it
(`succ` finds `succ.zero`). The names rename the goal's hidden hypotheses
(shown `n✝`), newest first: the last name goes to the newest one. An older
hypothesis hidden by a newer one of the same name is renamed too. A newer
hidden hypothesis does not hide an older visible one. `_` skips a
hypothesis. Names that are all `_` change nothing, so they are never too
many. The block then works on that goal alone and must close it. The
other goals come back after `by-end`, in their order.

The tag must be a name. Lean's other tag forms are refused, not supported
yet (error 72, plan FE5): the tag `_`, a tag written `@tag`, and a second
tag (`case t1 | t2 =>`).

Errors: 210 "Case tag `suc` not found.", then Lean's note or hint ("There
are no cases to select.", "The only available case tag is `succ`." or
"Available tags:"; Lean's previews of each tag after the hint are not
printed); 211 "too many variable names provided"; 89 unsolved goals at the
block's `=>`.

```text
\ tests/front/01-zero-add.lf: accepted with the S2 slice, term equal to Lean's
theorem zero_add'
  Nat explicit: n
  0 n + n =
:= by
  n by-induction
  by-case: zero =>       by-rfl                           by-end
  by-case: succ k ih =>  ' Nat.succ ih congrArg by-exact  by-end
end zero_add'
```

More cases are in `tests/front/s2-case.lf` (cases in another order, a tag
found by its end or its start, the exact tag before a tag that ends with
it, a hidden older `k`, `_`, the other goals in their order). Wrong twins:
`s2w-case-tag.lf`, `s2w-case-tags.lf`, `s2w-case-none.lf`,
`s2w-case-suffix.lf` (210), `s2w-case-names.lf` and `s2w-case-newer.lf`
(211), `s2w-case-unsolved.lf` and `s2w-case-shadow.lf` (89),
`s2w-case-under.lf` (97: three `_` are not too many, then `rfl` fails),
each refused with Lean's first message.

### D.7 `by-decide`, `by-omega`, `by-native-decide`, combinators (`**`)

Designed in [FE1I_AUTOMATION.md](../design/FE1I_AUTOMATION.md): `by-decide`
evaluates a closed decidable statement (`2 2 + 4 =`); `by-omega` closes
linear arithmetic over `Nat` and `Int` with every hypothesis in context (a
port of Lean's `omega`); `by-native-decide` always answers unsupported,
exit 2. `by-try`, `by-first`, `<;>` are mentioned in
[FE1G_TACTICS.md](../design/FE1G_TACTICS.md) §3 and §5 without a fixed
spelling. None of these words exists on main; `src/front/tactic-run.fs`
has rows for the eleven implemented kinds only.

```text
\ (design, not run) FE1I_AUTOMATION.md section 1
theorem two_add_two  2 2 + 4 =  := by  by-decide  end two_add_two
theorem zero_add_auto  Nat explicit: n  0 n + n =  := by  by-omega  end zero_add_auto
```

Lean: `decide`, `omega`.

---

## E. Vocabulary tools

There are no LeanForth words that list or look up words, names or
namespaces (grepped in `src/author/`, `src/front/` and `src/cli/` on
2026-11-15; none found). What exists:

| Tool | Stack comment | Function |
| --- | --- | --- |
| `EXPRESSION #check` | `( v -- )` | the type of a term, which finds what a name means (section A) |
| `namespace`, `open` | `( -- )` | change which names a short name means |
| `leanforth print --lf EXPORT` | command line | write a Lean export as one LeanForth text, to see the words and names |
| `lf-words`, `lf-locals`, `lf-consts` | Forth wordlists | the search order while a file runs; inspect from Forth (`src/author/groups.fs`) |
| `**` a command that lists words, a namespace's names, or a constant's signature (`Nat.zero #check` printing a signature is error 137) | | not designed as a word yet; signature form in [FE2_TERMS.md §2.2](../design/FE2_TERMS.md) (`#check` with `' NAME`) |

A name is Lean's own: the word `Nat.add_succ` exists for a library constant
when `--env` provides it; a word of that name is made for each name of the
text before its line runs. Errors 1 (unknown name), 26 (unknown namespace)
and 38 (unknown constant) say when a name is not found.

```text
\ tests/front/s1-now.lf
Nat.zero Eq.refl #check
```

```console
$ bin/leanforth print --lf tests/reference/composition.ndjson   # (illustration, not run here)
```

---

## F. File input

### F.1 Glossary

| Command | Function |
| --- | --- |
| `bin/leanforth check FILE.lf` | run the text, check every declaration with the kernel |
| `... check --env EXPORT FILE.lf` | the library comes from a Lean export |
| `... check --snapshot FILE FILE.lf` | the library from a saved snapshot (development mode, labelled) |
| `... check --elab-data FILE FILE.lf` | the library's elaboration data (instances, eliminators), needed by every natural file |
| `--elab-fuel N` | steps the elaborator may take per declaration (default 100,000,000; out of them is 138, exit 3) |
| `--fuel N` | the kernel's fuel |

### F.2 The commands

`bin/leanforth check FILE.lf` runs the file in the checker's own Gforth
with only LeanForth's words visible, builds the declarations, and hands
them to the kernel. A file that stops with an error is not checked;
the error is printed with line and column and an exit status (2 not
supported, 4 refused, 3 out of fuel). Exit 0 means every declaration was
accepted; a theorem proved with `by-sorry` is accepted but reported NOT
PROVED. A text of only `#check` lines checks nothing, exit 0.
Natural-form files need both `--env` (or `--snapshot`) and `--elab-data`.

```console
$ bin/leanforth check --env tests/front/s1-slice.ndjson \
    --elab-data tests/front/s1-slice.elab.ndjson tests/front/s1-rfl.lf
...
t: accepted; axioms: none
```

```console
$ bin/leanforth check --env tests/front/s2-slice.ndjson \
    --elab-data tests/front/s2-slice.elab.ndjson tests/front/01-zero-add-rw.lf
...
zero_add'': accepted; axioms: none
```

(From [ELABORATION.md](ELABORATION.md), run by `tests/front/check_elab.py`
and `check_s2.py`.) A kernel-form file needs only `--env`:
`bin/leanforth check --env tests/author/init-slice.ndjson tests/author/19-add-zero.lf`
(from [LEANFORTH_SYNTAX.md](LEANFORTH_SYNTAX.md#checking-a-file)).
`**` `import` and `export` lines are not supported (`import` is error 51, `export` error 54);
`section` is designed in FE2 only.

---

## G. Pretty printing

### G.1 Glossary

| Tool | Stack comment / command | Function |
| --- | --- | --- |
| `leanforth print [--name NAME] EXPORT` | command line | check, then print each accepted declaration's proof outline |
| `--detail` | `print` option | every step of the checker's log instead of the outline |
| `--latex` | `print` option | outlines as LaTeX fragments |
| `--statement lean,text,mathematics,leanforth` or `all` | `print` option | which forms of the statement to show |
| `leanforth print --lf EXPORT` | command line | write the export as LeanForth text (first line `kernel-form`) |
| `lf-author-print` | `( fuel -- outcome )` | print the run's declarations as words |
| `lf-print-forth-term`, `lf-print-forth-decl` | `( term fuel -- outcome )`, `( decl fuel -- outcome )` | a term or a declaration as words |
| `lf-outline-latex!` | `( flag -- )` | the outline printer's LaTeX switch |
| `**` printing a natural-form declaration back as natural LeanForth | | the printer writes the kernel form today |

### G.2 The tools

`leanforth print EXPORT` checks the export and prints, for each accepted
declaration, the verdict with its axioms, the statement in the chosen
forms (Lean notation, math text, LaTeX mathematics, LeanForth words) and
an outline in which every line names the checker steps behind it
([PROOF_OUTLINE.md](PROOF_OUTLINE.md), [TERM_PRINTER.md](TERM_PRINTER.md)).
`--latex` writes the outline as LaTeX. The notation table
(`src/present/notation-table.fs`) maps each operator word to the constant
it stands for (`+` to `HAdd.hAdd`, `=` to `Eq`, `≤` to `LE.le`), and the
reader checks the words against it when it loads. The printed words, run
again, give the identical term (`lf-author-print`, tested for every example
file), so printing a file writes its normal form.

```console
$ bin/leanforth print tests/reference/composition.ndjson
```

(Output in [COMMAND_LINE.md](COMMAND_LINE.md#printing-a-readable-proof);
illustration, not run here.)

```text
\ from LEANFORTH_SYNTAX.md "Printing a proof back as words": the printer's normal form
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

---

## Where words are defined

| Area | Files |
| --- | --- |
| declarations, kernel form, names | `src/author/words.fs`, `declarations.fs`, `namespaces.fs`, `runner.fs` |
| natural form, syntax tree | `src/front/reader.fs`, `syntax.fs` |
| tactics | `src/front/tactic-syntax.fs` (reading), `tactic-run.fs` (runner, `by-sorry`), `tactics/intro.fs`, `exact.fs`, `rfl.fs` (`by-intro:`, `by-exact`, `by-rfl`, on `meta-tactic/goal.fs`), `tactics/rewrite.fs` (`by-rewrite[`, `by-rw[`, on `meta-tactic/rewrite.fs`), `tactics/induction.fs` and `case.fs` (`by-induction`, `by-induction-with`, `by-case:`, on `meta-tactic/elim.fs`, `rename.fs` and `tactic-alts.fs`) |
| elaboration and `#check` | `src/front/elab-*.fs` |
| printing | `src/present/` |
| command line | `src/cli/leanforth.fs`, `check-lf.fs` |
