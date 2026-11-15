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

**Notation.** A word is **implemented** when its definition exists on
`main`; it carries no mark. A word marked **`**`** is *designed but not yet
implemented* (or implemented only in part, as the entry says), and the entry
cites its design document. A `**` word is never shown as running input
except in a block marked "(design, not run)". Sample blocks cite the
checked file they come from; a block I wrote that no test checks is marked
"(illustration, not run)". Stack comments are explained in
[Reading this reference](#reading-this-reference).

**Trust.** The words build terms and tactic steps. They decide nothing.
Only the kernel's check of the term accepts a theorem
(`bin/leanforth check`, [the checker](COMMAND_LINE.md)). LeanForth today
re-checks proofs written in LeanForth text and proofs that Lean exported;
it does not claim that "LeanForth proved" anything by itself.

**Other pages.** The same words are also described in
[LEANFORTH_SYNTAX.md](LEANFORTH_SYNTAX.md) (user view, kernel-form examples),
[LEANFORTH_WORDS.md](../programming/LEANFORTH_WORDS.md) (programming
reference, every error code) and [ELABORATION.md](ELABORATION.md) (what the
elaborator fills in). Where they differ from this page, the code and this
page's dated status decide; report the difference.

**Two forms.** A file is **natural LeanForth** by default (the form of this
page: `0 n + n =`, Lean's elaborator fills in hidden arguments). A file that
starts with `kernel-form` is in the **kernel form**, in which every hidden
argument and universe level is written out (`tests/author/*.lf`). Natural
forms need the library's elaboration data: `--elab-data`; without it the
elaborator stops with error 139. Most words below work in both forms; the
"Kind" and "Function" cells say where a word is of one form only.

| Part | Contents |
| --- | --- |
| [Reading this reference](#reading-this-reference) | stack comments, postfix order, the term stack, the authoring state |
| [Terms](#terms) | what NAME, universe, binder, goal, tactic and the other terms of the tables mean |
| [A. Theorems](#a-theorems) | declarations, binders, statements, `#check` |
| [B. Proof outlines](#b-proof-outlines) | the outline of a checked proof; labels and notes |
| [C. Proofs](#c-proofs) | proof terms |
| [D. Tactics](#d-tactics) | `:= by ... end`, every `by-` word |
| [E. Vocabulary tools](#e-vocabulary-tools) | finding words and names |
| [F. File input](#f-file-input) | `bin/leanforth check FILE.lf` |
| [G. Pretty printing](#g-pretty-printing) | `print`, outlines, `--latex`, notation |

---

## Reading this reference

**LeanForth is Forth.** A LeanForth file is read by Forth's own text
interpreter, one line at a time, with a private search order that holds only
LeanForth's words (`src/author/runner.fs`, `lfa-eval-line`, line 185; the
wordlists `lf-words`, `lf-locals`, `lf-consts` of `src/author/groups.fs`,
lines 44-52). Each token of a line is looked up and the word found is run at
once, left to right. A token that is a plain decimal number of at most nine
digits is a number; any other token that is no word is an error (codes 1, 35).
Words are **ordinary**, not Forth `immediate` words: none of them is run at
compile time, and a LeanForth run started while Forth is compiling is refused
(error 45, `runner.fs:133,184`). Names are case-sensitive even though Forth
is not (`groups.fs:12-20`). A line of a file must have fewer than 1024 characters (error 39).

**Postfix order.** An argument is written before the word that uses it.
`0 n + n =` means "zero, `n`, add, `n`, equal": the two operands of `+` are
`0` and `n`, the two sides of `=` are the sum and `n`. In Lean it is
`0 + n = n`. A name takes as many values from the stack as the thing it
names has explicit arguments, so `xs List.length` is Lean's `xs.length`.

**Stack comments.** Words are described in Forth-2012 notation,
`( before -- after )`: what the word takes from the stack, and what it leaves.
The rightmost item is the top of the stack. Text that a word reads *itself*
from the rest of the line is written in quotes in the same comment:

| Comment | Meaning |
| --- | --- |
| `( "name" -- )` | the word reads the next token on its line (one name) and leaves nothing on the stack |
| `( "name1" ... "terminator" -- )` | it reads tokens up to and including a terminator such as `=>` |
| `( "text\"" -- )` | it reads the characters up to the next `"` on the same line |
| `( v "name" -- )` | it takes a value from the stack and also reads a name |
| `( t1 t2 -- t3 )` | an ordinary word on terms: two terms in, one out |

In these comments `t` is a term, `s` a statement (a term that is a
proposition), `v` any LeanForth value (a term, or in natural form a syntax
tree for a term), `c` a constant waiting for universe levels, `l` a universe
level or a plain number, `n` a number. A *parsing word* is one that reads
text after itself; the column "Kind" says so. Text it reads is not run as
words: in `theorem foo` the token `foo` is a name for the word to use, not a
word to run. A parsing word that finds no token left on its line stops the
run with error 2.

**The term stack.** The values LeanForth builds live on Forth's data stack
(the "term stack" in the tables). A cell is not the term itself but a
reference to an item kept in a store (`src/author/values.fs:1-20`); a value
can be used once (a second use is error 34) and only inside the declaration
and binder that made it. A word that needs `n` values checks that they are
above the *frame*, the depth where the innermost open binder or the
declaration began (`lfa-args`, `src/author/scopes.fs:83`); too few is error
3. So the stack of one declaration is empty when a declaration starts (error
15) and holds exactly one value, the statement, when `:=` comes.

**Authoring state.** "Authoring" is the run of the words over the text. The
state they change, named in the tables' "State changed" column:

| Name in the tables | What it is |
| --- | --- |
| declaration | the record of the declaration being built (`lfa-current` and its slot in `lfa-decls`: kind, name, universe parameters, type, value, protected flag; `src/author/declarations.fs:54-60`, `constants.fs:22-29`); it exists from `theorem NAME` to `end NAME` |
| binders | the list of binders open now, innermost last: name, kind, type, where each began (`lfa-binders`, `src/author/scopes.fs:20-28`) |
| locals | the words made for variables, universe parameters and hypotheses (`lf-locals`, `groups.fs`); a binder's name is a word until its binder closes |
| term stack | the Forth data stack, as described above |
| statement tree | in natural form, the syntax tree of the statement and of the proof, kept until `end NAME` (`lfn-decl`, `src/front/reader.fs:46-51`) |
| steps | the tactic step list: one record per tactic word read (`tac-steps`, `tac-args`; `src/front/tactic-syntax.fs:96-124`) |
| goals | at run time, the list of goals still to prove (`src/front/goals.fs`, `lf-goals`) |
| namespaces | the namespaces entered and opened (`lfa-spaces`, `src/author/namespaces.fs:104-113`) |

**How a file is read.** The file runs from the top to the bottom. Between
declarations the words are `namespace`, `open`, `end` (of a namespace),
`kernel-form`, comments, and a term followed by `#check`; a file that stops
inside a declaration or with values left is error 33. `theorem NAME` (or `def`, `axiom`) opens a
declaration; binders, statement, `:=` and proof follow; `end NAME` closes it.
In natural form the words before `end NAME` only build syntax trees and
tactic steps. **At `end NAME`** the elaborator turns the trees into terms,
the tactics run, and the result is handed over as a finished declaration
(`lfn-end-declaration`, `reader.fs:192`; `lft-end-proof`,
`tactic-syntax.fs:312`). **The kernel check comes after the whole file has
run**: `bin/leanforth check` runs the text, then checks every finished
declaration (`src/cli/check-lf.fs:196`). The first error ends the run; later
text is not read.

---

## Terms

Each term is defined for a mathematician who has not used Lean. "Lean:"
gives the matching Lean spelling.

**NAME.** A name is how a declaration, variable, universe parameter or
namespace is called. It is a *token*, that is, text between blanks (space,
TAB, line ends); it may hold any characters a line may hold (letters of any
language, digits, `_`, `'`, `!`, `?`, ...), except control and formatting
characters (error 46). A dot is special: it separates the *parts* of a name,
so `Nat.add_succ` has two parts, the namespace `Nat` and the name
`add_succ`. A name has no empty part (`.a`, `a.`, `a..b` are error 30) and,
for the name of a declaration, universe, namespace or hypothesis, must not
look like a number to Forth: a first character that is a digit, or one of `+
- # $ % & '` with more text after it, is refused (error 30; error 35 for
such a token that is no name at all). A binder's name may look like a
number: it then gets no word, and `n var#` refers to the binder. A part that
is only digits is a number part (no leading zero; at most 18 digits on a
64-bit host, 9 on a 32-bit one); `«123»` (with the guillemets) is the string
`123`. Names are case-sensitive: `n` and `N` differ. A declaration's full
name may be 256 characters (error 62). `[anonymous]` is the name of a binder
that has none. *Hygienic names* are Lean's invisible names made by macros
(`HAdd.hAdd✝`); you never write them. LeanForth uses them for its operator
words: `+` means the global constant `HAdd.hAdd`, whatever local variable or
namespace is around (`src/front/syntax.fs:19-21`). Lean: identifiers
(`Nat.add_succ`, `n`, `zero_add''`).

**Declaration; theorem; axiom; def.** A *declaration* adds a named constant
to the library: a name, a type, and sometimes a value. A **theorem** has a
statement (its type, a proposition) and a proof (its value): once proved it
is a fact you can use by name. An **axiom** has a statement and no proof: it
is assumed, and every theorem that uses it reports it (`axioms: none` is
the good case). A **def** (a definition) has a type and a value that is data
or a function, for example `def double (n : Nat) : Nat := n + n`.
`import-stub` stands for a constant that a library would provide; the
checker refuses it. Lean: `theorem`, `axiom`, `def`.

**Universe level; universe; universe parameter.** To avoid the paradox of
"the set of all sets", Lean sorts its types into a hierarchy. `Prop` is the
sort of propositions; `Type` is the sort of ordinary types such as `Nat`;
`Type 1` holds types of types, and so on. The index is a *universe level*
(a natural number, or an expression like `u + 1`), and `Sort l` is the sort
at level `l`: `Prop` is `Sort 0`, `Type` is `Sort 1`, `Type l` is
`Sort (l + 1)`. A *universe parameter* is a level variable, like `u`, that
a declaration is generic in: `identity.{u} {A : Sort u} (a : A) : A` holds
for types of every level. `universe u` after the declaration's name
introduces one. Lean: `universe u`, `Sort u`, `Type u`, `Prop`.

**Binder.** A binder introduces a variable with a type, for the rest of
the declaration: the `(n : Nat)` of `theorem t (n : Nat) : ...`. Before
`:=`, the binders are the *parameters* of the declaration. In LeanForth a
binder is written as its type, a binder word and its name:
`Nat explicit: n` means "binder type `Nat`, binder kind *explicit*, name
`n`"; it is not a definition of `Nat`. Lean: `(n : Nat)`.

**Binder kinds.** *Explicit*, `(x : T)`: the caller must give the argument.
*Implicit*, `{x : T}`: Lean works it out from other arguments. *Strict
implicit*, `⦃x : T⦄`: like implicit, but only inserted once a later explicit
argument is given. *Instance implicit*, `[x : T]`: Lean finds it by instance
search (for a type class such as `Add Nat`). The words are `explicit:`,
`implicit:`, `strict-implicit:` and `instance:`
(`src/present/binder-table.fs:36-39`). The kind decides how many arguments a
name takes from the stack: only the explicit ones.

**Protected; private; namespace.** A *namespace* is a prefix of names that
groups them: `Nat.add_succ` lives in `Nat`; inside `namespace Nat`, `add_succ`
alone finds it. A *protected* declaration is not found by its short name
through a namespace: `protected theorem Nat.foo` can be written `Nat.foo`
even inside `namespace Nat`, but not `foo`. It needs a namespace in its name.
`private` (visible only in its file) has no LeanForth word. Lean:
`namespace`, `open`, `protected`, `private`.

**Term; statement; proof.** A *term* is a piece of mathematics the kernel
understands: a number, a variable, a function, an application `f a`, a
proposition `0 + n = n`, a proof. The *type* of a term says what it is: `n`
has type `Nat`; a proof has as its type the proposition it proves. A
theorem's *statement* is that proposition (the term before `:=`); its
*proof* (or *value*) is a term whose type is the statement. Lean: terms,
types, `theorem name : statement := proof`.

**Goal; hypothesis.** While tactics run, the *goal* is a statement still to
be proved, together with what may be assumed. A *hypothesis* is one of those
assumptions: a variable `n : Nat`, or an assumption `ih : 0 + k = k`. A tactic
step changes the goal list: it closes a goal, or replaces it by simpler ones.
Lean prints a goal as `n : Nat ⊢ 0 + n = n`.

**Tactic; alternative.** A *tactic* is a step of a proof that tells Lean how
to build the proof term: `rfl` (the two sides are equal by computation),
`exact t` (this term does it), `rw [h]` (rewrite with an equation),
`induction n` (prove it for zero, and from `k` to `k + 1`). An *alternative*
is the part of an `induction ... with` that proves one *case*, written
`| zero => ...` or `| succ k ih => ...`: the tag names the case, the names
after it name that case's variables and hypotheses. The tactics only build a
term; the kernel checks it.

**Motive.** An induction, and a rewrite, need a function from a value to a
statement: the *motive*. For induction on `n` in `0 + n = n` it is
`fun n => 0 + n = n`; the zero case proves the motive at zero, the step case
from `k` to `k + 1`. For a rewrite with `a = b` it is the goal with `a`
abstracted into a variable. LeanForth builds it as Lean does and
type-checks it (errors 212, 216, 217).

**Rewrite rule.** A rule is a proof of an equation `a = b` (a hypothesis,
or a theorem written `' NAME`). Rewriting replaces each `a` in the goal by
`b`. Lean: `rw [h]`.

**Elaboration.** Lean's elaborator turns what you wrote into a complete
term: it finds the type of each part, supplies hidden arguments, finds
instances and decides what a numeral like `0` means (here `OfNat Nat 0`).
LeanForth's elaborator (`src/front/`) does the same steps at `end NAME` or at
`#check`, as the pinned Lean does; see [ELABORATION.md](ELABORATION.md).

**Kernel check.** The kernel is the small trusted program that accepts a
term only if its type is correct. Words, elaborator and tactics are
untrusted; only an accepted kernel check makes a theorem true. Lean: the
kernel (`Lean.Environment.addDecl`).

**Axioms used.** After a theorem is accepted the checker lists the
axioms its proof depends on (`accepted; axioms: none`). A proof closed with
`by-sorry` depends on `sorryAx`: it is accepted but reported NOT PROVED.

**Authoring state.** The data the words change while the text runs; see
[Reading this reference](#reading-this-reference).

---

## A. Theorems

### A.1 Glossary

Errors named in the "Function" cells are codes of `src/author/errors.fs`.

| Word | Stack and parse effect | Kind | State changed | Function |
| --- | --- | --- | --- | --- |
| `theorem` | `( "name" -- )` | parsing: one name, on its line | starts the declaration (kind theorem); empty binders; its name becomes a word at `end` | Starts a theorem named NAME inside the current namespace; errors 2 no name, 14 inside a declaration, 15 values on the stack, 28 name already declared (also by the library), 30 bad name, 53 `_root_` in the name. |
| `def` | `( "name" -- )` | parsing: one name | as `theorem`, kind def | Starts a definition: the same, with a value instead of a proof. |
| `axiom` | `( "name" -- )` | parsing: one name | as `theorem`, kind axiom | Starts an axiom: binders and one statement, no `:=`; `end NAME` takes the statement. |
| `import-stub` | `( "name" -- )` | parsing: one name | as `theorem`, kind stub | Stands for a library constant; `bin/leanforth check` refuses it (error 48). |
| `protected` | `( "kind" "name" -- )` | parsing: two names, the kind word `theorem`, `def`, `axiom` or `import-stub`, then the name | as that kind; marks the declaration protected | Starts a declaration that short names cannot reach through a namespace; error 43 when the first token is no kind, 44 when the name has no namespace prefix. |
| `universe` | `( "name" -- )` | parsing: exactly one name; a second name is a new token to run | appends a universe parameter to the declaration (at most 8) and makes NAME a word in the locals | Declares a universe parameter NAME; it must come right after the declaration's name, before any binder, value or `:=` (error 16), once per name (28), at most 8 (10). |
| `explicit:` | `( v "name" -- )` | parsing: one name | opens a binder: pushes it on the binders; NAME becomes a word in the locals (not for `[anonymous]` or a number-like name) | Binds NAME with kind explicit and the type that is the value on the stack, `(name : T)`; errors 3 no type below, 2 no name, 65 too many binders. |
| `implicit:` | `( v "name" -- )` | parsing: one name | as `explicit:` | The same with kind implicit, `{name : T}`. |
| `strict-implicit:` | `( v "name" -- )` | parsing: one name | as `explicit:` | The same with kind strict implicit, `⦃name : T⦄`. |
| `instance:` | `( v "name" -- )` | parsing: one name | as `explicit:` | The same with kind instance implicit, `[name : T]`. |
| `:=` | `( s -- )` | ordinary; acts once per declaration | the statement tree (natural) or the declaration's type (kernel form) is stored; the binders open now become its parameters | Ends the statement. Errors 17 not allowed here (outside a declaration, an axiom, or a second `:=`), 18 the statement is not exactly one term or a value sits between binders. |
| `end` | `( "name" -- )` | parsing: one name; inside a declaration it completes it, outside it leaves a namespace | completes the declaration: closes binders around statement and proof, records type and value, publishes the name; or pops namespaces | NAME must repeat the declaration's name (error 22) or name the namespaces to leave (22, 23). In natural form it runs the elaborator and the tactics (errors 19 `:=` missing, 20 proof not one term, 21 binder still open, 82 block open, 86 value left over). |
| `namespace` | `( "name" -- )` | parsing: one name, may be dotted | enters one namespace per part | Between declarations only (error 24); `namespace A.B` enters `A`, then `A.B`; more than 16 namespaces entered and opened together is error 25. |
| `open` | `( "name" -- )` | parsing: one name | marks the namespace opened (until the enclosing `end`) | Makes the names of namespace NAME findable by their short names; unknown namespace is error 26. |
| NAME of a constant or variable | `( v1 ... vk -- v )` | ordinary (found by the interpreter; resolved when run) | pops its arguments, pushes one value | Applies the constant or variable to as many values as it has explicit arguments (k); errors 1 unknown, 27 ambiguous, 55 a short name of a library constant, 73 the count depends on unfolding a definition. |
| a numeral `0`, `2` | `( -- v )` | ordinary (read by Forth, not a LeanForth word) | pushes a number; its position is kept | In natural form Lean's numeral, a plain decimal of at most nine digits; other number forms are error 35. |
| `'` | `( "name" -- )` followed by NAME `( -- v )` | looks ahead: reads the next token without consuming it; natural form only | marks a pending tick; the next name word then takes no arguments | The function NAME itself, unapplied; error 59 when no name follows on the line. |
| `$` | `( f a -- v )` | ordinary | pops two values, pushes the application | One more argument: `f a $` is Lean's `f a`. |
| `+` `*` | `( a b -- v )` | ordinary; natural form only (error 58 in kernel form) | pops two, pushes an operator node | Lean's `a + b` and `a * b`, as `binop%` of `HAdd.hAdd` and `HMul.hMul`. |
| `=` `≤` | `( a b -- v )` | ordinary; natural form only | pops two, pushes a relation node | Lean's `a = b` and `a ≤ b`, as `binrel%` of `Eq` and `LE.le`. |
| `#check` | `( v -- )` | ordinary; natural form; outside declarations only | counts the check; prints one line `TERM : TYPE`; no declaration | Elaborates the term with no expected type and prints it with its type; inside a declaration it is error 140 (141 in a tactic block). |
| `kernel-form` | `( -- )` | ordinary; acts outside declarations | switches the run to the kernel form for the rest of the run | Error 57 inside a declaration. |
| `\` | `( "rest of line" -- )` | parsing: the rest of the line | none | A comment to the end of the line. |
| `(` | `( "text)" -- )` | parsing: text up to `)` on the same line | none | A comment; without `)` on its line it is error 42. |
| `->` | `( a b -- t )` | ordinary; kernel form only | pops two types, pushes the function type | `A B ->` is Lean's `A → B`. |
| `fun` `forall` | `( v -- t )` | ordinary; kernel form only | closes the innermost open binder around the one value above it | A λ or a Π over that binder; errors 13 no binder open, 12 body not one term. |
| `Prop` `Type` `Sort` `^` `var#` `lit#` `proj#` `level+` `level-max` `level-imax` `root:` | see [programming reference](../programming/LEANFORTH_WORDS.md#the-vocabulary) | kernel form only (natural form: error 70) | build kernel terms and levels | Levels, de Bruijn variables, literals, projections and universe arguments written out. |
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

**`#check`.** `TERM #check` (between declarations) elaborates TERM with no
expected type and prints `TERM : TYPE` (`edc-w-check`,
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

| Word | Stack and parse effect | Kind | State changed | Function |
| --- | --- | --- | --- | --- |
| `label:` | `( v "name" -- v' )` | parsing: one name; kernel form only (natural form: error 70) | gives the term its own node and adds a label entry to the note table (`src/present/note-table.fs`) | Names the step that built the value on top, so the printer can refer to it; a label repeated in one declaration is error 29, a missing name is 2. |
| `note"` | `( v "text\"" -- v' )` | parsing: the text up to the next `"` on its line; kernel form only | as `label:`, entry kind person | Attaches a note by a person; no closing `"` on the line is error 37. |
| `ai-note"` | `( v "text\"" -- v' )` | parsing: as `note"`; kernel form only | as `label:`, entry kind AI | Attaches a note tagged as written by an AI. |
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

| Word | Stack and parse effect | Kind | State changed | Function |
| --- | --- | --- | --- | --- |
| NAME of a theorem or constructor | `( a1 ... ak -- t )` | ordinary (resolved when run) | pops k values, pushes the application | Applies it to its explicit arguments: `n Eq.refl` is Lean's `Eq.refl n`; the elaborator supplies the hidden type and level. |
| `'` | `( "name" -- )`, then NAME `( -- t )` | looks ahead; natural form | marks a pending tick | The constant itself, unapplied. |
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

### D.1 Glossary

| Word | Stack and parse effect | Kind | State changed | Function | Lean |
| --- | --- | --- | --- | --- | --- |
| `by` | `( -- )` | ordinary; right after `:=` only (error 69 elsewhere; natural form; error 51 in kernel form) | read: records the proof's position and opens the tactic block (step 0) | Marks that a tactic proof follows `:=`. | `:= by` |
| `by-rfl` | `( -- )` | ordinary | read: a step. Run: assigns the main goal `Eq.refl` and removes it from the goals | Closes the goal `a = b` when both sides are definitionally equal; otherwise error 97. | `rfl` |
| `by-exact` | `( t -- )` | ordinary | read: a step holding the term. Run: elaborates t against the goal, assigns it, removes the goal | Closes the goal with the term t; a type mismatch is error 96, a wrong number of values 86 or 87. | `exact t` |
| `by-intro:` | `( "name" -- )` | parsing: one name, or `_` | read: a step; NAME becomes a hypothesis word in the locals. Run: replaces the goal by one with the first binder introduced | Introduces one hypothesis NAME from the goal's first binder; `_` leaves it inaccessible (it cannot be written afterwards); error 94 when there is none, 84 when NAME is a LeanForth word. | `intro NAME` |
| `by-sorry` | `( -- )` | ordinary | read: a step. Run: assigns the goal `sorryAx T Bool.false`, records an open part | Closes the goal with an open part; the declaration is accepted but reported NOT PROVED. | `sorry` |
| `by-induction` | `( t -- )` | ordinary | read: a step holding t. Run: replaces the main goal by one goal per case | Induction on the variable t; the cases are left open (alone it ends in error 89). | `induction t` |
| `by-induction-with` | `( t -- )` | ordinary; opens a block that `by-end` closes | read: a block step holding t. Run: as `by-induction`, each case taken by an alternative | Induction on t with the cases written as alternatives. | `induction t with` |
| `\|` | `( "tag" "name1" ... "=>" -- )` | parsing: tokens of its line up to `=>`; only right inside `by-induction-with` (error 83 elsewhere) | read: an alternative block; the names become hypotheses until the alternative ends. Run: introduces the case's fields and runs the block | One alternative: TAG names a case (`zero`, `succ`), the names name its fields and hypotheses; ends at the next `\|` or at `by-end`. | `\| tag names =>` |
| `=>` | | read only by `\|` and `by-case:` as their terminator; run alone it is error 84 | none | Ends an alternative's header. | `=>` |
| `by-end` | `( -- )` | ordinary | read: closes the innermost `by-induction-with` or `by-case:` block | Closes the block; with none open, error 83. | indentation |
| `by-rw[` | `( -- )` | ordinary; opens a rule block that `]` closes | read: a block step. Run: rewrites the goal with each rule, then tries `by-rfl` | Starts a list of rewrite rules; every value built until `]` is a rule. | `rw [` |
| `by-rewrite[` | `( -- )` | ordinary; opens a rule block that `]` closes | read: as `by-rw[`. Run: rewrites with each rule, no `by-rfl` | The same without the closing `rfl`. | `rewrite [` |
| `]` | `( r1 ... rn -- )` | ordinary | read: the n values become the block's rules, in order; closes it | Ends the rule list of `by-rw[` or `by-rewrite[`; with none open, error 83. | `]` |
| `**` `by-case:` | `( "tag" "name1" ... "=>" -- )` | parsing: as `\|`; closed by `by-end` | read: a case block. Run: error 80 | One case after `by-induction`; read today, running stops with error 80. | `case tag names =>` |
| `**` `by-decide` | `( -- )` | designed | n/a | Close a closed goal by evaluation. | `decide` |
| `**` `by-omega` | `( -- )` | designed | n/a | Linear arithmetic over `Nat` and `Int`. | `omega` |
| `**` `by-native-decide` | `( -- )` | designed; permanently unsupported (exit 2): it rests on `Lean.ofReduceBool` | n/a | n/a | `native_decide` |
| `**` `by-try`, `by-first`, `<;>` | | combinators; sketched in FE1G §4 and S2 §3 (the trail), no word fixed | n/a | n/a | `try`, `first`, `<;>` |
| `**` `by-alt: TAG NAMES... =>` | | an open question of the design: spelling alternatives without `\|` | n/a | n/a | `\| tag names =>` |
| `**` `by-refine`, `by-subst`, `by-cases`, `by-apply` and others | | named in FE2 §3/FE5 as later tactics; no spelling is fixed | n/a | n/a | `refine`, `subst`, ... |

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
definitionally equal and builds `Eq.refl` (`lfb-w-rfl`,
`src/front/tactic-basic.fs:381`). `by-exact` takes a term from the
stack and closes the goal with it (`lfb-w-exact`, line 344); a type mismatch is
error 96. `by-intro: NAME` reads NAME, makes it a hypothesis word and, when
run, introduces the goal's first binder as a hypothesis named NAME, usable
until the block ends; with no binder left it is error 94. `by-sorry` closes
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
"Tactic `rfl` failed: The left-hand side 0 + 0 is not definitionally equal to the right-hand side 1". `by-intro:` is defined (`src/front/tactic-basic.fs`)
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
the motive from the goal. Each `| TAG NAMES... =>` alternative takes its
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
(`tests/front/s2w-induction-plain.lf`); its cases are meant for `by-case:`,
which is `**` (D.6). Use `by-induction-with`.

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

`by-rw[ r1 r2 ... ]` is Lean's `rw [r1, r2, ...]`: each rule is a
hypothesis (written by name) or a theorem written `' NAME`; its equation's
left side is abstracted wherever it occurs in the goal (`kabstract` at
reducible transparency), the motive is type-checked, and the goal becomes
the rewritten one; then `rfl` is tried at reducible transparency
(`lfw-w-rw`, `src/front/tactic-rewrite.fs:242`).
`by-rewrite[ ... ]` is `rewrite` and does not try `rfl` (line 241). The rules
are the values built between `by-rw[` and `]`; each stays on the stack until
`]` takes them, in order. Every value between the brackets is a rule, so an
applied hypothesis is written with `$`: `ih k $` is Lean's `ih k`. No tactic
word may stand inside the brackets (error 82). Errors: 215 no occurrence of
the pattern, 216 motive not type correct, 217 dependent motive, 218 no
equation, 219 a metavariable pattern, 220 the occurs check, 99 a form not
ported (a definition as a rule, `Iff`, an instance binder). Not yet (`**`, S2
merge B and later): `←`, `at h`, `using`, `generalizing`, and `++` as a word.

```text
\ tests/front/ps-succ-add.lf (the owner's proof set; accepted, term pinned to Lean's)
theorem ps_succ_add
  Nat explicit: n  Nat explicit: m
  n Nat.succ m + n m + Nat.succ =
:= by
  m by-induction-with
  | zero =>       by-rw[ ' Nat.add_zero ' Nat.add_zero ]
  | succ k ih =>  by-rw[ ' Nat.add_succ ih ' Nat.add_succ ]
  by-end
end ps_succ_add
```

```text
\ tests/front/ps-length-append.lf (excerpt: rewriting with earlier theorems)
  | nil =>           by-rw[ ' List.nil_append ' List.length_nil ' ps_zero_add ]
  | cons x t ih =>   by-rw[ ' List.cons_append ' List.length_cons ' List.length_cons ih ' ps_succ_add ]
```

The other files of the owner's set are `ps-add-comm.lf` and `ps-mul-add.lf`.
Wrong twins: `s2w-rw-empty.lf` (`by-rw[ ]` leaves the goal: 89),
`s2w-rw-definition.lf` (a definition as a rule, 99), and `s2w-rw-unsolved.lf`,
`s2w-not-eq.lf`, `s2w-pattern.lf`, each refused with Lean's first message.

### D.6 `by-case:` (`**`)

`by-case: TAG NAMES... =>` ... `by-end` is read today (it checks the shape,
FE1g-2: `lft-w-case`, `tactic-syntax.fs:289`) but running it stops with
error 80, "not supported yet" (plan S2 merge B). Design:
[FE1G_TACTICS.md](../design/FE1G_TACTICS.md) §3.2,
[S2_INTERFACE.md](../design/S2_INTERFACE.md). Lean: `case succ k ih => ...`.

```text
\ tests/front/01-zero-add.lf (read; stops at end with error 80 until merge B)
n by-induction
by-case: zero =>       by-rfl                           by-end
by-case: succ k ih =>  ' Nat.succ ih congrArg by-exact  by-end
```

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
| `TERM #check` | `( v -- )` | the type of a term, which finds what a name means (section A) |
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
| tactics | `src/front/tactic-syntax.fs` (reading), `tactic-run.fs` (runner, `by-sorry`), `tactic-basic.fs` (`by-intro:`, `by-exact`, `by-rfl`), `tactic-induction.fs`, `tactic-rewrite.fs` |
| elaboration and `#check` | `src/front/elab-*.fs` |
| printing | `src/present/` |
| command line | `src/cli/leanforth.fs`, `check-lf.fs` |
