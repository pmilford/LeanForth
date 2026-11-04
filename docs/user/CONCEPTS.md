# Concepts, each in three forms

This page explains the words a LeanForth user meets — universe level,
`Sort`, `Prop` and `Type`, term, binder, de Bruijn index, constant,
declaration, theorem and definition, kernel, and the outcome vocabulary —
each with one concrete example in three forms:

- **Mathematics**, in ordinary notation.
- **LeanForth Forth**, *as the current Forth words build it today*. These
  are the internal, untrusted words of `src/core/`, `src/kernel/`,
  `src/import/` and `src/present/`, not a user language: a readable Forth
  syntax for *writing* terms and theorems is planned (task 8.1.1 of the
  [plan draft](../project/PLAN_DRAFT.md)). Nothing they report is a checked
  theorem.
- **Lean**, the language whose kernel LeanForth aims to check
  independently.

Every Forth example below was run on 2026-11-02 (commit `fc558cc`) with the
pinned Gforth 1.0.0 and with Gforth 0.7.3, CI's portability host, and
printed exactly the output shown. Every Lean example was checked with the
pinned Lean 4.35.0 binary and `-DwarningAsError=true`; the two examples that
Lean must reject were run and rejected with the messages quoted. The
examples are not yet run by `make test`, so they can fall behind the code;
the date and commit above say when they last ran.

If you are new to these words, [terms for new readers](TERMS_FOR_NEW_READERS.md)
gives shorter, example-free definitions, and
[what LeanForth is and is not](USER_GUIDE.md) says what can be trusted.

## Running the Forth examples

Start Gforth in the repository root with every module loaded, then paste
the prelude below, then one example:

```sh
.tools/gforth/bin/gforth src/main.fs
```

Each example starts with `fresh`, which empties the stores, so earlier
handles become stale. Run each example in a new Gforth session after the
prelude; pasted into one session, later examples still work but Gforth
prints harmless `redefined` warnings for names they reuse.

The prelude defines helpers for this page only; they are not part of
LeanForth. Most construction words return a *handle* — two cells, a store
index and that slot's identity — and a flag; `made` stops on a refused
construction, `ok!` on an outcome other than *ok*. `.term` and `.level`
print exactly what the stores hold, with bound variables as `#0`, `#1`, ….
`.lean` prints a term in Lean's notation with LeanForth's term printer
(`src/present/term-printer.fs`, [printing terms](TERM_PRINTER.md)), which
restores variable names from the binder names that `named` and `implicit`
record in its side table. Universe parameters are identified by name: in
every example `u` has name ID 1 and `v` name ID 2.

```forth
\ Helpers for the examples (documentation only, not part of LeanForth).
\ made ( ... true | false -- ... ): stop when a construction is refused.
: made ( flag -- ) 0= abort" refused" ;
\ ok! ( outcome -- ): stop unless an outcome is ok (0).
: ok! ( outcome -- ) outcome-ok <> abort" not ok" ;

\ fresh ( -- ): empty stores and side table; the universe parameters u and
\ v, whose identifiers are their name IDs, 1 and 2; a new session; and an
\ empty signature index, kept in index.
variable index
: param ( c-addr u -- ) 0 -rot lf-name-str made lf-lscope-context-add made ;
: fresh ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-pres-reset  s" u" param  s" v" param
  lf-ssession-begin made  lf-msp-begin made  lf-msp-token made index ! ;

\ Building terms from handles (index identity): wrap a body in a binder
\ whose domain is on top, or apply a function to an argument.
: >Pi ( body domain -- term ) 2swap lf-hterm-pi made ;
: >fun ( body domain -- term ) 2swap lf-hterm-lam made ;
: app ( function argument -- term ) lf-hterm-app made ;

\ .level ( level -- ) and .term ( term -- ): print what the stores hold,
\ with bound variables as #0, #1, ...
: .lf-name ( id -- ) lf-name-slot lf-name-bytes@ type ;
defer .level
: .level-node ( tag first second -- )
  rot case
    lf-level-tag-zero  of 2drop ." 0" endof
    lf-level-tag-succ  of drop ." (" .level ." +1)" endof
    lf-level-tag-max   of ." max(" swap .level ." , " .level ." )" endof
    lf-level-tag-imax  of ." imax(" swap .level ." , " .level ." )" endof
    lf-level-tag-param of drop .lf-name endof
    nip nip ." ?" endcase ;
:noname ( level -- ) lf-level-read made .level-node ; is .level
defer .term
: .levels ( cref identity -- )
  lf-cref-levels made ." .{" 0 ?do dup i lf-cref-pair@ drop .level loop drop ." }" ;
: .constant ( cref identity -- ) 2dup lf-cref-read made 2drop .lf-name .levels ;
: .binder ( domain body -- ) swap .term ." , " .term ." )" ;
: .term-node ( tag first second -- )
  rot case
    lf-tag-symbolic-sort of drop ." Sort " .level endof
    lf-tag-bvar     of drop ." #" 0 .r endof
    lf-tag-app      of ." (" swap .term space .term ." )" endof
    lf-tag-lam      of ." (fun " .binder endof
    lf-tag-pi       of ." (Pi " .binder endof
    lf-tag-constant of .constant endof
    nip nip ." ?" endcase ;
:noname ( term -- ) lf-term-read made .term-node ; is .term

\ The term printer (src/present): name the binder of a λ or Π handle,
\ explicit or implicit, then print a term in Lean's notation.
: binder-kind ( term identity c-addr u kind -- term identity )
  >r 0 -rot lf-name-str made  2 pick swap r> lf-pres-binder! ok! ;
: named ( term identity c-addr u -- term identity ) lf-binder-default binder-kind ;
: implicit ( term identity c-addr u -- term identity ) lf-binder-implicit binder-kind ;
' type lf-print-unicode lf-print-setup
: .lean ( term identity -- ) drop 10000 lf-print-term ok! ;
```

## Universe level

Types have types too, and Lean sorts them into a hierarchy indexed by
*universe levels*. A level is a small expression built from `0`, `+1`,
`max`, `imax` (below) and *parameters* such as `u`, which stand for any
level. A level is not a stack depth or a measure of difficulty.

**Mathematics.** The level $\max(u,\ v+1)$. With $u = 2$ and $v = 0$ its
value is $\max(2, 1) = 2$. For every $u$ and $v$,
$\max(u,\ v+1) = \max(v+1,\ u)$.

**LeanForth Forth.** Levels live in the level store (`src/core/levels.fs`,
64 entries); a parameter is a positive identifier — here the ID of its
name, which the printer needs — that must be declared in the parameter
context (`src/core/level-scope.fs`) before it is used.

```forth
fresh
1 lf-hlevel-param made 2constant u
2 lf-hlevel-param made 2constant v
v lf-hlevel-succ made 2constant v+1
u drop v+1 drop lf-level-max made constant max-u-v1   \ max(u, v+1)
v+1 drop u drop lf-level-max made constant max-v1-u   \ max(v+1, u)
max-u-v1 .level cr
lf-lassign-reset  1 2 lf-lassign-add made  2 0 lf-lassign-add made   \ u = 2, v = 0
max-u-v1 1000 lf-level-value-assigned . . cr   \ status, then value
max-u-v1 1000 lf-level-value . . cr            \ no assignment
max-u-v1 max-v1-u 1000 lf-level-compare . cr   \ Lean's level comparison
```

```text
max(u, (v+1))
0 2
3 -1
0
```

With the assignment the value is 2 (status 0, *ok*). Without one, the
parameter has no value and the answer is *unknown* (3), not a guess. The
comparison answers *ok* (0): LeanForth compares levels exactly as Lean's
kernel does ([ADR 0011, Amendment 1](../adr/0011-definite-rejection.md#amendment-1-proposed-2026-11-03-universe-levels-are-built-and-compared-as-lean-builds-and-compares-them)) —
equal as written, or equal after Lean's `normalize`, which sorts the
arguments of a `max` (`src/kernel/level-normalize.fs`). That procedure is
deliberately incomplete: $\mathrm{imax}(1, u+1)$ and $\max(1, u+1)$ have
the same value for every $u$, yet Lean's kernel calls them different, and
so does LeanForth (it answers *unknown* to the comparison, and rejects a
declaration that needs them equal, as Lean does). Such cases are recorded
in `docs/project/BEYOND_LEAN.md` for a possible later mode.

**Lean.** Lean's kernel shows the two levels equal:

```lean
universe u v
example : Sort (max u (v+1)) = Sort (max (v+1) u) := rfl
```

## Sort

`Sort l` is the type whose elements are the types (or propositions) at
level `l`. Every `Sort` is itself an element of the next one.

**Mathematics.** $\mathrm{Sort}\ u : \mathrm{Sort}\ (u+1)$.

**LeanForth Forth.** A `Sort` term holds the index of its level in the
level store. Inference (`lf-mixed-infer`, `src/kernel/mixed-infer.fs`) gives
its type:

```forth
fresh
1 lf-hlevel-param made lf-hterm-sort made 2constant Sort-u
Sort-u drop .term cr                              \ the term itself
index @ Sort-u 1000 lf-mixed-infer .              \ status
drop .term cr                                     \ the inferred type
```

```text
Sort u
0 Sort (u+1)
```

The term store also has an older, *concrete* `Sort` that carries a number
instead of a level; no current checker pass accepts it
([ADR 0007](../adr/0007-sort-representation-boundary.md)).

**Lean.**

```lean
universe u
example : Sort (u+1) := Sort u
```

## Prop and Type

`Prop` is `Sort 0`, the universe of propositions: its elements are
statements, and the elements of a statement are its proofs. `Type` is
`Sort 1`, the universe of ordinary data types such as the natural numbers;
`Type 1` is `Sort 2`, and so on. A "for all" over types lands one level
up, but a "for all" whose body is a proposition is again a proposition.
Lean expresses that with `imax a b`, which is $0$ when $b = 0$ and
$\max(a, b)$ otherwise.

**Mathematics.** $\mathrm{Prop} = \mathrm{Sort}\ 0$ and
$\mathrm{Type} = \mathrm{Sort}\ 1$.
$(\forall A : \mathrm{Prop},\ A \to A) : \mathrm{Prop}$, but
$(\forall A : \mathrm{Type},\ A \to A) : \mathrm{Type}\ 1 = \mathrm{Sort}\ 2$.

**LeanForth Forth.** `Pi` is the "for all" (and the function arrow, when
the body does not use the variable):

```forth
fresh
lf-hlevel-zero made 2constant zero
zero lf-hterm-sort made 2constant Prop                      \ Sort 0
zero lf-hlevel-succ made lf-hterm-sort made 2constant Type0  \ Sort 1, Lean's Type
0 lf-hterm-bvar made 2constant b0
1 lf-hterm-bvar made 2constant b1
b1 b0 >Pi  Prop >Pi   2constant all-prop     \ (A : Prop) -> A -> A
b1 b0 >Pi  Type0 >Pi  2constant all-type     \ (A : Type) -> A -> A
all-prop drop .term cr
: sort-of ( term identity -- )   \ infer the type, print it and its level's value
  index @ -rot 1000 lf-mixed-infer ok! drop
  dup .term ."  = Sort " lf-term-read made drop nip 1000 lf-level-value ok! . cr ;
all-prop sort-of
all-type sort-of
```

```text
(Pi Sort 0, (Pi #0, #1))
Sort 0 = Sort 0
Sort ((0+1)+1) = Sort 2
```

Inference builds the level of a `Pi` as Lean's kernel does, with Lean's
`mk_imax` (`src/kernel/level-make.fs`): $\mathrm{imax}(a, 0)$ is $0$, and
$\mathrm{imax}(a, b)$ for a $b$ that is never $0$ is $\max(a, b)$, which
for two numbers is the larger one. So the first answer is `Sort 0` and the
second $\mathrm{imax}(2, \mathrm{imax}(1, 1)) = \max(2, 1) = 2$, written
`Sort 2` at once. (`Type0` avoids the name `Type`: Gforth ignores case,
and `type` is a standard Forth word.)

**Lean.**

```lean
example : Prop = Sort 0 := rfl
example : Type = Sort 1 := rfl
example : Prop := (A : Prop) → A → A
example : Type 1 := (A : Type) → A → A
```

## Term

A *term* (or expression) is the data Lean's kernel checks: sorts, bound
variables, applications, functions (`fun`, also written λ), "for all"
types (Π) and constants. Types, statements and proofs are all terms.

**Mathematics.** The polymorphic identity:
$\lambda (A : \mathrm{Sort}\ u)\ (x : A).\ x \;:\; \Pi (A : \mathrm{Sort}\ u),\ A \to A$.

**LeanForth Forth.** Terms are nodes in a bounded store
(`src/core/terms.fs`, 64 nodes). A node has a tag and two fields; a child
must already exist, so a term is a graph without cycles in which a node can
be shared. Here the type and the value are built with the store's own
words (`lf-hterm-pi` takes the domain, then the body), printed raw and in
Lean's notation, and then listed node by node:

```forth
fresh
1 lf-hlevel-param made lf-hterm-sort made 2constant Sort-u
0 lf-hterm-bvar made 2constant b0
1 lf-hterm-bvar made 2constant b1
b0 b1 lf-hterm-pi made  Sort-u >Pi s" A" named  2constant id-type
b0 b0 lf-hterm-lam made s" x" named  Sort-u >fun s" A" named  2constant id-value
id-type drop .term cr
id-value drop .term cr
id-type .lean cr
id-value .lean cr
: .nodes ( -- )   \ every node: index, tag, first field, second field
  lf-term-count @ 0 ?do i 2 .r ." : " i lf-term-read made rot . swap . . cr loop ;
.nodes
```

```text
(Pi Sort u, (Pi #0, #1))
(fun Sort u, (fun #0, #0))
(A : Sort u) → A → A
fun A x ↦ x
 0: 6 1 0
 1: 2 0 0
 2: 2 1 0
 3: 5 1 2
 4: 5 0 3
 5: 4 1 1
 6: 4 0 5
```

Tags: 6 symbolic `Sort` (first field: level index 1, which is `u`), 2 bound
variable (first field: its index), 5 Π and 4 λ (fields: domain, body); 3 is
an application and 7 a constant. Node 1, the variable `#0`, is shared:
nodes 3 and 5 use it, and node 5 uses it twice. The names `A` and `x` are
not in the term at all; the printer finds them in its side table, and
prints the unnamed inner Π, whose body does not use its variable, as an
arrow. The [architecture page](../development/ARCHITECTURE.md#principal-records)
draws this term as a graph.

**Lean.** Lean's `#print` shows the same type and value as `.lean`:

```lean
universe u
def polyId : (A : Sort u) → A → A := fun (A : Sort u) (x : A) => x
set_option pp.unicode.fun true in
#print polyId
```

```text
def polyId.{u} : (A : Sort u) → A → A :=
fun A x ↦ x
```

## Binder

A *binder* introduces a variable for the part of a term after it. λ
(`fun`) binds a variable in a *value*; Π binds one in a *type*. Lean source
also gives a binder a name and an annotation (`{A}` for an implicit
argument, `(x)` for an explicit one); both are for people and the
elaborator, and Lean's kernel ignores them.

**Mathematics.** $\Pi (A : \mathrm{Sort}\ u),\ A$ is a type: its elements
take any $A$ to an element of $A$. $\lambda (A : \mathrm{Sort}\ u).\ A$ is a
function: it takes $A$ to $A$ itself, so its type is
$\Pi (A : \mathrm{Sort}\ u),\ \mathrm{Sort}\ u$.

**LeanForth Forth.** The two nodes differ only in their tag, but their
types differ:

```forth
fresh
1 lf-hlevel-param made lf-hterm-sort made 2constant Sort-u
0 lf-hterm-bvar made 2constant b0
b0 Sort-u >Pi   2constant all-A      \ (A : Sort u) -> A
b0 Sort-u >fun  2constant fun-A      \ fun (A : Sort u) => A
: .node ( term identity -- ) drop lf-term-read made rot ." tag " . swap . . ;
: .typed ( term identity -- )         \ the term, its node, its inferred type
  2dup drop .term ."   " 2dup .node ."   : "
  index @ -rot 1000 lf-mixed-infer ok! drop .term cr ;
all-A .typed
fun-A .typed
\ Names and annotations live in the printer's side table, not in the term:
all-A s" A" named .lean cr
all-A s" A" implicit .lean cr
fun-A s" T" named .lean cr
```

```text
(Pi Sort u, #0)  tag 5 0 1   : Sort imax((u+1), u)
(fun Sort u, #0)  tag 4 0 1   : (Pi Sort u, Sort u)
(A : Sort u) → A
{A : Sort u} → A
fun T ↦ T
```

The term store keeps neither binder names nor annotations: the same node
prints as `(A : Sort u) → A` or `{A : Sort u} → A` depending only on what
the printer's side table says. The NDJSON reader decodes both from an
export (see [Declaration](#declaration), whose output lists each binder
with its name and annotation), so they can be shown to people.

**Lean.** The first two lines restate the example; the third shows that the
kernel ignores binder names and annotations:

```lean
universe u
example : Sort (imax (u+1) u) := (A : Sort u) → A
example : (A : Sort u) → Sort u := fun (A : Sort u) => A
example : ({A : Sort u} → (x : A) → A) = ((B : Sort u) → B → B) := rfl
```

## De Bruijn index

Inside a term, a bound variable is not stored by name but by a *de Bruijn
index*: `#0` is the variable of the nearest enclosing binder, `#1` the next
one out, and so on. Renaming a variable therefore never changes a term, and
the same variable can have different indices in different places. These
indices are term data, not Forth stack positions.

**Mathematics.** The composition theorem: for propositions $A, B, C$,
$(A \to B) \to (B \to C) \to (A \to C)$, proved by
$\lambda f\ g\ x.\ g\ (f\ x)$. Inside the proof's innermost body the
binders are, from the nearest out, $x, g, f, C, B, A$, so $g\ (f\ x)$ is
`#1 (#2 #0)`. In the statement, $A \to B$ sits under $A, B, C$ and its own
arrow binder, so it reads `#2 -> #2`; $B \to C$ sits one binder deeper
(under $f$) and reads `#2 -> #2` as well.

**LeanForth Forth.** The pinned fixture `tests/reference/composition.lean`,
built innermost first with its binder names, printed raw and in Lean's
notation, then checked by the experimental definition probe:

```forth
fresh
lf-hlevel-zero made lf-hterm-sort made 2constant Prop
0 lf-hterm-bvar made 2constant b0          \ b0 is #0, the nearest binder
1 lf-hterm-bvar made 2constant b1
2 lf-hterm-bvar made 2constant b2
3 lf-hterm-bvar made 2constant b3
4 lf-hterm-bvar made 2constant b4
b2 b2 lf-hterm-pi made 2constant b2->b2    \ A -> B for f, and B -> C for g
\ (A B C : Prop) -> (f : A -> B) -> (g : B -> C) -> A -> C, innermost first
b4 b3 lf-hterm-pi made  b2->b2 >Pi  b2->b2 >Pi
Prop >Pi s" C" implicit  Prop >Pi s" B" implicit  Prop >Pi s" A" implicit
2constant statement
\ fun A B C f g value => g (f value), innermost first
b1  b2 b0 app  app  b4 >fun s" value" named  b2->b2 >fun s" g" named  b2->b2 >fun s" f" named
Prop >fun s" C" implicit  Prop >fun s" B" implicit  Prop >fun s" A" implicit
2constant proof
statement drop .term cr
proof drop .term cr
statement .lean cr
proof .lean cr
index @ statement proof 10000 lf-mixed-definition-probe . cr   \ 0: ok, untrusted
```

```text
(Pi Sort 0, (Pi Sort 0, (Pi Sort 0, (Pi (Pi #2, #2), (Pi (Pi #2, #2), (Pi #4, #3))))))
(fun Sort 0, (fun Sort 0, (fun Sort 0, (fun (Pi #2, #2), (fun (Pi #2, #2), (fun #4, (#1 (#2 #0))))))))
∀ {A B C : Prop}, (A → B) → (B → C) → A → C
fun {A B C} f g value ↦ g (f value)
0
```

`A -> B` and `B -> C` are one shared node, `b2->b2`, because indices are
relative to where they stand. The printer turns the indices back into
names without capturing one variable by another. The probe's *ok* is an
untrusted diagnostic, not an accepted theorem (see
[Kernel and checker](#kernel-and-checker)).

**Lean.** `#print` gives the same two lines as `.lean`:

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

## Constant

A *constant* is a reference, inside a term, to a named declaration,
together with *universe arguments* for that declaration's universe
parameters: `fixtureId.{u}` uses `fixtureId` at level `u`.

**Mathematics.** Given $\mathrm{fixtureId} : \Pi (A : \mathrm{Sort}\ u),\ A \to A$,
the function $\lambda (A : \mathrm{Sort}\ u)\ (x : A).\ \mathrm{fixtureId}_u\ A\ x$
has the same type.

**LeanForth Forth.** A constant node holds a *constant reference*
(`src/core/constant-references.fs`): an interned name plus level
arguments. LeanForth has no checked library of declarations yet, so the
constant's type comes from a *candidate signature* registered with
`lf-msp-put` — an unchecked assumption, which is why nothing here can be a
checked result. The checked environment that replaces it is designed in
[ADR 0012](../adr/0012-checked-environment.md) (approved by the owner, not
yet implemented).

```forth
fresh
1 lf-hlevel-param made 2constant u
u lf-hterm-sort made 2constant Sort-u
0 lf-hterm-bvar made 2constant b0
1 lf-hterm-bvar made 2constant b1
b1 b0 >Pi  Sort-u >Pi  2constant id-type      \ (A : Sort u) -> A -> A
\ Assume, unchecked, that fixtureId.{u} has that type: name, type, parameters.
0 s" fixtureId" lf-name-str made constant fixtureId
create params 1 ,                              \ its parameter list: u
index @ fixtureId id-type params 1 1000 lf-msp-put . cr   \ 0: recorded
\ The constant fixtureId.{u}: a name and one universe argument.
create args u swap , ,                         \ (index identity) of u
fixtureId lf-name-generation @ args 1 lf-cref-new made lf-cterm-new made
2constant fixtureId.{u}
\ fun (A : Sort u) (x : A) => fixtureId.{u} A x
fixtureId.{u} b1 app  b0 app  b0 >fun  Sort-u >fun  2constant poly
poly drop .term cr
index @ poly 1000 lf-mixed-infer . drop .term cr   \ status, inferred type
```

```text
0
(fun Sort u, (fun #0, ((fixtureId.{u} #1) #0)))
0 (Pi Sort u, (Pi #0, #1))
```

**Lean.** The pinned fixture `tests/reference/constant-fixture.lean`:

```lean
universe u
def fixtureId {α : Sort u} (x : α) : α := x
def fixturePoly {α : Sort u} (x : α) : α := fixtureId x
theorem fixtureUse {P : Prop} (h : P) : P := fixtureId h
```

## Declaration

A *declaration* is one named item of a library: its name, its universe
parameters, its type and (for a definition or theorem) its value. Lean's
exporter writes a library as an NDJSON file — one JSON record per line:
names, levels and expressions first, each declaration after the records it
uses.

**Mathematics.** $\mathrm{fixturePoly}_u : \Pi \{\alpha : \mathrm{Sort}\ u\},\ \alpha \to \alpha$,
defined as $\lambda \{\alpha\}\ (x : \alpha).\ \mathrm{fixtureId}_u\ x$.

**LeanForth Forth.** The Forth NDJSON reader (`src/import/ndjson.fs`,
[reader guide](../development/NDJSON_READER.md)) checks each record whole
and hands it to a handler chosen for its kind. Here names go into
LeanForth's name store, and binders and declarations are printed; every
other kind is read and ignored:

```forth
export: library
: ignore-record ( record -- outcome ) drop outcome-ok ;
: ignore-all ( export -- )
  kind-count 0 do ['] ignore-record i 2 pick export-handler ! loop drop ;
\ Names go into LeanForth's name store; name-ids maps export index -> name ID.
create name-ids 64 cells allot  0 name-ids !        \ 0 is the anonymous name
: name-id ( export-index -- id ) cells name-ids + @ ;
: on-name ( record -- outcome )
  dup record-index @ 64 < 0= if drop outcome-full exit then
  dup name-prefix @ name-id over name-part 2@ lf-name-str
  if swap record-index @ cells name-ids + ! outcome-ok else drop outcome-full then ;
: on-binder ( record -- outcome )   \ the name and annotation the export keeps
  ."   binder " dup binder-name @ name-id .lf-name
  binder-info @ if ."  (implicit)" then cr outcome-ok ;
: .kind ( record -- ) record-kind @ kind-thm = if ." theorem " else ." definition " then ;
: on-decl ( record -- outcome )
  dup .kind  dup decl-name @ name-id .lf-name
  ."  universe parameters: " dup decl-params @ over list-count .
  ." type: expression " dup decl-type @ .  ." value: expression " decl-value @ . cr
  outcome-ok ;
lf-name-reset  library export-init . cr  library ignore-all
' on-name kind-name-str library export-handler !
' on-binder kind-forall library export-handler !
' on-binder kind-lam library export-handler !
' on-decl kind-def library export-handler !
' on-decl kind-thm library export-handler !
s" tests/reference/constant-fixture.ndjson" library export-read . cr
```

```text
0
  binder x
  binder α (implicit)
  binder x
  binder α (implicit)
definition fixtureId universe parameters: 1 type: expression 4 value: expression 6
  binder x
  binder α (implicit)
definition fixturePoly universe parameters: 1 type: expression 4 value: expression 11
  binder P (implicit)
  binder h
  binder P (implicit)
theorem fixtureUse universe parameters: 0 type: expression 13 value: expression 18
0
```

`fixtureId` and `fixturePoly` share their type, expression 4. The reader
decides nothing about types: these are decoded records, input for a checker,
not checked declarations. The same reader decodes the whole pinned Mathlib
export (see [project progress](../project/PROJECT_PROGRESS.md#ndjson-support)).

**Lean.** The same three declarations as in [Constant](#constant).

## Theorem and definition

Both are declarations with a type and a value. A *theorem*'s type must be a
proposition — its type must be `Prop` for every choice of its universe
parameters — and its value is a proof. A *definition* may have any type.
Lean also treats them differently later (for example, which ones are
unfolded first), which does not matter here.

**Mathematics.** The composition statement is a proposition. The type
$\Pi (A : \mathrm{Sort}\ u),\ A \to A$ has sort
$\mathrm{Sort}\,(\mathrm{imax}(u+1, \mathrm{imax}(u, u)))$, which Lean's
kernel writes $\mathrm{Sort}\,(\mathrm{imax}(u+1, u))$; it is
$\mathrm{Sort}\ 0$ when $u = 0$ but $\mathrm{Sort}\ 2$ when $u = 1$; it is
not a proposition, so a value of that type can be a definition but not a
theorem.

**LeanForth Forth.** The level shows it; the experimental probe does not
yet check it:

```forth
fresh
1 lf-hlevel-param made lf-hterm-sort made 2constant Sort-u
0 lf-hterm-bvar made 2constant b0
1 lf-hterm-bvar made 2constant b1
b1 b0 >Pi  Sort-u >Pi  2constant id-type      \ (A : Sort u) -> (x : A) -> A
\ The statement's type is Sort l, for a level l that mentions u.
index @ id-type 1000 lf-mixed-infer ok! drop
dup .term cr  lf-term-read made drop nip constant l-of-id
\ The value of l when u = 0 and when u = 1:
: l-at ( n -- ) lf-lassign-reset 1 swap lf-lassign-add made
  l-of-id 1000 lf-level-value-assigned ok! . ;
0 l-at  1 l-at cr                               \ 0 2: not zero for every u
\ As a definition the pair is fine; as a theorem it is rejected (rule S3).
b0 b0 >fun  Sort-u >fun  2constant id-value
index @ id-type id-value 1000 lf-mixed-definition-probe .
index @ id-type id-value 1000 lf-mixed-theorem-probe . cr
```

```text
Sort imax((u+1), u)
0 2
0 4
```

The definition probe's *ok* only says the value has the claimed type. The
theorem probe also asks Lean's question "is the statement a proposition?":
the level of its Sort must be zero for every value of `u`, and with every
parameter 1 this one is 2, so rule S3 of
[ADR 0011](../adr/0011-definite-rejection.md) rejects it (Lean's
`normalizes_to_zero` is false exactly when that value is not zero).

**Lean.** As a definition the pair is accepted (`polyId` under
[Term](#term)); as a theorem Lean rejects it:

```lean
universe u
theorem polyIdThm : (A : Sort u) → A → A := fun (A : Sort u) (x : A) => x
```

```text
error: type of theorem `polyIdThm` is not a proposition
  (A : Sort u) → A → A
```

## Kernel and checker

The *kernel* is the small program that checks a declaration's value
against its type and decides whether it may join the library. Everything
else — parsers, tactics, AI tools, printers, the NDJSON reader — is
*untrusted*: its mistakes can at worst present the wrong claim to the
kernel, never make a wrong proof pass. LeanForth's kernel is being written
in `src/kernel/`; until it passes the review gate in `AGENTS.md` it is
"the checker under development", and its results are diagnostics.

**Mathematics.** $\lambda A\ x.\ x$ has the type
$\Pi (A : \mathrm{Sort}\ u),\ A \to A$; $\lambda A\ x.\ A$ does not (it
returns the type $A$, not an element of $A$).

**LeanForth Forth.** The experimental definition probe infers the value's
type and compares it with the claim:

```forth
fresh
1 lf-hlevel-param made lf-hterm-sort made 2constant Sort-u
0 lf-hterm-bvar made 2constant b0
1 lf-hterm-bvar made 2constant b1
b1 b0 >Pi  Sort-u >Pi  2constant id-type      \ (A : Sort u) -> (x : A) -> A
b0 b0 >fun  Sort-u >fun  2constant good-value \ fun (A : Sort u) (x : A) => x
b1 b0 >fun  Sort-u >fun  2constant bad-value  \ fun (A : Sort u) (x : A) => A
index @ id-type good-value 1000 lf-mixed-definition-probe .   \ 0: ok
index @ id-type bad-value 1000 lf-mixed-definition-probe .    \ 4: rejected
cr lf-diag. cr
```

```text
0 4
rejected: declared type mismatch (D1-D5) at mixed-definition-probe lf-mixed-definition-probe: 10 0 
```

The wrong value is *rejected* by the first checker's rules, which the
owner approved on 2026-11-02 ([ADR 0011](../adr/0011-definite-rejection.md))
and which the probe now applies (plan task 2.2.1; [kernel] code, not yet
through the review gate): its type ends in `Sort u` where the claim ends
in `A`, a Sort against a variable that is not a proof, so rule D2 shows
them different inside D4 — like the `returns-the-proposition` row of the
[expected results](../reviews/FIRST_CHECKER_EXPECTED.md). The diagnostic
names the rules used, as a set of bits (2 for D2, 8 for D4: 10). The full
check of a declaration, `check-declaration` (plan task 2.2.3; also
experimental and not yet through its gate), adds the name, the universe
parameters, the lookups of constants in the checked environment and, for
a theorem, the proposition test, and prints an accepted result as
*accepted (experimental, not independently audited); axioms: none*
([first check](FIRST_CHECK.md)).

**Lean.** Lean accepts `polyId` (under [Term](#term)) and rejects the wrong
value:

```lean
universe u
def wrongId : (A : Sort u) → A → A := fun (A : Sort u) (x : A) => A
```

```text
error: Type mismatch
  A
has type
  Sort u
of sort `Type u` but is expected to have type
  A
of sort `Sort u`
```

Lean also reports the axioms a theorem depends on; the first checker
prints the same list (always empty in its scope):

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
#print axioms composition
```

```text
'composition' does not depend on any axioms
```

## Outcomes

Every LeanForth check ends in exactly one *outcome*, a number from
`src/lib/outcome.fs` ([ADR 0008](../adr/0008-outcome-vocabulary.md)). The
numbers are stable; scripts may rely on them.

| Outcome | Value | Meaning | Lean counterpart |
| --- | ---: | --- | --- |
| ok | 0 | Succeeded. For the first checker: *accepted — experimental, not independently audited*. | Lean accepts. |
| invalid | 1 | Malformed input or corrupted state. | Input Lean's export cannot even express, such as a variable no binder covers. |
| exhausted | 2 | Out of fuel: the processing budget ran out. More time might decide it. | None comparable (Lean's own time limits differ). |
| unknown | 3 | Supported, but the cautious rules cannot decide. | Lean may accept or reject. |
| rejected | 4 | Definitely wrong, and Lean rejects it too, by a rule of [ADR 0011](../adr/0011-definite-rejection.md). | Lean rejects, for the same reason. |
| unsupported | 5 | Uses a feature LeanForth has not built yet (for example `let`, literals, data types). | Lean accepts the feature. |
| full | 6 | Out of room: a store, stack, depth or size limit was reached. More memory might decide it. | None comparable. |

For the owner's three-way summary: *ok* is **accepted**, *rejected* is
**rejected**, and *unknown* and *unsupported* together are
**unsupported/unknown**; *invalid*, *exhausted* and *full* are reported
separately. **Only ok is ever accepted;** no other outcome is ever
reported, stored or cached as success. An outcome is a status, not a flag:
0 means success, so test it with `ok?`, never with `IF`.

**LeanForth Forth.** Each outcome the current code can produce, reached on
purpose:

```forth
outcome-ok . outcome-invalid . outcome-exhausted . outcome-unknown .
outcome-rejected . outcome-unsupported . outcome-full . cr
fresh
1 lf-hlevel-param made lf-hterm-sort made 2constant Sort-u
0 lf-hterm-bvar made 2constant b0
1 lf-hterm-bvar made 2constant b1
b1 b0 >Pi  Sort-u >Pi  2constant id-type
b0 b0 >fun  Sort-u >fun  2constant id-value
b1 b0 >fun  Sort-u >fun  2constant bad-value
b0 b0 >fun  2constant open-term                        \ fun (x : #0) => x: #0 is unbound
0 s" k" lf-name-str made lf-name-generation @ 0 0 lf-cref-new made
lf-cterm-new made 2constant k-term                    \ a constant k, never declared
index @ id-type id-value 1000 lf-mixed-definition-probe .  \ ok
index @ open-term 1000 lf-mixed-infer . 2drop              \ invalid
index @ id-type id-value 10 lf-mixed-definition-probe .    \ exhausted: fuel 10
index @ k-term 1000 lf-mixed-infer . 2drop                 \ unknown
index @ id-type bad-value 1000 lf-mixed-definition-probe . \ rejected
: use-up-nodes ( -- ) begin 0 lf-hterm-bvar while 2drop repeat ;   \ all 64 nodes
use-up-nodes  index @ Sort-u 1000 lf-mixed-infer . 2drop   \ full
cr
export: library  library export-init drop
s" tests/reference/identity.ndjson" library export-read .  \ unsupported: no handlers
cr
```

```text
0 1 2 3 4 5 6
0 1 2 3 4 6
5
```

`k-term` is *unknown* to this experimental inference: the signature index
holds no candidate type for `k`, so it cannot tell (a declaration's check
asks the checked environment instead, where an undeclared name is rule
N1, *rejected*). Until 2026-11-03 this example used
`fun (A : Sort (max u u)) (x : A) => x`, which was *unknown* because the
comparison did not normalise levels; it now compares levels as Lean's
kernel does, equates `max u u` with `u` and answers *ok*, as Lean does
([ADR 0011, Amendment 1](../adr/0011-definite-rejection.md#amendment-1-proposed-2026-11-03-universe-levels-are-built-and-compared-as-lean-builds-and-compares-them)). The last
line is the NDJSON reader refusing a record kind for which no handler was
set: it never skips a record silently.

**Lean.** Lean has two answers, accepted or an error. The first checker's
expected-results table pairs Lean's verdict with LeanForth's required
outcome for the five pinned fixtures and their broken copies
([expected results](../reviews/FIRST_CHECKER_EXPECTED.md)); for example
`composition` above is accepted by Lean and must be *ok*, and `wrongId`
is rejected by Lean and must be *rejected* or *unknown* — never *ok*.
