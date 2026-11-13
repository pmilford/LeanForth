# FE2: natural terms, statements and definitions

Plan row FE2 ([plan](../project/PLAN_DRAFT.md#phase-8-front-end-fe1fe12-2026-11-12-replaces-831-and-832);
[front-end design](FRONT_END.md); [ADR 0021](../adr/0021-front-end.md)).
Status (2026-11-12): **designed**; nothing of it is written. FE2 comes
after FE1 and FE1i in the owner's order (FE1, FE1i, FE2, FE3–FE5, …) and
delivers plan row 8.6.10. This page is the design a Forth implementer
starts from: the scope, the LeanForth spelling of every term form, how
pinned Lean 4.35.0 elaborates each (file and line references under
`src/lean/Lean/` of the pinned toolchain), pinned Lean's terms for the
acceptance cases (probes in §10), what FE2 reuses from FE1, its modules,
tests and sub-steps, and three questions for the owner. Exactness (owner,
2026-11-12, "Front-end syntax", answer 7): every statement and every term
FE2 elaborates must equal Lean's node for node; where FE2 has not ported
what Lean would do, it answers *unsupported* at the token, never a
different term.

## In plain words

FE1 lets a person write $0 + n = n$ and prove it with a few tactic
words. FE2 is everything else a person writes in a statement or a short
proof: functions (`fun x => x + 1`), "for all" with hidden arguments
(`∀ {α : Type} (a : α), a = a`), local definitions (`let`, `have`),
pairs (`⟨1, 2⟩`), fields (`p.1`, `l.length`), hidden arguments given by
hand (`@Eq.refl Nat 0`, `Eq.refl (α := Nat) 0`), types left for the
elaborator to find (`_`), and names Lean binds by itself (`α` in
`(a : α)`). Each has a LeanForth spelling in postfix words, and each is
elaborated by Lean's own algorithm, ported to Forth, so the term is the
one Lean builds. One example in three forms:

- **Mathematics:** the function $x \mapsto x + 1$ on the natural numbers.
- **LeanForth:** `Nat explicit: x  x 1 +  fun` (read: "for a natural
  number $x$, $x + 1$; make it a function"), or with the type left to the
  elaborator, `_ explicit: x  x 1 +  fun`, where the expected type
  `Nat → Nat` supplies it.
- **Lean:** `fun (x : Nat) => x + 1`, or `(fun x => x + 1 : Nat → Nat)`.
  Pinned Lean elaborates both to `fun (x : Nat) => @HAdd.hAdd Nat Nat Nat
  (@instHAdd Nat instAddNat) x 1` (§4, A1 and A2).

As in FE1, nothing FE2 builds is trusted: every declaration goes to the
kernel through the export records (ADR 0021 D1), and every statement is
printed back in three forms (D4).

## 1. Scope

### 1.1 The forms FE2 gives natural LeanForth

The plan row lists: implicit, strict-implicit, instance and named
arguments, the explicit form inside natural text, holes `_` (error 52
lifted), `fun` with inferred binder types, `let`, `have`, `show`, type
ascription, anonymous constructors, casts (`h ▸ e`), `variable`,
`section`, auto-bound implicits, universe inference, postponement, the
printer's natural mode and a gap ledger. Each row below is one Lean form,
its LeanForth spelling (§2 gives the rules), the Lean elaborator, and
what FE2 does.

| Lean form | LeanForth (natural) | Lean elaborator | FE2 |
| --- | --- | --- | --- |
| `Prop`, `Type`, `Type u`, `Sort u`, `Type _` | `Prop`, `0 Type`, `u Type`, `u Sort`, `_ Type` | `elabProp`, `elabTypeStx`, `elabSort` (BuiltinTerm.lean:21-34) | yes (FE1a left the natural sorts out) |
| `A → B` | `A B ->` | `elabArrow` (Binders.lean:293): both sides `elabType`, independently; binder name `a` with a reserved macro scope | yes |
| `∀ (x : A), p`, `∀ {x : A}`, `∀ [C α]`, `∀ ⦃x⦄`, `(x : A) → B` | `A explicit: x  p  forall` (also `implicit:`, `instance:`, `strict-implicit:`) | `elabForall` (278), `elabDepArrow` (310), `elabBinders` (258): each binder type `elabType`, `withLocalDecl`, then the body `elabType`, `mkForallFVars` | yes |
| `fun (x : A) => b`, `fun {x} (y : A) => b` | `A explicit: x  b  fun` (one `fun` closes one binder) | `elabFun` (678), `elabFunBinders` (462): binder type `elabType`, then `propagateExpectedType` (410) unifies it with the expected domain, then the body `elabTermEnsuringType`; `mkLambdaFVars` | yes |
| `fun x => b`, `∀ x, p` (type omitted) | `_ explicit: x  b  fun` | `expandFunBinders` (360) gives the binder the type `_` (`mkHole`) | yes |
| `_` | `_` | `elabHole` (BuiltinTerm.lean:64): a natural metavariable of the expected type | yes (error 52 lifted) |
| `@f a b c` | `a b c @ f`; unapplied `@ ' f` | `elabExplicit` (App.lean:2278), `elabAppArgs` with `explicit := true`: implicit binders take arguments (`processImplicitArg`, 882); `_` at an instance binder is still synthesized (903) | yes |
| `f (x := v)` | `v named: x  f` | `elabAppArgs` named arguments: a binder whose name matches takes the value; an explicit binder left before it becomes an eta argument (`addEtaArg`, 734) unless a named argument depends on it (`findNamedArgDependsOnCurrent?`, 340) | yes |
| `f a` with `(b : T := d)` left out | `a f` | `processExplicitArg` (766): an `optParam` binder with no argument left takes its default | yes; `autoParam` answers unsupported until its tactic exists (§1.3) |
| `let x : T := v; b`, `let x := v; b` | `T v let: x  b  let`, `_ v let: x  b  let` | `elabLetDeclAux` (745): binders, `T` under `withSynthesize (postpone := .partial)`, `v` against `T`, then the body in `withLetDecl` | yes |
| `have h : T := v; b` | `T v have: h  b  have` | the same with `nondep := true` (942): the body cannot unfold `h` (`Meta/WHNF.lean`:400 unfolds only `nondep := false`) | yes |
| `show T from e` | `T e show` | `elabShow` (BuiltinNotation.lean:114): `T` unified with the expected type first, then elaborated as `have this : T := e; this` | yes |
| `(e : T)` | `e T :` | `elabTypeAscription` (428): `T` under `withSynthesize (postpone := .yes)`, then `e` against `T`, then `ensureHasType` | yes (`(e :)`, ascription without a type, left out: §1.3) |
| `⟨a, b, c⟩` | `⟨ a b c ⟩` | `elabAnonymousCtor` (43): postponed until the expected type is known; its `whnf` must be a one-constructor inductive; extra components nest into the last field | yes |
| `e.1`, `e.fst`, `e.f a` (generalized field notation) | `e .1`, `e .fst`, `e .f  a $` | `elabAppLValsAux` (App.lean:1843), `resolveLValAux` (1517), `findMethod?` (1453), `addLValArg` (1735), `mkBaseProjections` (1700) | yes |
| `"text"`, `'c'`, `1.5`, `nat_lit 5`, numerals of any size | `s" text"`, `'c'`, `1.5`, `5 nat_lit`, `123456789012345678901` | `elabStrLit` (198), `elabCharLit` (248: `Char.ofNat (nat_lit k)`), `elabScientificLit` (237: `OfScientific`), `elabRawNatLit` (231), `elabNumLit` (210) | yes |
| `sorry` | `sorry` | `elabSorry` (BuiltinNotation.lean:242): `mkLabeledSorry` with a unique tag | yes, as [ADR 0021 Amendment 1](../adr/0021-front-end.md#amendment-1-2026-11-12-late-night-sorry-as-in-lean-with-a-conditional-report) |
| `h ▸ e` | `h e ▸` | `elabSubst` (BuiltinNotation.lean:457): motive by `kabstract`, both sides tried, `Eq.rec` | yes, with FE1g's `kabstract`; its `subst` fallback waits for FE5 |
| operators beyond FE1's four: `≠ < > ≥ - / % ^ ∣ ∈ ∧ ∨ ↔ ¬ ∃ ×`, unary `-` | the same symbols as words (`neg-` for unary minus: question 2) | `binop%`, `binrel%`, `binrel_no_prop%`, `unop%`, `leftact%`, `rightact%` (`Elab/Extra.lean`), plain macros (`×` is `Prod`, `∃ x, p` is `Exists fun x => p`) | yes, one row of the notation table each (§2.3) |
| implicit lambda: `fun a => a` against `∀ {α}, α → α` | nothing to write | `useImplicitLambda` (TermElabM.lean:1771), `elabImplicitLambda` (1834) | yes |
| postponement: `(fun f => f 1) Nat.succ` | `_ explicit: f  f 1 $  fun  ' Nat.succ $` | `tryPostpone` (1370), `postponeElabTerm` (1636), `resumePostponed` (SyntheticMVars.lean:32) | yes (FE1e answers unsupported) |
| auto-bound implicits: `theorem t (a : α) : …` | `α explicit: a` with `α` unknown | `withAutoBoundImplicit` (TermElabM.lean:1988): restart with `{α : Sort ?u}`, then `addAutoBoundImplicits` (2100) | yes, Lean's default (on, relaxed: AutoBound.lean:17-25) |
| universe inference: `u_1`, `u_2` | nothing to write | `levelMVarToParam` (TermElabM.lean:1059), `sortDeclLevelParams` (DeclUtil.lean:79) | yes |
| `variable`, `section S … end S`, `universe u` | `variable  A explicit: x …`, `section S … end S`, `universe u` outside a declaration | `Command` scopes; inclusion of section variables (`withHeaderSecVars`, MutualDef.lean:455) | yes |
| `set_option autoImplicit false` | `set_option autoImplicit false` | the options of AutoBound.lean:17-25 | yes, for these two options only |
| `#check NAME` (signature) and terms with holes | `' NAME #check`, `_ explicit: x  x  fun #check` | `elabCheck` (BuiltinCommand.lean:434) | yes (FE1e answered unsupported) |
| nested tactic blocks `⟨x, by tac⟩`, `show T by tac` | `by … by-end` inside a term | `elabByTactic` (BuiltinTerm.lean:178): a synthetic opaque metavariable run at the end of elaboration | yes, with the tactics that exist (FE1g, FE1i) |

### 1.2 Additions to the plan row, with reasons

- **Local instances.** FE1e answers *unsupported* when an instance
  problem meets a local hypothesis whose type is a class (lifted by FE3 in
  FE1e's table). FE2 must lift it: instance binders are an FE2 form, and
  without local instances no statement with `[Add α]` elaborates (A6).
  Lean adds a local instance when a binder's type is a class
  (`elabFunBinderViews`, Binders.lean:444; `withLocalDecl` in `Meta`) and
  `getInstances` appends the local instances of the class after the global
  candidates (Meta/SynthInstance.lean:230-239), so they are tried first.
  Declaring classes and instances stays FE3.
- **The natural words FE1a left out**: `Prop`, `Type`, `Sort`, `->`,
  `fun`, `forall`, `_` (FE1a's status line; FE1G_TACTICS.md §3.1 waits
  for `Prop` and `->` to test `by-intro:` in a file), numerals of more
  than nine digits, and names whose argument count needs unfolding (error
  73, lifted with FE1c's `whnf`, §2.1).
- **`sorry`** as a term, decided by the owner after the plan row was
  written (ADR 0021 Amendment 1).
- **Operator words beyond `+ = * ≤`**, because the Init round trip of the
  plan row's acceptance prints every statement in natural form, and Init's
  statements use `<`, `≠`, `∧`, `∨`, `¬`, `↔`, `∃`, `-`, `/`, `%`, `^`,
  `∈`, `∣`, `×` and more (question 2).
- **Nested tactic blocks** in terms (Lean's `⟨2, by decide⟩`), because Lean
  writes them constantly and FE1g and FE1i already provide the proof
  state and the first tactics; only the term-level entry is new.

### 1.3 Left for later rows, with reasons

| Form | Why not FE2 | Row |
| --- | --- | --- |
| Coercions: `↑e`, insertion when `ensureHasType` fails, coercion in `binop%` trees | needs the coercion classes and their unfolding | FE4 (until then *unsupported*, as in FE1e; so a plain type mismatch, E7, is *unsupported* rather than Lean's error) |
| `class`, `instance` declarations, `#synth`, instance loops, Π-typed instance goals | the class machinery | FE3 |
| `match`, `fun` with patterns (`fun (a, b) => …`, `fun \| … `), `let` with a pattern, `..` in applications | pattern compilation | FE7 |
| Recursion (`let rec`, a definition that names itself), `termination_by` | structural and well-founded recursion | FE8 |
| `autoParam` binders left out (`(h : p := by tac)`) | runs a tactic; each one is supported when its tactic is | FE5, FE9, FE10 |
| Structure instances `{ x := 1, y := 2 }`, `{ s with … }` | `StructInst.lean` (1,422 lines) and structure declarations | FE6 |
| `·` function notation `(· + 1)` | needs parentheses to delimit its scope, which postfix text does not have; `_ explicit: x  x 1 +  fun` says the same | not planned (it is sugar for `fun`) |
| `(e :)`, `@` before anything but a name (`@(fun …)`, which only switches implicit lambdas off), `no_implicit_lambda%` | rare; each needs its own word | a later row if the round trip meets them |
| `?x` synthetic holes | used by `refine` | FE5 (`by-refine`) |
| `do` notation, `s!` interpolated strings, `\|>.`, `<\|>` | programs, macros | FE12 and later rows |

### 1.4 What answers unsupported in FE2, and when it is lifted

Everything FE1e's table (FE1E_APPLICATIONS.md §2.7) lists for FE2 is
lifted: postponement, implicit lambdas, named arguments, `@`, holes,
`optParam`, printing terms with holes, the other operator macros. What
remains *unsupported*, each at its token, with an error code that names
the row: a coercion (FE4); a Π-typed instance goal or an instance answer
that keeps metavariables (FE3, as in FE1e); an elaborator for a form of
§1.3; an
`autoParam` whose tactic does not exist; a notation whose word is not in
the notation table yet (§2.3). Never a guess, never a different term.

## 2. LeanForth spellings

### 2.1 Rules

Every natural text stands for exactly one Lean term in Lean's syntax
after macro expansion; the reader builds that syntax tree (FE1a's store,
new kinds in §5.1) and the elaborator runs Lean's algorithm on it, in
Lean's order, after the text that the tree belongs to has been read (the
statement at `:=`, the value at `end NAME`). So **reading order never
decides elaboration order**, and every case of §4 is a pair of a LeanForth
text and the Lean text it stands for. The printer's natural mode (§5.4)
writes the LeanForth text back.

1. **Binder words take a type, then read a name** (ADR 0017 §7, as in the
   kernel form): `A explicit: x`, `A implicit: x`, `A strict-implicit: x`,
   `A instance: x`. Where Lean omits the type, the type is the hole `_`
   (question 1): Lean itself turns `fun x` and `∀ x` into `(x : _)`
   (`expandFunBinders`, Binders.lean:375-387). `_` as a binder's *name*
   is Lean's `(_ : T)`, a fresh inaccessible name (`expandBinderIdent`,
   Binders.lean:31), and for an instance binder Lean's unnamed `[Add α]`,
   named `inst` with a macro scope (`expandOptIdent`, 37). A default value
   `(b : T := d)` is written as the type Lean makes of it, `T d optParam`
   (`expandBinderModifier`, 112; A31).
2. **Closers close one binder**: `fun` (λ), `forall` (Π), `∃` (`Exists
   fun x => …`), each taking the body; `let` and `have` close `let:` and
   `have:`. Consecutive closers are Lean's nested binders: pinned Lean
   gives the same term for `fun (x : Nat) => fun (y : Nat) => x + y` and
   `fun (x y : Nat) => x + y`, and for `fun {α} => fun (a : α) => a` and
   `fun {α} (a : α) => a` (probe p3, N1 and N2). So "there is a $y$
   with $x < y$" is `_ explicit: y  x y <  ∃` (the `exists: p` of
   [PROOF_DEVELOPMENT.md](PROOF_DEVELOPMENT.md) §5 was illustrative).
3. **A name takes its explicit arguments from the stack** (FE1a): as many
   as its type has explicit binders, counted on the type's Π telescope
   with each result unfolded by FE1c's `whnf` at default transparency (as
   Lean's `forallTelescopeReducing`; this lifts error 73), **not counting
   `optParam` and `autoParam` binders** (Lean fills those when no argument
   is left, so they are given with `$` or `named:`). For a variable the
   telescope is its binder's type, elaborated for this count alone in a
   saved state that is then rolled back (FE1g's undo trail), so the real
   elaboration still happens later in Lean's order; a type that is a hole
   or whose head is a metavariable counts 0, and such a variable is
   applied with `$` (`f 1 $`). An auto-bound name (§3.9) counts 0.
4. **`named:` values are taken first.** `v named: x` makes a named
   argument; a name word first takes every named argument on top of the
   stack, then its positional arguments, not counting an explicit binder
   that a named argument names (Lean's `(x := v)` may stand anywhere in
   the application; its place does not change the term).
5. **Modifiers before a name**: `'` (FE1a: the name applied to nothing,
   named arguments still taken), `@` (Lean's `@`: the name takes one value
   for *every* binder of its telescope, implicit and instance ones
   included, `optParam` too, since Lean's explicit mode fills nothing), and
   `@ '` (Lean's bare `@f`, applied later with `$`). `.{ … }` before a
   name gives its universe arguments (`.{ 1 } Eq` is `Eq.{1}`); levels
   are built with the kernel form's level words, which natural text gains
   too (`u 1 level+ Type` is `Type (u + 1)`, `u v level-max`, `_` for a
   level hole); in natural text `^` is Lean's power (question 2).
6. **Brackets mark the stack**: `⟨` marks the depth and `⟩` takes every
   value above it as the components, as FE1g's `by-rw[ … ]` does; nesting
   is allowed; an empty `⟨ ⟩` is Lean's `⟨⟩`.
7. **Field words**: a token `.NAME` or `.N` (a field name or index;
   no Lean identifier starts with `.`, so rule R1 holds) takes one value,
   the object, and builds Lean's `e.NAME`; further arguments with `$`
   (`l .map  ' Nat.succ $` is `l.map Nat.succ`, question 3).
8. **Values left on the stack** at `:=`, `end NAME`, a closer, `⟩` or a
   command word are errors, as in FE1a and FE1g.

### 2.2 The words

Stack effects are the reader's: `t` is a syntax value, `T` one standing
for a type. The tree node is the new kind of §5.1.

| Word | Stack effect | Lean syntax it stands for |
| --- | --- | --- |
| `Prop` | `( -- t )` | `Prop` |
| `Type`, `Sort` | `( l -- t )` | `Type l`, `Sort l` (as the kernel form; `0 Type` is Lean's `Type`, `_ Type` is `Type _`) |
| `->` | `( A B -- t )` | `A → B` |
| `explicit:` `implicit:` `strict-implicit:` `instance:` NAME | `( T -- )`, opens a binder | `(x : T)`, `{x : T}`, `⦃x : T⦄`, `[x : T]` |
| `fun`, `forall`, `∃` | `( body -- t )`, closes the innermost binder | `fun x => body`, `∀ x, body`, `∃ x, body` |
| `_` | `( -- t )` | `_` |
| `let:` NAME … `let` | `( T v -- )` … `( body -- t )` | `let x : T := v; body` |
| `have:` NAME … `have` | `( T v -- )` … `( body -- t )` | `have x : T := v; body` (Lean's unnamed `have : T := v` is the name `this`; `_` is Lean's `have _ : T := v`, a fresh inaccessible name) |
| `show` | `( T e -- t )` | `show T from e` |
| `:` | `( e T -- t )` | `(e : T)` |
| `⟨` … `⟩` | `( -- )` … `( c1 … ck -- t )` | `⟨c1, …, ck⟩` |
| `.NAME`, `.N` | `( e -- t )` | `e.NAME`, `e.N` |
| `@` NAME, `@ '` NAME | `( a1 … an -- t )`, `( -- t )` | `@NAME a1 … an`, `@NAME` |
| `named:` NAME | `( v -- n )` | `(NAME := v)`, taken by the next name word |
| `.{` … `}` | `( -- )` … `( l1 … lk -- )`, before a name | `NAME.{l1, …, lk}` |
| `s"` text`"` | `( -- t )` | `"text"` (ADR 0017 §14) |
| `'c'` | `( -- t )` | `'c'` (one UTF-8 character, or one of Lean's escapes such as `'\n'`; Forth-2012 reads `'c'` as the character's code, so the token already means that character to a Forth reader) |
| `1.5`, `15e-1` | `( -- t )` | Lean's scientific literal |
| `nat_lit` | `( n -- t )` | `nat_lit n` |
| `sorry` | `( -- t )` | `sorry` |
| `▸` | `( h e -- t )` | `h ▸ e` |
| operator words (§2.3) | `( a b -- t )`, `( a -- t )` | `a OP b`, `OP a` |
| `by` … `by-end` inside a term | `( -- t )` | `by tac` |
| `variable` | `( -- )` | `variable`: the binder words up to the next command word are section variables |
| `section` NAME, `end` NAME | `( -- )` | `section NAME`, `end NAME` (LeanForth's `end` reads a name, so sections are named) |
| `universe` NAME (outside a declaration) | `( -- )` | `universe u` |
| `set_option` NAME VALUE | `( -- )` | `set_option autoImplicit false` (and `relaxedAutoImplicit`) |
| `#check` | `( t -- )` | `#check t`; with `' NAME` the signature form |

Every word is either a Lean keyword (`fun`, `forall`, `let`, `have`,
`show`, `sorry`, `variable`, `section`, `universe`, `set_option`,
`Prop`, `Type`, `Sort`, `_`) or contains a character no Lean identifier
has, so rule R1 of ADR 0017 holds. `:`, `@`, `^`, `-`, `/` and `<` are
Forth words with other meanings, invisible in theorem text, which runs
with only LeanForth's wordlists in the search order (ADR 0017 §3; the
owner's answer 1 of 2026-11-12 for `+ = * ≤`); question 2 asks the owner
to extend that answer to these.

### 2.3 Operator words: the notation table, version 2

FE1a checks each operator word against the printer's notation table
(`src/present/notation-table.fs`), so one table says how a constant
prints and what the word builds. FE2 extends the table (version 2) with a
column for Lean's macro: `binop%` (`+ - * / %`, Init/Notation.lean:30x),
`binrel%` (`= < ≤ > ≥`, and `≠`, Init/Core.lean:882), `binrel_no_prop%`
(`==`, `!=`), `unop%` (unary `-`, Notation.lean:313), `rightact%` (`^`,
311), `leftact%`, `binop_lazy%`, or a plain notation (`∧`, `∨`, `↔`, `¬`
are `And`, `Or`, `Iff`, `Not` applications, Notation.lean:404-406 and
Core.lean:197: probe p1's A36 prints `Iff (Not (And p q)) (p → Not q)`;
`×` is `Prod`; `∈` is `Membership.mem` with its arguments swapped), and
the binder notation `∃` (`Exists fun x => p`). Each row records the macro
that pinned Lean's own expansion shows.
A row is added for each notation the Init round trip meets (§7.4), each
with Lean's macro from `Init/Notation.lean`, `Init/Core.lean` or
`Init/Prelude.lean`, checked against pinned Lean's macro expansion as
FE1a's four are. The word is Lean's symbol, in both of Lean's spellings
where Lean has two (`≤` and `<=`, `∧` and `/\`; Lean's ASCII `->` is
already the arrow word, with the same meaning), except unary minus, which
shares Lean's `-` with subtraction (proposed `neg-`, question 2).

### 2.4 Examples in three forms

**A function.** Mathematics: $x \mapsto x + 1$ on $\mathbb{N}$.
LeanForth: `Nat explicit: x  x 1 +  fun`. Lean: `fun (x : Nat) => x + 1`.

**"For all" with an implicit binder.** Mathematics: for every type
$\alpha$ and every $a \in \alpha$, $a = a$. LeanForth:

```text
0 Type implicit: α   α explicit: a   a a =   forall forall
```

Lean: `∀ {α : Type} (a : α), a = a`.

**`let` and `have`.** Mathematics: with $x = 2$, $x + x$; and "since
$1 = 1$ (by reflexivity), call that fact $h$; then $h$". LeanForth:
`_ 2 let: x  x x +  let` and `1 1 = rfl have: h  h  have`. Lean: `let x
:= 2; x + x` and `have h : 1 = 1 := rfl; h`.

**An anonymous constructor and a field.** Mathematics: the pair $(1, 2)$
in $\mathbb{N} \times \mathbb{N}$, and the first component of a pair $p$.
LeanForth: `⟨ 1 2 ⟩  Nat Nat ×  :` and `Nat Nat × explicit: p  p .1
fun`. Lean: `(⟨1, 2⟩ : Nat × Nat)` and `fun (p : Nat × Nat) => p.1`.

**Commutativity of addition** (the plan row's statement, in about as many
tokens as Lean's: 13 words against Lean's 14 tokens for `(m n : Nat) : m +
n = n + m`):

```text
\ Lean: theorem add_comm' (m n : Nat) : m + n = n + m := Nat.add_comm m n
theorem add_comm'
  Nat explicit: m   Nat explicit: n
  m n +  n m +  =
:=
  m n Nat.add_comm
end add_comm'
```

## 3. How each form elaborates in Lean, and what FE2 ports

Each paragraph names Lean's functions in the order they act; FE2 ports
them in that order (Lean's argument orders of `isDefEq` kept, as
FE1E_APPLICATIONS.md §2 requires).

### 3.1 Sorts and arrows

`elabProp`, `elabSort`, `elabTypeStx` (BuiltinTerm.lean:21-34) build
`Sort 0`, `Sort l`, `Sort (l+1)`; `elabLevel` (`Elab/Level.lean`) turns a
level hole into a level metavariable and a name into a parameter
(auto-bound when unknown and `autoImplicit` is on:
`isValidAutoBoundLevelName`, AutoBound.lean:69). `elabArrow`
(Binders.lean:293) elaborates both sides with `elabType`, independently
(no expected type), and names the binder `_internal.a` with the reserved
macro scope, the name the kernel form's `->` writes.

### 3.2 Binders, `∀` and the local context

`elabBinders` (Binders.lean:258) and `elabBinderViews` (208): for each
binder, `elabType` of its type, a check that an instance binder's type is
a class (`checkBinderAnnotations`, 216; `checkLocalInstanceParameters`),
then `withLocalDecl` with the binder's name, kind and type, which also
records a local instance when the type is a class. `elabForall` (278)
elaborates the body with `elabType` and closes with `mkForallFVars`.
FE2 builds these local declarations in FE1g-1's **context views**
(FE1G_TACTICS.md §4.1: free variable, user name, binder kind,
inaccessible flag), so a binder's name and kind reach the term exactly as
Lean's `LocalDecl` gives them to `mkForallFVars`; the view gains a
*local instances* list (Lean's `LocalInstances`, class name and free
variable), which FE1e's `getInstances` reads (§1.2).

### 3.3 `fun` and expected types

`elabFun` (678) calls `elabFunBinders` (462) with the expected type: for
each binder, `elabType` of its type (a hole becomes a metavariable),
then `propagateExpectedType` (410): the expected type is put in `whnfForall`
form and, when it is a Π, `isDefEq fvarType domain` (in that order) and
the expected type moves under the binder; when it is not, propagation
stops. The body is elaborated with `elabTermEnsuringType` against what is
left, and `mkLambdaFVars` closes. This is how `(fun x => x + 1 : Nat →
Nat)` gets `x : Nat` (A2) and why `theorem … : ∀ n : Nat, n + 0 = n :=
fun n => rfl` elaborates `rfl` against `n + 0 = n` (A4). A `fun` binder
whose type is a class becomes a local instance for the body
(`elabFunBinderViews`, 444).

### 3.4 Implicit lambdas and postponement

Before any elaborator runs (`elabTermAux`, TermElabM.lean:1851),
`useImplicitLambda` (1771) looks at the expected type: when its
`whnfForall` is a Π with an implicit or instance binder and the syntax is
not one that blocks it (`blockImplicitLambda`, 1744: `@`, an explicit
application, `fun` with an implicit binder, a hole, a `by` block,
`no_implicit_lambda%`, a type ascription),
`elabImplicitLambda` (1834) introduces those binders as locals, elaborates
the term against the rest and closes with `mkLambdaFVars` (A23: `def idFn :
∀ {α : Type}, α → α := fun a => a` gives `fun {α : Type} (a : α) => a`).
When the term is a local variable whose type is still a metavariable, the
elaborator postpones instead.

Postponement: an elaborator that needs a type not yet known calls
`tryPostpone` (1370), `tryPostponeIfMVar`, `tryPostponeIfNoneOrMVar` (used
by `⟨…⟩`), which throw a postpone exception when postponing is allowed;
`elabTermAux` catches it and `postponeElabTerm` (1636) makes a synthetic
metavariable of kind `.postponed` holding the syntax and the saved
context (local context, local instances, options). The rounds of
`synthesizeSyntheticMVars` (FE1e's `elab-pending.fs`) resume postponed
metavariables in creation order with `resumePostponed`
(SyntheticMVars.lean:32): first with `postponeOnError` true (an error
postpones again), and when nothing else progresses, with it false (the
error is reported). FE1e ported the rounds for type-class metavariables
only; FE2 adds the `.postponed` kind, the saved context and both modes.
A29's second case shows it: in `(fun f => f 1) Nat.succ`, `f 1` waits until
`Nat.succ` has fixed `f`'s type, and the binder's type comes out as
`(n : Nat) → Nat`, `Nat.succ`'s own binder name included (probe p2).

### 3.5 Applications in full: `@`, named arguments, defaults

FE1e's `elabAppArgs` state machine (FE1E_APPLICATIONS.md §2.2) gains:
`explicit` (true for `@`: implicit and strict-implicit binders become
explicit, `processImplicitArg` 882, `processStrictImplicitArg` 891; an
instance binder takes the next argument, except that a `_` there is still
an instance metavariable, 903-917: A8); the `namedArgs` list (a binder
whose user name matches takes that value; the named argument is removed;
a binder with no argument left: an `optParam` default, an `autoParam`
tactic (unsupported until it exists), an eta argument when named
arguments remain (`addEtaArg`, 734) or an implicit argument when a named
argument depends on it (`findNamedArgDependsOnCurrent?`, 340), else
`finalize`); and `etaArgs`, closed with `mkLambdaFVars` at `finalize`.
Errors as Lean's: "Invalid argument name" (E5), "invalid named argument,
already given".

### 3.6 `let`, `have`, `show`, ascription

`elabLetDeclAux` (Binders.lean:745): the type under `withSynthesize
(postpone := .partial)` (so pending instance problems may wait but
postponed terms are forced), an error "failed to infer `let` declaration
type" if it is still a metavariable at the end (E10), the value with
`elabTermEnsuringType` against it, then the body inside `withLetDecl`
(a local definition with its value; for `have`, `nondep := true`),
closed by `mkLetFVars` (`usedLetOnly := false`: an unused `let` stays).
FE2's local context entries therefore carry a value and a `nondep` flag,
and FE1c's `whnf` unfolds a let variable only when `nondep` is false
(Meta/WHNF.lean:400; `zetaDelta` is true by default, Meta/Basic.lean:196).
The term is Lean's `letE` with its `nonDep` flag, which the kernel's term
store already holds (`lf-tag-let-nondep`, `core/terms.fs`). `show T from
e` (BuiltinNotation.lean:114): `T` elaborated under `withSynthesize
(postpone := .yes)` and unified with the expected type (the answer
ignored), then `have this : T := e; this` elaborated against the
expected type (A14). `(e : T)` (428): `T` under `withSynthesize (postpone
:= .yes)`, `e` against `T`, then `ensureHasType T e` (a coercion is FE4).

### 3.7 Anonymous constructors and field notation

`elabAnonymousCtor` (BuiltinNotation.lean:43): `tryPostponeIfNoneOrMVar`
on the expected type, its `whnf`; the head must be an inductive type with
exactly one constructor (errors E2, E3 otherwise); the constructor's
explicit fields are counted after its parameters with
`forallTelescopeReducing`; with more components than fields the extra ones
nest into the last field as another `⟨…⟩` (probe p4: `(⟨1, 2, 3⟩ : Nat ×
Nat × Nat)` is `Prod.mk 1 (Prod.mk 2 3)`); fewer is an error ("Insufficient
number of fields"; Lean then fills with `sorry` to go on, LeanForth stops:
ADR 0021 D3); then the application of the constructor is elaborated.

Field notation (`elabAppLValsAux`, App.lean:1843): the object is
elaborated first; `resolveLValLoop` (1678) consumes its leading implicit
arguments (`consumeImplicits`), postpones while its type is a
metavariable (first trying default instances), and when a resolution
fails unfolds the type one definition at a time (`unfoldDefinition?`) and
tries again; `resolveLValAux` (1517) decides by the head: an index `.N` on a structure
gives its projection function (`Prod.fst`, A18), on another
one-constructor inductive the kernel's `Expr.proj`; a name on a structure
that has that field (`findField?`, through its parents) gives the
projection, applied to the object after `mkBaseProjections` (1700) walks
up to the parent that declares it; otherwise `findMethod?` (1453) looks
for `S.NAME` along the structure's resolution order, and `addLValArg`
(1735) passes the object as the argument of the first binder whose type's
head is `S`, positionally when that binder is explicit and the position
fits, else as a named argument (A19: `l.map Nat.succ` is `@List.map Nat
Nat Nat.succ l`); on a
function type, `Function.NAME`. This needs data the kernel export lacks:
which inductive types are structures, their fields, parents and
projection functions, and the resolution order. They come from the
elaboration data, format 3 (§6).

### 3.8 Holes, `sorry` and literals

`elabHole` (BuiltinTerm.lean:64) makes a natural metavariable of the
expected type; one left at the end of a declaration is Lean's error
"don't know how to synthesize placeholder" (E9). `elabSorry`
(BuiltinNotation.lean:242) makes `sorryAx (Lean.Name → T) false tag`
with a unique tag: pinned Lean writes the tag as a `Lean.Name` built from
the module name, the positions of `sorry` in the source, a hash and a
macro scope (probe p1, A24). LeanForth builds the same shape from the
LeanForth file's module name and positions; since positions in a `.lf`
file differ from those in a `.lean` file, the comparison erases the tag's
components (as FE1g compares binder names with macro scopes erased). The
declaration is reported NOT PROVED with `sorryAx` named, with the report
of ADR 0021 Amendment 1. Literals: `mkStrLit` (`core/string-literals.fs`
holds them), `Char.ofNat (nat_lit k)`, `OfScientific.ofScientific` with
an instance problem (as numerals), raw `nat_lit`; numerals of any size
through `lib/bignum.fs`.

### 3.9 Declarations: auto-bound implicits, universes, sections

A declaration header is elaborated inside `withAutoBoundImplicit`
(TermElabM.lean:1988): when elaboration meets an unknown identifier that
`checkValidAutoBoundImplicitName` (AutoBound.lean:56) allows (any atomic
name, since `relaxedAutoImplicit` is true by default; not the
declaration's own name), the state is restored, a local `{n : Sort ?u}`
is added, and the header is elaborated again from the start. Then
`addAutoBoundImplicits` (2100) puts the auto-bound locals first, each
preceded by the unassigned metavariables in its type
(`collectUnassignedMVars`), and refuses one that depends on an explicit
binder; level metavariables left become parameters `u_1`, `u_2`, … in
order (`levelMVarToParam`, TermElabM.lean:1059), and the declaration's
universe parameters are sorted as `sortDeclLevelParams` (DeclUtil.lean:79)
does. Probe p4: `theorem two_auto (x : β) (y : α) : x = x := rfl` gives
`two_auto.{u_1, u_2} : ∀ {β : Sort u_1} {α : Sort u_2} (x : β) (y : α), x
= x`.

In LeanForth the reader resolves names as it reads: today an unknown name
stops the run (error 1). In a declaration header (binder types and the
statement) and in a `variable` group, FE2's reader instead makes an
*unknown-name* node (§5.1) when the name is atomic, so the elaborator can
run Lean's restart loop on the tree; later uses of the same name in the
header refer to the same candidate, and in the value it is the auto-bound
variable. Anywhere else, and when
`set_option autoImplicit false` is in force, the reader still stops with
error 1, which is Lean's "Unknown identifier" (E8).

`variable` binders are section variables until the section or namespace
ends; a theorem includes those its header mentions, those they depend on
and the instance binders over included ones (`withHeaderSecVars`,
MutualDef.lean:455; probe p4: an unused `(j : Nat)` is left out; Lean's
`include` and `omit` commands are left for the row whose round trip meets
them); a definition also includes those its body uses
(`removeUnusedVars`, MutualDef.lean:603). `section S … end S` scopes
variables, `open` and `universe`; `universe u` outside a declaration is
Lean's command (inside one, after its name, it stays ADR 0017's list of
the declaration's parameters).

### 3.10 `▸`

`elabSubst` (BuiltinNotation.lean:457): the expected type (postponed while
it has metavariables), then `h` elaborated alone and its type matched as
an equation `a = b`; with an expected type, `kabstract` abstracts `b`
from it, or else `a` (and `h` is turned round with `Eq.symm`); `e` is
elaborated against the abstracted type with the other side put back; when
that fails, Lean tries to rewrite `e`'s own type instead; the motive `fun
x h => …` is checked for type correctness and the result is `Eq.rec`
(probe p1, A34: `@Eq.rec Nat a (fun x h => x = 0) p b h`). With no
expected type the same is done on `e`'s type. When the motive is not type
correct and one side is a free variable, Lean falls back to `by subst h;
exact e` (lines 507-519): that path answers *unsupported* until FE5's
`by-subst`. FE2 reuses FE1g's `kabstract` (FE1G_TACTICS.md §5.6).

## 4. Acceptance: pinned Lean's terms

Each case is a LeanForth text and the Lean text it stands for; pinned Lean
4.35.0 elaborated the Lean side with `set_option pp.all true` (probes
p1–p4, §10). Abbreviations: `#k` is `@OfNat.ofNat.{0} Nat (nat_lit k)
(instOfNatNat (nat_lit k))`; `+N` is `@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
(@instHAdd.{0} Nat instAddNat)`. This list is FE2's acceptance test: each
term must be equal node for node, universe arguments included; binder
names with macro scopes and `sorry` tags are compared erased.

| # | LeanForth | Lean | Pinned Lean's term (`pp.all`) |
| --- | --- | --- | --- |
| A1 | `Nat explicit: x  x 1 +  fun #check` | `#check fun (x : Nat) => x + 1` | `fun (x : Nat) => +N x #1 : (x : Nat) → Nat` |
| A2 | `_ explicit: x  x 1 +  fun  Nat Nat ->  :  #check` | `#check (fun x => x + 1 : Nat → Nat)` | the same as A1 |
| A3 | `def double  Nat explicit: n  Nat  :=  n n +  end double` | `def double (n : Nat) : Nat := n + n` | `fun (n : Nat) => +N n n` |
| A4 | `theorem add_zero_all  Nat explicit: n  n 0 + n =  forall  :=  _ explicit: n  rfl  fun  end add_zero_all` | `theorem add_zero_all : ∀ n : Nat, n + 0 = n := fun n => rfl` | type `∀ (n : Nat), @Eq.{1} Nat (+N n #0) n`, value `fun (n : Nat) => @rfl.{1} Nat (+N n #0)` |
| A5 | `0 Type implicit: α  α explicit: a  a a =  forall forall #check` | `#check ∀ {α : Type} (a : α), a = a` | `∀ {α : Type} (a : α), @Eq.{1} α a a : Prop` |
| A6 | `0 Type explicit: α  α Add instance: _  α explicit: a  a a +  a a +  =  forall forall forall #check` | `#check ∀ (α : Type) [Add α] (a : α), a + a = a + a` | `∀ (α : Type) [inst : Add.{0} α] (a : α), @Eq.{1} α (@HAdd.hAdd.{0, 0, 0} α α α (@instHAdd.{0} α inst) a a) (…the same…)` (a local instance) |
| A7 | `Nat 0 @ Eq.refl #check` | `#check @Eq.refl Nat 0` | `@Eq.refl.{1} Nat #0` |
| A8 | `Nat Nat Nat _ 1 2 @ HAdd.hAdd #check` | `#check @HAdd.hAdd Nat Nat Nat _ 1 2` | `+N #1 #2 : Nat` (the `_` at the instance binder synthesized) |
| A9 | `2 named: n Nat.le_refl #check` | `#check Nat.le_refl (n := 2)` | `Nat.le_refl #2 : @LE.le.{0} Nat instLENat #2 #2` |
| A10 | `0 Nat named: α Eq.refl #check` | `#check Eq.refl (α := Nat) 0` | `@Eq.refl.{1} Nat #0` |
| A11 | `_ 2 let: x  x x +  let #check` | `#check let x := 2; x + x` | `let x : Nat := #2; +N x x : Nat` |
| A12 | `Int 2 let: x  x x *  let #check` | `#check let x : Int := 2; x * x` | `let x : Int := @OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)); @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x x` |
| A13 | `1 1 = rfl have: h  h  have #check` | `#check have h : 1 = 1 := rfl; h` | `have h : @Eq.{1} Nat #1 #1 := @rfl.{1} Nat #1; h` |
| A14 | `1 1 + 2 = rfl show #check` | `#check show 1 + 1 = 2 from rfl` | `have this : @Eq.{1} Nat (+N #1 #1) #2 := @rfl.{1} Nat (+N #1 #1); this` |
| A15 | `2 Int : #check` | `#check (2 : Int)` | `@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)) : Int` |
| A16 | `⟨ 1 2 ⟩  Nat Nat ×  : #check`; `⟨ 1 2 3 ⟩  Nat Nat Nat × ×  : #check` | `#check (⟨1, 2⟩ : Nat × Nat)`; `(⟨1, 2, 3⟩ : Nat × Nat × Nat)` | `@Prod.mk.{0, 0} Nat Nat #1 #2`; `@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) #1 (@Prod.mk.{0, 0} Nat Nat #2 #3)` |
| A17 | `⟨ 0 Nat.zero_lt_one ⟩  1 Fin  : #check` | `#check (⟨0, Nat.zero_lt_one⟩ : Fin 1)` | `@Fin.mk #1 #0 Nat.zero_lt_one : Fin #1` |
| A18 | `Nat Nat × explicit: p  p .1  fun #check`; the same with `p .snd` | `fun (p : Nat × Nat) => p.1`; `… p.snd` | `fun (p : Prod.{0, 0} Nat Nat) => @Prod.fst.{0, 0} Nat Nat p`; `… @Prod.snd.{0, 0} Nat Nat p` |
| A19 | `Nat List explicit: l  l .length  fun`; `… l .map  ' Nat.succ $  fun`; `Nat explicit: n  n .succ .succ  fun` (each `#check`) | `fun (l : List Nat) => l.length`; `… l.map Nat.succ`; `fun (n : Nat) => n.succ.succ` | `@List.length.{0} Nat l`; `@List.map.{0, 0} Nat Nat Nat.succ l`; `Nat.succ (Nat.succ n)` |
| A20 | `s" hello" #check`; `'a' #check` | `#check "hello"`; `#check 'a'` | `"hello" : String`; `'a' : Char` (pinned Lean prints the literal; the term is `Char.ofNat (nat_lit 97)`, BuiltinTerm.lean:250, compared through the export of `def c : Char := 'a'`) |
| A21 | `theorem id_eq'  α explicit: a  a id a =  :=  rfl  end id_eq'` | `theorem id_eq' (a : α) : id a = a := rfl` | `id_eq'.{u_1} : ∀ {α : Sort u_1} (a : α), @Eq.{u_1} α (@id.{u_1} α a) a := fun {α : Sort u_1} (a : α) => @rfl.{u_1} α (@id.{u_1} α a)` (auto-bound) |
| A22 | `def myId  universe u  u Sort implicit: α  α explicit: a  α  :=  a  end myId` | `def myId {α : Sort u} (a : α) : α := a` | `myId.{u} : {α : Sort u} → (a : α) → α := fun {α : Sort u} (a : α) => a` |
| A23 | `def idFn  0 Type implicit: α  α α ->  forall  :=  _ explicit: a  a  fun  end idFn` | `def idFn : ∀ {α : Type}, α → α := fun a => a` | `fun {α : Type} (a : α) => a` (the implicit lambda) |
| A24 | `theorem open_part  1 2 =  :=  sorry  end open_part` | `theorem open_part : 1 = 2 := sorry` | `sorryAx.{0} (Lean.Name → @Eq.{1} Nat #1 #2) Bool.false TAG`; NOT PROVED |
| A25 | `Prop explicit: p  Prop explicit: q  p q p -> ->  forall forall #check` | `#check ∀ (p q : Prop), p → q → p` | `∀ (p q : Prop), p → q → p : Prop` |
| A26 | `Nat explicit: x  _ explicit: y  x y <  ∃  forall #check` | `#check ∀ x : Nat, ∃ y, x < y` | `∀ (x : Nat), @Exists.{1} Nat fun (y : Nat) => @LT.lt.{0} Nat instLTNat x y` |
| A27 | `_ Eq.refl  2 2 =  : #check` | `#check (Eq.refl _ : 2 = 2)` | `@Eq.refl.{1} Nat #2` |
| A28 | `theorem add_comm' …` (§2.4); `' Nat.succ_le_succ #check`; `@ ' List.length_append #check` | `theorem add_comm' (m n : Nat) : m + n = n + m := Nat.add_comm m n`; `#check Nat.succ_le_succ`; `#check @List.length_append` | `fun (m n : Nat) => Nat.add_comm m n`; `Nat.succ_le_succ {n m : Nat} : @LE.le.{0} Nat instLENat n m → …`; `@List.length_append.{u_1} : ∀ {α : Type u_1} {as bs : List.{u_1} α}, …` |
| A29 | `_ explicit: x  x  fun  1 $ #check`; `_ explicit: f  f 1 $  fun  ' Nat.succ $ #check` | `#check (fun x => x) 1`; `#check (fun f => f 1) Nat.succ` | `(fun (x : Nat) => x) #1 : Nat`; `(fun (f : (n : Nat) → Nat) => f #1) Nat.succ : Nat` (postponement) |
| A30 | `universe u` then `0 Type explicit: α  u Sort explicit: β  α β ->  fun fun #check`; `u Type explicit: α  α  fun #check` | `#check fun (α : Type) (β : Sort u) => α → β`; `fun (α : Type u) => α` | `fun (α : Type) (β : Sort u) => α → β : (α : Type) → (β : Sort u) → Sort u`; `fun (α : Type u) => α` |
| A31 | `def withDefault  Nat explicit: a  Nat 3 optParam explicit: b  Nat  :=  a b +  end withDefault`, then `1 withDefault #check` | `def withDefault (a : Nat) (b : Nat := 3) : Nat := a + b`; `#check withDefault 1` | `withDefault #1 #3 : Nat` (the default filled) |
| A32 | `0 Type implicit: α  α explicit: a  a  fun fun #check` | `#check fun {α : Type} (a : α) => a` | `fun {α : Type} (a : α) => a : {α : Type} → (a : α) → α` |
| A33 | `section S  variable  Nat explicit: k  Nat explicit: j  theorem uses_k  k k =  :=  rfl  end uses_k  end S` | `section S variable (k : Nat) (j : Nat) theorem uses_k : k = k := rfl end S` | `uses_k : ∀ (k : Nat), @Eq.{1} Nat k k := fun (k : Nat) => @rfl.{1} Nat k` (`j` not included) |
| A34 | `theorem subst_ex  Nat explicit: a  Nat explicit: b  a b = explicit: h  a 0 = explicit: p  b 0 =  :=  h p ▸  end subst_ex` | `theorem subst_ex (a b : Nat) (h : a = b) (p : a = 0) : b = 0 := h ▸ p` | `fun (a b : Nat) (h : a = b) (p : a = #0) => @Eq.rec.{0, 1} Nat a (fun (x : Nat) (h : @Eq.{1} Nat a x) => @Eq.{1} Nat x #0) p b h` |
| A35 | `_ explicit: x  x  fun #check` | `#check fun x => x` | `fun (x : ?m.1) => x : (x : ?m.1) → ?m.1` (holes printed as Lean prints them) |
| A36 | `Prop explicit: p  Prop explicit: q  p q ∧ ¬  p q ¬ ->  ↔  forall forall #check` | `#check ∀ (p q : Prop), ¬(p ∧ q) ↔ (p → ¬q)` | `∀ (p q : Prop), Iff (Not (And p q)) (p → Not q) : Prop` |
| A37 | `0 Type explicit: α  α explicit: x  α explicit: y  x y =  fun fun fun #check` | `#check fun (α : Type) (x y : α) => x = y` | `fun (α : Type) (x y : α) => @Eq.{1} α x y` |
| A38 | `theorem app_hyp  Prop explicit: p  Prop explicit: q  p q -> explicit: h  p explicit: hp  q  :=  hp h  end app_hyp` | `theorem app_hyp (p q : Prop) (h : p → q) (hp : p) : q := h hp` | `fun (p q : Prop) (h : p → q) (hp : p) => h hp` (`h` takes one argument: its type has one explicit binder) |
| A39 | `Int explicit: i  i neg-  fun #check` | `#check fun (i : Int) => -i` | `fun (i : Int) => @Neg.neg.{0} Int Int.instNegInt i` |
| A40 | `3 named: m ' Nat.lt_of_lt_of_le #check` | `#check Nat.lt_of_lt_of_le (m := 3)` | `@Nat.lt_of_lt_of_le ?m.1 #3 ?m.4 : … → … → …` (no positional argument: the explicit binders stay) |

Wrong inputs, each with Lean's error (probe p2) and LeanForth's outcome
(the text stops at the token, nothing is checked, exit 4; *unsupported*
exit 2):

| # | LeanForth | Lean's error | LeanForth |
| --- | --- | --- | --- |
| E1 | `_ explicit: f  f 1 $  fun #check` | "Function expected at f but this term has type ?m.1" (after postponement fails) | invalid, Lean's message |
| E2 | `def bad  Nat  :=  ⟨ 1 2 ⟩  end bad` | "Invalid `⟨...⟩` notation: The expected type `Nat` has more than one constructor" | invalid |
| E3 | `⟨ 1 2 ⟩ #check` | "The expected type of this term could not be determined" | invalid |
| E4 | `Nat Nat × explicit: p  p .3  fun #check` | "Invalid projection: Index `3` is invalid for this structure" | invalid (Lean goes on with `sorry`; LeanForth stops, ADR 0021 D3) |
| E5 | `2 named: m Nat.le_refl #check` | "Invalid argument name `m` for function `Nat.le_refl`" | invalid |
| E6 | `def bad6  True  :=  1  end bad6` | "numerals are data in Lean, but the expected type is a proposition" | invalid |
| E7 | `def bad7  1 2 =  :=  rfl  1 1 =  :  end bad7` | "Type mismatch" | *unsupported* until FE4 (Lean looks for a coercion first; FE1e's rule) |
| E8 | `set_option autoImplicit false` then `theorem no_auto  α explicit: a  a a =  :=  rfl  end no_auto` | "Unknown identifier `α`" | invalid, error 1 |
| E9 | `def holeLeft  Nat  :=  _  end holeLeft` | "don't know how to synthesize placeholder" | invalid |
| E10 | `def bad10  Nat  :=  _  _ explicit: y  y  fun  let: x  0  let  end bad10` | "Failed to infer type of binder `y`"; "failed to infer `let` declaration type" | invalid |

## 5. Reuse, new pieces, modules and words

### 5.1 What FE2 reuses from FE1

| FE1 piece | Used by FE2 for |
| --- | --- |
| FE1a reader (`src/front/reader.fs`, `syntax.fs`), the name groups and scopes of `src/author/` | every word of §2; new node kinds (below); binder frames and `DEPTH` checks; positions on every node |
| FE1b metavariables (`mvars.fs`) and FE1g-1's undo trail | holes, postponed and synthetic metavariables; the saved state of the arity count (§2.1) and of the auto-bound restarts |
| FE1c `whnf`, `inferType`, `isDefEq`, `instantiate`, level unification | `whnfForall` for propagation and implicit lambdas; arity through unfolding; `let` values (`nondep`); `mkLambdaFVars`, `mkForallFVars`, `mkLetFVars` |
| FE1d/FE1e elaboration data | instances, default instances, reducibility, `elab_without_expected_type`; format 3 adds structures (§6) |
| FE1e `elabAppArgs`, `elabTerm`, `ensureHasType`, `elabType`, pending list, instance search | every application; explicit mode, named arguments and eta arguments are new states of the same machine; local instances added to `getInstances` |
| FE1f header and hand-over | declarations with natural binders; auto-bound loop and universe parameters wrap it |
| FE1g context views, goals, tactic runner, `kabstract` | binders' local declarations; nested `by` blocks; `▸` |
| FE1i `by-decide`, `by-omega` | the tactics a nested `by` block can run at first |

Two changes to FE1's plans follow: FE1f should elaborate a header from
its syntax tree at `:=` (not binder by binder as the words run), so that
FE2's auto-bound restarts can run it again; and FE1g-1's context view
entries carry a value and a `nondep` flag for `let`/`have`, and the view
keeps its local instances.

New syntax kinds (`syntax.fs`): `syn-k-hole`, `syn-k-sort` (Prop, Type,
Sort and a level node), `syn-k-arrow`, `syn-k-binder` (kind, name, type
node; for `fun`, `forall`, `∃`, `let`, `have`, with the body and, for
`let`/`have`, the value), `syn-k-show`, `syn-k-ascribe`, `syn-k-anon` (its
components as argument nodes), `syn-k-field` (a name ID or an index),
`syn-k-named` (on application nodes, as Lean's `namedArgs`), an
`explicit` flag and an optional universe list on `syn-k-const`,
`syn-k-str`, `syn-k-char`, `syn-k-sci`, `syn-k-rawnat`, `syn-k-sorry`,
`syn-k-subst`, `syn-k-unop` and the other macro kinds of §2.3,
`syn-k-unknown` (an auto-bound candidate) and `syn-k-by` (a nested tactic
block: its kept source span, as FE1g keeps blocks).

### 5.2 New Meta and Elab pieces

| Piece | Lean | Notes |
| --- | --- | --- |
| Binder elaboration | `elabBinders`, `elabBinderViews`, `elabFunBinders`, `propagateExpectedType` (Binders.lean:208-470) | local declarations in FE1g-1's views; local instances; the class check of instance binders |
| `∀`, `→`, `fun` | `elabForall`, `elabArrow`, `elabDepArrow`, `elabFun` | `mkForallFVars`, `mkLambdaFVars` with Lean's binder names and kinds |
| `let`, `have` | `elabLetDeclAux` and `withLetDecl` | local definitions with values; `mkLetFVars`; `nondep` |
| Postponement | `tryPostpone*`, `postponeElabTerm`, `resumePostponed`, `synthesizeSyntheticMVarsStep` with `postponeOnError` | a saved elaboration context per postponed metavariable; resumed in creation order |
| Implicit lambdas | `useImplicitLambda`, `elabImplicitLambda`, `blockImplicitLambda` | part of `elabTerm`'s main loop |
| Application states | `explicit`, `namedArgs`, `etaArgs`, `optParam`, `findNamedArgDependsOnCurrent?` | extensions of FE1e's `elab-app.fs` |
| Field notation | `elabAppLValsAux`, `resolveLValAux`, `resolveLValLoop` (`consumeImplicits`, postponement, unfolding of the object's type), `findMethod?`, `addLValArg`, `mkBaseProjections`, `mkProjAndCheck` | needs format 3 of the elaboration data |
| Notations | `elabAnonymousCtor`, `elabShow`, `elabTypeAscription`, `elabSorry`/`mkLabeledSorry`, `elabSubst`, literals, `unop%` and the other `Extra.lean` macros | `▸` with FE1g's `kabstract` |
| Header | `withAutoBoundImplicit`, `addAutoBoundImplicits`, `collectUnassignedMVars`, `levelMVarToParam`, `sortDeclLevelParams`, section variables (`withHeaderSecVars`, `removeUnusedVars`) | the restart loop uses the undo trail |
| Commands | `variable`, `section`, `universe`, `set_option` (two options), `#check` with holes and the signature form | scopes in `author/namespaces.fs`' frames |

### 5.3 Files (all `src/front/` unless said; untrusted; tests in `tests/front/`)

| File | Contents | Uses |
| --- | --- | --- |
| `reader.fs` (FE1a, extended) and `reader-terms.fs` (new) | the words of §2.2, the arity rule of §2.1, field tokens, literals, brackets | syntax.fs, author/ |
| `syntax.fs` (extended) | the kinds of §5.1 | lib/ |
| `elab-binders.fs` | binders, `∀`, `→`, `fun`, `let`, `have`, local instances | elab-app, mvars, FE1g-1 views |
| `elab-postpone.fs` | postponed metavariables, saved contexts, resumption, implicit lambdas | elab-pending (FE1e) |
| `elab-app.fs` (FE1e, extended) | explicit mode, named and eta arguments, `optParam` | — |
| `elab-field.fs` | field notation | elab-app, elab-data format 3 |
| `elab-notation.fs` | `⟨⟩`, `show`, `:`, `sorry`, `▸`, literals, the macro kinds of §2.3 | elab-app, FE1g `kabstract` |
| `elab-header.fs` | auto-bound loop, universe parameters, section variables, commands | FE1f |
| `elab-data.fs` (FE1d, format 3) and `scripts/export-elab.sh` | structures: fields, parents, projection functions, resolution order | lib/json.fs |
| `src/present/print-natural.fs` | the printer's natural mode (§5.4) | present/, notation table v2 |
| `src/present/notation-table.fs` (version 2) | the macro column and the new rows of §2.3 | — |

### 5.4 The printer's natural mode and the Init round trip

`leanforth print --lf` gains the natural form (today it writes the kernel
form, starting with `kernel-form`); FE2i proposes the natural form as its
default, as natural text is the default to read (owner's answer 4), with
an option for the kernel form. The natural printer omits what the
elaborator will find again: implicit and instance arguments, binder types
where `fun` gets them from the expected type, universe arguments, the
`OfNat` of numerals, and uses the operator words. Lean's delaborator does
not guarantee that its output elaborates back to the same term; its
option `pp.analyze` (`PrettyPrinter/Delaborator/TopDownAnalyze.lean`)
decides where `@`, named arguments or ascriptions are needed so that it
does. The natural printer starts conservative (it writes `@ NAME` with
every argument wherever its check is unsure) and becomes more natural row
by row; the round trip measures it. **Round trip** (plan row): for each
of Init's 59,349 declarations, print its statement in natural form, read
it back, elaborate it, compare with the export node for node; report "K of
59,349 identical", each failure listed by cause (unsupported form and its
row, printer too terse, elaboration differs) in a gap ledger, a new file
`FRONT_END_GAPS.md` beside the plan, which FE2a creates. The count rises
as FE3 and FE4 land (instances, coercions).

### 5.5 Public words, state, outcomes, errors

| Word | Stack effect | Lean |
| --- | --- | --- |
| `lf-elab-binders` | `( node -- n outcome )` | `elabBinders`: opens `n` local declarations in the current view |
| `lf-elab-fun` | `( node expected -- term outcome )` | `elabFun` |
| `lf-elab-let` | `( node expected -- term outcome )` | `elabLetDeclAux` |
| `lf-elab-postpone` | `( node expected -- mvar outcome )` | `postponeElabTerm` |
| `lf-elab-header` | `( decl -- type outcome )` | header with auto-bound loop and universe parameters |
| `lf-elab-field` | `( node expected -- term outcome )` | `elabAppLValsAux` |
| `lf-arity` | `( node -- n )` | the reader's count of §2.1 (scratch elaboration, rolled back) |
| `lf-print-natural` | `( term width -- outcome )` | the natural printer |

State (ADR 0009): members of the checker context: the postponed
metavariables' saved contexts (a store), the section scopes (variables,
options), the auto-bound list of the header being elaborated;
everything grows in the heap; no host recursion (elaboration runs on
`lib/frame.fs` steps, as FE1e's). Fuel: one unit per elaboration visit, a
restart of the auto-bound loop counted like a visit; *exhausted* when out.
Outcomes: ok, invalid (a front-end error with Lean's message), unsupported
(§1.4), exhausted, full; never ok for a failure. Error codes: the next
free ones of `src/author/errors.fs` after FE1g's and FE1i's, one per
Lean error of §4's table and per unsupported condition, each naming the
row that lifts it; error 52 (holes) and 73 (arity needs unfolding) are
retired.

## 6. Elaboration data, format 3

FE1d's records (instances, default instances, reducibility, eliminators)
and FE1e's format 2 (keys, ranks, classes, tags) gain: for each structure,
its fields in order with their projection functions and binder kinds, its
parents with their projections, and its resolution order (Lean's
`getStructureResolutionOrder`), which `findMethod?` walks. LeanForth
checks each record against the export (the structure is an
inductive with one constructor whose explicit fields are the listed ones;
each projection function exists and has the projection's shape) and fails
closed, as FE1d does. Probe needed in FE2f: the counts for Init.

## 7. Tests

### 7.1 Comparisons with pinned Lean

`tests/front/check_terms.py` (in `make check`, beside FE1e's
`check_elab.py`): every case of §4 as a LeanForth text and a Lean text.
Declarations (A3, A4, A21–A24, A28, A31, A33, A34, A38) are compared
through the export records, node for node; `#check` cases through pinned
Lean's `pp.all` text and LeanForth's printer in the same mode (FE1e's
method), with `def`-wrapped twins where `pp.all` hides a node (A20's
character). A harness self-test refuses a known-wrong row. The E cases
compare the error kind and the token. `tests/frontend/02-statements.lf`
is the plan row's file: the `#check` lines of A28 and of about twenty
Init statements (`Nat.succ_le_succ`, `List.length_append`,
`Nat.lt_irrefl`, `Nat.le_antisymm`, `List.map_append`, `Nat.add_sub_cancel`,
…), printed equal to pinned Lean's.

### 7.2 Coverage classes ([TEST_COVERAGE_REVIEW.md](../development/TEST_COVERAGE_REVIEW.md#owners-coverage-classes))

1. **Every outcome:** a term (A1–A40); each error of E1–E10; each
   unsupported condition of §1.4 reached by one input (a coercion, an
   `autoParam` with no tactic, a pattern `fun`); exhausted (fuel 1 for
   A29's postponement); full (each new store refused in turn with
   `tests/support/heap-watch.fs`); `sorry` reported NOT PROVED, never
   proved.
2. **Malformed input:** a binder word with no type, closers with no
   binder open or the wrong one (`let:` closed by `have`), `⟩` without
   `⟨`, `named:` not followed by a name word, `@` not followed by a name,
   a field token with nothing below it, `.0` (Lean: "Index must be
   greater than 0"), `'ab'`, an unterminated `s"`, a scientific literal
   Forth reads otherwise, `set_option` of an unknown option, `variable`
   inside a declaration, values left at a command word; format 3's
   damaged records.
3. **Interfaces:** stack effects of every new word under
   `tests/support/checks.fs`' `run-case`; each error code in the
   catalogue; every outcome through `outcome-sane`.
4. **Workflows and I/O:** `bin/leanforth check --env tests/author/init-slice.ndjson
   --elab-data …` on `02-statements.lf` and the files of A3–A38; the
   natural printer's output read back (`print --lf`, then `check`); the
   JSON form of the errors.
5. **Resources:** a `fun` of 10,000 binders; a `let` chain of 10,000;
   an anonymous constructor of 10,000 components; an auto-bound header
   with 100 names (100 restarts, fuel counted); heap refusals.
6. **State:** after a failed declaration, the next one elaborates as in a
   fresh run (postponed list, scopes, auto-bound list reset); a section's
   variables gone after `end S`; `set_option` scoped to its section; the
   arity count leaves no metavariable behind (trail unit test).
7. **Regression pins:** golden `#check` lines of §4; fuel counts of A2,
   A21 and A29; the round-trip count.

### 7.3 Planted faults (`tests/mutants/faults.toml`, each caught)

`fe2-no-binder-propagation` (A2's binder stays a hole: the term or the
outcome differs), `fe2-propagate-arg-order` (`isDefEq domain fvarType`
swapped: a case where the order assigns differently), `fe2-let-as-have`
and `fe2-have-as-let` (A11, A13), `fe2-show-no-have` (A14 gives `rfl`
alone), `fe2-named-arg-positional` (A10 fills `a`), `fe2-explicit-inst-hole`
(A8's `_` left natural: "don't know how to synthesize"),
`fe2-no-implicit-lambda` (A23 fails), `fe2-no-postpone` (A29 fails),
`fe2-postpone-order` (resumption newest first: a two-postponement case),
`fe2-autobound-order` (p4's `two_auto` gets `α` first),
`fe2-autobound-ignores-option` (E8 accepted), `fe2-optparam-unfilled`
(A31), `fe2-proj-index-off-by-one` (A18 gives `snd`), `fe2-field-first-explicit`
(A19's `l` put in `List.map`'s first explicit slot), `fe2-anon-flat`
(A16's three components not nested), `fe2-local-instance-ignored` (A6:
"failed to synthesize"), `fe2-secvar-all` (A33 includes `j`),
`fe2-level-param-order` (`u_1`, `u_2` swapped), `fe2-sorry-proved` (A24
counted proved), `fe2-arity-counts-optparam` (A31's `1 withDefault`
waits for two values), `fe2-subst-direction` (A34's motive over `a`).

### 7.4 The round trip

`make roundtrip-natural` (not in `make check`: it runs over all of Init,
on the snapshot; run by FE2j and the done checker) writes the count and
the gap ledger. A harness self-test plants a printer that drops an
explicit argument and must see the count fall.

## 8. Sub-steps

Each step ends with its focused tests, its faults and a logged Forth
review; sizes are the plan's S (under a day), M (days) and L.

| Step | What | Size | Needs |
| --- | --- | --- | --- |
| FE2a | Reader words, part 1: `Prop`, `Type`, `Sort`, the level words, `->`, binder closers (`fun`, `forall`, `∃`), `_`, `.{ }`; the arity rule with `whnf` and the scratch count (error 73 retired); syntax kinds; the gap ledger file | S–M | FE1a, FE1c (`whnf`), FE1g-1 (trail) |
| FE2b | Binder elaboration: `∀`, `→`, `fun` with propagation, local declarations in context views, local instances in `getInstances`; A1, A5, A6, A25, A32, A37, A38 | M | FE1e, FE1g-1 |
| FE2c | Postponement and implicit lambdas; `#check` with holes; A2, A4, A23, A29, A35, E1 | M | FE2b |
| FE2d | Applications in full: `@`, `@ '`, `named:`, eta arguments, `optParam`; A7–A10, A31, A40, E5 | M | FE1e (`elab-app.fs`), FE2a |
| FE2e | `let`, `have`, `show`, `:`, `sorry` (with Amendment 1's report), literals (strings, characters, scientific, big numerals, `nat_lit`), `▸`; A11–A15, A20, A24, A27, A34, E6, E9, E10 | M | FE2b, FE1g (`kabstract`) |
| FE2f | Elaboration data format 3 (structures) in the exporter and reader; field notation; anonymous constructors; A16–A19, E2–E4 | M | FE1d, FE2d |
| FE2g | Notation table version 2: the macro column, the rows Init needs, `unop%`, `rightact%`, `leftact%`, `binop_lazy%`, `binrel_no_prop%`; A36, A39 | S–M | FE1e7 |
| FE2h | Declarations and commands: auto-bound loop, universe parameters, `variable`, `section`, `universe`, `set_option`, the signature form of `#check`, nested `by … by-end`; A21, A22, A28, A30, A33, E8 | M | FE1f, FE2b |
| FE2i | The printer's natural mode; `print --lf` natural by default | M | FE2a–FE2h |
| FE2j | `check_terms.py` with §4, `tests/frontend/02-statements.lf`, the Init round trip and its count, faults of §7.3, the user page's sections in three forms, the done-checker run | M–L | all above |

FE2 as a whole stays **L**: *speculative* 5,000 to 9,000 lines of Forth
and as much in tests. FE2a and FE2g can start once FE1a and FE1e7 are
merged; FE2b–FE2e follow FE1e and FE1g-1; FE2i needs most of the rest.

## 9. Questions for the owner

1. **Types left to the elaborator.** Lean lets you leave out a binder's
   type (`fun x => x + 1`, `∀ x, p x`, `let x := 2`). In LeanForth every
   binder word takes a type from the stack, so a left-out type needs a
   spelling. Options: (a) write the hole `_` where the type would be:
   `_ explicit: x  x 1 +  fun`, `_ 2 let: x … let`; (b) separate words
   that take no type (`fun: x`, `let-infer: x`, …), one per binder kind;
   (c) a binder word takes no type when the stack holds nothing for it.
   *Recommendation: (a).* It is exactly what Lean does inside (Lean
   turns `fun x` into `fun (x : _)` before elaborating), it adds one
   character, it keeps one word per binder kind, and `_` already means
   "the elaborator finds this" everywhere else. (b) doubles the binder
   words; (c) is ambiguous, because values meant for an enclosing
   application may be on the stack.
2. **Lean's symbols as words in theorem text.** You allowed `+ = * ≤` in
   theorem text (2026-11-12). FE2 needs more of Lean's symbols: `@`
   (hidden arguments given by hand, `Nat 0 @ Eq.refl`), `:` (type
   ascription, `2 Int :`), `⟨ ⟩` (anonymous constructor), `.name` (field
   notation, `p .1`, `l .length`), the remaining operators (`≠ < > ≥ - /
   % ^ ∣ ∈ ∧ ∨ ↔ ¬ ∃ ×`), with `^` meaning power as in Lean (in natural
   text a constant's universe arguments, rarely written, become `.{ 1 }
   Eq`), and unary minus, which shares Lean's `-` with subtraction and so
   needs a word of its own. Options: (a) Lean's symbols, in theorem text
   only, with `neg-` for unary minus; (b) spelled-out words (`explicit@`,
   `as-type:`, `anon[ ]`, `field: name`); (c) (a) for the operators only,
   (b) for the rest. *Recommendation: (a).* It extends your answer 1 on
   the same ground (Forth's `@`, `:` and `^` are not visible in theorem
   text, which runs with only LeanForth's words), keeps statements close
   to Lean's, and every one of these spellings is one a Lean reader
   already knows; `^` must be power for Mathlib's statements (`x ^ 2`),
   which are far more common than explicit universe arguments.
3. **Field notation with arguments.** Lean writes `l.map f`. In postfix,
   `.map` must know how many values to take. Options: (a) `.map` takes
   only the object; more arguments follow with `$`: `l .map f $`; (b)
   `.map` takes as many values as the function it resolves to has
   explicit arguments besides the object: `l f .map`. *Recommendation:
   (a).* Which function `.map` means depends on the object's type, which
   LeanForth knows only after elaborating it; (b) would have to elaborate
   the object while reading, out of Lean's order, and could take a
   different number of values for a different object. (a) builds exactly
   Lean's tree `(l.map) f` and is predictable; `n .succ .succ` and
   `h .symm` need no `$` at all.

## 10. Sources and probes

Lean 4.35.0 sources read (pinned toolchain, `src/lean/Lean/`):
`Elab/Binders.lean` (24-470, 645-968), `Elab/BuiltinNotation.lean`
(43-160, 242-540), `Elab/BuiltinTerm.lean` (21-275),
`Elab/App.lean` (340, 700-930, 1435-1880, 2256-2292),
`Elab/Term/TermElabM.lean` (1059, 1365-1410, 1636, 1744-1850, 1918,
1988-2134), `Elab/AutoBound.lean` (all), `Elab/SyntheticMVars.lean`
(23-70, 540-580), `Elab/MutualDef.lean` (440-480, 595-610),
`Elab/DeclUtil.lean` (79), `Meta/SynthInstance.lean` (203-239),
`Meta/Basic.lean` (180-200), `Meta/WHNF.lean` (395-410, 590-635),
`Init/Notation.lean` (293-313, 390-410), `Init/Core.lean` (197, 777,
882).

Probes, run with the pinned binary
(`.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, never an
elan proxy), `ulimit -u 500`, `timeout -k 5 120`, `nice -n 15`, kept in
`.claude/work/D2/probes/` of the design worktree (`p1.lean` … `p4.lean`
with their `.out` files; machine-local working files, so the Lean side of
every case is also given in §4 and the probes can be rerun from this
page, each file starting with `set_option pp.all true`):

- p1: A1–A38's Lean side (`set_option pp.all true`, `#check` and
  `#print`), 0.3 s.
- p2: postponement (A29), chained fields, a hypothesis applied, and the
  errors E1–E10.
- p3: nested and merged `fun` (the same terms), `l.map Nat.succ`, `have`
  without a type, unary minus, a named argument with no positional ones,
  `∃` with a typed binder.
- p4: `⟨1, 2, 3⟩` nested, auto-bound order (`two_auto`), an unused
  section variable left out, the character literal.

## 11. Limits of this design

- The arity rule (§2.1) decides how a postfix text is cut into Lean
  syntax; it is FE1a's rule, extended. A theorem whose conclusion unfolds
  to a Π takes more values than a Lean user might expect (its explicit
  binders after unfolding count); `' NAME … $` is the way out. The
  printer writes what reads back, so printed text is always right.
- `sorry` tags and macro-scoped binder names are compared erased; both
  carry source positions, which differ between `.lf` and `.lean` files.
- A type mismatch answers *unsupported* until FE4 (§1.3), where Lean
  reports an error; listed in the gap ledger as a temporary gap.
- The Init round trip's count depends on FE3 and FE4 for statements with
  instances of their own and coercions; FE2's done check uses the
  acceptance list of §4 and the count as it stands, with every failure
  listed by row.
- Scientific literals: Gforth 1.0 reads `1e5` as a float when its
  recognizers are not limited; LeanForth limits them in theorem text
  (ADR 0017 §18), and Gforth 0.7.3 must give the same tokens: tested in
  FE2e on both.
