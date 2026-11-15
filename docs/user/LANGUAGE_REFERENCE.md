# LeanForth language reference: theorems, proofs and tactics

> **IMPORTANT: keep this page current.** The implementation is changing
> fast. Whoever changes, adds, renames or retires a LeanForth word updates
> this page **in the same branch** (owner, 2026-11-15; `AGENTS.md`).
>
> **Status date: 2026-11-15**, written against `main` at the commit that
> added it. It lists what the words' definitions in `src/author/`,
> `src/front/` and `src/present/` do and what the checked files under
> `tests/front/` and `tests/author/` show.

**Notation.** A word is **implemented** when its definition exists on
`main`; it carries no mark. A word marked **`**`** is *designed but not yet
implemented* (or implemented only in part, as the entry says), and the entry
cites its design document. A `**` word is never shown as running input
except in a block marked "(design, not run)". Stack effects are Forth's:
`( before -- after )`, with *t* a term, *l* a universe level, *n* a number.
Sample blocks cite the checked file they come from; a block I wrote that
no test checks is marked "(illustration, not run)".

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
elaborator stops with error 139.

| Part | Contents |
| --- | --- |
| [A. Theorems](#a-theorems) | declarations, binders, statements, `#check` |
| [B. Proof outlines](#b-proof-outlines) | the outline of a checked proof; labels and notes |
| [C. Proofs](#c-proofs) | proof terms |
| [D. Tactics](#d-tactics) | `:= by ... end`, every `by-` word |
| [E. Vocabulary tools](#e-vocabulary-tools) | finding words and names |
| [F. File input](#f-file-input) | `bin/leanforth check FILE.lf` |
| [G. Pretty printing](#g-pretty-printing) | `print`, outlines, `--latex`, notation |

---

## A. Theorems

### A.1 Glossary

| Word | Stack comment | Function |
| --- | --- | --- |
| `theorem NAME` | `( -- )` | start a theorem (empty stack) |
| `def NAME` | `( -- )` | start a definition |
| `axiom NAME` | `( -- )` | declare an axiom (its statement only) |
| `protected KIND NAME` | `( -- )` | protected declaration, as Lean's `protected` |
| `import-stub NAME` | `( -- )` | stands for a library constant; refused by `check` |
| `universe NAME` | `( -- )` | a universe parameter, right after the name |
| `Nat explicit: n` | `( T -- )` | open an explicit binder `(n : Nat)` |
| `implicit:`, `strict-implicit:`, `instance:` | `( T -- )` | binders `{x : T}`, `⦃x : T⦄`, `[x : T]` |
| `:=` | `( t -- )` | end the statement; the binders become parameters |
| `end NAME` | `( t -- )` | close the declaration (or a namespace); hands it to the elaborator |
| `namespace NAME`, `open NAME` | `( -- )` | enter or open a namespace, between declarations |
| NAME (a constant or variable) | `( a1 .. ak -- t )` | apply to as many values as it has explicit binders |
| a numeral `0`, `2` | `( -- t )` | Lean's `OfNat` numeral |
| `' NAME` | `( -- t )` | the function NAME, applied to nothing |
| `$` | `( f a -- t )` | one more argument |
| `+`, `*` | `( a b -- t )` | Lean's `a + b`, `a * b` (`binop%`) |
| `=`, `≤` | `( a b -- t )` | Lean's `a = b`, `a ≤ b` (`binrel%`) |
| `TERM #check` | `( t -- )` | print `TERM : TYPE`; nothing is checked |
| `kernel-form` | `( -- )` | switch the rest of the file to the kernel form |
| `\`, `(` ... `)` | `( -- )` | comments, on one line |
| `->`, `fun`, `forall` | `( t t -- t )`, `( t -- t )` | kernel form only: arrow, λ and Π closing the innermost binder |
| `Prop`, `Type`, `Sort`, `^`, `var#`, `lit#`, `proj#`, `level+`, `level-max`, `level-imax`, `root:` | see [programming reference](../programming/LEANFORTH_WORDS.md#the-vocabulary) | kernel form only: levels, de Bruijn variables, literals, projections |
| `**` `->`, `fun`, `forall`, `Prop`, `∃`, `_`, `let:`, `have:`, `show`, `⟨ ⟩`, `.NAME`, `@`, `++` and more, in natural form | `( A B -- t )` etc. | natural spellings of every term form: designed, [FE2_TERMS.md §2.2](../design/FE2_TERMS.md); today error 70 |
| `**` `variable`, `section`, `set_option` | `( -- )` | commands: [FE2_TERMS.md §2.2](../design/FE2_TERMS.md) |

### A.2 The words

**Declarations.** `theorem`, `def` and `axiom` start a declaration on an
empty stack; `end NAME` closes it and the name must repeat. A theorem has
binders, then the statement (one term), then `:=`, then the proof (a term,
section C, or `by` and tactics, section D), then `end NAME`. Lean
equivalents: `theorem NAME (binders) : statement := proof`. A definition
is the same with a value; an axiom has no `:=` proof. `protected` precedes
the KIND (error 44 outside a namespace); `universe NAME` declares a
universe parameter (`universe u`); `import-stub` stands for a constant an
import would provide and is refused by `leanforth check` (error 48), which
takes the library from `--env`. `namespace`, `open` and `end` work as in
Lean, with Lean's name resolution (innermost namespace first, protected
names, ambiguity error 27).

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

**Binders.** `T explicit: x` opens a binder `(x : T)` whose type is the
tree written before it; `Nat List explicit: xs` is `(xs : List Nat)`.
Every binder before `:=` becomes a parameter of the declaration. The words
`implicit:`, `strict-implicit:` and `instance:` exist in both forms; no
checked natural-form file uses them (a binder kind the elaboration does not
give is error 136). The kernel form's `fun`, `forall` and `->` close
binders (`tests/author/01-identity.lf`, `02-composition.lf`).

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
`xs.length` and `n Nat.succ` is `Nat.succ n`; `' NAME` pushes the function
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
expected type and prints `TERM : TYPE`. It is never part of a verdict: a
file of only `#check` lines ends "nothing checked by the kernel", exit 0.
Lean: `#check 0 + 0 = 0`, which prints `0 + 0 = 0 : Prop`.

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

**Comments.** `\ ...` and `( ... )` as in Forth, on one line.

---

## B. Proof outlines

A *proof outline* is a printed, step-by-step reading of an accepted proof.
It is untrusted presentation: its sentences are not checked reasoning, and
each line names the checker steps behind it
([PROOF_OUTLINE.md](PROOF_OUTLINE.md)). Printing is section G; this
section is the words in the text that go into it.

### B.1 Glossary

| Word | Stack comment | Function |
| --- | --- | --- |
| `label: NAME` | `( t -- t )` | name a step; unique in the declaration |
| `note" text"` | `( t -- t )` | a note by a person on the term |
| `ai-note" text"` | `( t -- t )` | a note by an AI, tagged as such |
| `**` English line per tactic step (plan 8.6.12) | | from the step log, `--steps`; designed in [S2_INTERFACE.md](../design/S2_INTERFACE.md), not on main |

### B.2 The words

`label:` and the two note words attach a name or a sentence to the term on
the stack, and the printer shows them again; they are available in the
kernel form (`tests/author/09a-chain-draft.lf`, `09b-chain-edit.lf`).
A label must not repeat (error 29); a note ends with `"` on its line
(error 37). Notes never change the term, so editing a note does not
change a verdict. Lean has no equivalent; the nearest is a comment.

```text
\ tests/author/09a-chain-draft.lf, kernel form (excerpt)
h  g  f a $   label: to-B  ai-note" f turns the proof a of A into a proof of B"
      $       label: to-C  ai-note" g turns that into a proof of C"
   $          label: to-D  note" h finishes the chain: a proof of D"
```

```text
\ (illustration, not run) a note on a natural-form term proof
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

| Word | Stack comment | Function |
| --- | --- | --- |
| `NAME` (a theorem or constructor) | `( a1 .. ak -- t )` | apply it to its explicit arguments: `n Eq.refl` is `Eq.refl n` |
| `' NAME` | `( -- t )` | the constant itself, unapplied |
| `$` | `( f a -- t )` | one more argument |
| `Eq.refl`, `Nat.zero_add`, `congrArg`, ... | `( a -- t )` | any constant of the library named with `--env` |
| `Eq.refl 1 ^ Nat $ n $` | | kernel form: explicit universe levels with `^` and every argument with `$` |
| `**` `fun`, `⟨ ⟩`, `show`, `▸`, `calc`, `let:` and `have:` in natural form | | proof-term forms: [FE2_TERMS.md §2.2](../design/FE2_TERMS.md) |

### C.2 The words

A proof term is a term whose type is the statement. Names are applied to
their explicit arguments exactly as in statements, so `n Eq.refl` builds
`Eq.refl n : n = n` and the elaborator supplies the hidden type and level.
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
tactic word starts with `by-` (the block words `|` and `]` are the only
exceptions). The words run in order on a list of goals, the statement's
goal first, as Lean runs them; LeanForth stops at the first error, Lean
goes on to report more. A tactic never makes a theorem accepted: the term
it builds is checked by the kernel.

### D.1 Glossary

| Word | Stack comment | Function | Lean |
| --- | --- | --- | --- |
| `by` | `( -- )` | after `:=`: a tactic proof follows | `:= by` |
| `by-rfl` | `( -- )` | close the goal by reflexivity | `rfl` |
| `t by-exact` | `( t -- )` | close the goal with the term t | `exact t` |
| `by-intro: NAME` | `( -- )` | introduce one hypothesis (`_` for none) | `intro NAME` |
| `by-sorry` | `( -- )` | close the goal with an open part (NOT PROVED) | `sorry` |
| `t by-induction` | `( t -- )` | induction on variable t, one goal per case | `induction t` |
| `t by-induction-with` | `( t -- )` | the same, cases written as alternatives up to `by-end` | `induction t with` |
| `\| TAG NAMES... =>` | `( -- )` | one alternative of `by-induction-with` | `\| tag names =>` |
| `by-end` | `( -- )` | close the innermost `by-induction-with` | indentation |
| `by-rw[ r1 .. ]` | `( -- )` | rewrite with each rule, then try `rfl` | `rw [r1, ...]` |
| `by-rewrite[ r1 .. ]` | `( -- )` | rewrite with each rule, no `rfl` | `rewrite [r1, ...]` |
| `**` `by-case: TAG NAMES... =>` ... `by-end` | `( -- )` | one case after `by-induction`; read today, running stops with error 80 | `case tag names =>` |
| `**` `by-decide` | `( -- )` | close a closed goal by evaluation | `decide` |
| `**` `by-omega` | `( -- )` | linear arithmetic over `Nat` and `Int` | `omega` |
| `**` `by-native-decide` | `( -- )` | permanently unsupported (exit 2): it rests on `Lean.ofReduceBool` | `native_decide` |
| `**` `by-try`, `by-first`, `<;>` | | combinators; sketched in FE1G §4 and S2 §3 (the trail), no word fixed | `try`, `first`, `<;>` |
| `**` `by-alt: TAG NAMES... =>` | | an open question of the design: spelling alternatives without `\|` | `\| tag names =>` |
| `**` `by-refine`, `by-subst`, `by-cases`, `by-apply` and others | | named in FE2 §3/FE5 as later tactics; no spelling is fixed | `refine`, `subst`, ... |

Designs: [FE1G_TACTICS.md](../design/FE1G_TACTICS.md) (the first tactics,
§3.2 words, §7 FE1i hook), [FE1I_AUTOMATION.md](../design/FE1I_AUTOMATION.md)
(§4 `by-decide`, §5 `by-omega`, stack table at line 266),
[S2_INTERFACE.md](../design/S2_INTERFACE.md) §4, §5 and appendix G
(induction and rewriting; it overrides FE1G where they differ).

### D.2 `by`, `by-end` and the block words

`by` must follow `:=` directly (error 69 elsewhere); at `end NAME` every
block must be closed (82), and no value may be left (86). `by-induction-with`
opens a block of alternatives; `by-end` closes it. Mistakes in a shape each
stop at their word with a code, listed in the
[programming reference](../programming/LEANFORTH_WORDS.md#errors). A tactic
word outside a tactic proof is 81. An empty proof is read; it stops when run
with Lean's "unsolved goals" (89) at `by`.

```text
\ (illustration, not run; tests/front/05-unsolved.lf and s2w-rw-empty.lf are the checked cases)
theorem t   0 0 + 0 =   := by   end t
```

### D.3 `by-rfl`, `by-exact`, `by-intro:`, `by-sorry`

`by-rfl` is Lean's `rfl`: it closes `a = b` when both sides are
definitionally equal and builds `Eq.refl`. `by-exact` takes a term from the
stack and closes the goal with it; a type mismatch is error 96. `by-intro:
NAME` introduces one binder as a hypothesis named NAME, usable until the
block ends; with no binder left it is error 94. `by-sorry` closes the goal
with `sorryAx`; the declaration is then accepted but reported NOT PROVED,
with each open part listed.

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
`T.rec`. Each `| TAG NAMES... =>` alternative takes its case's goal and
names its explicit fields (`| succ k ih =>`: the number `k` and the
hypothesis `ih : 0 + k = k`). The header is on one line. Blocks nest; an
inner `ih` hides the outer one. Errors: 205 no inductive type, 206 a name
of no case (`suc`), 207 a case not written, 208 too many names, 209 mutual
or nested types, 213 a name written twice, 99 a form not ported (a target
that is no variable, hypotheses depending on it, index targets).
Plain `n by-induction` is defined too: it makes one goal per case and
leaves them open, so alone it ends in error 89 (`tests/front/s2w-induction-plain.lf`);
its cases are meant for `by-case:`, which is `**` (D.6). Use `by-induction-with`.

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
the rewritten one; then `rfl` is tried at reducible transparency.
`by-rewrite[ ... ]` is `rewrite` and does not try `rfl`. Every value
between the brackets is a rule, so an applied hypothesis is written with
`$`: `ih k $` is Lean's `ih k`. Errors: 215 no occurrence of the pattern,
216 motive not type correct, 217 dependent motive, 218 no equation, 219 a
metavariable pattern, 220 the occurs check, 99 a form not ported (a
definition as a rule, `Iff`, an instance binder). Not yet (`**`, S2 merge B
and later): `←`, `at h`, `using`, `generalizing`, and `++` as a word.

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
FE1g-2) but running it stops with error 80, "not supported yet" (plan S2
merge B). Design: [FE1G_TACTICS.md](../design/FE1G_TACTICS.md) §3.2,
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
| `TERM #check` | `( t -- )` | the type of a term, which finds what a name means (section A) |
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
`**` `import` and `export` lines are not supported (`export` is error 54);
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
