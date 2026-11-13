# FE1g: the first tactics, designed

> **2026-11-13:** for slice S1, [S1_INTERFACE.md](S1_INTERFACE.md) overrides this design where they differ (when tactics run, §3.2; the trail of §4.2; error codes, §4.6; fuel, §4.5; binder kinds).

**Status (2026-11-13): designed; FE1g-2 written and tested alone
(`src/front/tactic-syntax.fs`: the words of §3.2 but `.goals` read into a
record, their blocks' shape checked, error codes 80 to 88 of §4.6;
nothing runs); FE1g-1 written and tested alone on branch `fe1g1`** (§4.7:
each metavariable's own local context, tags, the goal list and the
proof state, the text of `.goals`; nothing runs a tactic yet). The rest
is not built. This is the
design of plan row FE1g (proof state and tactics) of
[the plan](../project/PLAN_DRAFT.md), part of FE1 ($0 + n = n$ proved
from LeanForth text), detailed from [FRONT_END.md](FRONT_END.md) §4.5 and
§8 and [ADR 0021](../adr/0021-front-end.md). Coding starts once FE1c (the
unifier), FE1e (application elaboration) and FE1f (the hand-over to the
kernel) have landed; §9 says which sub-step needs which. Every Lean fact
below was read in pinned Lean 4.35.0's sources
(`.tools/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`) or
observed by running pinned Lean on 2026-11-12 (§2.6 gives the commands).

## 1. In plain words

A *tactic proof* is a proof written as instructions ("by induction on
$n$", "by computation", "rewrite with this lemma") instead of as a proof
term. Lean runs the instructions on a list of *goals* (what is still to be
proved) and builds the proof term as it goes; its kernel then checks the
term. FE1g gives LeanForth the same: tactic words (`by-induction`,
`by-rfl`, `by-exact`, `by-intro:`, `by-rw[ … ]`, cases and alternatives)
that act on a goal list, build exactly the proof term Lean builds, and
hand it to LeanForth's kernel, which alone decides. Tactics are untrusted:
a wrong tactic can only make the kernel refuse, never accept a false
statement. Each step also records the goal before and after and the rule
it used, so that `leanforth print` can later explain the proof line by
line in English (plan 8.6.12).

The main finding of the Lean runs: Lean 4.35.0 does induction on a natural
number with `Nat.recAux` (not `Nat.rec`), whose cases are written `0` and
`n + 1`; `rw [Nat.add_succ, ih]` builds two `Eq.mpr`/`congrArg` steps and
closes the last goal with `Eq.refl`; and `rfl` is four alternatives tried
in a fixed order. LeanForth reproduces each of these node for node. One
detail cannot be reproduced and is compared differently: names Lean
invents for unnamed hypotheses carry a hash of the file name and a counter
(§2.3), so binder names are compared with those *macro scopes* erased.

## 2. The acceptance proofs, traced in pinned Lean

Abbreviations in the terms below (all from `set_option pp.all true`):
`0` and `1` are `@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))`
and the same with 1; `a + b` is
`@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b`;
`a = b` between natural numbers is `@Eq.{1} Nat a b`.

### 2.1 $0 + n = n$ by induction with alternatives and `rw` (FE1g's main test)

```lean
theorem t1 (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

Accepted by pinned Lean with `-DwarningAsError=true`. The goals, from
`trace_state` between the steps (the `rw` split into `rewrite [Nat.add_succ]`,
`rewrite [ih]`, `with_reducible rfl`, which is what the `rw` macro expands
to; Init/Tactics.lean line 632):

| Step | Goals before | What Lean does | Goals after |
| --- | --- | --- | --- |
| `by` | — | goal `?g : 0 + n = n`, synthetic opaque, no tag, context `n : Nat` | `n : Nat ⊢ 0 + n = n` |
| `induction n with` | `⊢ 0 + n = n` | eliminator `Nat.recAux` (attribute `induction_eliminator`, Init/Data/Nat/Basic.lean line 37); level `?u`, motive `?motive : Nat → Sort ?u`; `?zero : ?motive 0` tagged `zero`; `?succ : (n : Nat) → ?motive n → ?motive (n + 1)` tagged `succ`; `?motive := fun n => 0 + n = n`, so `?u := 0`; `?g := @Nat.recAux.{?u} ?motive ?zero ?succ n` | `case zero ⊢ 0 + 0 = 0`; `case succ k : Nat, ih : 0 + k = k ⊢ 0 + (k + 1) = k + 1` (both with `n` cleared) |
| `\| zero => rfl` | `case zero ⊢ 0 + 0 = 0` | `0 + 0` and `0` are definitionally equal (default transparency): `@Eq.refl.{1} Nat (0 + 0)` | none in this case |
| `\| succ k ih =>` | the `succ` goal | `introN 2 [k, ih]`: `?succ := fun k ih => ?s k ih` with `?s` delayed-assigned to the new goal over `k ih` | `k : Nat, ih : 0 + k = k ⊢ 0 + (k + 1) = k + 1` |
| `rewrite [Nat.add_succ]` | as above | `Nat.add_succ : ∀ (n m : Nat), n + Nat.succ m = Nat.succ (n + m)`; new `?n ?m`; `kabstract` at reducible transparency finds `0 + (k + 1)` (`?n := 0`, `?m := k`, by the `Nat` offset rule) but not `k + 1`; motive `fun _a => _a = k + 1`; old goal `:= Eq.mpr (id (congrArg motive (Nat.add_succ 0 k))) ?r1` | `⊢ (0 + k).succ = k + 1` |
| `rewrite [ih]` | as above | finds `0 + k`; motive `fun _a => Nat.succ _a = k + 1` | `⊢ k.succ = k + 1` |
| `with_reducible rfl` (inside `try`) | as above | `Nat.succ k` and `k + 1` equal at reducible transparency (offsets): `@Eq.refl.{1} Nat (Nat.succ k)` | none |

The final term (`#print t1`, `pp.all`, abbreviated as above):

```text
fun (n : Nat) =>
  @Nat.recAux.{0} (fun (n : Nat) => 0 + n = n)
    (@Eq.refl.{1} Nat (0 + 0))
    (fun (k : Nat) (ih : 0 + k = k) =>
      @Eq.mpr.{0} (0 + (k + 1) = k + 1) (Nat.succ (0 + k) = k + 1)
        (@id.{0} (@Eq.{1} Prop (0 + (k + 1) = k + 1) (Nat.succ (0 + k) = k + 1))
          (@congrArg.{1, 1} Nat Prop (0 + Nat.succ k) (Nat.succ (0 + k))
            (fun (_a : Nat) => _a = k + 1) (Nat.add_succ 0 k)))
        (@Eq.mpr.{0} (Nat.succ (0 + k) = k + 1) (Nat.succ k = k + 1)
          (@id.{0} (@Eq.{1} Prop (Nat.succ (0 + k) = k + 1) (Nat.succ k = k + 1))
            (@congrArg.{1, 1} Nat Prop (0 + k) k
              (fun (_a : Nat) => Nat.succ _a = k + 1) ih))
          (@Eq.refl.{1} Nat (Nat.succ k))))
    n
```

Points an implementer must reproduce exactly:

- `congrArg`'s first two value arguments are the rule's sides with its
  metavariables instantiated (`0 + Nat.succ k`, not the goal's
  `0 + (k + 1)`); the motive abstracts the goal's own subterm.
- `Eq.mpr`'s first argument is the goal's type *as stored* (`?motive (k + 1)`
  before instantiation); it reads `0 + (k + 1) = k + 1` only because
  instantiating `?motive` beta-reduces. So the instantiation of FE1b must
  do Lean's beta step for an assigned metavariable at the head (FE1b left
  it unsupported until FE1c).
- `rfl` gives `Eq.refl` of the *left* side, instantiated.
- The binder names `k ih` are the user's names (given to `introN`); `_a` is
  `rewrite`'s fixed name.

### 2.2 The same theorem with `case` and `exact` (FRONT_END.md §8.1)

```lean
theorem t5 (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ k ih => exact congrArg Nat.succ ih
```

Goals after `induction n`: `case zero ⊢ 0 + 0 = 0` and
`case succ n✝ : Nat, a✝ : 0 + n✝ = n✝ ⊢ 0 + (n✝ + 1) = n✝ + 1`; `case succ
k ih =>` renames the two inaccessible hypotheses to `k ih` and removes the
tag. Term:

```text
fun (n : Nat) =>
  @Nat.recAux.{0} (fun (n : Nat) => 0 + n = n)
    (@Eq.refl.{1} Nat (0 + 0))
    (fun (n : Nat) (a : 0 + n = n) =>
      @congrArg.{1, 1} Nat Nat (Nat.add 0 n) n Nat.succ a)
    n
```

`Nat.add 0 n` comes from the unifier (`0 + (n + 1) =?= Nat.succ ?a₁`
assigns `?a₁ := Nat.add 0 n`, FE1c's acceptance case).

### 2.3 Binder names Lean invents

Without names, `induction` introduces the fields with *hygienic* names:
the stored binder names of t5's minor premise are
`n._@.<module>._hygCtx._hyg.15` and `a._@._internal.<module>._hygCtx._hyg.16`
(`<module>` is the file's module name, plus a hash; observed with a
metaprogram printing `repr` of the stored value, §2.6). `#print` erases the
scopes. `intro` without a name does the same (`t3` with `intro; assumption`
stores `a._@…_hyg.10`). The numbers come from Lean's macro-scope counter
and the module name, which LeanForth cannot and should not reproduce.

**Rule.** Terms are compared node for node with Lean's export, universe
arguments included; binder names are compared after erasing macro scopes
(Lean's `Name.eraseMacroScopes`: `n._@…_hyg.15` becomes `n`), and a
difference is reported separately, as FRONT_END.md §6 already says for
binder names (the kernel ignores them). Where the user gives names (`with |
succ k ih`, `by-intro: h`), they are compared exactly. LeanForth itself
gives such hypotheses the erased name and marks them inaccessible (printed
`n✝`), as Lean shows them.

### 2.4 The three small acceptance proofs

| Lean | Goals | Term (`pp.all`) |
| --- | --- | --- |
| `theorem t2 (n : Nat) : n + 0 = n := by rfl` | `n : Nat ⊢ n + 0 = n` → none | `fun (n : Nat) => @Eq.refl.{1} Nat (n + 0)` |
| `theorem t3 (p : Prop) : p → p := by intro h; exact h` | `p : Prop ⊢ p → p` → `p : Prop, h : p ⊢ p` → none | `fun (p : Prop) (h : p) => h` |
| `theorem t4 (n : Nat) : 0 + n = n := by exact Nat.zero_add n` | `n : Nat ⊢ 0 + n = n` → none | `fun (n : Nat) => Nat.zero_add n` |

Two more rewrites, for the occurrence rules of `kabstract` (§5.6):

| Lean | Motive in the term | Closed by |
| --- | --- | --- |
| `theorem t6 (k : Nat) (ih : 0 + k = k) : (0 + k) + (0 + k) = k + k := by rw [ih]` | `fun (_a : Nat) => _a + _a = k + k` (both occurrences) | `@Eq.refl.{1} Nat (k + k)` |
| `theorem t7 (a b : Nat) (h : a = b) : a + a = b + b := by rw [h]` | `fun (_a : Nat) => _a + _a = b + b` (the side is a free variable: every syntactic occurrence, no unification) | `@Eq.refl.{1} Nat (b + b)` |

How `rfl` ran in t2 (`set_option trace.Elab.step true`): the `rfl` syntax
has four macro rules, tried newest first (Lean's `getEntries` lists the
most recent first; `evalTactic`'s `expandEval` tries them in that order,
restoring the state after each failure): `exact Iff.rfl` (Init/Core.lean
line 1042) failed, `exact HEq.rfl` failed, `eq_refl` succeeded; `apply_rfl`
would have come last. When all four fail, Lean reports the error of the
last one tried, `apply_rfl`'s ("first registered / last tried", Basic.lean
line 218), which is why a failing `rfl` says "The left-hand side … is not
definitionally equal to the right-hand side …".

### 2.5 Wrong proofs and Lean's errors

Each was run in pinned Lean (§2.6, file `p2.lean`); FE1g must refuse each
at the same step with the same kind of error (code below, §4.6).

| Wrong proof | Lean's first error | Where |
| --- | --- | --- |
| claim `0 + n = n + 1`, same proof as 2.1 | `Tactic \`rfl\` failed: The left-hand side 0 + 0 is not definitionally equal to the right-hand side 0 + 1` and the goal `case zero ⊢ 0 + 0 = 0 + 1` | `rfl` |
| `\| succ k ih => exact ih` | `Type mismatch: ih has type 0 + k = k but is expected to have type 0 + (k + 1) = k + 1` | `ih` |
| `\| succ k ih => rw [Nat.mul_comm]` | `Tactic \`rewrite\` failed: Did not find an occurrence of the pattern ?n * ?m in the target expression 0 + (k + 1) = k + 1` and the goal | the rule |
| `\| succ k ih => rw [Nat.add_succ]` | `unsolved goals case succ … ⊢ (0 + k).succ = k + 1` | the alternative's `=>` |
| `\| suc k ih => …` | `Invalid alternative name \`suc\`: Expected \`succ\`` (then `Alternative \`succ\` has not been provided`) | the alternative |
| only `\| zero => rfl` | `Alternative \`succ\` has not been provided` | `induction` |
| `\| succ k ih extra => …` | `Too many variable names provided at alternative \`succ\`: 3 provided, but 2 expected` | the alternative |
| `by intro h` on `0 + n = n` | `Tactic \`introN\` failed: There are no additional binders or \`let\` bindings in the goal to introduce` and the goal | `intro` |
| `by skip` | `unsolved goals n : Nat ⊢ 0 + n = n` | `by` |
| `theorem w9 : 2 + 2 = 5 := by rfl` | the `rfl` error with `2 + 2` and `5` | `rfl` |
| `induction h` with `h : p` | `Tactic \`induction\` failed: major premise type is not an inductive type p` and an explanation | `induction` |

Lean goes on after an error (it admits the goal and reports more); LeanForth
stops at the first (ADR 0021 D3). So LeanForth's error must be Lean's
*first* message; the order matters where Lean checks something up front:
`induction … with` checks every alternative's name before running any
alternative (`checkAltNames`), so a misspelt second alternative is reported
before a failure in the first.

### 2.6 How the traces were made

Probe files (kept in the implementer's notes; their text is the Lean
above): `p1.lean` (the five terms with `set_option pp.all true` and
`#print`), `p2.lean` (`trace_state` between steps and the wrong proofs),
`p3.lean` (`trace.Elab.step` and `trace.Elab.tactic.backtrack` for `rfl`),
`p4.lean` (`import Lean` and a `#eval` printing `repr` of the stored values,
for §2.3), `p5.lean` (t6, t7, `decide` and `omega`, for §2.4 and §7). Each
was run as

```sh
bash -c 'ulimit -u 500; timeout -k 5 120 nice -n 10 \
  .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -DwarningAsError=true FILE'
```

FE1g-8 (§9) turns them into checked-in test sources under `tests/front/`.

## 3. LeanForth text for tactic blocks

Following the owner's decisions of 2026-11-12 ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md),
"Front-end syntax"): tactic words carry the prefix `by-`; `:=` means "is
proved by" and `:= by` starts a tactic proof; natural LeanForth is the
default; `+` and `=` are words in theorem text.

### 3.1 The FE1 files

The main FE1g test, the proof of §2.1 (proposed name
`tests/front/01-zero-add-rw.lf`):

```text
\ Lean: theorem zero_add'' (n : Nat) : 0 + n = n := by
\         induction n with
\         | zero => rfl
\         | succ k ih => rw [Nat.add_succ, ih]
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

FRONT_END.md §8.1's file (`tests/front/01-zero-add.lf`, Lean's `case`
form of §2.2), with the closing word this design adds (question 1):

```text
theorem zero_add'
  Nat explicit: n
  0 n + n =
:= by
  n by-induction
  by-case: zero =>       by-rfl                           by-end
  by-case: succ k ih =>  ' Nat.succ ih congrArg by-exact  by-end
end zero_add'
```

And the three small ones of §2.4:

```text
theorem add_zero'   Nat explicit: n   n 0 + n =   := by  by-rfl   end add_zero'
theorem self_imp    Prop explicit: p  p p ->      := by  by-intro: h  h by-exact   end self_imp
theorem zero_add_ex Nat explicit: n   0 n + n =   := by  n Nat.zero_add by-exact   end zero_add_ex
```

(`self_imp` needs `Prop` and `->` in natural form, which FE1a left for
later (plan FE2); no statement FE1a can read has a Π to introduce. Until
they exist, FE1g-4 tests `by-intro:` in Forth unit tests on goals built
directly, and `self_imp` joins the file when FE2's words land.)

Read aloud, `n by-induction-with | zero => by-rfl | succ k ih => by-rw[
' Nat.add_succ ih ] by-end` is "by induction on $n$: in the case zero, by
computation; in the case succ with $k$ and the hypothesis `ih`, by
rewriting with `Nat.add_succ` and then with `ih`".

### 3.2 The words

| Word | Stack effect | Lean | What it does |
| --- | --- | --- | --- |
| `:= by` | `( -- )` | `:= by` | elaborates the statement (FE1e), opens the proof state with one goal |
| `by-rfl` | `( -- )` | `rfl` | closes the main goal by reflexivity (§5.3) |
| `by-exact` | `( t -- )` | `exact t` | elaborates `t` against the main goal's type and closes it (§5.2) |
| `by-intro:` NAME | `( -- )` | `intro NAME` | introduces one binder or `let` as NAME (§5.1); `by-intro: _` an inaccessible one |
| `by-induction` | `( t -- )` | `induction t` | induction on `t`; leaves one goal per case, tagged (§5.4) |
| `by-induction-with` | `( t -- )` | `induction t with` | the same, with the alternatives that follow, up to `by-end` |
| `\|` TAG NAMES… `=>` | `( -- )` | `\| tag names =>` | one alternative: names the case's new hypotheses and runs the words up to the next `\|` or `by-end` on that case's goal, which must then be closed |
| `by-case:` TAG NAMES… `=>` | `( -- )` | `case tag names =>` | focuses the first goal whose tag is TAG, renames its last inaccessible hypotheses, runs the words up to `by-end`, which must close it (§5.5) |
| `by-end` | `( -- )` | end of indentation | closes the innermost `by-induction-with` or `by-case:` block |
| `by-rw[` … `]` | `( -- )` | `rw [r₁, …]` | rewrites the main goal with each rule built between the brackets, in order, then tries `rfl` at reducible transparency (§5.6) |
| `by-rewrite[` … `]` | `( -- )` | `rewrite [r₁, …]` | the same without the `rfl` |
| `.goals` | `( -- )` | `trace_state` | prints the goals in Lean's format, as Forth's `.s` prints the stack |

Rules:

- **Tactic words run when they are read** (FRONT_END.md §4.5: a proof is a
  Forth program over a goal list). That is Lean's order: Lean elaborates
  the statement before the `by` block and runs each tactic before the
  next; a term argument is elaborated when its tactic runs, against that
  tactic's goal. It also gives every name its arity when it is read: `ih`
  takes as many values as its type, known once the alternative ran, has
  explicit binders (FE1a's rule), so a tactic-introduced hypothesis is
  used exactly like a binder.
- **Blocks.** `by-induction-with … by-end` and `by-case: … by-end` are
  blocks, like Forth's `CASE … ENDCASE`; blocks nest, and every block ends
  with `by-end` (question 1). `end NAME` with a block open is an error.
  `by-induction-with` first scans its block's text (up to the matching
  `by-end`, skipping nested blocks) for its alternatives' headers `| TAG
  NAMES… =>`, so that their names are checked before any alternative runs,
  as Lean's `checkAltNames` does (§2.5). Where a block's text must be read
  again or skipped (an alternative
  that applies to several goals later, `by-first`, `by-try`, `<;>` in
  FE5), the block's source span is kept and run again with the text runner
  (`lib/text-run.fs`), as Lean elaborates the same syntax again.
- **Term arguments come from the stack.** `by-exact` takes one value;
  `by-rw[` marks the stack depth and `]` takes every value built since,
  in order, as the rules (each value is syntax; `]` elaborates the first
  rule, rewrites with it, then elaborates the next, as Lean's
  `withRWRulesSeq` does); `←` after a rule (`' Nat.add_comm ←`) marks it
  right-to-left (FE5; unsupported in FE1). A tactic word that finds the
  wrong number of values is a malformed-input error. A rule that is a
  theorem is written with `'` (`' Nat.add_succ`), as Lean writes the bare
  name `Nat.add_succ`; a hypothesis by its name. Inside the brackets
  every value is a rule: a hypothesis there takes no values, and one
  applied to arguments is written with `$` (`ih k $` is Lean's
  `rw [ih k]`; decided in FE1g-2 after review fe1g2 L1), so the rules
  never depend on a hypothesis's type.
- **No value may be left on the stack** at `:= by`, at a tactic word that
  takes none, or at `end NAME`.
- Labels and notes (ADR 0017 §11) may follow a tactic word as they follow a
  term; they attach to that step's record (§6).

## 4. The tactic framework in Forth

New folder `src/tactic/` (FRONT_END.md §4.5; untrusted; uses `lib/`,
`core/`, `present/`, `author/` and `front/`, never `kernel/`).

### 4.1 Proof state

One context record (ADR 0009), `pst`, holds:

| Field | Meaning | Lean |
| --- | --- | --- |
| `pst-goals` | the goal list: a handle into the goal-list store (below) | `Tactic.State.goals` |
| `pst-root` | the declaration's goal `?g` | the `by` metavariable |
| `pst-depth` | open blocks | — |
| `pst-recover` | always false | `Tactic.Context.recover` (LeanForth never recovers, ADR 0021 D3) |
| `pst-fuel` | tactic steps left | `maxHeartbeats` / `maxRecDepth` |
| `pst-step` | the next step number for the log (§6) | — |

**Goals** are FE1b's term metavariables of kind *synthetic opaque*.
FE1g adds to each metavariable record of `front/mvars.fs` a **tag** (a name
ID, Lean's `MetavarDecl.userName`, set by `induction` to `zero`, `succ`,
cleared by `case`).

**Each goal has its own local context.** In Lean every metavariable
carries a `LocalContext`, and tactics change it per goal: `induction`
clears the target `n` from both cases' goals (`tryClear`), `introN` adds
different hypotheses in different cases, `case` renames hypotheses in one
goal only. The names matter for the term, not only for display:
`mkLambdaFVars` takes each binder's name from the goal's local context
(the motive's `fun n =>`, the alternatives' `fun k ih =>`). FE1b's model,
"a metavariable sees the first *count* free variables of the one
growing local context", cannot express a cleared or renamed hypothesis.
FE1g-1 therefore replaces `mvd-lctx` (a count) by a **context view**: an
ordered run of entries (free variable, user name, binder kind,
inaccessible flag) in an append-only heap store, shared by goals until one
changes it (a change appends a new run). The free variables' types and
values stay in `core/local-context.fs`, which keeps neither names nor
binder kinds; the view adds them, as Lean's `LocalDecl` has them. FE1c's
assignment check (Lean's `checkAssignment`: a value may only use free
variables of the metavariable's context) asks the view; this is a change
to FE1b's interface that FE1c must use, to be agreed before either lands.

**The goal list** is a list of metavariable leaves. It lives in an
append-only heap store of cells (`lib/store.fs`); a list is a pair (start,
count) of that store and is never changed in place: `replaceMainGoal [g₁ …
gₖ]` appends `g₁ … gₖ` followed by the old list's tail and makes the new
pair current. Lists are short (FE1: at most two goals), so copying is
cheap, and a saved state needs only the pair and the store's mark. "The
main goal" is the first goal that is not yet assigned (Lean's
`getMainGoal` skips assigned goals; `getUnsolvedGoals` filters them).

### 4.2 Saved states and backtracking

Lean's states are persistent values: `saveState` is a pointer copy. Forth's
stores are mutable, so FE1g needs an **undo trail** (as Prolog systems
keep one):

- `front/mvars.fs` gains a trail store and three words:
  `lf-mctx-save ( -- save )`, `lf-mctx-restore ( save -- outcome )`,
  `lf-mctx-commit ( save -- )`. While a save is open, every change to a
  record that existed before it (an assignment, a delayed assignment, a
  level assignment, a kind change, a tag change) first pushes (address,
  old value) on the trail. A restore undoes the trail back to the save,
  newest first, then rolls the term, level and reference stores back with
  their scratch mark (`core/scratch-marks.fs`, which already gives back
  nodes, levels, references and the local-context entries made since) and
  the metavariable and goal-list stores with their store marks. Saves are
  LIFO, like scratch marks.
- The same trail is what FE1c's `isDefEq` needs for Lean's
  `checkpointDefEq` (a failed unification leaves no assignment behind); it
  should be built once, in FE1g-1 or in FE1c, whichever lands first.
- A **tactic saved state** is (mctx save, goal-list pair, proof-state
  fields, the step log's count). `by-first`, `by-try`, the `rfl`
  alternatives (§5.3), `rw`'s `try` and Lean's `observing?` restore it on
  failure; on success the save is committed (its trail entries merge into
  the enclosing save, or are dropped when there is none).
- Error messages are not part of the state: LeanForth stops at the first
  error that is not caught by a combinator, so there is nothing to restore.

### 4.3 Running tactic words

A tactic word runs at once on the current proof state and either succeeds
(the state changed) or fails with an error record (code, position, the
goals as they stood, the terms the message names). Combinators turn a
failure into backtracking:

- `focus` (Lean's): the block words run with only the main goal in the
  list; at the block's end the goals left are put in front of the rest.
- `closeUsingOrAdmit` (Lean's, for `case`, alternatives and the whole
  `by`): at the block's end no goal may be left, else the error "unsolved
  goals" with them, at the block's `=>` (alternatives, `case`) or at `by`
  (the whole proof). LeanForth never admits.
- Choice points (FE1: the four `rfl` alternatives, `rw`'s `try`; FE5:
  `by-first`, `by-try`, `<;>`): save, run the alternative, on failure
  restore and run the next, and when all fail report the error Lean
  reports (for macro alternatives, the last one tried). A block that is
  tried again is re-read from its kept source span.

Nothing here recurses on the host stack: nested blocks are frames on a heap
stack (`lib/frame.fs`), one frame per open block with its kind, its saved
goal list, its `=>` position and, for a choice point, its save. A frame is
pushed by the opening word and popped by `by-end`, `|` or the end of an
alternative, so the depth of nesting has no limit but the heap's (plan task
6.2.0 (b)). Meta-level work (`whnf`, `isDefEq`, instantiation) runs on
FE1c's heap stacks.

### 4.4 Assembling the term and the hand-over

At `:= by` (after FE1e has elaborated the statement to a type `T` in the
local context of the declaration's binders): make `?g : T`, synthetic
opaque, untagged; open the proof state with goals `[?g]`. At `end NAME`:
no block may be open; the goal list must be empty (else "unsolved goals",
Lean's message, at `by`); then the value is the binders abstracted over
`?g` (Lean's `mkLambdaFVars`), and FE1f's `lf-handover ( decl type value --
outcome )` instantiates every metavariable (with the beta step and
delayed assignments, §2.1) and refuses the declaration if any hole is
left. The export writer refuses a metavariable whatever the front end
decided (ADR 0021 D2), and the kernel checks the term like any other: no
tactic result is ever trusted. Lean also runs the synthetic-metavariable
loop after the block (`Term.runTactic`); FE1's tactics leave none, and a
pending instance problem at that point answers unsupported (FE3).

### 4.5 Fuel and resources

Each tactic word spends one unit of `pst-fuel` (default and `--fuel` as
for the rest of the front end); every call into FE1c passes on its own
fuel. Exhausted fuel is the outcome *exhausted*, never a closed goal;
a full store is *full*. Both stop the declaration at the token that ran
out, as every other front-end failure does.

### 4.6 Errors

Every failure maps to the outcome vocabulary (ADR 0008) and to an error
code of `author/errors.fs` with the token's line and column; a tactic
error also prints the goals, as Lean does. Proposed codes (numbers fixed
when FE1g-1 lands, after FE1e's):

| Code (name) | Lean's message | Outcome |
| --- | --- | --- |
| `lfa-e-tac-rfl` | `Tactic \`rfl\` failed: The left-hand side … is not definitionally equal to the right-hand side …` | invalid |
| `lfa-e-tac-mismatch` | `Type mismatch: … has type … but is expected to have type …` (`exact`) | invalid |
| `lfa-e-tac-no-intro` | `Tactic \`introN\` failed: There are no additional binders …` | invalid |
| `lfa-e-tac-not-inductive` | `Tactic \`induction\` failed: major premise type is not an inductive type …` | invalid |
| `lfa-e-tac-alt-name` | `Invalid alternative name …` / `Duplicate alternative name …` / `Missing alternative name …` | invalid |
| `lfa-e-tac-alt-missing` | `Alternative … has not been provided` | invalid |
| `lfa-e-tac-alt-names` | `Too many variable names provided at alternative …` (alternatives) / `too many variable names provided` (`case`) | invalid |
| `lfa-e-tac-unassigned` | `don't know how to synthesize …` (`exact` left a new metavariable unassigned) | invalid |
| `lfa-e-tac-case-tag` | `Case tag … not found.` | invalid |
| `lfa-e-tac-no-pattern` | `Tactic \`rewrite\` failed: Did not find an occurrence of the pattern …` | invalid |
| `lfa-e-tac-motive` | `motive is not type correct` / `Motive is dependent` (`rewrite`) | invalid |
| `lfa-e-tac-not-eq` | `Invalid rewrite argument: Expected an equality or iff proof …` | invalid |
| `lfa-e-tac-unsolved` | `unsolved goals …` | invalid |
| `lfa-e-tac-no-goals` | `No goals to be solved` | invalid |
| `lfa-e-tac-open` (82) | (LeanForth) a block left open at `end`, or a tactic word inside `by-rw[ ]` | invalid |
| `lfa-e-tac-closer` (83) | (LeanForth) `by-end`, `]` or `\|` with no block of its kind (`\|` outside a `-with` block) | invalid |
| `lfa-e-tac-header` (84) | (LeanForth) a header not `TAG NAMES… =>` on one line; `=>` alone | invalid |
| `lfa-e-tac-empty` (85) | `unexpected token …; expected … tactic` (an alternative or case with no tactic) | invalid |
| `lfa-e-tac-values` (86) | (LeanForth) values left on the stack, or too few for the word | invalid |
| `lfa-e-tac-outside` (81) | (LeanForth) a tactic word outside `:= by` | invalid |
| `lfa-e-tac-arity` (87) | (LeanForth, FE1g-2 only) more values than a word takes, where a hypothesis read with values below it might take them | unsupported |
| `lfa-e-tac-run` (80) | (LeanForth, until FE1g-3) a tactic proof read whole, not run | unsupported |
| `lfa-e-tac-full` (88) | (LeanForth) the tactic record's stores out of room | full |
| `lfa-e-tactic` (72, exists) | not supported yet: the token names the tactic or case | unsupported |

The command line exits 4 for a front-end failure, 2 for unsupported,
as FRONT_END.md §8.3 says; nothing reaches the kernel.

FE1g-2 fixed the reading side's codes (2026-11-12; `author/errors.fs`
holds the ranges: 74 to 79 FE1c, FE1e and FE1f, 80 to 89 FE1g): the
proposed `lfa-e-tac-block` became 82, 83, 84 and 86 of the table above,
with 81, 85, 87, 88 and 80. Pinned Lean parses an empty `by` and
`induction n with` with no alternative and refuses them only when it
runs them ("unsolved goals", "Alternative `zero` has not been
provided"), so FE1g-2 reads both; it refuses an alternative with no
tactic, as Lean's parser does (85, at the word that ends it, with its
`=>`, where Lean reports, as the second place);
`tests/front/tactic-shapes.lean` keeps these shapes checked against
pinned Lean.

### 4.7 What FE1g-1 built (2026-11-13, branch `fe1g1`)

- **Runs** (`lib/runs.fs`, a library of its own): sequences of cells that never change, in two
  heap slabs; a handle is one cell, 0 the empty run; push appends in place
  when the run ends at the slab's top, else copies it there first; take,
  after and concatenation share cells. Local contexts and goal lists are
  runs, so a saved one is a handle, as Lean's persistent values are.
- **Locals and views** (`front/lctx-views.fs`): a local is Lean's
  `LocalDecl` (free variable, user name, binder kind, `LocalDeclKind`,
  inaccessible flag, a local instance's class); a view is a run of locals,
  Lean's `LocalContext`: push (`mkLocalDecl`), erase, rename
  (`setUserName`), find, `findFromUserName?`, `isSubPrefixOf` with and
  without `exceptFVars`. The types and values stay in
  `core/local-context.fs`, which now keeps Lean's `nondep` flag
  (`lf-lctx-have`; a have's value is hidden, so `whnf` leaves the variable
  as Lean's `whnfEasyCases` does).
- **Metavariables** (`front/mvars.fs`): each has its view (the current
  one, Lean's Meta `lctx`, or one given: `mkFreshExprMVarAt`) and a tag;
  `lf-mvar-sees?` is `lctx.contains`; the trail of the marks also restores
  tags and kinds with their old values (this is §4.2's trail: FE1b's marks
  extended, not a second mechanism); `lf-depends-on?` is
  `exprDependsOn`.
- **Goals** (`front/goals.fs`): `mkFreshExprMVarAt` for a synthetic opaque
  goal, `MVarId.clear` and `MVarId.rename` (a new goal in a new view, the
  old one assigned), the proof state's goal list with `getMainGoal`,
  `getUnsolvedGoals`, `replaceMainGoal`, `appendGoals`. FE1g-3 adds the
  runner's fields (open blocks, fuel, step count) to the record `pst`.
- **`.goals`** (`front/goal-print.fs`): §5.7 as Lean's `ppGoal`:
  `sanitizeNames` tombstones (`n✝`, `x✝¹`), groups of one type
  (`a b : Nat`, Lean's `==`), lets with their values or `⋯` past
  `approxDepth` 254, hidden implementation details, `case TAG`, a blank
  line between goals. `tests/front/check_goals.py` compares 18 goal states
  with pinned Lean's `trace_state`: 15 print the same; 3 differ by gaps of
  the term printer (plan 8.6: `x.succ` for `Nat.succ x`, `∀` where Lean
  infers that a Π is a proposition). Also not as Lean yet (plan 8.6):
  lines Lean breaks past width 120, a binder Lean renames because its body
  uses a hypothesis of that name, Lean's numbers of anonymous
  metavariables (`?m.N`) and its display of delayed assignments.

## 5. The tactics of FE1

For each: Lean's algorithm (file and function), the faithful subset FE1g
ports, and exactly when it answers *unsupported* (never a guess). "Lean's
term" means the comparison of §8.

### 5.1 `by-intro:` (Lean `intro h`; `Meta/Tactic/Intro.lean`, `introNImp`)

Algorithm: take the main goal's type; if it is a Π (`forallE`) or a `let`,
use it, else instantiate metavariables and if still neither, `whnf` it
(default transparency) and try again; else the `introN` error. For a Π:
a new free variable with the binder's domain (`headBeta`'d) and the given
name, explicit binder info kept; for a `let`: a let-variable with its
value. Then a new synthetic-opaque goal with the body (instantiated with
the new variable, `headBeta`'d) and the same tag, in the extended local
context, and the old goal `:= ` the new one abstracted over the variable
(`mkLambdaFVars`, or a `let` for a let-variable), which for a goal
metavariable makes a delayed assignment (FE1b's `lf-mvar-delay`). Name `_`
or no name: the binder's own name made inaccessible (§2.3; an anonymous
binder becomes `a`).

FE1 subset: one name per word; Π and `let`. Unsupported: patterns and
type ascriptions in `intro` (`intro ⟨a, b⟩`, `intro (h : p)`), `intro`
with several names in one word (use several words: Lean's `intro a b` is
the same as `intro a; intro b`), and a goal whose `whnf` needs a step FE1c
answers unsupported.

### 5.2 `by-exact` (Lean `exact e`; `Elab/Tactic/ElabTerm.lean`, `evalExact`)

Algorithm (`closeMainGoalUsing`): take the main goal off the list;
elaborate `e` against the goal's type (`elabTermEnsuringType`: FE1e's term
elaborator with the expected type, then the synthetic-metavariable rounds
with no postponing, then `isDefEq (type of e) (goal type)` with synthetic
opaque metavariables assignable, *no* coercion); any new metavariable left
unassigned is an error ("don't know how to synthesize"); then assign the
goal with the occurs check. On failure the goal goes back in front.

FE1 subset: whatever FE1e elaborates; unsupported wherever FE1e is
(holes `_` and `?_`, coercions, …). The term is FE1e's, so its identity
with Lean's is FE1e's comparison plus the assignment.

### 5.3 `by-rfl` (Lean `rfl`; Init/Tactics.lean lines 474–482, Init/Core.lean 1042, `Meta/Tactic/Refl.lean`, `Meta/Tactic/Rfl.lean`)

Algorithm: the macro's four alternatives, newest first, each from a saved
state: (1) `exact Iff.rfl`, (2) `exact HEq.rfl`, (3) `eq_refl`, (4)
`apply_rfl`; the first that succeeds wins; if all fail, the state of (4)'s
failure and its error. `eq_refl` (`MVarId.refl`, with synthetic opaque
metavariables assignable): the goal's type instantiated and put in weak
head normal form; it must be `@Eq.{u} α lhs rhs`; `isDefEq lhs rhs` at the
current transparency (default; reducible under `with_reducible`, as in
`rw`); the goal `:= @Eq.refl.{u} α lhs` with `lhs` instantiated.
`apply_rfl` does the same test (with `approxDefEq`) and on `Eq` the same
assignment; on other relations it uses `@[refl]` lemmas.

FE1 subset: when the goal's type, instantiated, has the constant `Eq` at
its head with three arguments, alternatives (1) and (2) fail without a
trace (unifying `Iff ?a ?a` or `@HEq ?α ?a ?α ?a` with an `Eq`
application: three different inductive types, nothing unfolds, so
`isDefEq` is false at every transparency and their state is restored), so
FE1g runs (3) directly and, if its `isDefEq` is false, reports (4)'s error
`lfa-e-tac-rfl` (the same `isDefEq` test fails). Unsupported: a goal
whose head is anything but `Eq` (`HEq`, `Iff`, a relation with `@[refl]`
lemmas, a definition that unfolds to one): FE5 ports `exact` of
`Iff.rfl`/`HEq.rfl` and the `@[refl]` table from the elaboration data. The
comparisons of §8 check every `rfl` of the acceptance files against Lean;
the fault `fe-rfl-non-eq` (§8.3) checks the unsupported answer.

### 5.4 `by-induction`, `by-induction-with` (Lean `induction t [with …]`; `Elab/Tactic/Induction.lean` `evalInduction`, `evalInductionCore`, `ElimApp.mkElimApp`, `setMotiveArg`, `evalAlts`; `Meta/Tactic/ElimInfo.lean`)

The `induction` tactic of Lean 4.35.0 does not go through
`Meta/Tactic/Induction.lean`'s `MVarId.induction` (an older,
recursor-only procedure); it builds the eliminator application itself.
Algorithm, for one target without `using` and `generalizing`:

1. **Target.** Elaborate `t` (FE1e, no expected type). If it is not a free
   variable, or is a let-variable, Lean generalizes it first
   (`elabElimTargets`, `MVarId.generalize`).
2. **Eliminator.** The target's type, instantiated and `headBeta`'d (no
   `whnf`), must have a constant `C` at its head; the custom eliminator
   for `(induction, [C])` is looked up in the elaboration data (FE1d's
   `elab-eliminator-for`; for `Nat`: `Nat.recAux`). Without one, the type
   is put in `whnf` and must be an inductive type `C` (else the
   `not-inductive` error), not mutual and not nested, and the eliminator
   is `C.rec`. The eliminator gets fresh universe level metavariables.
3. **ElimInfo** (`getElimExprInfo`): over the eliminator's type as a
   telescope (`forallTelescopeReducing`), the conclusion must be the
   motive applied to arguments; the targets are the leading arguments
   that are binders of the telescope; `motivePos`, `targetsPos`; each
   other *explicit* binder is an alternative with its binder name, its
   number of fields (the Π-binders and lets of its type, `altArity`) and
   whether it proves the motive.
4. **Generalize** the hypotheses that depend on the target (`generalizeVars`:
   revert them; they are re-introduced in each case).
5. **mkElimApp**: walk the eliminator's type: the motive becomes a new
   synthetic-opaque metavariable; a target position takes the target (its
   type checked with `ensureHasType`); implicit and strict-implicit binders
   become natural metavariables; instance binders synthetic ones, solved by
   instance synthesis (FE1e); every other binder an alternative: a new
   synthetic-opaque goal tagged with the binder's name appended to the main
   goal's tag (`zero`, `succ`). After the walk, the conclusion must be the
   motive applied to the targets (`complexArgs` are the rest).
6. **setMotiveArg**: the motive is the goal's type abstracted over the
   targets (`mkLambdaFVars`); its inferred type must be definitionally
   equal to the motive's expected type (this assigns the level, `?u := 0`).
7. The main goal `:=` the eliminator application.
8. **Alternatives** (`evalAlts`). With `with`: check every alternative's
   name first (`checkAltNames`: known, not repeated, a wildcard `_` only
   last); then, in the order written, for each: `introN` its fields with
   the given names (more names than explicit fields is an error), then
   re-introduce the generalized hypotheses, clear the target (`tryClear`),
   and run the alternative's words on that goal with `closeUsingOrAdmit`.
   Then every alternative not written is an error ("has not been
   provided"). Without `with`: for each alternative in the eliminator's
   order, `introN` with inaccessible names, the same clearing, and the goal
   is appended to the goal list with its tag.

FE1 subset: one target that is a free variable of the local context
(not a let-variable); the eliminator from the elaboration data or
`C.rec` of a non-mutual, non-nested inductive type; no hypothesis depends
on the target (nothing to generalize); no complex motive arguments; no
instance binders in the eliminator; alternatives with names, no `@`, no
wildcard, no pre-tactic (`with tac`), no multi-name `| a | b =>`.
Unsupported (exit 2 at the token): `using`, `generalizing`, several
targets, a target that is not a free variable, hypotheses that depend on
the target, an eliminator with instance arguments or complex motive
arguments, a mutual or nested type, the wildcard and `@` forms, indices
(`addImplicitTargets` with implicit targets), and `Cases.unifyEqs?` with
equations (only `cases` makes them). The term must equal Lean's
(§2.1, §2.2); `fe-eliminator-ignored` (FRONT_END.md §8.4) shows that using
`Nat.rec` instead is caught.

### 5.5 `by-case:` (Lean `case tag x y => tac`; `Elab/Tactic/BuiltinTactic.lean` `evalCase`, `findTag?`, `renameInaccessibles`)

Algorithm: find a goal whose tag, macro scopes erased, *is* the given tag;
else one whose tag ends with it; else one whose tag begins with it (else
"Case tag … not found."). Rename (`Elab/Tactic/RenameInaccessibles.lean`):
walk the goal's local context from the newest hypothesis back; each one
that is inaccessible (made by a tactic without a user name) or shadowed (a
newer hypothesis has its name) takes the *last* remaining given name (`_`
leaves it as it is) until the names run out; names left over are the
error "too many variable names provided" (Lean logs it and goes on;
LeanForth stops). The renamed context goes to a new goal assigned to the
old one. Clear the goal's tag; run the block with only that goal
(`closeUsingOrAdmit`: it must be closed at `by-end`); the other goals stay
as they were. Renaming changes the local context's display names only,
not the binder names already in the term (§2.2).

FE1 subset: one tag per `by-case:` (Lean's `case a | b =>` is
unsupported), the three tag searches, renaming. The binder names stay
the hygienic ones Lean would have (compared with scopes erased, §2.3).

### 5.6 `by-rw[ … ]`, `by-rewrite[ … ]` (Lean `rw`, `rewrite`; `Elab/Tactic/Rewrite.lean` `evalRewriteSeq`, `withRWRulesSeq`, `rewriteTarget`; `Meta/Tactic/Rewrite.lean` `MVarId.rewrite`; `Meta/KAbstract.lean`; `Meta/Tactic/Replace.lean` `replaceTargetEq`)

`rw [r₁, …, rₙ]` is the macro `rewrite [r₁, …, rₙ]; try (with_reducible
rfl)`. `rewrite` takes the rules in order; for each:

1. **The rule.** A hypothesis name: that hypothesis. A global name: if
   it is a definition with equation theorems, Lean rewrites with those
   (unsupported in FE1, FE8); a theorem is elaborated as the bare constant
   (FE1e, no expected type, postponing allowed, then the synthetic rounds).
2. **The equation.** The rule's type, instantiated; its leading Π-binders
   become new metavariables (`forallMetaTelescopeReducing`: natural, or
   synthetic for instance binders); the conclusion must be `@Eq α lhs
   rhs` (or `Iff`, made an equation with `propext`: unsupported in FE1).
   `lhs` may not be a metavariable application.
3. **kabstract** the instantiated goal type `e` over `lhs`, under the
   rewrite's configuration (`Rewrite.Config`, Init/Meta/Defs.lean line
   1729: transparency *reducible*, offset constraints on, all
   occurrences). If `lhs` is a free variable, every syntactic occurrence is
   abstracted, with no unification (t7 of §2.4). Otherwise visit `e` in
   pre-order, left to right (a node is tested before its children; an
   application's function before its argument; a binder's domain before its
   body, which has one more bound variable): a node with loose bound
   variables is not tested; a node whose head symbol and number of
   arguments equal the pattern's is tested with `isDefEq` against the
   pattern (instantiated by earlier matches); a match (which may assign the
   rule's metavariables) becomes the bound variable of its depth and its
   children are not visited; otherwise its children are. Every match is
   abstracted (t6 of §2.4). No match is the error "Did not find an
   occurrence of the pattern".
4. **The motive** `fun (_a : α) => eAbst` must type-check (Lean's
   `Meta.check`; else "motive is not type correct") and its body's type
   must equal `e`'s type with `_a` free (else "Motive is dependent").
5. **The proof** `@congrArg.{u₁, u₂} α eType lhs rhs motive heq` (`u₁`,
   `u₂` the levels of `α` and of `e`'s type); new goals: the rule's
   metavariables left unassigned (FE1: none, else unsupported).
6. **replaceTargetEq**: a new synthetic-opaque goal with type `eNew`
   (`eAbst` with `rhs` put in, instantiated) and the old tag; the old goal
   `:= @Eq.mpr.{v} target eNew (@id.{0} (@Eq.{1} Prop target eNew) proof)
   new` where `target` is the old goal's type *as stored* and `v` its
   level.

Then `try (with_reducible rfl)`: §5.3 at reducible transparency from a
saved state; a failure is forgotten (the goal stays).

FE1 subset: rules that are a hypothesis or a theorem constant, left to
right, at the goal (no `at h`), with all their metavariables assigned by
`kabstract`, `Eq` conclusions. Unsupported: `←`, `at`, `Iff` rules,
definitions (equation lemmas), rules leaving new goals, `occs` and other
configuration, and any `isDefEq` step FE1c answers unsupported. FE1c must
supply `isDefEq` at the *reducible* transparency (as well as default, for
`rfl`) with Lean's `Nat` offset rule (§2.1 needs `k + 1 =?= Nat.succ ?m`
and `Nat.succ k =?= k + 1`), and `Meta.check` of the motive (its type
inference).

### 5.7 `.goals` (Lean `trace_state`)

Prints each goal as Lean does: `case TAG` when tagged, the hypotheses
(`k : Nat`; inaccessible names with `✝`), `⊢` and the target, goals
separated by a blank line; with `--json` the same as records (§6). The
terms are printed by the printer of `src/present/`; where its Lean form
differs from Lean's own printing (Lean prints `Nat.succ x` as `x.succ`),
the golden files say so and plan 8.6 owns the gap.

## 6. Recording for explained proofs (plan 8.6.12)

### 6.1 What is recorded

Each tactic step that changes the state appends one record to the
declaration's **step log** (a heap store in the proof state, reset with the
declaration; a restore of §4.2 drops the records made since the save, so
only steps that took effect remain):

| Field | Meaning |
| --- | --- |
| `step` | number, from 1, in the order the steps took effect |
| `tactic` | `induction`, `case`, `rfl`, `exact`, `intro`, `rewrite`, `rfl-after-rw`, … |
| `rule` | how the goal was closed or changed: `induction` (with `eliminator`), `case-split` (the alternative's tag and new hypotheses), `defeq-refl` (by computation), `exact` (the term), `intro` (the new hypothesis), `rewrite` (the rule's statement, its direction, the occurrence) |
| `goal_before` | the goal acted on: tag, hypotheses, target (term handles; printed with the declaration's printer) |
| `goals_after` | the goals it left in its place (none when it closed the goal) |
| `refs` | the constants used (`Nat.recAux`, `Nat.add_succ`, `Eq.refl`) and the hypotheses (`ih`) |
| `location` | for `rewrite`: the side and position of the rewritten subterm in `goal_before`'s target (a path of argument indices) |
| `source` | line and column of the tactic word; the label (ADR 0017 §11) when there is one |
| `parent` | the step whose goal this one works on (induction → its cases), so the log is a tree |

### 6.2 Format

`leanforth check --steps FILE.ndjson` (or `--json`, which embeds them)
writes, per declaration, one header line and one line per step:

```json
{"tactic_steps":{"format":"leanforth-tactic-steps","format_version":1,"declaration":"zero_add''","steps":7}}
{"step":1,"parent":0,"tactic":"induction","rule":"induction","eliminator":"Nat.recAux","target":"n","goal_before":{"tag":null,"hyps":[["n","Nat"]],"target":"0 + n = n"},"goals_after":[{"tag":"zero","hyps":[],"target":"0 + 0 = 0"},{"tag":"succ","hyps":[],"target":"∀ (n : Nat), 0 + n = n → 0 + (n + 1) = n + 1"}],"refs":["Nat.recAux"],"source":"9:5"}
{"step":4,"parent":1,"tactic":"alternative","rule":"case-split","case":"succ","names":["k","ih"],"goal_before":{"tag":"succ","hyps":[],"target":"∀ (n : Nat), 0 + n = n → 0 + (n + 1) = n + 1"},"goals_after":[{"tag":"succ","hyps":[["k","Nat"],["ih","0 + k = k"]],"target":"0 + (k + 1) = k + 1"}],"refs":[],"source":"11:3"}
{"step":5,"parent":4,"tactic":"rewrite","rule":"rewrite","statement":"n + Nat.succ m = Nat.succ (n + m)","direction":"ltr","location":[1],"goal_before":{"tag":"succ","target":"0 + (k + 1) = k + 1"},"goals_after":[{"tag":"succ","target":"(0 + k).succ = k + 1"}],"refs":["Nat.add_succ"],"source":"11:26"}
```

(Steps 2 and 3 are the `zero` alternative and its `rfl`; 6 and 7 the
rewrite with `ih` and the closing `rfl`. With `with`, the cases' fields are
introduced by each alternative, a step of rule `case-split`; without it,
the induction step's own `goals_after` already hold them with inaccessible
names, and a `by-case:` step records the renaming.)

Terms appear in Lean's notation (the printer's Unicode form) and, under
`"kernel"`, in kernel form for tools. The JSON Schema
`schemas/tactic-steps-1.schema.json` (FE1g-7) fixes every field, as the
other LeanForth formats do (AGENTS.md: versioned, JSON-Schema'd,
deterministic, with structured error codes). The log is presentation
data: nothing reads it to decide anything, it changes no verdict, and it
is written only for a declaration the kernel accepted (a refused one
gives its error, not a log).

### 6.3 From steps to English

`leanforth print` (plan 8.6.12) turns the step tree into lines; each line
is a statement in mathematical notation and, beside it, why it follows
from the line before, from a fixed template per rule:

| Rule | Template | FE1 example |
| --- | --- | --- |
| `induction` | "Proof, by induction on *t*:" then one heading per case: "Case *t* = *pattern*, assuming *IH*:" (the pattern from the eliminator's conclusion in that case, the assumption from the hypotheses that prove the motive) | "Proof, by induction on n:", "Case n = 0:", "Case n = k + 1, assuming 0 + k = k:" |
| `defeq-refl` | "— by computation" (the two sides are equal by unfolding definitions) | "0 + 0 = 0 — by computation" |
| `rewrite` with a hypothesis | "— by the induction hypothesis" when the hypothesis is the case's induction hypothesis, else "— by *h*" | "= k + 1 — by the induction hypothesis" |
| `rewrite` with a theorem | "— by *name*", or the phrase the explanation table gives for it | "0 + (k + 1) = (0 + k) + 1 — by the definition of +" (`Nat.add_succ` → "the definition of +") |
| `exact` | "— by *term*" | "— by congrArg Nat.succ ih" |
| `intro` | "Assume *h* : *P*." | |

A chain of rewrites on one side of an equation prints as a calculation:
the first line `lhs = lhs₁`, then `= lhs₂`, …; the closing `rfl` after a
rewrite is printed only when its two sides print differently
(`Nat.succ k` and `k + 1` print alike in the mathematical form, so 8.6.12's
"= k + 1 — by the induction hypothesis" is the last line). The phrase
table (theorem name → English) is a versioned data file reviewed like the
notation table; a theorem not in it prints its name.

Every printed explanation is tagged `structured-template` (proof steps of
INTERFACE_CONTRACTS.md, `"source":"structured-template","proofBased":true`),
points to a step that took effect in a declaration the kernel accepted,
and names no premise the step did not use. It is explanation, not proof:
the kernel's check of the term is the proof. Explanations of proofs
imported from Lean's export (no tactic log) are reconstructed from the
term and tagged `reconstructed from the proof term`, as plan 8.6.12 says.

## 7. Where FE1i plugs in (`by-decide`, `by-omega`)

The owner's rule for search tactics: the same outcome as Lean (the same
statements proved or refused) and a kernel-accepted term; identical terms
measured, not required. They plug into this framework as ordinary tactic
words:

- **`by-decide`** (Lean `decide`, `Elab/Tactic/Decide.lean`
  `evalDecideCore`, `doElab`): through `closeMainGoalUsing` (§5.2), the
  goal's type `p`, instantiated and zeta-reduced, must contain no
  metavariable and no free variable (Lean: "Expected type must not contain
  free variables", observed for `n + 1 = n`); synthesize `Decidable p`
  (instance synthesis, FE1e/FE3; FE1i needs at least the instances of
  `Nat`'s `=`, `≤`, `<`, `∧`, `¬`); put `Decidable.decide p inst` in weak
  head normal form at (at least) default transparency with the `Nat`
  literal arithmetic (FE1c's `whnf`, `lib/bignum.fs`); if the result is
  `true`, the goal `:= @of_decide_eq_true p inst (@id.{0} (@Eq.{1} Bool
  (@Decidable.decide p inst) true) (@Eq.refl.{1} Bool true))` (observed
  for `2 + 2 = 4`); the kernel then re-does the computation. Otherwise
  Lean's diagnosis (evaluates to `false`, or failed to reduce, naming the
  stuck subterm). The `+kernel`, `+native` and `+revert` options are
  unsupported (`+native` permanently: `Lean.ofReduceBool`). Only the
  outcome is required (plan FE1i); the term, which this recipe should make
  identical, is compared and the result reported.
- **`by-omega`** (Lean `omega`, `Elab/Tactic/Omega/`): a port of Lean's
  algorithm (facts collected from hypotheses and the negated goal,
  linear combinations over `Int`, the omega decision procedure, the proof
  term built from Lean's `omega` lemmas), first slice `Nat` and `Int`
  linear arithmetic with `+`, numerals, `=`, `≤`, `<`. It works on the
  goal through this framework (`falseOrByContra`, `intro` of the negation,
  `exact` of the found contradiction), so it records steps like any
  tactic (rule `omega`, explained as "by linear arithmetic"). Pinned Lean
  proves `n + m = m + n` by `omega` and refuses `n + 1 = n` with "omega
  could not prove the goal: a possible counterexample may satisfy the
  constraints …"; FE1i refuses with the same kind of error (the
  counterexample text is measured, not required).
- Both are words of the tactic vocabulary, take no arguments in FE1i,
  and answer unsupported for anything outside their slice. Their terms are
  compared with Lean's and the comparison reported, but only the outcome
  is required.

**What FE9's `simp` will need from this framework** (noted only;
`Elab/Tactic/Simp.lean`, `Meta/Tactic/Simp/Main.lean` `simpTargetCore`,
`Meta/Tactic/Simp/Types.lean` `applySimpResultToTarget`): `simp` rewrites
the goal's instantiated target to a new expression with a proof of their
equality and then uses the same `replaceTargetEq` as `rw` (§5.6), or
`replaceTargetDefEq` when no proof is needed, or closes the goal with
`of_eq_true` when the result is `True`. So FE9 reuses the goal list,
saved states, errors and step log unchanged and adds the simplifier
itself (simp sets from the elaboration data, discrimination trees of FE3,
congruence, simprocs); its step record lists the lemmas used (Lean's
`usedSimps`), which is what an explanation "by simplification with …"
needs.

## 8. Tests

### 8.1 Identity with Lean (node for node)

`tests/front/fe1g.lean` holds the Lean source of every acceptance proof
(§2.1, §2.2, §2.4); `make reference-fe1g` (a pinned-Lean target with the
Lean cache, like the other comparisons) compiles it with
`-DwarningAsError=true` and exports it with `scripts/export.sh`. The
LeanForth twin `tests/front/fe1g.lf` is checked against the same
environment slice (which must contain `Nat.recAux`, `Nat.add_succ`,
`Nat.zero_add`, `congrArg`, `Eq.mpr`, `id` and the eliminator record of
`Nat.recAux`; the slice of ELABORATION_DATA.md has none today), and
`tests/front/check_fe1g.py` compares, per theorem, LeanForth's exported
records with Lean's: every node equal, universe arguments included;
binder names equal after erasing macro scopes, a difference reported in
its own column (§2.3). Goals are compared the same way: a small Lean
command in the test source writes each `trace_state` goal as export
records, and `.goals --json` writes LeanForth's; both compared node for
node. A harness self-test feeds the comparison a known-wrong table and
must see it refused.

### 8.2 Coverage classes ([TEST_COVERAGE_REVIEW.md](../development/TEST_COVERAGE_REVIEW.md))

1. **Pass, fail and every outcome.** Accepted: the theorems of §2 (t3
   once natural `Prop` and `->` exist).
   Front-end failure (exit 4, nothing checked): each wrong proof of §2.5,
   with the error code and position compared with Lean's first message.
   Unsupported (exit 2 at the token): `using`, `generalizing`, `←`, `at`,
   `rfl` on `Iff`, a definition as a rewrite rule, `intro` with a pattern,
   `case a | b`. Rejected by the kernel (exit 1): a test hook that makes
   `by-rfl` skip its `isDefEq` (fault `fe-rfl-no-defeq`) on the wrong twin:
   the kernel refuses `Eq.refl` of `0 + 0 = 0 + 1`. Axioms: a proof with
   `propext` named in `by-exact` reports it.
2. **Malformed input.** `by-end` without a block; `end` with a block open;
   `|` outside `by-induction-with`; `=>` missing; an empty tag; `by-rw[`
   without `]` and `]` without `by-rw[`; `by-exact` with no value or two;
   values left at `:= by`, at a tactic word or at `end`; a tactic word
   outside `:= by`; a second `:= by`; `by-intro:` without a name; a tag or
   name that is not a valid name. Each a stable code, nothing checked.
3. **Interfaces.** The stack effect of every new word under
   `tests/support/checks.fs`' `run-case`; every error code in the
   catalogue; every failure an outcome other than ok; the save, restore
   and commit words of the trail (a restore after assignments, kind and tag
   changes gives back exactly the earlier context; a stale save refused).
4. **Workflows and I/O.** `bin/leanforth check --env SLICE FILE.lf` on
   each file, text and `--json`; `.goals` after each tactic word (golden,
   and compared with Lean's `trace_state` as terms); `--steps` output
   validated against `schemas/tactic-steps-1.schema.json`; the step log of
   `zero_add''` golden.
5. **Resources.** Tactic fuel: `--fuel` small enough that `by-rfl` on
   $0 + 0 = 0$ runs out: exhausted, never accepted; nesting: 1,000 nested
   `by-case:` blocks (heap frames, no host recursion); a rewrite in a
   target 10,000 nodes deep (kabstract on heap stacks); store exhaustion
   under `--memory-per-check`: full.
6. **State and rollback.** After a failed declaration, the next one in
   the same process gives the same verdict as alone; a failed `rfl`
   alternative and a failed `try` leave no assignment, tag or goal behind
   (trail checked field by field); metavariables of an earlier declaration
   refused (stale); determinism over two runs and with `--jobs 2`.
7. **Regression pins.** Golden outputs of every file above; the terms in
   kernel form; fuel counts; the step logs.

### 8.3 Planted faults (`tests/mutants/faults.toml`)

`fe-rfl-no-defeq` (caught by the kernel's rejection), `fe-rfl-non-eq`
(the `Eq` head check dropped, so an `Iff` goal reaches `eq_refl` and
fails as invalid: caught by the unsupported test of class 1),
`fe-eliminator-ignored` (`Nat.rec` instead of `Nat.recAux`: caught
by the term comparison), `fe-intro-no-delay` (the old goal assigned
`fun h => ?new` without the delayed assignment, so `h` stays free in
`?new`'s value: caught where the term meets the export's audit, which
refuses a free variable (`core/unsupported-forms.fs`), and by the term
comparison), `fe-alt-names-late` (alternative names checked after running
the alternatives: caught by the first-error test of §2.5),
`fe-case-unclosed` (a block ends with its goal open: caught by the
unsolved-goals test), `fe-kabstract-first-only` (only the first match
abstracted: t6's motive becomes `fun _a => _a + (0 + k) = k + k` and its
`rfl` fails: caught by the term comparison and the unsolved-goals test),
`fe-kabstract-fvar-unify` (a free-variable side matched with `isDefEq`
instead of syntactically: caught by a unit test where the two differ),
`fe-rw-no-rfl` (`rw` without its `try
rfl`: caught by the unsolved-goals test), `fe-mpr-instantiated-target`
(`Eq.mpr` given the instantiated target: the same final term after
instantiation, so *not* caught by the term test; caught by a unit test of
the stored assignment, which shows why that test exists), `fe-trail-skip`
(an assignment not trailed: caught by the rollback test of class 6),
`fe-steps-unchecked-premise` (the log names a hypothesis the step did not
use: caught by the step-log golden).

## 9. Sub-steps

Sizes as in the plan (S up to ~300 lines of Forth, M up to ~800, L more),
each with its tests and a logged Forth review.

| Step | What | Needs | Size |
| --- | --- | --- | --- |
| FE1g-1 | Trail of the metavariable context (save, restore, commit) in `front/mvars.fs`; goal tags; per-goal context views (names, binder kinds, inaccessible flags) replacing `mvd-lctx`'s count; the goal-list store; the proof-state record; `.goals` | FE1b (on `main`); the trail and the views shared with FE1c (`checkpointDefEq`, `checkAssignment`): agree the interface first | M |
| FE1g-2 | Reader words: `by-` tactic words, `by-induction-with`, `\|`, `by-case:`, `by-end`, `by-rw[ ]`, block frames on a heap stack, kept source spans, the malformed-input errors | FE1a (on `main`): can start now | S–M |
| FE1g-3 | Runner: `:= by` opens the proof state after FE1e elaborates the statement; focus, closeUsingOrAdmit, choice points; error records with goals; fuel; `end NAME` assembles the value and calls FE1f's hand-over | FE1e, FE1f | M |
| FE1g-4 | `by-exact`, `by-intro:`, `by-rfl` (eq_refl path, the alternatives' order and error) | FE1c (`isDefEq`, `whnf`, `inferType`), FE1e, FE1b's delayed assignments and beta step | S–M |
| FE1g-5 | `by-induction`, `by-induction-with`, alternatives, `by-case:` (ElimInfo, mkElimApp, setMotiveArg, introN with names, tryClear, checkAltNames, findTag?, renameInaccessibles) | FE1c, FE1d (eliminator records), FE1g-4 | M |
| FE1g-6 | `by-rewrite[ ]`, `by-rw[ ]` (kabstract, motive checks, congrArg, replaceTargetEq, `try (with_reducible rfl)`) | FE1c at reducible transparency with `Nat` offsets, and `Meta.check`; FE1g-4 | M |
| FE1g-7 | Step log, `--steps`, `schemas/tactic-steps-1.schema.json`; the hook 8.6.12's printer reads | FE1g-3 | S |
| FE1g-8 | `tests/front/fe1g.lean` and `.lf`, the slice with `Nat.recAux`'s eliminator record, `check_fe1g.py` (terms and goals node for node, binder names with scopes erased), the wrong-proof table, the faults of §8.3 | FE1g-1 to 7 | M |

Total *speculative* 2,000 to 3,000 lines of Forth and as much in tests
(FRONT_END.md §8.2's 4,000 to 7,000 for all of FE1 includes FE1a–f).
FE1g-1 and FE1g-2 can start before FE1c and FE1e land; FE1g-4 to FE1g-6
cannot. FE1h (tests of all of FE1 and the done check) follows; FE1i
(`by-decide`, `by-omega`) builds on FE1g-3's runner (§7).

## 10. Questions for the owner

**Answered by the owner on 2026-11-12 (about 22:40): question 1 option (a), Lean's `|` lines with `by-end`; question 2 yes, `by-rw` is part of FE1** ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md)).

1. **How are induction cases and `case` blocks written and closed?**
   Lean writes `induction n with | zero => rfl | succ k ih => rw [...]` and
   ends each case by indentation; Forth does not use indentation. Options:
   (a) `n by-induction-with  | zero => by-rfl  | succ k ih => by-rw[ ' Nat.add_succ ih ]  by-end`:
   Lean's `|` and `=>`, one closing word for the whole group, and
   `by-case: … =>` blocks closed by `by-end` too; (b) the same with
   `by-alt: zero =>` instead of `|`, so that every proof word starts with
   `by-`; (c) only `by-case:` (no alternatives; Lean's `case`), ending at
   the next `by-case:` or `end` as FRONT_END.md §4.5 sketched, which cannot
   nest and gives Lean's other proof term (§2.2). *Recommendation: (a).*
   It reads like Lean, so Lean users and AI tools translate it line by
   line; a mandatory closing word works like Forth's `CASE … ENDCASE` and
   lets cases nest (an induction inside a case) without counting spaces;
   `|` cannot be confused with a name. The cost is one extra word per
   block, and FRONT_END.md §8.1's sample gains two `by-end`s.
2. **Should FE1 also prove $0 + n = n$ with rewriting (`by-rw[ … ]`)?**
   The plan's FE1 proof uses `exact congrArg Nat.succ ih`; the explained
   proof you asked for (8.6.12: "0 + (k + 1) = (0 + k) + 1 — by the
   definition of +; = k + 1 — by the induction hypothesis") is the proof
   by rewriting of §2.1, step for step. *Recommendation: yes*, as FE1g-6
   (size M): `rw` is one of the most used tactics (`rw [` occurs about
   7,000 times in Init's sources, a text count; Init proves a neighbouring
   lemma with `rw [Nat.add_succ, …]`), so FE5 would need it anyway, and
   with it FE1's demonstration is the explained proof.

## 11. Limits of this design

- It covers FE1's slice of each tactic; every other form answers
  unsupported, never a guess, and is named in §5 with the milestone that
  ports it (FE5 for the rest of the core tactics).
- Goal printing reuses the printer, which does not yet print every term
  as Lean does (`x.succ`); the comparison of goals is by terms, the text
  comparison lists the known differences.
- The undo trail is new machinery shared with FE1c; its rollback is a
  [bypass]-relevant part of the front end only in that a wrong rollback
  could leave a wrong assignment, which the kernel's check of the final
  term catches.
- LeanForth stops at the first error; Lean reports more. Only the first
  is compared.
