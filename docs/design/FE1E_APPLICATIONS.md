# FE1e: elaborating applications, numerals, `+`, `=` and instance search

Plan row FE1e ([plan](../project/PLAN_DRAFT.md#phase-8-front-end-fe1fe12-2026-11-12-replaces-831-and-832);
[front-end design §8](FRONT_END.md#8-fe1-in-full-0--n--n-proved-natively);
[ADR 0021](../adr/0021-front-end.md)). Status (2026-11-12): **designed**;
nothing of it is written. This page is the design a Forth implementer
starts from. It was written from pinned Lean 4.35.0's sources (file and
line references below, under `src/lean/Lean/` of the pinned toolchain) and
from pinned Lean's own traces of the cases (probes in §9). Exactness
(owner, 2026-11-12, "Front-end syntax", answer 7): every term FE1e builds
must be identical to Lean's, node for node; where FE1e has not ported what
Lean would do, it answers *unsupported* at the token, never a different
term.

## In plain words

When Lean reads `0 + n = n`, much more is filled in than is written. The
`0` could be a number of any type; `+` could be addition on any type;
`=` needs the type of both sides. Lean leaves these as holes
(*metavariables*), learns from `n : Nat` that both sides are natural
numbers, and then looks up, in a table of *instances*, how `+` and `0` are
defined for `Nat`. The finished statement names every piece:

```text
@Eq.{1} Nat
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  n
```

FE1e ports the parts of Lean that do this: the elaborator of function
applications (which inserts the hidden arguments), numerals, the
operator trees of `+` and `=`, the rounds that come back to holes later,
and instance search. In three forms:

- **Mathematics:** for every natural number $n$, $0 + n = n$.
- **LeanForth:** `0 n + n =` (the reader builds the tree
  `binrel% Eq (binop% HAdd.hAdd 0 n) n`, FE1a).
- **Lean:** `0 + n = n`, which Lean's parser turns into the same tree.

The instance table comes from the elaboration data (FE1d), which pinned
Lean writes; FE1e checks each instance against its type before using it
(§4), and every finished term is checked by the kernel (ADR 0021 D1).

## 1. What FE1 needs: the trace of `0 + n = n`

### 1.1 The cases FE1 elaborates

FE1's file (design §8.1) needs elaboration at four places, and only
three of them are FE1e's:

| Where | Term | Expected type | Who |
| --- | --- | --- | --- |
| binder `n` | `Nat` | `Sort ?u` | FE1e (`elabType`), called by FE1f's header |
| statement | `0 n + n =` | `Sort ?u` (header) or none (`#check`) | FE1e, called by FE1f |
| `succ` case | `' Nat.succ ih congrArg by-exact` | the goal `0 + (k + 1) = k + 1` | FE1e (`elabTermEnsuringType`), called by FE1g |
| the two goals | `0 + 0 = 0`, `0 + (k + 1) = k + 1` | — | FE1g: not elaborated (§1.5) |

FE1f's term proof `n Eq.refl` (plan row FE1f, `n + 0 = n`) is the fifth
case (§1.4).

### 1.2 The statement, step by step

Pinned Lean's trace (`#check fun (n : Nat) => (0 + n = n)` and the
theorem header, probes p1 and p7) shows these steps. The local context
holds `n : Nat`. As a theorem header the statement is elaborated by
`elabType` (TermElabM.lean:1980) with the expected type `Sort ?u`;
`binrel%` does not use the expected type on the branch taken here
(Extra.lean:545-553), so the term is the same as for `#check` (p7).
Metavariables are named here in order of creation: `?T` (the numeral's
type), `?i` (its instance), `?α ?β ?γ ?s` (the arguments of `HAdd.hAdd`),
`?A` (the argument of `Eq`); level metavariables `u1` (of `Eq`), `u2 u3
u4` (of `HAdd.hAdd`), `v`, `w` (of the numeral).

| # | Lean (file:line) | What happens |
| --- | --- | --- |
| 1 | `elabBinRelCore` (Extra.lean:497) | node `binrel% Eq L R`: resolve `Eq`, giving `Eq.{u1}`; open `withSynthesizeLight` (SyntheticMVars.lean:681): the pending list is saved and emptied |
| 2 | `toTree` (Extra.lean:183) on `L` | `binop% HAdd.hAdd 0 n`: resolve `HAdd.hAdd`, giving `HAdd.hAdd.{u2,u3,u4}`; its operands are leaves, each elaborated with `elabTerm leaf none` |
| 3 | `elabNumLit` (BuiltinTerm.lean:210) on `0` | `mkFreshTypeMVar .synthetic`: `?T : Sort v` (no expected type, so no unification); `getDecLevel ?T`: `v := w+1`; `mkInstMVar (OfNat.{w} ?T 0)` (TermElabM.lean:1954): `?i` synthetic; result `@OfNat.ofNat.{w} ?T (nat_lit 0) ?i` |
| 4 | `synthesizeInstMVarCore` (TermElabM.lean:1232) | instance problem `OfNat.{w} ?T 0`: **stuck** (§1.3, problem 1): `?i` registered as a pending type-class metavariable |
| 5 | `elabAtom` (App.lean:2261) on `n` | `elabAppArgs n [] none` (App.lean:1351): no binders, no arguments: `finalize` gives `n` |
| 6 | end of `toTree` | `synthesizeSyntheticMVars (postpone := .yes)`: resume `?i`: stuck again (problem 2); no progress, stop (no default instances with `.yes`) |
| 7 | `toTree` on `R` | leaf `n` (as step 5); then the same round: `?i` stuck (problem 3) |
| 8 | `analyze` (Extra.lean:256) | leaves in order `0 : ?T` (unknown: `hasUnknown`), `n : Nat` (max type := `Nat`), `n : Nat` (`isDefEqGuarded Nat Nat` at a new depth with `isDefEqStuckEx`: true). Result: max type `Nat`, `hasUncomparable` false |
| 9 | `applyCoe` (Extra.lean:415), `isPred` | root `Eq`: a predicate, so its operands are visited with `f? := Eq`; the operand `binop% HAdd.hAdd`: `hasHomogeneousInstance HAdd.hAdd Nat` (Extra.lean:387): `mkAppM HAdd #[Nat, Nat, Nat]` gives `HAdd.{0,0,0} Nat Nat Nat`, `trySynthInstance` of it: found (problem 4), so its leaves are visited with `f? := HAdd.hAdd` |
| 10 | `applyCoe`, leaf `0` (lhs) | type `?T` unknown: `hasHeterogeneousDefaultInstances HAdd.hAdd Nat true` (Extra.lean:367): `HAdd` has one default instance, so false; `isDefEqGuarded Nat ?T`: `?T := Nat`, and through `?T`'s type `w := 0` |
| 11 | `applyCoe`, leaves `n`, `n` | `isDefEqGuarded Nat Nat`: true, no coercion |
| 12 | `toExprCore` (Extra.lean:325) on `L` | `mkBinOp` (Extra.lean:316): `elabAppArgs HAdd.hAdd.{u2,u3,u4} [expr 0', expr n] none (explicit := false) (resultIsOutParamSupport := false)`. Binders: `{α}` gives natural `?α`; `{β}` `?β`; `{γ : outParam}` `?γ`; `[self : HAdd α β γ]` synthetic `?s`, kept in `instMVars`; `(a : α)`: `ensureArgType`: `isDefEq Nat ?α` (`?α := Nat`, `u2 := 0`); `(b : β)`: `?β := Nat`, `u3 := 0`; no binder left: `finalize` (App.lean:610): no expected type, so `synthesizeAppInstMVars`: problem 5 assigns `?γ := Nat`, `u4 := 0`, `?s := @instHAdd.{0} Nat instAddNat` |
| 13 | `toExprCore` on the root | `elabAppArgs Eq.{u1} [expr L', expr n] none`: `{α : Sort u1}` gives `?A`; `(a : α)`: `isDefEq Nat ?A` (`?A := Nat`, `u1 := 1`); `(b : α)`: `isDefEq Nat Nat`; `finalize` |
| 14 | end of `withSynthesizeLight` | `synthesizeSyntheticMVars (postpone := .yes)`: resume `?i : OfNat.{0} Nat 0`: found (problem 6), `?i := instOfNatNat (nat_lit 0)`; the saved pending list is put back |
| 15 | caller | `#check`: `synthesizeSyntheticMVarsNoPostponing` (nothing left), `Meta.check`, `instantiateMVars`, `levelMVarToParam` (nothing left), print `e : type` (BuiltinCommand.lean:434). Theorem header: `ensureType` (TermElabM.lean:1964): the type of the term is `Prop`, a sort |

Every metavariable is assigned at the end; the instantiated term is the
one above. Mapped onto FE1a's syntax tree, the elaborators are: `syn-k-binrel`
step 1, `syn-k-binop` step 2, `syn-k-num` step 3, `syn-k-var` step 5.

### 1.3 The instance problems, in order

| # | Problem | Kind (§3.4) | Candidates, in the order tried | Result |
| --- | --- | --- | --- | --- |
| 1-3 | `OfNat.{w} ?T 0`, `?T` of the outer depth | type has metavariables, no out-parameters | all `OfNat` instances; first tried `Lean.Grind.CommRing.OfCommSemiring.instOfNatQ` (priority 10000) | **stuck**: `?T =?= Lean.Grind.Ring.OfSemiring.Q …` with `?T` read-only throws `isDefEqStuck`; `trySynthInstance` answers undef |
| 4 | `HAdd.{0,0,0} Nat Nat Nat` | no metavariables: `preprocessOutParam` still replaces `γ` and its level (out-parameter 2, out-level 2) | table key `HAdd.{0,0,_tc.0} Nat Nat _tc.1`; `instHAdd`; its subgoal `Add.{0} Nat`: `instAddNat` (1000), then `Lean.Grind.Semiring.toAdd`, `Lean.Grind.AddCommMonoid.toAdd` (100) | `@instHAdd.{0} Nat instAddNat`, cached under `HAdd.{0,0,0} Nat Nat Nat` |
| 5 | `HAdd.{0,0,u4} Nat Nat ?γ` | metavariables and out-parameters: cache key `HAdd.{0,0,*} Nat Nat *`, a miss | as 4 | as 4; `assignOutParams` gives `?γ := Nat`, `u4 := 0` |
| 6 | `OfNat.{0} Nat 0` | no metavariables, no out-parameters | `instOfNatNat` (1000), `Zero.toOfNat0` (300), `Lean.Grind.Semiring.ofNat` (100) | `instOfNatNat (nat_lit 0)` |

No default instance fires for FE1's statement: `?T` is assigned by step
10. Default instances fire for a numeral that nothing else types, such as
`#check 0` and `2 + 2 = 4` (§2.5, cases C10 and C16 of §6.1).

### 1.4 The `succ` case and the term proof

`congrArg Nat.succ ih` against the goal
`G = 0 + (k + 1) = k + 1` (probe p2; App.lean step names):

1. `elabAppArgs congrArg.{u,v} [stx Nat.succ, stx ih] G`: implicit
   `{α} {β} {a₁ a₂}` give natural `?A ?B ?x ?y`.
2. `(f : α → β)`: `propagateExpectedType` (App.lean:563): `G` is not
   `Prop`; `getResultingType?` (App.lean:449) consumes `f` and `h`; the
   result `f ?x = f ?y` mentions `f`, so propagation is postponed. Then
   `Nat.succ` is elaborated with expected type `?A → ?B`: `elabAtom`, no
   arguments, `finalize`: `isDefEq (?A → ?B) (Nat → Nat)` assigns both
   (and `u := 1`, `v := 1`).
3. `(h : a₁ = a₂)`: `propagateExpectedType` again: the result is now
   `@Eq Nat (Nat.succ ?x) (Nat.succ ?y)`, without loose variables:
   `isDefEq G (that)` assigns `?x := Nat.add (OfNat.ofNat 0) k` and
   `?y := k` (FE1c's acceptance case: `0 + (k + 1) =?= Nat.succ ?x`).
   `ih` is elaborated with expected type `Nat.add 0 k = k`; `finalize`
   unifies it with `ih`'s type `0 + k = k` (true by unfolding).
4. `finalize`: `isDefEq G (Nat.succ (Nat.add 0 k) = Nat.succ k)`: true.

Result: `@congrArg.{1, 1} Nat Nat (Nat.add (@OfNat.ofNat.{0} Nat (nat_lit
0) (instOfNatNat (nat_lit 0))) k) k Nat.succ ih`, the subterm of Lean's
proof term (design §2.1). No instance problem. The propagation in step 3
is what makes `a₁` `Nat.add 0 k` rather than `0 + k`: a port that skips
it gives a different term (fault `fe-no-propagation`, §6.3).

FE1f's `n Eq.refl` against `n + 0 = n`: `{α}` gives `?A`; `(a : α)`:
propagation postponed (`a = a` mentions `a`); `n` with expected type
`?A`: `?A := Nat`; `finalize`: `isDefEq (n + 0 = n) (@Eq Nat n n)`, true
by unfolding. Result `@Eq.refl.{1} Nat n`.

### 1.5 The induction goals are not elaborated

`n by-induction` (FE1g) applies `Nat.recAux`, whose type in the export
already holds `0` and `n + 1` as elaborated terms; the goals are the
motive `fun n => 0 + n = n` applied to them and head-beta reduced. Pinned
Lean's goals (p2, `trace_state`):

```text
⊢ @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
k : Nat
ih : @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
       (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k) k
⊢ @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

These are FE1g's test, not FE1e's.

### 1.6 The trace is the acceptance test

FE1e prints its own trace when a test switch is on (`lf-elab-trace!`,
§5): one line per event, metavariables numbered in order of creation:
elaborator entered (syntax kind, line and column), metavariable made
(kind, type), instance problem (type in `pp.all` form, kind, candidates in
order, result: found and the instance, none, or stuck), default instance
applied, pending metavariable resumed (succeeded, not ready),
unification of the max type and leaves, final term. The golden file
`tests/front/fe1e-trace-zero-add.txt` is the event list of §1.2-1.3,
written once from pinned Lean's trace (p1) and reviewed; the test
compares LeanForth's trace with it line by line, and the final term with
pinned Lean's `pp.all` output node for node. Lean's own trace numbers
metavariables per message, so the golden file is not produced from
Lean's text mechanically; the term comparison is (§6.1). The golden
events, with the names of §1.2 (the file numbers them):

```text
binrel Eq                    resolve Eq.{u1}; open withSynthesizeLight
 tree L: binop HAdd.hAdd     resolve HAdd.hAdd.{u2,u3,u4}
  leaf 0: num                ?T synthetic : Sort v; v := w+1
                             ?i synthetic : OfNat.{w} ?T 0
                             synth OfNat.{w} ?T 0: stuck (instOfNatQ); pending ?i
  leaf n: var                n
  round (postpone yes)       resume ?i: synth OfNat.{w} ?T 0: stuck; not ready
 tree R: leaf n: var         n
  round (postpone yes)       resume ?i: synth OfNat.{w} ?T 0: stuck; not ready
 analyze                     0 : ?T unknown; n : Nat, max Nat; n : Nat =?= Nat
                             max Nat; uncomparable false; unknown true
 applyCoe Eq, predicate
  binop HAdd.hAdd            homogeneous: synth HAdd.{0,0,0} Nat Nat Nat:
                               instHAdd.{0} Nat instAddNat (subgoal Add.{0} Nat: instAddNat)
  leaf 0                     heterogeneous defaults: false; Nat =?= ?T: ?T := Nat, w := 0
  leaf n                     Nat =?= Nat
  leaf n                     Nat =?= Nat
 app HAdd.hAdd.{u2,u3,u4}    ?α natural; ?β natural; ?γ natural; ?s synthetic, instance
                             arg 0: Nat =?= ?α: ?α := Nat, u2 := 0
                             arg n: Nat =?= ?β: ?β := Nat, u3 := 0
                             finalize: synth HAdd.{0,0,u4} Nat Nat ?γ:
                               instHAdd.{0} Nat instAddNat; out-parameters ?γ := Nat, u4 := 0
 app Eq.{u1}                 ?A natural
                             arg: Nat =?= ?A: ?A := Nat, u1 := 1
                             arg: Nat =?= Nat; finalize
 round (postpone yes)        resume ?i: synth OfNat.{0} Nat 0: instOfNatNat 0; succeeded
 close withSynthesizeLight
term @Eq.{1} Nat (@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
       (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) n
```

## 2. The minimal faithful subset

Every piece is Lean's algorithm in Lean's order. Where Lean would reach
something not ported, the elaborator stops with *unsupported* and a
stable error code at the token whose elaboration needed it (§2.7). Lean's
argument orders matter and are kept: `ensureHasType` asks
`isDefEq (type of e) expected`; `finalize` and `propagateExpectedType`
ask `isDefEq expected found`; `applyCoe` and `analyze` ask
`isDefEqGuarded max type`; `mkFreshTypeMVarFor` asks
`isDefEq expected ?T`.

### 2.1 Elaborators by syntax kind

| FE1a node | Lean elaborator | FE1e |
| --- | --- | --- |
| `syn-k-num` | `elabNumLit` (BuiltinTerm.lean:210) | all of it; values of any size as `nat_lit` (FE1a reads up to 9 digits today) |
| `syn-k-const` (applied to nothing: `' NAME`) | `elabIdent` = `elabAtom` (App.lean:2261), `elabAppArgs f [] [] expected` with `f` the constant at fresh level metavariables | yes |
| `syn-k-var` | the same with `f` the free variable | yes |
| `syn-k-app` | `elabApp` (App.lean:2256): `elabAppArgs f [] args expected`, each argument `Arg.stx` | yes; the reader has resolved the name to one declaration (Lean's overload resolution is FE2) |
| `syn-k-binop` | `elabOp` (Extra.lean:475) | yes, `binop%` only (`binop_lazy%`, `leftact%`, `rightact%`, `unop%` are FE2) |
| `syn-k-binrel` | `elabBinRelCore false` (Extra.lean:497) | yes (`binrel_no_prop%` is FE2) |

`elabTerm` itself (`elabTermAux`, TermElabM.lean:1851): macro expansion (none:
the reader builds expanded trees), the elaborator by kind, `withInfoContext`
(no output effect, not ported), postponement (§2.5) and implicit lambdas
(unsupported, §2.7).

### 2.2 Applications: `elabAppArgs` as a state machine

State (App.lean:178): `f`, `fType`, `fArgs`, the remaining `args`
(each either a syntax node or an elaborated term), `expectedType?`,
`instMVars`, `propagateExpected`, `resultTypeOutParam?`; context
`explicit` (false in FE1e), `ellipsis` (false), `resultIsOutParamSupport`
(true for `elabApp` and `elabAtom`, false for `binop%`/`binrel%`; Lean
sets it false unless `Lean.Internal.coeM` is in the environment, which it
is in `Init`). Initial `propagateExpected` is false when `f` is a constant
tagged `elab_without_expected_type` (App.lean:1330; tag from the
elaboration data, §3.1).

Before the loop: `inferType f`, `instantiateMVars`; `tryPostponeIfMVar
fType` when there are arguments (unsupported, §2.7); `elabAsElim?`
(App.lean:1397): when `f` is a recursor, a `casesOn`, `recOn` or `brecOn`,
or tagged `elab_as_elim`, unsupported (FE5).

`main` (App.lean:926), one step per binder:

1. `fTypeIsForall` (App.lean:238): `fType` is a Π (its domain instantiated
   with `fArgs`), or `whnfForall` of it is; else, with arguments left,
   `synthesizePendingAndNormalizeFunType` (App.lean:373; coercion to a
   function: unsupported), with none left, `finalize`.
2. By the binder's kind (no named arguments in FE1e):
   - implicit: `addImplicitArg` (App.lean:745): a fresh natural
     metavariable of the binder's type. When `resultIsOutParamSupport`
     and the binder is the result type and an out-parameter of a later
     instance binder (`isNextOutParamOfLocalInstanceAndResult`,
     App.lean:681: `HAdd.hAdd`'s `γ` when written as an application),
     it is recorded as `resultTypeOutParam?` and `propagateExpected :=
     false`.
   - strict implicit: as implicit when arguments are left, else `finalize`.
   - instance implicit: `processInstImplicitArg` (App.lean:903): a fresh
     synthetic metavariable, pushed to `instMVars`.
   - explicit: `processExplicitArg` (App.lean:766): with an argument left,
     `propagateExpectedType arg` (below), then `elabAndAddNewArg`
     (App.lean:433): a syntax argument is elaborated with the binder's
     type as expected type, an elaborated one is taken as it is; both go
     through `ensureArgType` (`ensureHasType`). With no argument left:
     an `optParam` or `autoParam` binder is unsupported (FE2), otherwise
     `finalize` (or an eta argument when the rest has opt/auto params:
     unsupported).
3. `propagateExpectedType` (App.lean:563), only for a syntax argument
   that is not a hole or `by`, while `propagateExpected` and with an
   expected type: an expected type that is `Prop` itself switches it off;
   `getResultingType?` (App.lean:449) walks the remaining binders as
   `main` would, consuming the remaining argument count at explicit
   binders, and gives up (`none`) when the result still mentions a
   binder or more arguments than binders remain; otherwise
   `trySynthesizeAppInstMVars` (App.lean:355) and `isDefEq expected
   result`; on success `propagateExpected := false`.
4. `finalize` (App.lean:610): `eType := inferType f-applied`; with
   `resultTypeOutParam?`: `synthesizeAppInstMVars`, and if that
   metavariable is still unassigned and is `eType`,
   `synthesizeSyntheticMVarsUsingDefault`; else, with an expected type:
   `trySynthesizeAppInstMVars` and `isDefEq expected eType` (its answer
   ignored: the caller checks); then `synthesizeAppInstMVars` (App.lean:75):
   each instance metavariable by `synthesizeInstMVarCore`, the stuck ones
   registered as pending type-class metavariables.

The recursion (an argument elaborated inside `main`) runs as frame steps
(`src/lib/frame.fs`): an `elabAppArgs` activation is a record on a heap
store, its index saved on the frame stack while an argument is
elaborated, so no depth uses the host's stacks.

### 2.3 Numerals

`elabNumLit` (BuiltinTerm.lean:210): `mkFreshTypeMVarFor expected`
(BuiltinTerm.lean:203: a synthetic `?T : Sort ?v`, and `isDefEq expected
?T` when there is an expected type); `getDecLevel ?T` (decLevel of the
sort's level: an assignable level metavariable `v` becomes `w+1`); the
failure branches (expected type a proposition: error "numerals are data")
are errors with their own codes; `mkInstMVar (OfNat.{w} ?T (nat_lit k))`;
result `@OfNat.ofNat.{w} ?T (nat_lit k) ?i`. Literals use
`core/literals.fs`, big ones `lib/bignum.fs`.

### 2.4 `binop%` and `binrel%`

Ported from Extra.lean as written, for `binop%` and `binrel%` only:

- `toTree` (183): leaves elaborated with no expected type; operator names
  resolved at the root (the reader's hygienic names); after the tree,
  `synthesizeSyntheticMVars (postpone := .yes)`.
- `analyze` (256): the max type, as in step 8 of §1.2. When a leaf's
  type is known but `isDefEqGuarded max type` (new depth,
  `isDefEqStuckEx`) is false, Lean asks `hasCoe` (coercions):
  **unsupported** (FE4).
- `applyCoe` (415), `toExprCore` (325), `toExpr` (457), `mkBinOp` (316),
  `hasHomogeneousInstance` (387, with `mkAppM`, AppBuilder.lean:345, at a
  new depth), `hasHeterogeneousDefaultInstances` (367: reads the default
  instances of the operator's class and the instance's type body). A leaf
  that would get a coercion (`mkCoe`): unsupported.
- `elabBinRelCore` (497): `withSynthesizeLight`; both branches. The
  branch with no max type (all leaves of unknown type, `2 + 2 = 4`)
  elaborates the sides, applies `ensureHasType (type of lhs) rhs` and
  `elabAppArgs f [lhs, rhs] expected`.

### 2.5 Pending metavariables, postponement and default instances

The pending list (`pendingMVars`: newest first) and the kinds FE1e
makes: `typeClass` only. Ported from SyntheticMVars.lean:

- `synthesizeSyntheticMVars postpone` (611) with its step (573: resume
  each pending metavariable in creation order; a resumed `typeClass`
  metavariable runs `synthesizeInstMVarCore`), and for `postpone` not
  `.yes`: the step with `postponeOnError`, then `synthesizeUsingDefault`
  (215), then the remaining steps; with `.no`, a metavariable still
  pending is an error ("typeclass instance problem is stuck"), except for
  `#check` (`ignoreStuckTC`), where a term with holes left is unsupported
  in FE1e (printing holes: FE2).
- Default instances: `synthesizeUsingDefault` (215) over the priorities
  in descending order; `synthesizeSomeUsingDefaultPrio` (193) visits the
  pending metavariables in creation order; `synthesizeUsingDefaultPrio`
  (113) tries the class's default instances of that priority in Lean's
  list order (most recently added first), each under `commitWhen`
  (rolled back on failure, `core/scratch-marks.fs` and the metavariable
  trail of §3.5): instantiate the default instance with fresh
  metavariables, `isDefEqGuarded`, then synthesize its instance
  arguments (`synthesizePending`, 186), recursively through further
  default instances.
- `withSynthesize` (662) and `withSynthesizeLight` (681): save the pending
  list, run, synthesize (with `.yes`: `synthesizeUsingDefaultLoop`, 653,
  only in `withSynthesize`), put the saved list back.
- `synthesizeSyntheticMVarsUsingDefault` (658), for `finalize`.
- Postponed elaboration (`.postponed` metavariables, `tryPostpone`):
  never made by FE1e's elaborators except `tryPostponeIfMVar` in
  `elabAppArgs`; that answers unsupported (FE2).

### 2.6 `ensureHasType`, `elabType` and `#check`

- `ensureHasType` (TermElabM.lean:1334): `isDefEq (inferType e) expected`;
  false leads to `mkCoe`: unsupported (FE4).
- `elabType` (1980): a fresh level `u`, `elabTerm stx (Sort u)`, then
  `ensureType` (1964): `isType`, or `isDefEq (type) (Sort ?)`; a
  coercion to a sort is unsupported.
- `elabTermEnsuringType` (1918) for FE1g's `by-exact` and FE1f's term
  proofs: `elabTerm` with the expected type, then `ensureHasType`;
  `catchExPostpone` is irrelevant (FE1e never postpones).
- `#check TERM` (BuiltinCommand.lean:434): a word of natural text,
  `0 n + n = #check`. Not the signature form (`#check NAME` of a bare
  constant prints its signature: FE2). Elaborate with no expected type,
  `synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)`,
  `Meta.check` (FE1c's type inference with checking), instantiate,
  `levelMVarToParam` (a level metavariable left: unsupported in FE1e),
  print `e : type` with the term printer (`0 + n = n : Prop`).

### 2.7 What answers unsupported, and when

Each line is a Lean condition that FE1e detects before it would act, the
error (§5.3) and the plan row that lifts it.

| Lean would… | Condition (Lean source) | Lifted by |
| --- | --- | --- |
| insert a coercion | `analyze` finds `isDefEqGuarded max type` false (Extra.lean:307); `ensureHasType`'s `isDefEq` false (TermElabM.lean:1337); `applyCoe` leaf not defeq (Extra.lean:448) | FE4 |
| coerce to a function or a sort | `fTypeIsForall` false with arguments left (App.lean:947); `ensureType` needs `coerceToSort?` | FE4 |
| postpone an elaboration | `tryPostponeIfMVar fType` with arguments (App.lean:1367): `f`'s type an unassigned metavariable | FE2 |
| add an implicit lambda | the expected type, after `whnfForall`, is a Π whose binder is implicit or instance-implicit, unless it carries the no-implicit-lambda annotation (`useImplicitLambda`, TermElabM.lean:1771) | FE2 |
| use named arguments, `@`, `..`, holes `_` | not built by the reader | FE2 |
| fill an `optParam` or `autoParam` | explicit binder with no argument left whose type is `optParam`/`autoParam`, or eta arguments | FE2 |
| elaborate as an eliminator | `elabAsElim?` (App.lean:1397): recursor, `casesOn`, `recOn`, `brecOn` or `elab_as_elim` | FE5 |
| use a local instance | a local hypothesis whose type is a class (`isClass?`) when an instance problem is solved | FE3 |
| try an instance the export lacks | a candidate list that holds an `instance_left_out` record (§3.1) | the exporter, if such a case is ever met |
| synthesize a Π-typed instance goal | the goal type, after `forallTelescopeReducing`, has binders | FE3 |
| keep an answer with metavariables | an answer whose instantiated value has metavariables of the synthesis depth (`abstractMVars` with `numMVars > 0` or level parameters) | FE3 |
| run `check` on an answer | `checkMayHaveSideEffects` true (SynthInstance.lean:862) | FE3 |
| print a term with holes or universe variables | `#check` with metavariables or level metavariables left | FE2 |
| use `binop_lazy%`, `leftact%`, `rightact%`, `unop%`, `binrel_no_prop%` | not built by the reader | FE2 |
| unify what FE1c does not port | FE1c's own unsupported answers (max levels, postponed level constraints) pass through unchanged | FE1c, FE2 |

The unsupported answers never replace an error Lean gives: an elaboration
error that Lean reports before reaching the condition (an instance that
does not exist, a numeral against a proposition) is reported as the
error. A type mismatch is not such an error in FE1e: Lean looks for a
coercion first, so FE1e answers unsupported there.

## 3. Instance search

### 3.1 Elaboration data, format 2

What `getInstances` returns, and in which order, depends on facts the
first slice (FE1d) does not export. Lean keeps instances in a
discrimination tree (`instanceExtension`, Instances.lean:95); the
candidates of a goal are the tree's `getUnify` result
(DiscrTree/Main.lean:567), stably sorted by priority
(SynthInstance.lean:214), and tried **from the end**. The order of the
tree's children is `Key.lt` (DiscrTree/Basic.lean:40), which compares
constants by `Name.quickLt`, a comparison of Lean's 64-bit name hashes;
the order of values in a leaf is the order of insertion, that is the
import order of modules and the order of declarations in each.
Neither can be recovered from the export. Probe p6 confirms, for
`OfNat ?m 0`, `OfNat Nat 0`, `HAdd Nat Nat ?`, `Add Nat` (56, 56, 104
and 41 instances), that `getUnify`'s result is exactly the depth-first
order of the tree, children in their stored order, filtered to the
matches.

So the exporter (`scripts/export_elab.lean`, plan sub-step FE1e1) adds,
as format version 2:

| Record | New members | Lean source |
| --- | --- | --- |
| `instance` | `keys`: the instance's stored `InstanceEntry.keys`; `rank`: its position in the depth-first walk of its root's tree (children in stored order, values in stored order; the walk is `dfs` of probe p6) | `instanceExtension.getState env` |
| `default_instance` | `rank`: its position in `getDefaultInstances class` (most recent first) | `defaultInstanceExtension` |
| `instance_left_out` (new kind) | `keys`, `rank`, `priority` of an instance whose declaration the export does not have (FE1d leaves 31 such instances of `Init` out: private or unsafe declarations), so that the tree keeps its place | as `instance` |
| `class` (new kind) | `name`, `out_params`, `out_level_params` | `classExtension` (Class.lean:14): the class set and out-parameter positions |
| `tag` (new kind) | `name`, `tag`: `elab_as_elim`, `elab_without_expected_type`, `cases_on`, `rec_on`, `brec_on` | the tag attributes and the auxiliary-recursor tags (if plan row FE1d2 lands first with the auxiliary recursors, its records are used instead) |

A key is a JSON value: `"star"`, `"other"`, `"arrow"`, `{"const":NAME,"arity":N}`,
`{"fvar":…}` (never in global instances: refused), `{"lit":N}` or
`{"lit_str":S}`, `{"proj":NAME,"idx":I,"arity":N}`. The reader (FE1d's,
extended) checks forms, that every name is a declaration of the right
kind, that no two instances of a root key share a rank (ranks may have
gaps where the exporter leaves an instance out, as FE1d does for
instances that are not declarations of the export), that each
default instance's rank is unique per class, and that the header counts
the new kinds; version 1 files are refused as "another format version"
(unsupported) once version 2 exists. Ranks and the class set are taken on
trust from pinned Lean, like priorities (ELABORATION_DATA.md, "Trust");
the keys, the class of each instance and the out-parameter positions are
checked (§4).

### 3.2 The instance table and `getUnify`

At first use, the instances of each root key (the `instance_left_out`
records among them, marked) are inserted, in rank
order, into a tree (a trie): a node holds its values and its children
(key, node) in insertion order, which, inserted in rank order, is Lean's
child order. Inserting in rank order makes every child list Lean's
stored order without Lean's name hash. (LeanForth's own `instance`
declarations, FE3, need `Key.lt` and therefore Lean's `Name.hash`:
FE3's work.)

`getUnify` (DiscrTree/Main.lean:567) is ported as written, with an
explicit stack of (node, remaining subterms) pairs whose subterm lists
are shared cons lists (`lib/cons.fs`): at the root the query's key is
`getUnifyKeyArgs e root` (Main.lean:350); a star root key (the goal is a
bare metavariable) folds over the root map in hash order: unsupported
(never reached by instance problems, whose goal is a class
application). Below the root, for each remaining subterm the key is
computed only when the node has children (as Lean, so `isDefEqStuck`
is thrown exactly when Lean throws it): a star query key visits every
child with its arity skipped; any other key visits the star child first,
then the child with the same key. Values are appended when no subterm is
left.

Query keys (`getKeyArgs`, Main.lean:350) at reducible transparency:
`reduceDT` (whnfCore, `unfoldDefinition?`, strict eta; at the root, stop
before a bad key), a numeral below the root is a literal key
(`toNatLit?`), a constant gives `const c n` but throws `isDefEqStuck` when
the term has metavariables and `c` is reducible, a matcher with a
metavariable in a discriminant, or a recursor (the matcher test needs
matcher data: unsupported until FE1d2); a metavariable is a star (with
`isDefEqStuckEx`, always the case in instance search); a free variable,
projection, arrow or anything else as Lean.

### 3.3 `getInstances`

SynthInstance.lean:202: `forallTelescopeReducing` the goal; `isClass?`
of the body (`Meta/Basic.lean:1392-1577`, needing the class set of
§3.1); `getUnify`; stable insertion sort by priority, ascending; erased
instances do not occur (the exporter leaves them out); the "private
instance while exporting" filter does not apply (LeanForth texts are not
Lean modules); each instance's universe parameters replaced by fresh
level metavariables; local instances: unsupported (§2.7). The
instances are then tried from the last to the first.

### 3.4 `synthInstance`: tabled resolution as Lean does it

Port of SynthInstance.lean, in Lean's order:

- `synthInstanceCore?` (962): configuration `isDefEqStuckEx`, transparency
  `instances`, `foApprox`, `ctxApprox`, no `constApprox`, no `univApprox`
  (FE1c's unifier must take these flags); instantiate the goal;
  `preprocess` (741): `forallTelescopeReducing`, `whnf` of the body, the
  kind (no metavariables; metavariables without out-parameters;
  metavariables with out-parameters) and the cache key (out-parameter
  arguments and out-level parameters replaced by wildcards).
- The cache (`Meta.Cache.synthInstance`): key (local instances, cache
  key type, `synthPendingDepth`); a hit goes through
  `applyCachedAbstractResult?` (932), a miss through the search and
  `cacheResult` (947), which stores the result in the two forms Lean
  stores. The cache lives as long as the declaration's metavariable
  context (`lf-mctx-reset` empties it).
- The search runs inside `withNewMCtxDepth (allowLevelAssignments :=
  true)` (Meta/Basic.lean:2008): the depth goes up by one, level
  metavariables of the outer depth stay assignable (FE1c review, I1:
  `levelAssignDepth`), and **every assignment made inside is undone at the
  end** (Lean restores the saved metavariable context): the answer leaves
  the search abstracted.
- `preprocessOutParam` (779) for both kinds that need it: the
  out-parameter arguments become fresh metavariables of their binder
  types and the out-level parameters fresh level metavariables.
- `main` (679): a fresh metavariable of the goal, its table key
  (`mkTableKey`, 160: assignable metavariables become `_tc.i` free
  variables, level metavariables of the current depth `_tc.i` level
  parameters, numbered in order of a left-to-right walk), `newSubgoal`
  with the root waiter, then `synth` (671) runs `step` (656) until the
  root has an answer or both stacks are empty:
  - the resume stack first: `resume` (639): take the top (consumer,
    answer), `tryAnswer` (428) in the consumer's snapshot, and on success
    `consume` the rest of its subgoals with size `cNode.size +
    answer.size`;
  - else `generate` (594) on the top generator: no instance left, pop
    it; with `canonInstances` (on by default) and a goal type without
    metavariables that already has an answer without metavariables, pop
    it; else try the instance at `currInstanceIdx - 1` with `tryResolve`
    (346): `forallTelescopeReducing` the goal, `getSubgoals` (317: a
    metavariable for each binder of the instance's type, `whnf` of the
    type when the binders run out, the subgoals in the instance's
    `synth_order`, each marked *instance-typed* (line 358), which changes
    how the unifier assigns them: `checkTypesAndAssign`,
    ExprDefEq.lean:640), `isDefEq goalBody instanceBody`, then the value
    `mkLambdaFVars xs instVal (etaReduce := true)` assigned directly when
    the goal has no metavariables, else by `isDefEq mvar instVal`; on
    success `consume` (538) with size 0.
  - `consume`: drop subgoals already assigned; none left: `addAnswer`
    (469: refused when `size ≥ maxResultSize`; `mkAnswer` instantiates
    and abstracts; a new answer, by `resultType` inequality, is stored
    and wakes the waiters: the root takes an answer without
    metavariables as the result, a consumer goes on the resume stack);
    else the first subgoal's table key: a known key adds the consumer as
    a waiter and queues all its answers; an unknown one first tries
    `removeUnusedArguments?` (516; a goal type with an unused Π binder:
    unsupported in FE1e, with the Π-typed goals of §2.7), then
    `newSubgoal`.
- After the search: `applyAbstractResult?` (881): open the answer,
  `assignOutParams` (829: `isDefEq type (inferType result)` at default
  transparency, assigning the out-parameters of the original goal),
  instantiate, then `check` only when `checkMayHaveSideEffects`
  (unsupported, §2.7).
- `trySynthInstance` (1018) maps the stuck signal to *undef*;
  `synthesizeInstMVarCore` (TermElabM.lean:1232) then returns false (try
  later), an answer is assigned (or, when the metavariable was assigned
  meanwhile, compared with `isDefEq`), no answer is the error "failed to
  synthesize" (a front-end error, outcome invalid, never accepted).
- `synthPendingImp` (1037), Lean's hook from `isDefEq` into instance
  search for class-typed metavariables, with `maxSynthPendingDepth`
  (default 1): FE1e provides it to FE1c's unifier as a deferred word;
  until then FE1c answers unsupported where Lean would call it.

**The stuck signal.** Lean throws `isDefEqStuck` when, with
`isDefEqStuckEx`, a unification needs to assign a read-only metavariable
(FE1c review, I2), and `getKeyArgs` throws it too. LeanForth has no
exceptions in these walks: FE1c's `isDefEq` and FE1e's key computation
return a distinct internal code, `lf-meta-stuck`, beside the ADR 0008
outcomes; it is never stored or printed, `outcome-sane` turns it into
invalid if it ever escapes the Meta layer, and only `trySynthInstance`,
`isDefEqGuarded` (false) and `synthPendingImp` (false) consume it, as
Lean's catches do.

### 3.5 Metavariable snapshots

Lean's generator and consumer nodes each keep a `MetavarContext` and
switch between them (`withMCtx`); Lean's context is a persistent value,
LeanForth's (`src/front/mvars.fs`) a mutable store. FE1e adds to mvars.fs
an **assignment trail**: every assignment (expression or level) during a
search is a trail record (metavariable, value, previous record); a
snapshot is a trail record. Switching to a snapshot undoes assignments
back to the common ancestor and redoes the target's records; the
metavariables made in another branch stay declared but unassigned, as
nothing in the target refers to them. `withNewMCtxDepth`'s restore is a
switch to the entry snapshot plus resetting the depth and the stores'
counts of metavariable declarations (the scratch marks of
`core/scratch-marks.fs`); terms built inside stay in the term store (the
answer is among them). Words: `lf-mctx-snapshot ( -- snap )`,
`lf-mctx-switch ( snap -- outcome )`, `lf-mctx-deeper-levels ( -- )`
(Lean's `incDepth allowLevelAssignments`). FE1c's caches must hold only
pairs without metavariables, as Lean's do, so that no cached answer
depends on a snapshot.

### 3.6 Why not a simpler order

A depth-first search over the candidates (try the best instance, solve
its subgoals in order, backtrack) gives the same first answer as tabled
resolution only when no subgoal is shared or repeated. It differs from
Lean when a subgoal's table already has answers (they are queued in table
order, not found again in instance order), when goals repeat in a cycle
(tabling terminates, depth-first search does not), when `canonInstances`
skips a generator, when an answer equal by `resultType` is dropped, and
when `maxResultSize` cuts an answer. Each can change which instance is
returned, hence the term, so FE1e ports tabled resolution and nothing
simpler. It is tested by a table of instance problems compared with
pinned Lean's `#synth` (`pp.all`), including failures and stuck goals
(§6.1), and by the term comparisons.

### 3.7 Limits, fuel and outcomes

| Lean limit | FE1e |
| --- | --- |
| `synthInstance.maxSize` (128, SynthInstance.lean:25): answers of size ≥ 128 dropped | ported exactly: part of the algorithm |
| `maxSynthPendingDepth` (1) | ported exactly |
| `synthInstance.maxHeartbeats` (20,000 × 1,000 small allocations) | cannot be reproduced (it counts Lean's memory allocations); LeanForth's fuel: one unit per `step` and the unifier's own fuel; out of fuel is *exhausted*, never "failed to synthesize" (owner question 1) |
| `maxRecDepth` (512) in elaboration | not reproduced: elaboration runs on heap stacks without a depth limit (owner question 1) |
| store sizes | *full* (ADR 0008), never an answer |

## 4. The instance-class check (fe1d review, M1)

Lean takes an instance's class from its type when the instance is added
(`addInstance`, Instances.lean:283: `checkNonClassInstance`, line 270,
then `mkInstanceKey`, line 104), and a default instance's class the same
way (`addDefaultInstance`, line 406). FE1e repeats both before it uses
the data:

1. For each `instance` record (declaration `d`, class `C`, keys `K`):
   `forallTelescopeReducing` of `d`'s type at **default** transparency
   (a Π is entered with a fresh local; any other type is put in whnf, and
   entered if it became a Π: so `DecidableEq Nat` unfolds to
   `(a b : Nat) → Decidable (a = b)`); `isClass?` of the conclusion
   (`isClassQuick?`, then `isClassExpensive?` at reducible transparency,
   Meta/Basic.lean:1392-1577) must be `C`; else refused: "instance `d`
   is recorded as an instance of `C` but its type is not" (invalid).
2. Its keys: `forallMetaTelescopeReducing` (metavariables at a new depth),
   then `DiscrTree.mkPath` (Main.lean:329, reducible: `reduceDT`,
   `pushArgs` with `ignoreArg`: instance-implicit arguments, implicit
   arguments that are not types, and proofs become stars; literals,
   offsets, projections and arrows as Lean) must equal `K`; else refused:
   "instance `d`'s keys differ from its type's" (invalid).
3. For each `default_instance` record (class `C`, instance `d`): the head
   of `d`'s type's conclusion (`forallTelescopeReducing`) must be the
   constant `C`, and `C` a class.
4. For each `class` record: the out-parameter positions recomputed from
   the class's type (`checkOutParam`, Class.lean:106; `computeOutLevelParams`,
   line 140) must equal the record's.

When: the first instance problem or default-instance query of a run
runs steps 1, 3 and 4 over every record (the class of an instance
decides in which class's candidates it appears, so all must be known
before any search), and step 2 for all instances of a root key when that
root is first queried. Not in the reader: the reader (FE1d) is loaded
below the Meta words it would need. A check that FE1c's whnf cannot
finish marks the instance *unverified*; a query whose root has an
unverified instance, or any instance problem while an instance's class
is unverified, answers unsupported. `make reference-elab-data` reports
the number of unverified instances in `Init` (target 0). Outcomes:
invalid for a mismatch (with the record's line), unsupported as above,
exhausted and full as always.

Tests: each of the following data files, made from the slice's good data,
is refused at first use with its code and line: `instAddNat` recorded as
an instance of `Mul`; `instOfNatNat`'s keys changed to `[OfNat, Nat, 0]`
(a literal where Lean has a star);
a default instance recorded under the wrong class; a class with a wrong
`out_params`; a non-class declaration as an instance (`Nat.add`, kind
check passes, class check refuses). Passing: an instance whose class
appears only after reducible unfolding (`instDecidableEqNat`, through
`DecidableEq`). The slice's good data passes with 0 unverified; all of
`Init`'s instances recomputed equal the exported keys (`make
reference-elab-data`, about 3,000 instances).

## 5. Modules, data structures and words

### 5.1 Files (all `src/front/`, untrusted, each with its tests in `tests/front/`)

| File | Contents | Uses |
| --- | --- | --- |
| `elab-data.fs` (FE1d, extended) | format 2: keys, ranks, classes, tags | lib/json.fs |
| `discr-keys.fs` | DiscrTree keys: `mkPath` (instances) and `getUnifyKeyArgs` (queries), `reduceDT`, `toNatLit?`, offsets, `ignoreArg` with the binder infos of `getFunInfoNArgs` | FE1c whnf, inferType |
| `instances.fs` | class set and out-parameters; the per-root tries; `getUnify`; `getInstances`; default instances and their priorities; the class check (§4) | elab-data, discr-keys |
| `synth.fs` | `synthInstance`: preprocess, cache, tabled resolution, answers, out-parameters; `trySynthInstance`; `synthPending` | instances, FE1c isDefEq, mvars trail |
| `elab-pending.fs` | the pending list, `synthesizeSyntheticMVars`, default instances, `withSynthesize`/`withSynthesizeLight`, `mkInstMVar`, `synthesizeInstMVarCore` | synth |
| `elab-app.fs` | `elabAppArgs` (§2.2), `elabAtom`, `elabApp` | elab-pending |
| `elab-term.fs` | `elabTerm` dispatch, `elabNumLit`, `ensureHasType`, `elabType`, `elabTermEnsuringType`, `binop%`/`binrel%` (§2.4), `#check`, the trace switch | elab-app |

`mvars.fs` gains the trail of §3.5 and `levelAssignDepth`.

### 5.2 Public words

Outcomes are ADR 0008's; a failed word gives -1 for its result.
`expected` is a term or -1 (none).

| Word | Stack effect | Lean |
| --- | --- | --- |
| `lf-elab-term` | `( node expected -- term outcome )` | `elabTerm` |
| `lf-elab-term-ensuring` | `( node expected -- term outcome )` | `elabTermEnsuringType` |
| `lf-elab-type` | `( node -- type outcome )` | `elabType` |
| `lf-elab-ensure-type` | `( term expected -- term' outcome )` | `ensureHasType` |
| `lf-elab-synthesize` | `( mode -- outcome )`, mode `lf-postpone-yes`, `-partial`, `-no` | `synthesizeSyntheticMVars` |
| `lf-elab-light{` `}lf-elab-light` | `( -- saved )` `( saved outcome -- outcome )` | `withSynthesizeLight` (also `lf-elab-synth{`… for `withSynthesize`) |
| `lf-elab-check` | `( node -- term type outcome )` | `#check` |
| `lf-elab-error` | `( -- code pos )` | the last error, for the reader's report |
| `lf-elab-trace!` | `( flag -- )` | the test trace of §1.6 |
| `lf-elab-reset` | `( -- )` | with `lf-mctx-reset` |
| `lf-synth-instance` | `( type -- inst flag outcome )`, flag true found, false none; outcome `lf-meta-stuck` only inside the Meta layer | `synthInstance?` |
| `lf-try-synth` | `( type -- inst code outcome )`, code some, none or undef | `trySynthInstance` |
| `lf-inst-candidates` | `( type -- addr n outcome )` | `getInstances` |
| `lf-inst-ready` | `( -- outcome )` | the class check of §4 |
| `lf-class?` | `( term -- class true outcome \| false outcome )` | `isClass?` |
| `lf-class-out-params` | `( class -- addr n )` | `getOutParamPositions?` |
| `lf-default-instances` | `( class -- addr n )` cells of (instance, priority) | `getDefaultInstances` |
| `lf-dt-path` | `( type -- keys outcome )`, `keys` a key list of the key store | `mkPath` |
| `lf-dt-unify-key` | `( term root? -- key args outcome )`, `key` a key of the key store, `args` a cons list of subterms (`lib/cons.fs`) | `getUnifyKeyArgs` |
| `lf-mctx-snapshot`, `lf-mctx-switch` | `( -- snap )`, `( snap -- outcome )` | `withMCtx` |

FE1f's deferred `lf-front-elaborate ( -- type value )` is set to a word
built on `lf-elab-type` and `lf-elab-term-ensuring`.

### 5.3 State, stacks, fuel, errors

- State (ADR 0009, members of the checker context): `ec` (the
  elaborator: frames record, pending list store, trace flag, error), `ea`
  (the store of `elabAppArgs` activation records), `it` (instance tables:
  tries in a slab, the class set in a hash table, `lib/htab.fs`), `sy`
  (synthesis: generator and resume stacks, the table from key terms to
  entries, answers, the cache). Everything grows in the heap
  (`lib/store.fs`, `lib/slab.fs`); a store that cannot grow is *full*.
- No host recursion: elaboration runs as `lib/frame.fs` steps (an
  argument's elaboration is a child visit); `toTree`, `analyze`,
  `applyCoe` and `toExprCore` are walks over the tree on frames;
  `getUnify` and the key computation use heap stacks; `synth` is a loop.
- Fuel: one unit per elaboration visit and per synthesis step, plus
  FE1c's; `--fuel` sets it; out of fuel is *exhausted*.
- Error codes: the authoring catalogue (`src/author/errors.fs`), the next
  free numbers after FE1f's (74), for instance "failed to synthesize"
  (invalid), "typeclass problem is stuck" (invalid), "type mismatch"
  (invalid), "numerals are data, the expected type is a proposition"
  (invalid), "instance's class or keys differ from its type"
  (invalid), and one per unsupported condition of §2.7 (exit 2), each
  naming the plan row that lifts it.

## 6. Tests

### 6.1 Comparisons with pinned Lean

`tests/front/check_elab.py` (in `make check`, beside `check_meta.py`):
each case is written as LeanForth natural text with `#check` and as
Lean (`variable (n m k a b : Nat) (h : a = b) (i : Int)`, `set_option
pp.all true`, `#check …`); LeanForth's term, printed in kernel form, must
equal Lean's node for node (universe arguments included); a harness
self-test refuses a known-wrong row. Expected terms are pinned Lean's
output of probe p3 (abbreviated: `OfNat k` is `@OfNat.ofNat.{0} Nat
(nat_lit k) (instOfNatNat (nat_lit k))`, `+` is `@HAdd.hAdd.{0,0,0} Nat
Nat Nat (@instHAdd.{0} Nat instAddNat)`):

| Case | Lean | Expected (pinned Lean) |
| --- | --- | --- |
| C1 | `0 + n = n` | `@Eq.{1} Nat (+ (OfNat 0) n) n` |
| C2 | `n + 0 = n` | `@Eq.{1} Nat (+ n (OfNat 0)) n` |
| C3 | `1 + n` | `+ (OfNat 1) n : Nat` |
| C4 | `n * m` | `@HMul.hMul.{0,0,0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n m` |
| C5 | `n ≤ m` | `@LE.le.{0} Nat instLENat n m` |
| C6 | `n < m` | `@LT.lt.{0} Nat instLTNat n m` |
| C7 | `n = n` | `@Eq.{1} Nat n n` |
| C8-C10 | `0`, `1`, `2` | `OfNat k : Nat` (default instance `instOfNatNat`, priority 100) |
| C11 | `4294967296` | `OfNat 4294967296` (above 2^32) |
| C12 | `123456789012345678901234567890` | its `OfNat` (big number) |
| C13 | `n + m + k = n + (m + k)` | nested `+`, left associated on the left |
| C14 | `n + 1 = Nat.succ n` | `@Eq.{1} Nat (+ n (OfNat 1)) (Nat.succ n)` |
| C15 | `Nat.succ n = n + 1` | the mirror |
| C16 | `2 + 2 = 4` | `@Eq.{1} Nat (+ (OfNat 2) (OfNat 2)) (OfNat 4)` (default instances: `instHAdd` first at priority 1000, rolled back while `Add ?α` is stuck, then `instOfNatNat` at 100, then `instHAdd` again) |
| C17 | `0 + 0 = 0` | as C16 |
| C18 | `0 + n * m` | `+ (OfNat 0) (HMul … n m)` |
| C19 | `Nat.add 0 n = n` | `@Eq.{1} Nat (Nat.add (OfNat 0) n) n` |
| C20 | `Nat.le_refl n` | `Nat.le_refl n : @LE.le.{0} Nat instLENat n n` |
| C21 | `Nat.succ_le_succ (Nat.le_refl n)` | `@Nat.succ_le_succ n n (Nat.le_refl n)` (implicits from the argument) |
| C22 | `congrArg Nat.succ h` | `@congrArg.{1,1} Nat Nat a b Nat.succ h` |
| C23 | `Eq.symm h` (the `a = b → b = a` case) | `@Eq.symm.{1} Nat a b h : @Eq.{1} Nat b a` |
| C24 | `2 * n + 1 ≤ n * n` | `@LE.le.{0} Nat instLENat (+ (HMul (OfNat 2) n) (OfNat 1)) (HMul n n)` |
| C25 | expected type given: `0` against `Nat`; `n Eq.refl` against `n + 0 = n`; `congrArg Nat.succ ih` against FE1's `succ` goal | `OfNat 0`; `@Eq.refl.{1} Nat n`; §1.4's term (a Forth test calls `lf-elab-term-ensuring`; the ascription word `(e : T)` is FE2's) |
| C26 | `n + i` (`i : Int`) | Lean coerces `n` (`@Nat.cast.{0} Int instNatCastInt n`): **unsupported** (exit 2, coercion, FE4), never another term |

The instance table: `tests/front/check_synth.py` compares
`lf-synth-instance` with pinned Lean's `#synth` (`pp.all`) on about 40
goals over `Init`: `Add Nat`, `HAdd Nat Nat ?`, `OfNat Nat 5`, `OfNat Nat
0` (where `Zero.toOfNat0` and `Lean.Grind.Semiring.ofNat` also match),
`LE Nat`, `LT Nat`, `Mul Nat`, `HMul Nat Nat ?`, `HPow Nat Nat ?`,
`Decidable (n = m)`, `DecidableEq Nat`, `Inhabited Nat`, `BEq Nat`, …;
failures (`Add Prop`, `OfNat Bool 0`: none), stuck goals (`OfNat ?α 0`,
`HAdd ?α ?β ?γ`), and goals where the tree order and the priority order
differ (probe p8 over `Init`: in `HPow`'s tree `instHPow` (1000) comes
before `Lean.Grind.Semiring.npow` and `Lean.Grind.Field.zpow` (100), so
`HPow Nat Nat Nat` is answered `@instHPow.{0, 0} Nat Nat (@instPowNat.{0}
Nat instNatPowNat)` only because of the priority sort: without it,
`Lean.Grind.Semiring.npow` is tried first and succeeds, since `Init` has
`Lean.Grind.Semiring Nat` (probe p9); in `Add`, `Mul`, `Sub`, `LE`, `LT` and `OfNat` a `Lean.Grind`
instance of priority 10000 sits in the middle of the tree). Pinned Lean's
answers seen so far (p8): `Decidable (2 = 3)`: `instDecidableEqNat 2 3`;
`DecidableEq Nat`: `instDecidableEqNat`; `Inhabited Nat`:
`instInhabitedNat`; `BEq Nat`: `instBEqOfDecidableEq`; `LE Nat`:
`instLENat`. The FE1 statement's trace (§1.6) and C1's term are
FE1e's acceptance; with FE1f, `0 n + n = #check` printing `0 + n = n :
Prop` is the plan row's.

### 6.2 Coverage classes ([TEST_COVERAGE_REVIEW.md](../development/TEST_COVERAGE_REVIEW.md#owners-coverage-classes))

1. **Every outcome:** a term (C1-C25); a front-end error, each with
   its code: `0` against the proposition `a = b` ("numerals are data"),
   `0` against `Bool` ("failed to synthesize `OfNat Bool 0`"), a
   type-class problem still stuck when nothing may be postponed (a Forth
   test with the default instances left out of the data); each
   unsupported condition of §2.7 reached by one input (C26, a recursor
   applied, a Π-typed instance goal; note that a type mismatch is
   unsupported in FE1e, since Lean first looks for a coercion);
   exhausted (fuel 1 for C1); full (each store refused in turn with
   `tests/support/heap-watch.fs`); no failure ever gives a term.
2. **Malformed input:** the damaged elaboration data of §4 and format 2's
   new members (each refused with its code and line); syntax nodes that
   are not live; a stale metavariable.
3. **Interfaces:** the stack effect of every public word under
   `tests/support/checks.fs`' `run-case`; every error code in the
   catalogue test; `lf-meta-stuck` never leaving the Meta layer
   (`outcome-sane` test).
4. **Workflows and I/O:** `#check` lines in a `.lf` file through
   `bin/leanforth check --env tests/author/init-slice.ndjson --elab-data
   …` (the slice and its data extended with the instances the cases
   need); the trace switch's golden file.
5. **Resources:** a numeral of 10,000 digits; a sum of 10,000 terms
   (`0 n + n + … =`: frames, no host recursion); a goal whose search
   exhausts fuel; heap refusals for every store.
6. **State:** after a failed elaboration, the next declaration's terms
   are as in a fresh run (stores, pending list, cache, trail reset);
   snapshots switched back and forth leave the assignments of the
   target only (unit test of the trail); `commitWhen` rollback of a
   failed default instance (C16) leaves no assignment.
7. **Regression pins:** golden traces of C1, C16 and C22; the candidate
   order of `OfNat Nat 0` and `Add Nat`; fuel counts of C1.

### 6.3 Planted faults (`tests/mutants/faults.toml`, each caught)

`fe-instance-try-order` (candidates tried from the front: C1's
`OfNat Nat 0` answer changes), `fe-priority-unsorted` (no priority sort:
`HPow Nat Nat ?γ`'s answer changes; FE1d's `fe-priority-ignored`, a
priority read as 0, is then caught by the same case), `fe-rank-ignored`
(children in key order),
`fe-outparam-kept` (`γ` not replaced: `HAdd Nat Nat ?γ` stuck, C1
fails), `fe-stuck-as-failure` (stuck read as "no instance": C1 reports
"failed to synthesize"), `fe-no-default-instance` (C8 left with a hole),
`fe-default-prio-ascending` (C16's trace differs), `fe-implicit-not-inserted`,
`fe-no-propagation` (C25's `congrArg` term gets `0 + k`),
`fe-defeq-arg-order` (`isDefEq expected type` swapped where Lean's order
decides an assignment), `fe-class-check-skipped` and `fe-keys-unchecked`
(the damaged data accepted), `fe-trail-no-redo` (snapshot switch
without redo: the trail unit test), `fe-max-size-off-by-one` (a stub
table chain in a Forth unit test), `fe-cache-key-no-wildcard`
(problem 5 answered from problem 4's cache entry with `assignOutParams`
skipped: the trace differs).

## 7. Sub-steps

Each step ends with its focused tests, its faults and a logged Forth
review; sizes are the plan's S (under a day), M (days) and L.

| Step | What | Size | Needs |
| --- | --- | --- | --- |
| FE1e0 | **Asks of FE1c**, done there: `isDefEq` with the flags of §3.4 and the `lf-meta-stuck` code (review I2); `levelAssignDepth` and `incDepth allowLevelAssignments` (I1); a metavariable's assignment that also unifies the types (`checkTypesAndAssign`, ExprDefEq.lean:640: `?T := Nat` gives `w := 0`), with its instance-typed case; `decLevel` (DecLevel.lean:22); `whnf` with delta at each transparency, `whnfForall`, `unfoldDefinition?`, strict eta; `inferType`, `isType`, `isProof`, `check`; `instantiateForall`, `mkLambdaFVars (etaReduce)`; a deferred `synthPending`; caches only for terms without metavariables | (in FE1c) | — |
| FE1e1 | Elaboration data format 2: exporter writes keys, ranks, classes, tags and left-out instances; reader checks and serves them; `make reference-elab-data` compares | S-M | FE1d |
| FE1e2 | `discr-keys.fs`: `mkPath` and `getUnifyKeyArgs`; all of `Init`'s instance keys recomputed equal the exported ones | M | FE1e1, FE1e0 (whnf, inferType) |
| FE1e3 | `instances.fs`: class set, tries, `getUnify`, `getInstances`, default instances; the class check of §4 (closes fe1d M1) | M | FE1e2 |
| FE1e4 | Metavariable trail and snapshots in `mvars.fs` (§3.5) | S-M | FE1b |
| FE1e5 | `synth.fs`: tabled resolution, preprocess, cache, out-parameters, `trySynthInstance`, `synthPending`; `check_synth.py` | L | FE1e3, FE1e4, FE1e0 (isDefEq) |
| FE1e6 | `elab-pending.fs` and `elab-app.fs`: pending list, default instances, `elabAppArgs`, atoms, applications, numerals | M-L | FE1e5 |
| FE1e7 | `elab-term.fs`: dispatch, `binop%`/`binrel%`, `ensureHasType`, `elabType`, `#check` word, trace switch; `check_elab.py`; FE1f's `lf-front-elaborate` | M | FE1e6 |
| FE1e8 | Tests of §6 completed, faults, the user page's section in three forms, Forth review | S-M | FE1e7 |

FE1e as a whole is **L** rather than the plan row's M: tabled resolution
with snapshots and the discrimination tree are each larger than the
plan row assumed. FE1e1-FE1e4 can start before FE1c's unifier lands
(FE1e1, FE1e4 at once; FE1e2 needs whnf and inferType); FE1e5 needs
`isDefEq`.

## 8. Questions for the owner

**Answered by the owner on 2026-11-12 (about 22:40): option (a), LeanForth's own fuel, differences listed in BEYOND_LEAN.md** ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md)).

1. **Lean's work limits.** Lean gives up on an elaboration after a fixed
   amount of work, counted in its own memory allocations (instance
   search: 20 million), or at nesting depth 512. LeanForth cannot count
   Lean's allocations, so it cannot stop at exactly the same point.
   Options: (a) LeanForth uses its own work limit (`--fuel`) and its own
   memory limits; where Lean would give up and LeanForth finishes, the
   statement is still checked by the kernel and the case is listed in
   [BEYOND_LEAN.md](../project/BEYOND_LEAN.md); (b) as (a), but also stop
   at nesting depth 512 as Lean does, approximately (Lean counts depth in
   many places, so "approximately" means some inputs still differ);
   (c) refuse anything near Lean's limits. *Recommendation: (a).* The
   limits are about time and memory, not meaning; no input FE1 to FE5
   plans comes near them; (b) would add a rule that still differs from
   Lean, and (c) would refuse things Lean accepts.

## 9. Sources and probes

Lean 4.35.0 sources read (pinned toolchain, `src/lean/Lean/`):
`Elab/App.lean` (75, 178-955, 1330-1400, 2206-2264), `Elab/Extra.lean`
(154-566), `Elab/BuiltinTerm.lean` (203-229), `Elab/SyntheticMVars.lean`
(79-222, 540-699), `Elab/Term/TermElabM.lean` (1232-1349, 1954-1984),
`Elab/BuiltinCommand.lean` (434-455), `Meta/SynthInstance.lean` (all),
`Meta/Instances.lean` (50-110, 265-441), `Meta/DiscrTree/Main.lean`
(53-433, 540-608), `Meta/DiscrTree/Basic.lean` (40-47, 135-175),
`Meta/DiscrTree/Types.lean`, `Meta/Basic.lean` (1374-1577, 2008-2035),
`Class.lean` (14-217), `Meta/AppBuilder.lean` (345).

Probes, run with the pinned binary (`.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`,
`ulimit -u 500`, `timeout -k 5 120`, `nice -n 10`), kept in
`.claude/work/D1E/probes/` of the main checkout:

- p1: `#check fun (n : Nat) => (0 + n = n)` with `pp.all` and the traces
  `Elab.step`, `Elab.binop`, `Elab.binrel`, `Elab.app`, `Elab.postpone`,
  `Elab.resume`, `Meta.synthInstance`, `Meta.synthPending` (§1.2-1.3).
- p2: FE1's theorem with `trace_state` and the `exact` step traced, and
  `theorem add_zero' (n : Nat) : n + 0 = n := Eq.refl n` (§1.4-1.5).
- p3: the comparison cases of §6.1, `pp.all`.
- p4, p5: `#check 2 + 2 = 4` with `Elab.defaultInstance` (§2.5, C16).
- p6: `import Lean`; the instance tree of `OfNat`, `HAdd`, `Add` walked
  depth first against `getUnify`, priorities, default instances,
  out-parameters (§3.1).
- p7: the theorem header (`Sort ?u`), `#check 0`, and `n + i`'s coercion.
- p8: for every root of the instance tree, pairs that the priority sort
  reorders (`Init`'s instances only); `#synth` of six goals; the errors
  of `0` against a proposition and against `Bool`.
- p9: `#synth Lean.Grind.Semiring Nat` and `#synth HPow Nat Nat Nat`
  (`pp.all`).
