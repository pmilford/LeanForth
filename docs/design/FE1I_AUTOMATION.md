# FE1i: LeanForth finds a proof by itself (`by-decide`, `by-omega`)

**Status (2026-11-12): designed.** Nothing here is built. This is the
design of plan row FE1i of [the plan](../project/PLAN_DRAFT.md), which
the owner brought forward on 2026-11-12 ("Yes bring forward the leanforth
finds a proof by itself";
[OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md), "Front-end syntax",
answer 5). It builds on [FRONT_END.md](FRONT_END.md) §4.7 and §8,
[ADR 0021](../adr/0021-front-end.md) (D5 Lean's behaviour, D6 the front
end's own reduction, D7 no `native_decide`),
[FE1E_APPLICATIONS.md](FE1E_APPLICATIONS.md) (elaboration and instance
search) and [FE1G_TACTICS.md](FE1G_TACTICS.md) (the goal list, tactic
words, §7 "Where FE1i plugs in"). Every Lean fact below was read in pinned
Lean 4.35.0's sources
(`.tools/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`) or
observed by running pinned Lean on 2026-11-12 (§2.7 gives the commands).

## 1. In plain words

So far every proof checked by LeanForth was written by someone: by Lean,
or by hand. FE1i adds the first two words with which LeanForth *finds* a
proof itself:

- **`by-decide`** proves a statement without variables by computing it:
  $2 + 2 = 4$ holds because $2 + 2$ computes to $4$. Lean's `decide`
  builds a tiny proof that says "evaluate the decision procedure for this
  statement; it says *true*", and the kernel does the evaluation again
  when it checks the proof.
- **`by-omega`** proves statements of linear arithmetic over natural
  numbers and integers, with variables: $0 + n = n$, $n + m = m + n$,
  "if $a < b$ then $a + 1 \le b$". Lean's `omega` assumes the opposite,
  turns every fact into linear inequalities, and derives a contradiction
  by eliminating variables (the *omega test*). The proof it builds lists
  the steps; the kernel checks each one.

The owner's rule (2026-11-12, question 7): `decide` is a core tactic, so
LeanForth's term must be *identical* to Lean's; `omega` is a search
tactic, so LeanForth must succeed *exactly where Lean succeeds* and fail
where Lean fails, with a kernel-checked term; identical terms are
measured, not required. Either way, nothing the tactic says is trusted:
only the kernel's check of the finished term counts.

Three findings shape the design:

1. **The kernel needs nothing new.** LeanForth's kernel already accepts
   pinned Lean's own proofs of all three target lines and of the nearby
   cases (§2.6: 1,484 declarations accepted, the same axioms reported).
   FE1i is front-end work only; no [kernel] gate.
2. **Lean's `omega` is deliberately incomplete.** It leaves out two parts
   of the omega test (the "dark" and "grey" shadows) and does not look
   inside definitions or reorder products. So it *fails* on true
   statements: Pugh's textbook example, $x y = y x$, `f n > n` for
   `def f n := n + 1`, a hypothesis `p → x < 3` with `p` (§2.5). A
   procedure of LeanForth's own that is "better" would prove these and
   break the owner's rule; matching Lean's failures means running Lean's
   algorithm. The recommendation (§5.4, question 1) is therefore a
   faithful port of Lean's `omega`, which also gives Lean's terms.
3. **`omega` proofs live in a helper theorem.** Lean puts the proof into a
   separate theorem (`a1._proof_1_1`) and proves the statement by
   contradiction with it; both are declarations of the export. The
   hand-over to the kernel (FE1f) must send both.

## 2. The target proofs, traced in pinned Lean

### 2.1 The three lines in three forms

| Mathematics | LeanForth (`tests/frontend/02-auto.lf`, proposed) | Lean |
| --- | --- | --- |
| for every natural number $n$, $0 + n = n$ | `theorem zero_add_auto  Nat explicit: n  0 n + n =  := by  by-omega  end zero_add_auto` | `theorem zero_add_auto (n : Nat) : 0 + n = n := by omega` |
| for all natural numbers $n, m$, $n + m = m + n$ | `theorem add_comm_auto  Nat explicit: n  Nat explicit: m  n m + m n + =  := by  by-omega  end add_comm_auto` | `theorem add_comm_auto (n m : Nat) : n + m = m + n := by omega` |
| $2 + 2 = 4$ | `theorem two_add_two  2 2 + 4 =  := by  by-decide  end two_add_two` | `theorem two_add_two : 2 + 2 = 4 := by decide` |

The plan row's short form `0 n + n = := by-omega` stands for the first
line: the statement after its binders, and a one-word tactic block in
FE1g's form (`:= by … end NAME`; question 2). Read aloud: "zero plus $n$
equals $n$, by linear arithmetic"; "two plus two equals four, by
computation".

Abbreviations below (all from `set_option pp.all true`): `0`, `2`, `4`
are `@OfNat.ofNat.{0} Nat (nat_lit k) (instOfNatNat (nat_lit k))`; `a + b`
is `@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b`;
`a = b` is `@Eq.{1} Nat a b`; on `Int`, `k` is `@OfNat.ofNat.{0} Int
(nat_lit k) (@instOfNat (nat_lit k))`.

### 2.2 `2 + 2 = 4` by `decide`

```text
@of_decide_eq_true (2 + 2 = 4) (instDecidableEqNat (2 + 2) 4)
  (@id.{0} (@Eq.{1} Bool (@Decidable.decide (2 + 2 = 4) (instDecidableEqNat (2 + 2) 4)) Bool.true)
    (@Eq.refl.{1} Bool Bool.true))
```

205 nodes as a tree, 48 distinct nodes, 14 constants, no axioms. The
shape is fixed by `Lean/Elab/Tactic/Decide.lean` (`doElab`, lines
101-111): the instance comes from `mkDecide`
(`Lean/Meta/AppBuilder.lean` 570: `Decidable.decide p` with the instance
synthesized), and the `id` is `mkExpectedPropHint` around Lean's constant
`reflBoolTrue` (`Lean/Expr.lean` 2408). Instance search for
`Decidable (2 + 2 = 4)` has one candidate in Init, `instDecidableEqNat`
(observed with `trace.Meta.synthInstance`).

### 2.3 `0 + n = n` and `n + m = m + n` by `omega`

The theorem itself (`#print a1`):

```text
fun (n : Nat) =>
  @Decidable.byContradiction (0 + n = n) (instDecidableEqNat (0 + n) n)
    fun (a : Not (0 + n = n)) => a1._proof_1_1 n a
```

and the helper theorem `a1._proof_1_1 : ∀ (n : Nat), ¬(0 + n = n) → False`
(`mkAuxTheorem`, `Lean/Meta/Closure.lean` 457; the comment in
`Omega/Frontend.lean` 694: "Omega proofs are typically rather large, so
hide them in a separate definition"), whose value starts

```text
fun (n : Nat) (a : ¬(0 + n = n)) =>
  @Or.elim (0 + n < n) (0 + n > n) False (@Nat.lt_or_gt_of_ne (0 + n) n a)
    (fun (h₁ : 0 + n < n) =>
      @Lean.Omega.Constraint.not_sat'_of_isImpossible
        (Lean.Omega.Constraint.mk (@Option.some.{0} Int 1) (@Option.some.{0} Int 0))
        (@of_decide_eq_true (… Constraint.isImpossible … = Bool.true) (instDecidableEqBool …) (@id.{0} … (@Eq.refl.{1} Bool Bool.true)))
        … (Lean.Omega.Coeffs.ofList [↑n]) …)
    (fun (h₂ : 0 + n > n) => …)
```

What happened (`set_option trace.omega true`): `omega` first tried
`assumption`; `falseOrByContra` applied `Decidable.byContradiction`
(instance `instDecidableEqNat`) and introduced `a : ¬(0 + n = n)`; the
fact `¬(x = y)` on `Nat` became `x < y ∨ x > y` (`Nat.lt_or_gt_of_ne`);
with no contradiction yet, the disjunction was split (`Or.elim`); in each
branch the fact was cast to `Int` (`Int.ofNat_lt_of_lt`), the sides turned
into linear combinations of the atom `↑n` (`Int.natCast_add`,
`LinearCombo.coordinate_eval_0`, …), and the constraint, normalized
("tidy"), became "0 lies between 1 and 0" (`Constraint.mk (some 1) (some
0)`, an empty interval); the proof of `False` is
`Constraint.not_sat'_of_isImpossible` with a `decide` proof that this
constraint is impossible. The kernel evaluates `Constraint.isImpossible`
on that literal constraint.

Sizes and constants (`#size`, §2.7):

| Declaration | Tree nodes | Distinct nodes | Constants | Axioms (`#print axioms`) |
| --- | --- | --- | --- | --- |
| `a1` (`0 + n = n`) | 105 | 39 | 11 | `propext`, `Quot.sound` |
| `a1._proof_1_1` | 6,363 | 375 | 60 | `propext`, `Quot.sound` |
| `a2` (`n + m = m + n`) | 133 | 37 | 9 | `propext`, `Quot.sound` |
| `a2._proof_1_1` | 10,557 | 518 | 61 | `propext`, `Quot.sound` |
| `a3` (`2 + 2 = 4`, `decide`) | 205 | 48 | 14 | none |

The axioms come from Init's lemmas that the proof uses (for instance
`Int.natCast_add`), not from `omega`; both are on the allowlist and are
reported, as for any accepted theorem.

### 2.4 Nearby cases

| Lean | Outcome | Term (shape) | Tree / distinct / constants |
| --- | --- | --- | --- |
| `10 < 20 := by decide` | proved | `of_decide_eq_true` with `Nat.decLt 10 20` (candidates tried: `Nat.decLt`, after `@instDecidableRelLt`, `@Std.instDecidableLT` in Lean's order, the last listed tried first) | 113 / 40 / 13 |
| `∀ x < 5, x*x < 30 := by decide` | proved | instance `@Nat.decidableBallLT 5 (fun x a => x*x < 30) fun n h => (fun n => Nat.decLt (n*n) 30) n` (an unreduced β-redex from instance search, kept by Lean) | 365 / 69 / 17 |
| `123456789 * 987654321 = 121932631112635269 := by decide` | proved | as `2 + 2 = 4` with `*` | 205 / 52 / 14 |
| `(3 : Int) - 5 < 0 := by decide` | proved | `Int.decLt` | — |
| `¬ (7 = 8) ∧ 2 ≤ 2 := by decide` | proved | instances for `And`, `Not`, `Nat.decLe` | — |
| `(a b : Nat) (h : a < b) : a + 1 ≤ b := by omega` | proved | `Decidable.byContradiction … (Nat.decLe (a + 1) b) fun a_1 => o1._proof_1_1 a b h a_1` | main 125 / 53 / 14; helper 6,115 / 409 / 61 |
| `(a b : Nat) : a - b ≤ a := by omega` | proved | helper uses `Lean.Omega.Int.ofNat_sub_dichotomy` (the case split on truncated subtraction) | helper 12,765 / 503 / 70 |
| `(x : Nat) : x / 2 ≤ x := by omega` | proved | helper uses `Int.mul_ediv_self_le`, `Int.lt_mul_ediv_self_add` (the new variable for `x / 2`) | helper 17,159 / 622 / 82 |
| `(x : Nat) (h : x < 3) : x < 3 := by omega` | proved | `fun x h => h`: the `assumption` step, no `omega` proof at all | — |
| `(q : Prop) (x : Nat) (h : x < 0) : q := by omega` | proved | no `Decidable q` instance, so `Classical.byContradiction`: axioms `propext`, `Classical.choice`, `Quot.sound` | — |
| `2 ^ 300 > 0 := by decide` | proved, with Lean's warning that the exponent exceeds the threshold 256 | `Nat.pow` unfolded instead of folded | — |
| `(a : Int) : a + 1 > a := by omega` | proved | instance `Int.decLt a (a + 1)` (`>` unfolded) | helper 1,829 / 243 / 51 |
| `(x y : Nat) (h1 : 2*x + 3*y = 7) : x ≤ 3 := by omega` | proved | a hard equality: `Lean.Omega.bmod_div_term`, `bmod_sat` | helper 51,123 / 749 / 82 |
| `x % 2 < 2`, `x - 5 + 5 ≥ x`, `(x : Int) / 2 * 2 ≤ x`, `x % 3 = 1 → x ≠ 6`, `x = y → y = x`, `n.succ > n`, `min a b = 3 → a ≥ 3`, `2 ∣ x → x % 2 = 0`, `x.natAbs ≥ 0`, `(↑x : Int) ≥ 0`, `x < 0 → 5 = 7`, `x + y = 10 → x - y = 4 → x = 7`, `2 * x ≠ 7`, `3 * x = 2 * x + 1 → x = 1`, `x ≤ 2^3 → x ≤ 8`, `x * x ≥ 0`, `x ^ 2 ≥ 0` (all `omega`) | proved | — | — |

Two of these matter for the design: tree sizes reach 51,000 nodes while
the distinct nodes stay under 750 (LeanForth's hash-consed term store
keeps the distinct ones); and the helper's constants are Init's
`Lean.Omega.*` lemmas and functions, which every export of Init contains.

### 2.5 Wrong and unprovable statements: Lean's errors

Lean's first message for each (LeanForth stops at the first error, ADR
0021 D3, so only the first is compared):

| Lean | First error |
| --- | --- |
| `2 + 2 = 5 := by decide` | ``Tactic `decide` proved that the proposition`` / `2 + 2 = 5` / `is false` |
| `(n : Nat) : n + 1 = n := by decide` | `Expected type must not contain free variables` / `n + 1 = n` / ``Hint: Use the `+revert` option to automatically clean up and revert free variables`` |
| `(n : Nat) : n + 0 = n := by decide` | the same (true, but `decide` refuses variables) |
| `∀ x < 5, x*x < 10 := by decide` | ``Tactic `decide` proved that the proposition`` / `∀ (x : Nat), x < 5 → x * x < 10` / `is false` |
| `∀ x : Nat, x = x := by decide` | `failed to synthesize` / `Decidable (∀ (x : Nat), x = x)` |
| `open Classical in (fun x : Nat => x) = id := by decide` | ``Tactic `decide` failed to reduce`` / `@decide ((fun x => x) = id) (propDecidable ((fun x => x) = id))` / ``to `true` or `false`.`` / ``After unfolding the instance `propDecidable`, reduction got stuck at`` / `choice ⋯` / a hint about classical instances |
| `(h : 1 = 1) : 2 = 2 := by decide` | accepted (only the statement must be closed, not the context) |
| `(n : Nat) : n + 1 = n := by omega` | `omega could not prove the goal:` / `a possible counterexample may satisfy the constraints` / `a ≥ 0` / `where` / ` a := ↑n` |
| `(a b : Nat) : a - b = a := by omega` | the same kind, constraints `d ≥ 1`, `c ≥ 0`, `c ≥ 0`, `c + d ≥ 0` with `c := ↑(a - b)`, `d := ↑b` |
| `2 + 2 = 5 := by omega` | `omega could not prove the goal:` / ``No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.`` |
| **true, but Lean's `omega` fails:** `(x y : Nat) : x * y = y * x` | counterexample with atoms `↑y * ↑x` and `↑x * ↑y` (products are atoms, not reordered) |
| **true, but fails:** Pugh's example `27 ≤ 11x + 13y ≤ 45`, `-10 ≤ 7x - 9y ≤ 4` (integers) `⊢ False` | counterexample `-10 ≤ 7*a - 9*b ≤ 4`, `27 ≤ 11*a + 13*b ≤ 45` (it has real but no integer solutions; finding that needs the dark shadow, which Lean leaves out) |
| **true, but fails:** `(p : Prop) (x : Nat) (h : p → x < 3) (hp : p) : x < 3` | counterexample `a ≥ 3` (the implication becomes `¬p ∨ x < 3` with a classical instance; in the `¬p` branch `hp` is not arithmetic) |
| **true, but fails:** `def f (n : Nat) := n + 1`; `f n > n` | counterexample with atom `↑(f n)` (definitions are not unfolded) |
| `(x y : Nat) (h : x ≤ y ∨ y < x) : True := by omega` | counterexample (the goal `True` is not arithmetic) |

The bold rows are the reason for §5.4's recommendation: each is a place
where "the same outcome" means LeanForth must also fail.

### 2.6 What the kernel needs, and LeanForth's kernel today

Checking these terms needs, in the kernel: `Nat` literals with the
GMP-style operations (`Nat.add`, `Nat.mul`, `Nat.beq`, `Nat.ble`, …),
δ-unfolding of instances and of `Nat.decEq`, projections of structure
instances (`Decidable` is a structure in Lean 4.35.0: fields `decide :
Bool` and `reflects_decide`, `Init/Prelude.lean` 1146), ι-reduction on
`Bool`, `Option`, `List` and `Int` (for `Constraint.isImpossible`,
`Coeffs`, `LinearCombo.eval`), structural recursion compiled to `brecOn`
(`Nat.decidableBallLT`), and proof irrelevance. No well-founded recursion
is reduced in these cases.

LeanForth's kernel has all of these (`src/kernel/reduce-nat.fs` for the
literal operations, `whnf.fs`, `iota.fs`, `infer-proj.fs`, `defeq.fs`),
and has accepted all of Init and all of Mathlib, including the proofs
behind Init's 730 uses of `by decide` and 1,801 of `by omega` (text
counts in Init's sources). Checked directly for this design: pinned Lean compiled the six theorems
`a1 a2 a3 o1 d1 d2` (`.claude/work/D1I/Fe1iProbe.lean` in the
designer's worktree), `scripts/export.sh` exported them with their
dependencies, and `bin/leanforth check --jobs 2` printed `1484
declarations: 1484 accepted`, with `a1`, `a2`, `o1` and their helper
theorems `accepted; axioms: propext, Quot.sound` and `a3`, `d1`, `d2`
`accepted; axioms: none`, as Lean reports. **Missing kernel features:
none.** One resource difference stays possible: LeanForth's kernel
counts fuel (default 20,000,000 per declaration), Lean's does not, so a
`decide` with a very long computation could end *exhausted* in
LeanForth where Lean's kernel finishes; that is the owner's fuel rule of
2026-11-12 (FE1E_APPLICATIONS.md question 1), listed in
[BEYOND_LEAN.md](../project/BEYOND_LEAN.md) when met, never accepted.

### 2.7 How the probes were made

Probe files in the designer's notes (`.claude/work/D1I/` of the
worktree): `p1.lean` (the three targets, `pp.all`, `#print`, `#print
axioms`), `p2.lean` (`decide` cases), `p3.lean` and `p7.lean` (wrong
and unprovable statements, edge cases), `p4.lean` (`omega` cases),
`p5.lean` (`import Lean`, a `#size` command: tree size, distinct nodes,
constants), `p6.lean` (the helper theorem printed, `trace.omega`),
`p8.lean` (`trace.Meta.synthInstance`), `p9.lean` (the `assumption`
step, the classical fallback, the exponent threshold). Each was run as

```sh
bash -c 'ulimit -u 500; timeout -k 5 120 nice -n 15 \
  .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean FILE'
```

The kernel run: `lean -o ol/Fe1iProbe.olean Fe1iProbe.lean`, then
`LEAN_PATH=ol:<toolchain>/lib/lean scripts/export.sh fe1i.ndjson Fe1iProbe
-- a1 a2 a3 o1 d1 d2`, then `bin/leanforth check --jobs 2 fe1i.ndjson`
(exit 0). FE1i-9 (§7) turns them into checked-in test sources.

## 3. LeanForth text

The test file `tests/frontend/02-auto.lf` holds the three theorems of
§2.1, each with its Lean twin as a comment, as FE1's file does
([FRONT_END.md](FRONT_END.md) §8.1). Its wrong twin
`tests/frontend/wrong/02-auto.lf` holds the refusals of §6.1.

| Word | Stack effect | Lean | What it does |
| --- | --- | --- | --- |
| `by-decide` | `( -- )` | `decide` | closes the main goal by evaluation (§4) |
| `by-omega` | `( -- )` | `omega` | closes the main goal by linear arithmetic over `Nat` and `Int`, using every hypothesis in its context (§5) |
| `by-native-decide` | `( -- )` | `native_decide` | always *unsupported* (exit 2): it rests on `Lean.ofReduceBool` (ADR 0021 D7); FE10's row keeps this permanent |

Both take no values from the stack (a value left there is the
malformed-input error of FE1g §3.2). Lean's options (`decide +kernel`,
`+native`, `+revert`, `omega +splitNatAbs` and the rest of
`OmegaConfig`) have no spelling in FE1i; when FE10 adds them, an option
not ported answers unsupported at its token. Both words are tactic words
of FE1g's vocabulary: they run when read, on the main goal, through
FE1g's runner, and record a step (rule `decide`, explained "by
computation"; rule `omega`, explained "by linear arithmetic", plan
8.6.12).

## 4. `by-decide`: the faithful port

### 4.1 Lean's algorithm

`evalDecide` → `evalDecideCore` with the default configuration
(`Decide.lean` 83-146):

1. `closeMainGoalUsing` (`Elab/Tactic/ElabTerm.lean` 85-101; FE1g §5.2
   ports it for `exact`): take the main goal off the list, run in its
   local context with its type; on failure put the goal back and rethrow.
2. `preprocessPropToDecide` (lines 24-33): instantiate metavariables; if
   the type has a free variable, ζ-reduce (`zetaReduce`: replace let
   variables by their values); then a metavariable is the error
   "Expected type must not contain metavariables", a free variable the
   error "Expected type must not contain free variables" with its hint.
3. `mkDecide p`: `Decidable.decide p ?inst` with the instance synthesized
   (`mkAppOptM`, so instance search of FE1e; failure is Lean's "failed
   to synthesize").
4. `withAtLeastTransparency .default <| whnf dec` (line 106): weak head
   normal form at default transparency (or above, if the ambient one is
   `all`).
5. If the result is the constant `Bool.true`: the value
   `of_decide_eq_true p inst (@id (@Eq Bool dec Bool.true) (@Eq.refl
   Bool Bool.true))`; `closeMainGoalUsing` checks that it made no new
   unassigned metavariable and assigns the goal (`checkedAssign`).
6. Otherwise `diagnose` (lines 148-194): `Bool.false` gives "proved that
   the proposition … is false"; anything else is re-reduced with
   diagnostics on (`blameDecideReductionFailure`, lines 39-68, follows
   `Bool.rec`/`Decidable.rec` major premises, `Decidable.intro`'s first
   argument, the projection `decide`, and matcher discriminants of type
   `Bool` or `Decidable`, to the subterm that is stuck) and reports
   "failed to reduce … to `true` or `false`", the stuck subterm, the
   `Decidable` instances that were unfolded (sorted by name), and a hint
   when the stuck term is `Eq.rec` or `Classical.choice`.

FE1i ports steps 1-6 as they are. The term is then identical to Lean's
by construction, provided FE1e elaborates the same statement and
synthesizes the same instance (both compared node for node, §6.2).

### 4.2 The reduction it relies on

Two reductions do the same computation, and neither is trusted:

- **The front end's `whnf`** (FE1c, ADR 0021 D6; branch `fe1c-2` has
  `whnfCore`): it decides whether `decide` succeeds. For `2 + 2 = 4`
  the path is: `Decidable.decide` is a projection function (unfolded when
  its structure argument reduces to a constructor: Lean's
  `unfoldDefinition?` with `getProjectionFnInfo?`, which FE1d2 adds to the
  elaboration data); `instDecidableEqNat` (an instance, unfolded at
  default) → `Nat.decEq (2 + 2) 4` (reducible) → the structure instance
  `{ decide := Nat.beq (2 + 2) 4, … }`; the projection gives
  `Nat.beq (2 + 2) 4`; `reduceNat?` (`Meta/WHNF.lean` 1010-1034) folds
  `Nat.beq` once both arguments reduce to literals (`withNatValue`, lines
  975-985: refuses at once a term with free variables, instantiates
  metavariables, reduces with `whnf`), which needs `HAdd.hAdd` →
  `instHAdd` → `Add.add` → `instAddNat` → `Nat.add 2 2` → `4`, and
  `OfNat.ofNat Nat 2 (instOfNatNat 2)` → `2`; result `Bool.true`. For
  `10 < 20`: `Nat.decLt` → `Nat.decLe 11 20` → `Nat.ble`. For `∀ x < 5,
  …`: `Nat.decidableBallLT` is structural recursion with matches on
  `Decidable` values, which needs matcher information and smart
  unfolding (`_sunfold`) — facts the export lacks, FE1d2 — and literals
  turned into `Nat.succ` for ι (`Nat` literal to constructor). For `∧`,
  `∨`, `¬`: Bool's `and`, `or`, `not` (Prelude, by `match`).
- **The kernel**, when it checks the term: `Eq.refl Bool.true :
  Decidable.decide p inst = Bool.true` holds only if the kernel reduces
  `Decidable.decide p inst` to `Bool.true` itself (§2.6). A front-end
  fault that says "true" for a false statement produces a term the
  kernel rejects (fault `fe-decide-skip-whnf`, §6.3).

The front end's `whnf` must fold `Nat` literals as Lean's `Meta` does
(with `lib/bignum.fs`, as the kernel's `reduce-nat.fs` does, but in its
own code: D6), including `reducePow`'s exponent threshold: above 256
Lean prints the warning "exponent 300 exceeds the threshold 256,
exponentiation operation was not evaluated, use `set_option
exponentiation.threshold <num>` to set a new threshold" and goes on by
unfolding `Nat.pow` (observed: `2 ^ 300 > 0 := by decide` is still proved,
with that warning). LeanForth prints the same warning and takes the same
path.

### 4.3 Failure modes, codes and outcomes

Codes in `src/author/errors.fs` (numbers fixed when FE1i-1 lands, after
FE1g's); all stop the declaration before the kernel (exit 4), except
unsupported (exit 2):

| Code (name) | When | Lean's message | Outcome |
| --- | --- | --- | --- |
| `lfa-e-decide-mvars` | the statement still has a metavariable | `Expected type must not contain metavariables` | invalid |
| `lfa-e-decide-fvars` | it has a free variable after ζ | `Expected type must not contain free variables` + hint | invalid |
| `lfa-e-decide-no-instance` | instance search fails | `failed to synthesize` `Decidable p` | invalid |
| `lfa-e-decide-false` | `whnf` gives `Bool.false` | `Tactic `decide` proved that the proposition … is false` | invalid |
| `lfa-e-decide-stuck` | `whnf` gives anything else | `Tactic `decide` failed to reduce … reduction got stuck at …` (+ unfolded instances, + hint) | invalid |
| (FE1g's) `lfa-e-tac-no-goals` | no goal left | `No goals to be solved` | invalid |
| `lfa-e-tactic` (72) | a reduction step not ported yet (a definition whose facts FE1d2 has not supplied, a quotient, …): FE1c answers unsupported, and `by-decide` passes it on at its token | — (Lean decides) | unsupported |
| — | fuel of `whnf` or instance search runs out | Lean: `maximum recursion depth` or heartbeats | exhausted |

"Stuck" and "unsupported" are kept apart: Lean's `whnf` ending at a term
it cannot reduce is Lean's answer (invalid, with Lean's message), while
FE1c not knowing how Lean would continue is LeanForth's gap
(unsupported, never a guess). The diagnosis's list of unfolded instances
needs FE1c's `whnf` to report the constants it δ-unfolded during the
re-reduction (Lean's `diagnostics` unfold counter); FE1i-2 adds that hook.

### 4.4 What it needs

| Piece | From | For |
| --- | --- | --- |
| goal list, `closeMainGoalUsing`, checked assignment, step record | FE1g-3, FE1g-4 | steps 1, 5 |
| `instantiateMVars`, `zetaReduce`, `hasFVar`/`hasMVar` | FE1b, FE1c | step 2 |
| instance synthesis: `instDecidableEqNat`, `Nat.decLt`, `Nat.decLe`, `Int.decLt`, `Int.decEq`, `instDecidableAnd`/`Or`/`Not`, `Nat.decidableBallLT` (needs the β-redex answer of §2.4) | FE1e5 (Init's instances via FE1d's data) | step 3 |
| `whnf` at default with δ, projection functions, `reduceNat?`, `withNatValue` | FE1c (delta part not started), FE1d2 (projection-function facts) | step 4, first slice |
| matchers, smart unfolding, literal → constructor, `brecOn` | FE1c, FE1d2 | step 4, bounded `∀` and `∧`/`∨`/`¬` |
| the unfold hook, `blame` | FE1c (hook), FE1i-2 | step 6 |
| hand-over of the finished term | FE1f | — |

## 5. `by-omega`

### 5.1 Lean's algorithm

`evalOmega` (`Omega/Frontend.lean` 703-710) → `omegaTactic` (680-699),
about 1,700 lines of Lean in `Lean/Elab/Tactic/Omega/` (`Frontend.lean`
714, `Core.lean` 578, `OmegaM.lean` 262, `MinNatAbs.lean` 150) and the
overview in `Omega.lean` (197), plus `Elab/Tactic/FalseOrByContra.lean`
and `Meta/Canonicalizer.lean` (152). Its lemmas and the functions the
kernel evaluates are in `Init/Omega/` (Int, IntList, Coeffs,
LinearCombo, Constraint, Logic: 1,486 lines, mostly theorems), which are
part of every Init export and need no port.

1. **`assumption` first**, at reducible-and-instances transparency: if a
   hypothesis already has the goal's type, that is the proof.
2. **`falseOrByContra`**: `whnfR` of the goal; `False` stays; `¬P` and a
   Π are introduced (`intro1P`) and repeated; any other proposition `P`
   gets `Decidable.byContradiction` applied (with its instance
   synthesized; if there is none, `Classical.byContradiction`, which
   brings `Classical.choice` into the axioms) and `¬P` introduced; a
   non-proposition gets `False.elim`.
3. **Collect facts**: every hypothesis of the local context
   (`getLocalHyps`). For each, `addFact` (Frontend 425-509) matches the
   `whnfR` of its type: `=`, `≤`, `<`, `>`, `≥`, `≠`, `∣` over `Nat`,
   `Int` and `Fin` are rewritten by named Init lemmas into `Int` facts
   `0 ≤ e` or `e = 0`; `¬` is pushed inward (`pushNot`, 372-423); `∧`,
   `∃`, `Subtype` are split; `↔` and `→` between propositions become
   disjunctions (with `Classical.propDecidable`); `∨` is kept for later
   splitting; anything else is ignored.
4. **Linear combinations** (`asLinearCombo`, 105-334): each side is
   turned into a `LinearCombo` (a constant and a coefficient list) over
   *atoms*, with a proof (built lazily) that the side equals its
   evaluation. `+`, `-`, `*` by a constant, `-x`, `/` and `%` by a
   literal, `Nat`-to-`Int` casts pushed inward (`Int.natCast_add`, …),
   `Nat.succ`, `min`, `max`, ground powers (`2 ^ 3`) are
   understood; anything else is an atom. Atoms are compared up to
   definitional equality at instances transparency by the canonicalizer
   (a hash that ignores implicit arguments, then `isDefEq`). A new atom
   brings facts (`0 ≤ ↑x` for a cast `x : Nat`; bounds for `x / k`; for
   `↑(a - b)` the dichotomy `b ≤ a ∧ … ∨ a < b ∧ … = 0`).
5. **The omega test** (`Core.lean`): constraints are normalized (leading
   coefficient positive, divided by the GCD with the constant rounded,
   matching lower and upper bounds tightened into equalities or found
   impossible); equalities are solved, easy ones (a coefficient ±1)
   first, hard ones with Pugh's balanced-mod step (`bmod`, a new
   variable); then Fourier–Motzkin elimination of one variable at a time,
   preferring *exact* eliminations (all lower or all upper coefficients
   ±1) and then the fewest new constraints. **No dark or grey shadow**:
   when the real shadow is satisfiable, `omega` gives up on that branch.
6. **Disjunctions** are split only when the rest gives no contradiction,
   first in, first out (`splitDisjunction`, 620-647), each branch proved
   separately and joined with `Or.elim`.
7. **The proof**: each derived constraint carries a `Justification`
   (assumption, tidy, combine, combo, bmod); at the end
   `Constraint.not_sat'_of_isImpossible` with a `decide` proof
   (`mkDecideProof`) that the final constraint is impossible. The whole
   proof of `False` is put into a helper theorem (`mkAuxTheorem`:
   abstracted over the free variables it uses, named by
   `mkAuxDeclName` with kind `_proof`, observed `a1._proof_1_1`, and
   cached per module by its statement, so a second identical goal in the
   same file reuses the first helper), applied to those variables.
8. **Failure**: "omega could not prove the goal:" with either "No usable
   constraints found…" or "a possible counterexample may satisfy the
   constraints" and the remaining constraints over named atoms
   (`formatErrorMessage`, 533-618).

### 5.2 Option (a): port Lean's `omega`

Port steps 1-8 as written, so that LeanForth makes the same choices in
the same order and builds the same term.

- **What makes the order Lean's.** The problem keeps its constraints in a
  `Std.HashMap Coeffs Fact` and its equalities in a `Std.HashSet Coeffs`,
  and the algorithm *iterates* them: `selectEquality` folds the set (ties
  between equalities go to whichever comes first) and
  `fourierMotzkinData` walks the map (the order of the new constraints,
  and so which contradiction is found first). To give Lean's terms, and
  Lean's outcome even in tie cases, LeanForth reproduces that order: Lean's
  `hash` on `List Int` (`foldl mixHash 7`, `Init/Data/Hashable.lean` 64:
  `hash (ofNat n) = 2n`, `hash (negSucc n) = 2n + 1`; `mixHash` is
  `lean_uint64_mix_hash` in `include/lean/lean.h` 2293, 64-bit
  arithmetic), `Std`'s bucket index (`scrambleHash`, `mkIdx` in
  `Std/Data/DHashMap/Internal/Index.lean` 51), initial size 8, growth
  (`expandIfNecessary`), where a new or replaced entry goes in its bucket,
  and the fold order — each confirmed against Lean's own iteration order
  by FE1i-5's test. This is a small LeanForth-only
  module (its header says why it is not a general library: its only
  purpose is Lean's iteration order).
- **Integers.** Coefficients and constants are Lean `Int`s of any size:
  a new standalone library `lib/bigint.fs` (signed numbers over
  `lib/bignum.fs`: add, subtract, multiply, Euclidean `/` and `%` as
  Lean's `Int.ediv`/`emod`, `bmod`, `gcd`, `natAbs`, compare), with its
  own tests outside the checker.
- **Lazy proofs.** Lean's `Proof` is an `OmegaM Expr` run only after a
  contradiction is found, and `asLinearCombo` returns proof thunks. In
  Forth these become *proof recipes*: records (kind, arguments) in a heap
  store, expanded at the end by a walk on `lib/frame.fs` steps (no host
  recursion), in Lean's order, so that metavariable numbers, `instantiateMVars`
  and the shared subterms come out as Lean's.
- **Terms of data.** Constraints, coefficient lists and linear
  combinations appear in the proof as terms (`Constraint.mk (some 1)
  (some 0)`, `Coeffs.ofList [↑n]`, `LinearCombo.mk 0 [1]`), built as
  Lean's `toExpr` builds them (`Int` literals as `OfNat.ofNat Int k
  (instOfNat k)`, negatives with `Neg.neg`).
- **Size.** About 1,700 lines of Lean plus the canonicalizer (152), parts
  of `Closure.lean` (`mkValueTypeClosure`) and `falseOrByContra`;
  *speculative* 2,800 to 4,300 lines of Forth with the integer library
  and the hash order, and as much in tests (§7).
- **Risk.** Medium. The algorithm is deterministic and documented; the
  parts that are hard to get exactly right (hash order, proof-recipe
  order, the canonicalizer) affect terms first and outcomes only in rare
  ties, and both are measured by §6.2's corpus. The front-end pieces it
  needs (`whnfR`, `inferType`, `isDefEq` at instances transparency,
  `instantiateMVars`, instance search for `Decidable`, `apply`, `intro`)
  are FE1c, FE1e and FE1g work that FE5 needs anyway.

### 5.3 Option (b): LeanForth's own `omega` with its own certificate

Write a decision procedure of LeanForth's own (for instance the complete
omega test, or Fourier–Motzkin with a simplex for speed) and turn its
result into a kernel-checked term from Init's lemmas (a linear
combination of the hypotheses and a `decide` on the result).

- **Size.** The procedure itself is smaller (*speculative* 1,500 to
  2,500 lines of Forth); the preprocessing (step 3 and 4: which facts and
  atoms count) is needed in full either way, because it decides what is
  provable.
- **Risk.** High, for the owner's rule. A complete procedure proves the
  bold rows of §2.5 that Lean refuses (Pugh's example needs the dark
  shadow); it would then have to be weakened to fail exactly where Lean
  fails, which means re-deriving Lean's elimination order, its
  preference for exact eliminations, its first-in-first-out splitting and
  its atom rules — Lean's algorithm again, without Lean's code as the
  reference. The terms differ from Lean's everywhere, the axioms reported
  may differ (Lean's use `propext` and `Quot.sound`; another choice of
  lemmas could add `Classical.choice` or drop both), and an Init export
  re-proved this way could not be compared term for term.
- **Same outcome, tested how.** Only by the corpus of §6.2; every
  difference would be a gap to close by making the procedure behave more
  like Lean's.

### 5.4 Recommendation: option (a)

Port Lean's `omega`, with Lean's iteration order. Reasons: (1) the
outcome rule cannot be met reliably by any other algorithm, because
Lean's `omega` is defined by where it gives up (§2.5); (2) identical terms
come with it, so FE10's "re-prove Init's 1,801 `omega` proofs and compare"
becomes a term comparison, the strongest test LeanForth has; (3) the
axioms reported are Lean's; (4) the cost is moderate (the core is 578
lines of Lean) and the front-end pieces it needs are needed by FE5 in any
case. Question 1 asks the owner.

### 5.5 What FE1i's first slice of `omega` covers

Everything of §5.1 that the corpus families of §6.2 reach: `Nat` and
`Int`; `+`, `-` (with the truncation split), `*` by constants, `/`, `%`
and `∣` by literals, `min`, `max`, `Nat.succ`, casts, ground powers;
`=`, `≤`, `<`, `≥`, `>`, `≠`, `¬`, `∧`, `∨`, `→`, `↔`, `∃` in hypotheses;
atoms for everything else; the error messages. Left for FE10, answering
unsupported at `by-omega` when met (never a guess): `Fin` facts and
`Fin` atoms (`Fin.val_congr`, …), `Prod.Lex`, `Int.natAbs` and
`Int.toNat` splitting (`splitNatAbs`, `splitMinMax` cases beyond `min`
and `max` of two `Nat`s), `BitVec` and `UIntN` (`bv_omega`), and options.
Where a fact or atom of the left-out kind appears, LeanForth cannot know
whether Lean would use it, so the answer is unsupported rather than
"could not prove".

## 6. Tests

### 6.1 The acceptance files

`tests/frontend/02-auto.lf` (§2.1) and `tests/frontend/02-auto.lean`
(the Lean twins, compiled by pinned Lean with `-DwarningAsError=true` and
exported with `scripts/export.sh`, through the Lean cache).
`bin/leanforth check --env tests/frontend/init-fe1.ndjson
tests/frontend/02-auto.lf` (the slice gains `Decidable.byContradiction`,
`of_decide_eq_true`, `instDecidableEqNat`, `Nat.lt_or_gt_of_ne` and the
`Lean.Omega` lemmas the helpers use) prints

```text
zero_add_auto._proof_1_1: accepted; axioms: propext, Quot.sound
zero_add_auto: accepted; axioms: propext, Quot.sound
add_comm_auto._proof_1_1: accepted; axioms: propext, Quot.sound
add_comm_auto: accepted; axioms: propext, Quot.sound
two_add_two: accepted; axioms: none
```

and exit 0, no Lean tool in the run; on the full Init snapshot the same
with `--snapshot init.lfsnap --elab-data init.elab.ndjson`, which is the
done checker's command. The wrong twin `tests/frontend/wrong/02-auto.lf`:
`n 1 + n =` by `by-omega` (counterexample, exit 4), the same by
`by-decide` (free variables, exit 4), `2 2 + 5 =` by `by-decide` (false,
exit 4) and by `by-omega` ("No usable constraints found", exit 4),
`by-native-decide` (unsupported, exit 2). Each refusal's code and first
message are compared with pinned Lean's for the twin `.lean` file.

### 6.2 Comparisons with pinned Lean

1. **Terms, node for node** (`tests/frontend/check_fe1i.py`, as FE1g
   §8.1): every theorem of §2.1, §2.4 and the corpus below that both
   prove: LeanForth's exported records against Lean's, universe arguments
   included, binder names with macro scopes erased (FE1g §2.3; the
   hypothesis `a` that `falseOrByContra` introduces is such a name).
   `by-decide`: required identical (core tactic). `by-omega`: reported as
   "K of N identical" and pinned as a regression value (under option (a)
   the expected value is N of N; a drop fails the test).
2. **The `omega` outcome corpus** (`tests/frontend/omega_corpus.py
   --seed S --count N`): writes the same N goals as a `.lean` file (each
   `theorem cNNNN … := by omega`) and as a `.lf` file. Families: linear
   `Nat` and `Int` goals in 1-4 variables with coefficients −20…20 and
   every relation; hypotheses with `¬ ∧ ∨ → ↔ ∃`; truncated subtraction;
   `/`, `%`, `∣` by literals 0-7; `min`, `max`; casts; products and powers
   as atoms (`x*y = y*x`); Pugh-type systems with real but no integer
   solutions; irrelevant or non-arithmetic hypotheses; definitions that
   must not be unfolded; coefficients above $2^{64}$; problems of 8-12
   variables and 20 constraints (fuel, term size); ties between
   equalities (hash order); and the left-out kinds of §5.5 (expected
   unsupported). About half are true by construction (implied
   constraints), half random. Pinned Lean runs the `.lean` file once
   (Lean cache); each case's outcome is read from its error position
   (proved, "could not prove: counterexample", "No usable constraints",
   other); LeanForth checks the `.lf` file with each declaration judged on
   its own (a refused declaration does not stop the next, as in Lean).
   **Required: zero outcome differences** among the cases LeanForth does
   not answer unsupported, and the unsupported ones listed with their
   plan row. Harness self-test: a brute-force search over a box finds no
   counterexample to any case Lean proves, and a known-wrong outcome table
   is refused. In `make test` (no Lean): 300 cases of a fixed seed
   against their checked-in Lean outcome table; in `make check`: 3,000
   cases with pinned Lean through the Lean cache; a 100,000-case run once
   before FE1i is called done.
3. **The core alone**, before any front end exists: a Lean program
   (`import Lean`) builds random constraint systems directly as
   `Lean.Elab.Tactic.Omega.Problem` values, runs Lean's `runOmega`, and
   prints `possible` and the justification text (`explanation?`) for each;
   the Forth core (§7, FE1i-6) must print the same text for every system.
   This tests the hash order, normalization, equality solving and
   elimination without elaboration, on many more systems than the corpus.
4. **`decide` cases**: every row of §2.4 and §2.5 for `decide`, plus
   seeded closed statements over `Nat` and `Int` literals with `+ - * / %`
   and every relation, true and false: outcome, message code and, when
   proved, the term, all equal to Lean's.

### 6.3 Coverage classes ([TEST_COVERAGE_REVIEW.md](../development/TEST_COVERAGE_REVIEW.md#owners-coverage-classes))

1. **Pass, fail and every outcome.** Accepted: §6.1's three theorems and
   §2.4's cases. Front-end failure (exit 4, nothing checked): every row of
   §2.5. Unsupported (exit 2): `by-native-decide`; a `Fin` fact under
   `by-omega`; a `decide` whose reduction meets a definition FE1d2's data
   does not describe. Rejected by the kernel (exit 1): fault
   `fe-decide-skip-whnf` on `2 2 + 5 =` hands over `of_decide_eq_true`
   anyway; fault `fe-omega-tidy-round` gives an unsound helper theorem.
   Exhausted: a tiny `--fuel` for each word. Axioms: the `omega` theorems
   report `propext, Quot.sound` as Lean does; a goal whose instance search
   fails falls back to `Classical.byContradiction` and reports
   `Classical.choice` as Lean does.
2. **Malformed input.** A value left on the stack before `by-decide` or
   `by-omega`; either word outside `:= by`; with no goal left (Lean's "No
   goals to be solved"); `by-decide` on a goal holding a metavariable
   (a hole, once FE2 allows one: until then a Forth unit test builds the
   goal directly).
3. **Interfaces.** The stack effect of every new public word (§7) under
   `tests/support/checks.fs`' `run-case`; each error code of §4.3 and its
   `omega` codes in the catalogue; every failure an outcome other than ok;
   `lib/bigint.fs` against Lean's `Int` operations on 10,000 seeded pairs
   (signs, zero, $\pm 2^{64}$, $2^{200}$), including `ediv`/`emod`/`bmod` by
   negative divisors; the hash-order module against Lean's own iteration
   order (a Lean program prints `toList` of a `Std.HashMap (List Int) Nat`
   after seeded inserts, erases and replacements).
4. **Workflows and I/O.** The commands of §6.1, text and `--json`;
   `.goals` before and after each word (golden); the step log of each
   theorem (rule `decide`, `omega`); `leanforth print` of the helper
   theorem; the corpus workflow.
5. **Resources.** Fuel: `by-decide` on `123456789 * 987654321 = …`
   (literal folding is one step) and on a bounded `∀` over 1,000 values
   (many steps); `by-omega` on a problem whose Fourier–Motzkin elimination
   grows quadratically per variable; exhausted, never accepted. A
   coefficient of $2^{300}$. A helper theorem of 50,000 tree nodes (o6)
   kept as about 750 distinct nodes. Store exhaustion: *full*.
6. **State and rollback.** A failed `by-omega` leaves no assignment, no
   helper theorem and no hypothesis behind (FE1g's trail); the next
   declaration in the same process gives the same result as alone; the
   per-module helper cache: two identical `omega` goals in one file share
   one helper (Lean's `mkAuxLemma` cache), and a refused declaration
   leaves no cache entry; determinism over two runs and with `--jobs 2`.
7. **Regression pins.** Golden outputs and terms of §6.1; the corpus's
   outcome table and its "K of N identical" count; fuel counts.

### 6.4 Planted faults (`tests/mutants/faults.toml`, each caught)

| Fault | What it does | Caught by |
| --- | --- | --- |
| `fe-decide-skip-whnf` | `by-decide` builds the term without reducing | the kernel rejects `2 2 + 5 =` (exit 1) |
| `fe-decide-fvar-allowed` | the free-variable check dropped | the message-code test of `n 1 + n =` (stuck instead of free variables) |
| `fe-decide-false-as-stuck` | `Bool.false` reported as stuck | the message-code test of `2 2 + 5 =` |
| `fe-decide-no-hint` | the `id` around `Eq.refl` left out | the term comparison (the kernel still accepts: this is why the identity test exists) |
| `fe-omega-dark-shadow` | a complete dark-shadow step added | the corpus: Pugh's example proved where Lean fails |
| `fe-omega-unfold-atoms` | atoms put in `whnf` at default | the corpus: `f n > n` proved where Lean fails |
| `fe-omega-commute-products` | products ordered before becoming atoms | the corpus: `x*y = y*x` proved where Lean fails |
| `fe-omega-natsub-no-split` | no dichotomy for `↑(a - b)` | the corpus: `a - b ≤ a` refused where Lean proves |
| `fe-omega-tidy-round` | the constant rounded the wrong way when dividing by the GCD | the kernel rejects the helper theorem (exit 1), and the core comparison |
| `fe-omega-insertion-order` | constraints iterated in insertion order, not Lean's hash order | the core comparison's justification texts and the term count pin |
| `fe-omega-no-assumption` | the `assumption` step skipped | the term comparison of `(h : x < 3) : x < 3` |
| `fe-omega-inline-proof` | the proof not put into a helper theorem | the term comparison and the export-shape test |
| `fe-omega-classical` | `Classical.byContradiction` always | the axiom-report pin (`Classical.choice` appears) |
| `fe-bigint-ediv-sign` | `ediv` rounds toward zero for a negative divisor | the bigint test against Lean |

### 6.5 Other checks

Fuzzing of seeded word sequences with `by-decide` and `by-omega` in
every position (never a crash, never accepted unless the kernel accepts);
portability (Gforth 0.7.3 runs the tests; the hash order needs 64-bit
wrapping multiplication, which a 32-bit host does with double cells:
`lib/u32.fs`'s style, tested on both); timeouts on every new make recipe;
the coverage and style ratchets (new files start at zero long words); a
logged Forth review of every step.

## 7. Modules, words and sub-steps

### 7.1 Files

All untrusted, each with its tests; tactic words in `src/tactic/`
(FE1g's folder), the integer library in `src/lib/`.

| File | Contents | Lean |
| --- | --- | --- |
| `src/lib/bigint.fs` | signed big integers over `lib/bignum.fs`: `+ - *`, `ediv`, `emod`, `bmod`, `gcd`, `natAbs`, compare, sign; standalone, with an example in its header | `Int` in `Init/Data/Int` |
| `src/tactic/decide.fs` | `by-decide`, `by-native-decide`; preprocess, `mkDecide`, the term; `diagnose`, `blame` | `Elab/Tactic/Decide.lean` |
| `src/tactic/omega-hash.fs` | Lean's `hash` for coefficient lists and `Std.HashMap`/`HashSet` order (insert, replace, erase, grow, fold) | `Init/Data/Hashable.lean`, `Std/Data/DHashMap/Internal` |
| `src/tactic/omega-core.fs` | constraints, coefficient lists, facts, justifications, the problem; tidy, combine, equalities (easy, hard with `bmod`), Fourier–Motzkin, elimination; `proveFalse`; the justification text | `Omega/Core.lean`, `MinNatAbs.lean`, `Init/Omega/*` functions |
| `src/tactic/omega-proof.fs` | proof recipes and their expansion into terms on frames; `toExpr` of constraints, coefficients, linear combinations | `Core.lean` (`proof`, `tidyProof`, …), `Frontend.lean` (`mkEvalRflProof`, …) |
| `src/front/canon.fs` | the canonicalizer: hash ignoring implicit arguments, buckets checked with `isDefEq` at instances transparency | `Meta/Canonicalizer.lean` |
| `src/tactic/omega-atoms.fs` | atoms, the linear-combination cache, `groundNat?`/`groundInt?`, `analyzeAtom`, `asLinearCombo` | `Omega/OmegaM.lean`, `Frontend.lean` 36-334 |
| `src/tactic/omega-facts.fs` | `addFact`, `pushNot`, `processFacts`, `splitDisjunction`, `omegaImpl`, the error message | `Frontend.lean` 336-670 |
| `src/tactic/omega.fs` | `by-omega`: `assumption`, `falseOrByContra`, the hypotheses, the run, the helper theorem (closure, name, per-file cache), the assignment | `Frontend.lean` 672-710, `FalseOrByContra.lean`, `Meta/Closure.lean` |

FE1f's hand-over gains *auxiliary declarations*: a tactic may add a
theorem (name, universe parameters, type, value) that is sent to the
kernel before the declaration that uses it, as Lean's export lists it.

### 7.2 Public words

Outcomes are ADR 0008's; a failed word gives -1 for its result.

| Word | Stack effect | Lean |
| --- | --- | --- |
| `by-decide`, `by-omega`, `by-native-decide` | `( -- )` | `decide`, `omega`, `native_decide` |
| `lf-decide-term` | `( prop -- term outcome )` | `doElab` |
| `lf-decide-diagnose` | `( prop dec reduct -- code outcome )` | `diagnose` |
| `lf-false-or-by-contra` | `( goal -- goal' flag outcome )`, flag false when closed | `MVarId.falseOrByContra` |
| `lf-aux-theorem` | `( type value -- term outcome )` | `mkAuxTheorem` |
| `lf-canon` | `( term -- term' outcome )` | `canon` |
| `lf-omega` | `( facts goal -- outcome )` | `omega` |
| `lf-omega-problem` | `( -- problem )` | `Problem` (empty) |
| `lf-omega-add` | `( problem const coeffs recipe kind -- problem' )` | `addInequality`, `addEquality` |
| `lf-omega-run` | `( problem -- problem' outcome )` | `runOmega` |
| `lf-omega-false` | `( problem -- recipe flag )` | `proveFalse?` |
| `lf-omega-explain` | `( problem -- c-addr u )` | `explanation?` (for the core comparison) |
| `bigint+`, `bigint-`, `bigint*`, `bigint-ediv`, `bigint-emod`, `bigint-bmod`, `bigint-gcd`, `bigint-compare` | as `lib/bignum.fs`'s words, with an arena | `Int` |

### 7.3 State, fuel, errors

- State (ADR 0009): `om` (the problem: constraint and equality hash
  stores, eliminations, flags), `oa` (atoms, the cache, the
  canonicalizer's buckets), `or` (proof recipes); all in heap stores
  (`lib/store.fs`), members of the checker context, reset per
  declaration except the per-file helper cache.
- No host recursion: `addFact`'s repeated rewriting, `asLinearCombo`'s
  descent, the disjunction splits and the recipe expansion are frames on
  `lib/frame.fs` heap stacks.
- Fuel: one unit per fact processed, per normalization, per elimination
  step and per recipe expanded, plus FE1c's for `whnfR` and `isDefEq`;
  out of fuel is *exhausted*, never a proof and never "could not prove".
- Codes: `lfa-e-omega-failed` (counterexample or no usable constraints;
  Lean's message, invalid), `lfa-e-omega-unsupported` (a left-out kind of
  §5.5, unsupported), with §4.3's for `decide`.

### 7.4 Sub-steps

Sizes as in the plan (S up to about 300 lines of Forth, M up to about
800, L more), each with its focused tests, faults and a logged Forth
review.

| Step | What | Needs | Size |
| --- | --- | --- | --- |
| FE1i-1 | `by-decide` for closed statements whose instances reduce by δ, projections and literal folding (`2 2 + 4 =`, `10 20 <`, `Nat`/`Int` relations): preprocess, `mkDecide`, term, the codes of §4.3 except the diagnosis details | FE1g-3, FE1g-4 (`closeMainGoalUsing`), FE1e5 (instances), FE1c `whnf` with δ and `reduceNat?`, FE1d2 (projection functions), FE1f | S–M |
| FE1i-2 | the diagnosis: `blame`, the unfold hook in FE1c's `whnf`, Lean's three messages and hints | FE1i-1 | S |
| FE1i-3 | `by-decide` on bounded `∀`, `∧`, `∨`, `¬` (matchers, smart unfolding, literals as constructors) — mostly FE1c work on the data of FE1d2 | FE1i-1, FE1d2 | S |
| FE1i-4 | `lib/bigint.fs` and its tests against Lean's `Int` | — (can start now) | S–M |
| FE1i-5 | `omega-hash.fs` and its test against Lean's `Std.HashMap` order | FE1i-4 | S–M |
| FE1i-6 | `omega-core.fs`: the omega test on constraints, justifications and their text; the core comparison of §6.2 item 3 | FE1i-4, FE1i-5 (can start now) | M |
| FE1i-7 | `omega-proof.fs`, `canon.fs`, `omega-atoms.fs`, `omega-facts.fs`: facts, atoms, linear combinations, disjunctions, recipes to terms, messages | FE1i-6, FE1c (`whnfR`, `inferType`, `isDefEq`, `instantiateMVars`), FE1e5 | L |
| FE1i-8 | `omega.fs`: `assumption`, `falseOrByContra` (`apply` with instance, `intro`), the helper theorem and its cache; FE1f's auxiliary declarations | FE1i-7, FE1g-4 | S–M |
| FE1i-9 | `02-auto.lf` and `.lean`, the wrong twins, the slice, `check_fe1i.py`, the corpus generator and its reference runs, the faults of §6.4, the user page in three forms | FE1i-1 to 8 | M |

Total *speculative* 3,300 to 5,000 lines of Forth and as much in tests;
the plan row's M–L becomes **L**. FE1i-4, FE1i-5 and FE1i-6 need no front
end and can start before FE1 is finished (question 3); FE1i-1 is the
earliest point at which LeanForth finds a proof (`2 2 + 4 =`), and FE1i-8
the first `by-omega` proof.

## 8. Questions for the owner

1. **How should `by-omega` find its proofs?** (a) Port Lean's `omega`
   algorithm exactly, including the order in which it visits its
   constraints, so LeanForth proves exactly what Lean proves and builds
   Lean's proof; (b) write LeanForth's own arithmetic procedure and its
   own proof, and test that it proves the same statements as Lean.
   *Recommendation: (a).* Lean's `omega` deliberately skips part of the
   textbook algorithm and does not look inside definitions, so it fails
   on some true statements (§2.5, for example $xy = yx$ and Pugh's
   example). Your rule is that LeanForth must succeed exactly where Lean
   succeeds; a procedure of our own would prove those statements and break
   the rule, and making it fail in the same places means rebuilding
   Lean's algorithm anyway, without Lean's code to compare against. With
   (a) the proofs are also identical to Lean's (the strongest check we
   have) and report the same axioms (`propext`, `Quot.sound`). Cost:
   about 1,700 lines of Lean to port, *speculative* 3,000 to 4,000 lines
   of Forth.
2. **May the acceptance test say exactly what Lean says?** The plan row
   asks that the false statement $n + 1 = n$ be "refused by each" word.
   Lean's `decide` refuses it, but not because it is false: it refuses
   every statement with a variable ("Expected type must not contain free
   variables"), true or not. Options: (a) keep $n + 1 = n$ for both
   words and add $2 + 2 = 5$, which `decide` refuses because it computes
   *false* (and `omega` refuses with "No usable constraints found"), each
   refusal compared with Lean's message; also write the plan's short
   `0 n + n = := by-omega` as full theorems with binders and `:= by
   by-omega end NAME` (FE1g's form); (b) leave the row as it is.
   *Recommendation: (a)*: it tests both reasons `decide` refuses, says
   exactly what Lean does, and uses the tactic-block form you approved
   for FE1g.
3. **May the parts of `omega` that need no elaborator start now?** The
   integer library, Lean's table order and the omega core itself
   (FE1i-4 to FE1i-6) can be built and compared with Lean's own `omega`
   core directly, before FE1 is finished, on 100,000 generated problems.
   Options: (a) start them now, in parallel with FE1c, FE1e and FE1g;
   (b) wait until FE1 is done, as the plan's order says. *Recommendation:
   (a)*: you brought FE1i forward; this is about half of `by-omega`, it
   does not touch the kernel or FE1's files, and when FE1 lands
   `by-omega` needs only its front-end half.

## 9. Limits of this design

- It covers FE1i's slice; every other form answers unsupported at its
  token, named in §5.5 with FE10 as the row that lifts it. FE10 keeps
  "re-prove Init's `decide` and `omega` proofs, K of N" (Init's sources
  use `by decide` 730 times and `by omega` 1,801 times, text counts).
- `by-decide` depends on the elaboration data's second slice (FE1d2,
  not started) for anything beyond δ, projections and literal folding.
- Lean's `omega` keeps changing between Lean versions; this design
  follows 4.35.0 exactly and is re-checked by the corpus at any toolchain
  change.
- Lean's own limits (heartbeats, recursion depth) are not reproduced:
  LeanForth's fuel replaces them, as the owner decided on 2026-11-12;
  where they differ in result, the case goes to
  [BEYOND_LEAN.md](../project/BEYOND_LEAN.md).
- The error messages' wording is compared by code and first line; the
  counterexample listing of `omega` is compared as text once the
  printer prints `↑n` and `x * y` as Lean does (FE1g §11).
