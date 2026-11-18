# The elaborator: what LeanForth fills in

Status (2026-11-14, plan slice S1): **done**: works end to end on all of `Init` (the stages of
[DONE_CHECKER.md](../development/DONE_CHECKER.md); done check
[2026-11-14-s1.md](../development/done-checks/2026-11-14-s1.md)), with instance search (`synth.fs`) and lazy
unfolding (S2's merge A). S1's files run on the S1 slice as below in seconds; on all of `Init`,
`bin/leanforth check --jobs 2 --env init.ndjson --elab-data init.elab.ndjson tests/front/s1-rfl.lf` takes about 18
minutes (it checks `Init` first), or about 70 s from a snapshot of `Init` (`--snapshot FILE` in place of `--env`,
development mode, labelled so). What you write in natural LeanForth leaves things
out that Lean fills in: hidden (implicit) arguments, universe levels, which `+` and which `0` you mean. The
elaborator (`src/front/elab-pending.fs`, `elab-app.fs`, `elab-term.fs`, `elab-decl.fs`) fills them in, step for
step as Lean 4.35.0's elaborator does ([S1_INTERFACE.md](../design/S1_INTERFACE.md),
[FE1E_APPLICATIONS.md](../design/FE1E_APPLICATIONS.md)). It is **untrusted**: what it builds goes to the kernel,
which checks every declaration as it checks Lean's own exports. A mistake in the elaborator can change what a
statement says (the comparisons with pinned Lean below guard that); it can never make a wrong proof accepted.

## One example in three forms

- **Mathematics:** $0 + 0 = 0$ (natural numbers), by reflexivity.
- **LeanForth** (`tests/front/s1-rfl.lf`):

  ```text
  theorem t
    0 0 + 0 =
  := by
    by-rfl
  end t
  ```

- **Lean** (`tests/front/s1-rfl.lean`): `theorem t : 0 + 0 = 0 := by rfl`

You wrote three numerals, `+` and `=`. Lean's numerals are polymorphic: each `0` becomes `@OfNat.ofNat ?T 0 ?i`
with a hole `?T` for its type and an instance problem `OfNat ?T 0`; `+` is `HAdd.hAdd` with hidden types and an
instance `HAdd ?α ?β ?γ`; `=` takes a hidden type. Nothing says `Nat` yet, so the problems wait. At the end of
the statement Lean's **default instances** fire, in Lean's order: `instHAdd` for `HAdd` first (its `[Add ?α]`
cannot be found while `?α` is open, so it is rolled back), then `instOfNatNat` makes the first numeral a `Nat`,
then `instHAdd` again with `Add Nat` found by **instance search**. The statement LeanForth builds is Lean's, node
for node:

```text
(app (app (app Eq.{1} Nat.{}) (app (app (app (app (app (app HAdd.hAdd.{0,0,0} Nat.{}) Nat.{}) Nat.{})
  (app (app instHAdd.{0} Nat.{}) instAddNat.{})) (app (app (app OfNat.ofNat.{0} Nat.{}) 0)
  (app instOfNatNat.{} 0))) (app (app (app OfNat.ofNat.{0} Nat.{}) 0) (app instOfNatNat.{} 0))))
  (app (app (app OfNat.ofNat.{0} Nat.{}) 0) (app instOfNatNat.{} 0)))
```

`by-rfl` then builds `@Eq.refl.{1} Nat (0 + 0)`, and the kernel checks it. Run it:

```text
$ bin/leanforth check --env tests/front/s1-slice.ndjson \
    --elab-data tests/front/s1-slice.elab.ndjson tests/front/s1-rfl.lf
...
t: accepted; axioms: none
548 declarations: 548 accepted
accepted: 548; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED
```

(exit 0; the library's own verdicts are left out here.) Its wrong twin `tests/front/s1-rfl-wrong.lf`
(`0 0 + 1 =`) stops at `by-rfl` with Lean's own message, `Tactic `rfl` failed: The left-hand side 0 + 0 is not
definitionally equal to the right-hand side 1` (exit 4), and `tests/front/s1-check.lf` (`0 0 + 0 = #check`, S1's
midpoint) prints `0 + 0 = 0 : Prop` and exits 0. `tests/front/check_elab.py` runs all three and compares the nine
theorems of `tests/front/s1-now.lf` (`t` among them) with pinned Lean node for node and its `#check` lines with
Lean's (Lean prints `Eq.refl Nat.zero`, without `@`: LeanForth's printer shows a hidden argument when it cannot
read its binder's kind; the term is the same).

## What runs today and what waits

| Form | Example | Today |
| --- | --- | --- |
| A constant, a variable, an application with hidden arguments | `n Eq.refl`, `n Nat.succ` | elaborated as Lean does |
| Numerals, `+` and `=` (Lean's `binop%`, `binrel%`), default instances | `0 0 + 0 =`, `2 2 + 4 =`, `n n + n n + =` | elaborated as Lean does |
| A term proof, `by-rfl`, `by-exact` | `tests/front/s1-now.lf` | accepted by the kernel |
| `#check` | `0 0 + 0 = #check` | prints `0 + 0 = 0 : Prop` |
| Induction with alternatives, rewriting (S2) | `tests/front/01-zero-add-rw.lf`, `tests/front/ps-*.lf` | accepted by the kernel, the proof term pinned Lean's node for node |

### Induction and rewriting (plan S2, branch `s2-tactics`)

The worked example, $0 + n = n$ for every natural number $n$, by induction on $n$: for $n = 0$, $0 + 0 = 0$ by
computation; for $n = k + 1$, $0 + (k + 1) = (0 + k) + 1$ by the definition of $+$ (`Nat.add_succ`) and
$(0 + k) + 1 = k + 1$ by the induction hypothesis $0 + k = k$.

```text
theorem zero_add''   Nat explicit: n   0 n + n =
:= by
  n by-induction-with
  | zero =>       by-rfl
  | succ k ih =>  by-rw[ ' Nat.add_succ ih ]
  by-end
end zero_add''
```

Lean: `theorem zero_add'' (n : Nat) : 0 + n = n := by induction n with | zero => rfl | succ k ih => rw [Nat.add_succ, ih]`.

```console
$ bin/leanforth check --env tests/front/s2-slice.ndjson \
    --elab-data tests/front/s2-slice.elab.ndjson tests/front/01-zero-add-rw.lf
...
zero_add'': accepted; axioms: none
```

`n by-induction-with` finds `Nat.recAux` (the eliminator the elaboration data registers for `Nat`), builds the
motive `fun n => 0 + n = n` and one goal per case, `zero` and `succ`; `| succ k ih =>` names the case's fields
`k` and `ih : 0 + k = k`. `by-rw[ ' Nat.add_succ ih ]` rewrites with `Nat.add_succ` (its left side `?n + Nat.succ
?m` found as `0 + (k + 1)`), then with `ih`, then closes `Nat.succ k = k + 1` by `rfl` at reducible
transparency, as Lean's `rw`. The term LeanForth builds (`Nat.recAux`, `Eq.mpr`, `congrArg`, `id`) is pinned
Lean's node for node (`tests/front/check_s2.py`, against `tests/front/s2-proofs.lean`), and the kernel checks
it; with the full `Init` snapshot and its elaboration data the same files are accepted too. A wrong proof stops
with Lean's message: `| suc k ih =>` is error 206, "Invalid alternative name `suc`: Expected `succ`";
`by-rw[ ' Nat.mul_succ ]` is 215, "Tactic `rewrite` failed: Did not find an occurrence of the pattern", the
pattern, the target and the goal. The owner's proof set (`tests/front/ps-*.lf`: $\mathrm{succ}\,n + m =
\mathrm{succ}(n + m)$, $n + m = m + n$, $n + (m + k) = (n + m) + k$, $n(m + k) = nm + nk$ and
$|xs \mathbin{+\!\!+} ys| = |xs| + |ys|$) is accepted the same way; where appendix G of
`docs/design/S2_INTERFACE.md` closes a case by `rfl` (for $n + (m + k)$ and $n(m + k)$, goal
`n + (m + 0) = n + m + 0`), `by-rfl` still stops there with error 93, "not supported yet", although S2 merge B
(smart unfolding) is merged; the files rewrite with `Nat.add_zero` or `Nat.mul_zero` instead, a form pinned Lean
accepts too. Not yet: `by-case:` (still error 80 now that merge B is merged; plan FE1g-5), `++` as a word
(`HAppend.hAppend` is written out), `←`, `at h`, `using`, `generalizing`.

The unit tests (`tests/front/elab.fs`) also pin the order of events against pinned Lean's (golden traces of
`0 + 0 = 0` and `0 + n = n`): the problems made, the default instances tried and rolled back, and where lazy
unfolding opens `outParam` (never for `0 + 0 = 0`, three times for `0 + n = n`, as Lean's `isDefEq.delta`
trace shows). Lean's `#check` also type-checks its term (`Meta.check`, where Lean unfolds `outParam` once for
`0 + 0 = 0`); LeanForth does not port that check yet (S2), its `#check` only prints. On the S1 slice a class whose
search tries an instance the slice leaves out answers 119 (not supported) where all of `Init` would decide.

## `#check`, the work limit, errors

- `TERM #check` (a natural word, between declarations) elaborates TERM with no expected type and prints
  `TERM : TYPE`. Inside a declaration in a term position it is error 140, Lean's "unexpected token '#check';
  expected term". Inside a tactic block it is error 141: Lean's parser ends the block at `#check` (a command),
  reports the goals left unsolved or accepts the proof as far as it goes, then runs `#check`; in LeanForth the
  block runs to `end NAME`, so put `#check` after it. A text of only `#check` lines checks nothing: it ends with
  `nothing checked by the kernel` and exit 0, as Lean. A constant alone (`Nat.zero #check`, where Lean prints a
  signature) and a term with a hole left are not supported yet (137).
- `--elab-fuel N` limits the elaborator's steps per declaration (elaboration, instance problems, unification,
  reduction and tactic steps), default 100,000,000; out of them is error 138, exit 3. `--fuel N` stays the
  kernel's.
- Lean's errors keep Lean's meaning and their own codes: 125 failed to synthesize, 126 typeclass instance problem
  is stuck, 127 and 128 numerals are data, 129 failed to assign a synthesized instance, 130 type expected; a
  search's own refusals keep their codes (110-121, `synth.fs`). Forms
  not ported yet answer *not supported* (exit 2) with the plan that ports them: 131 a coercion (FE4), 132
  postponing (FE2), 133 an implicit lambda (FE2), 134 `optParam`/`autoParam` (FE2), 135 an eliminator (FE5), 136
  a binder kind the declaration does not give (S5), 137 `#check` forms (FE2), 139 any other step (FE2-FE5, S2).
  The catalogue is [LEANFORTH_WORDS.md](../programming/LEANFORTH_WORDS.md).

## Trust and limits

Nothing the elaborator says is a verdict. The kernel checks the declarations it hands over; `#check` output is
presentation and never reaches the kernel (Lean's `Meta.check` of it is not ported yet, S2). The library facts the
elaborator reads (instances, default instances, tags) come from the elaboration data that pinned Lean writes
(`--elab-data`); without it the elaborator answers 139.
