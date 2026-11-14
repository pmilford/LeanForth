# The elaborator: what LeanForth fills in

Status (2026-11-13, branch `s1-elab`, plan slice S1): **written and tested alone** (the stages of
[DONE_CHECKER.md](../development/DONE_CHECKER.md)); not done. What you write in natural LeanForth leaves things
out that Lean fills in: hidden (implicit) arguments, universe levels, which `+` and which `0` you mean. The
elaborator (`src/front/elab-pending.fs`, `elab-app.fs`, `elab-term.fs`, `elab-decl.fs`) fills them in, step for
step as Lean 4.35.0's elaborator does ([S1_INTERFACE.md](../design/S1_INTERFACE.md),
[FE1E_APPLICATIONS.md](../design/FE1E_APPLICATIONS.md)). It is **untrusted**: what it builds goes to the kernel,
which checks every declaration as it checks Lean's own exports. A mistake in the elaborator can change what a
statement says (the comparisons with pinned Lean below guard that); it can never make a wrong proof accepted.

## One example in three forms

- **Mathematics:** for every natural number $n$, $\operatorname{succ}(n) = \operatorname{succ}(n)$.
- **LeanForth** (`tests/front/s1-now.lf`):

  ```text
  theorem succ_eq
    Nat explicit: n
    n Nat.succ n Nat.succ =
  := by
    by-rfl
  end succ_eq
  ```

- **Lean** (`tests/front/s1-now.lean`): `theorem succ_eq (n : Nat) : Nat.succ n = Nat.succ n := by rfl`

You wrote `=` with two arguments. The elaborator finds that `Eq` takes a hidden type argument `{α : Sort u}` (from
`Eq`'s declared type), makes a hole for it, fills it with `Nat` from the type of `Nat.succ n`, and settles the
level `u := 1`. The statement it builds is Lean's, node for node:

```text
(pi Nat.{} (app (app (app Eq.{1} Nat.{}) (app Nat.succ.{} #0)) (app Nat.succ.{} #0)))
```

`by-rfl` then builds `fun n => @Eq.refl.{1} Nat (Nat.succ n)`, and the kernel checks it. Run it:

```text
$ bin/leanforth check --env tests/front/s1-slice.ndjson \
    --elab-data tests/front/s1-slice.elab.ndjson tests/front/s1-now.lf
Nat.zero = Nat.zero : Prop
@Eq.refl Nat Nat.zero : Nat.zero = Nat.zero
...
succ_eq: accepted; axioms: none
...
accepted: 552; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED
```

(exit 0; the library's own verdicts are left out here.) `tests/front/check_elab.py` compares the five theorems of
that file with pinned Lean node for node and its `#check` lines with Lean's (Lean prints `Eq.refl Nat.zero`, without
`@`: LeanForth's printer shows a hidden argument when it cannot read its binder's kind; the term is the same).

## What runs today and what waits

| Form | Example | Today |
| --- | --- | --- |
| A constant, a variable, an application with hidden arguments | `n Eq.refl`, `n Nat.succ` | elaborated as Lean does |
| `=` (Lean's `binrel%`) of terms of a known type | `Nat.zero Nat.zero =` | elaborated as Lean does |
| A term proof, `by-rfl`, `by-exact` on such statements | `tests/front/s1-now.lf` | accepted by the kernel |
| `#check` of such a term | `Nat.zero Nat.zero = #check` | prints `Nat.zero = Nat.zero : Prop` |
| Numerals, `+` | `0 0 + 0 = #check` | **pending**: error 139 (below) |

Numerals need **instance search** (Lean's `OfNat Nat 0` gives `instOfNatNat 0`; plan FE1e5, `synth.fs`), and `+`
needs Lean's **lazy unfolding** of `outParam` (S2's merge A). Until both land, S1's own files stop, never with a
different term:

```text
$ bin/leanforth check --env tests/front/s1-slice.ndjson \
    --elab-data tests/front/s1-slice.elab.ndjson tests/front/s1-check.lf
error: unsupported: the LeanForth text was not checked: error 139 at line:col 10:11 (token `#check`):
not supported yet: an elaboration step (plans FE2-FE5, S2); see line:col 10:1
```

When they land, `tests/front/s1-check.lf` (`0 0 + 0 = #check`) prints `0 + 0 = 0 : Prop` and exits 0 (S1's
midpoint), `tests/front/s1-rfl.lf` (`theorem t 0 0 + 0 = := by by-rfl end t`) is accepted, and its wrong twin
`0 0 + 1 =` stops at `by-rfl` with Lean's "Tactic `rfl` failed". The unit tests (`tests/front/elab.fs`) already
run those paths with stand-ins for instance search: numerals through default instances (`0 0 =` gives
`@Eq.{1} Nat (OfNat 0) (OfNat 0)`), and the golden traces of `0 + 0 = 0` and `0 + n = n` up to where unfolding
is needed.

## `#check`, the work limit, errors

- `TERM #check` (a natural word, between declarations) elaborates TERM with no expected type and prints
  `TERM : TYPE`. A text of only `#check` lines checks nothing: it ends with `nothing checked by the kernel` and
  exit 0, as Lean. A constant alone (`Nat.zero #check`, where Lean prints a signature) and a term with a hole
  left are not supported yet (137).
- `--elab-fuel N` limits the elaborator's steps per declaration (elaboration, instance problems, unification,
  reduction and tactic steps), default 100,000,000; out of them is error 138, exit 3. `--fuel N` stays the
  kernel's.
- Lean's errors keep Lean's meaning and their own codes: 125 failed to synthesize, 126 typeclass instance problem
  is stuck, 127 and 128 numerals are data, 129 a synthesized instance that does not fit, 130 type expected. Forms
  not ported yet answer *not supported* (exit 2) with the plan that ports them: 131 a coercion (FE4), 132
  postponing (FE2), 133 an implicit lambda (FE2), 134 `optParam`/`autoParam` (FE2), 135 an eliminator (FE5), 136
  a binder kind the declaration does not give (S5), 137 `#check` forms (FE2), 139 any other step (FE2-FE5, S2).
  The catalogue is [LEANFORTH_WORDS.md](../programming/LEANFORTH_WORDS.md).

## Trust and limits

Nothing the elaborator says is a verdict. The kernel checks the declarations it hands over; `#check` output is
presentation and never reaches the kernel (Lean's `Meta.check` of it is not ported yet, S2). The library facts the
elaborator reads (instances, default instances, tags) come from the elaboration data that pinned Lean writes
(`--elab-data`); without it the elaborator answers 139.
