# ADR 0014: Definitional equality as Lean's kernel decides it

Status: task **4.2.2a implemented and approved** [kernel] by the owner on 2026-11-04 ([decisions](../project/OWNER_DECISIONS.md#free-variables-approved-2026-11-04)); **4.2.2b and 4.2.2c implemented** 2026-11-04, their gate pending; **4.2.2d implemented** 2026-11-04, its gate pending (see [Progress](#progress)); 4.2.2e next; **4.2.4 (eta) and 4.2.5 (proof irrelevance) implemented** 2026-11-05 on a branch, their gate pending. **Accepted** by the owner on 2026-11-03 (G5 and Q-A to Q-D as recommended; Q-E: within twice Lean's one-thread time before phase 6, then close the gap, by algorithms first — [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)). Previously: **proposed**, 2026-11-03 (plan task 4.1.1, with the sections task
4.1.3 asks for: eta, proof irrelevance, `let` and metadata). A [kernel]
design: it passes the review gate in `AGENTS.md` only with the owner's
approval of the plain-language summary below, and the code that implements
it (plan tasks 4.2.2–4.2.7) needs its own gate with its test results.
Nothing in `src/` changes with this record. It builds on ADR 0003 and its
Amendment 1 (comparing under binders), ADR 0011 with its Amendment 1 (Lean's
levels) and Amendment 2, ADR 0012 (the checked environment), ADR 0013 (the
derivation log, accepted) and ADR 0016 (the compact store, accepted), and
answers gate question G5 of [the first checker's gate](../reviews/FIRST_CHECKER_GATE.md#questions-for-you)
(do theorems unfold?).

## Summary in plain words

**What this is about.** To check a proof, a checker must often decide
whether two expressions *mean the same thing by definition*: whether
`twice A` and `A → A` are the same claim when `twice` is *defined* as
`fun A => A → A`, or whether `fun x => f x` and `f` are the same function.
Lean calls this *definitional equality*. Its kernel decides it with one
fixed procedure, a few hundred lines of C++ in `type_checker.cpp`. That
procedure is deliberately *incomplete*: there are true equalities it does
not find, and it finds the ones it does in a particular order. Because the
owner's rule is that LeanForth gives exactly Lean's verdicts ("too soon to
improve Lean; working worse than Lean is of no use"), LeanForth must copy
the *procedure*, step by step, not the mathematics behind it. Where Lean's
procedure misses a true equality, LeanForth misses it too, and the case is
recorded in [BEYOND_LEAN.md](../project/BEYOND_LEAN.md).

**How Lean decides, in six steps.** Asked whether `t` and `s` are equal,
Lean's kernel:

1. answers *yes* at once if they are written the same way (ignoring the
   names of bound variables) or were found equal before; two `Sort`s, two
   `fun`s or two "for all"s are decided at once, part by part;
2. simplifies both without opening any definition: it applies functions to
   their arguments (*beta*) and replaces local definitions by their values
   (*zeta*, `let`);
3. if `t` is a proof, answers by comparing the two *statements* only: any
   two proofs of the same statement are equal (*proof irrelevance*);
4. otherwise opens definitions lazily, one side at a time, the side with
   the "taller" definition first (*lazy delta reduction*); each definition
   carries a *height* (how deep it is built on other definitions), and
   *abbreviations* open first, theorems and definitions marked *opaque*
   last; when both sides start with the same definition it first tries the
   arguments, and opens both only if they differ;
5. once neither side can be opened, compares them part by part (function
   with function, argument with argument);
6. finally tries *eta* (`f` equals `fun x => f x`), and the rules for
   structures, single-value types and string literals, which need data
   types and wait for phase 5.

**What this record decides.**

1. **Port, do not approximate.** LeanForth implements these steps as
   copies of Lean's functions, in Lean's order, with Lean's caches. A *no*
   from the copy is Lean's *no*, so it becomes *rejected* with Lean's own
   reason. The cautious rules of ADR 0011 that answer *unknown* wherever
   unfolding, eta or proof irrelevance might matter (K1–K3) and the
   rejection analysis that works around them (D1–D5, S1, S2, S4, F1 on
   "rigid" terms) are replaced by the copy.
2. **Theorems unfold, as in Lean** (G5). Lean's kernel unfolds a theorem
   like a definition, only last. Opaque declarations and statements
   assumed without proof never unfold. LeanForth does the same, so every
   theorem's proof stays in memory (ADR 0016's decision stands).
3. **Free variables inside the checker.** When the checker steps inside a
   `fun` or a "for all", it names the bound variable with a fresh *free
   variable*, as Lean does, instead of counting binders. This is what lets
   the caches be exactly Lean's.
4. **Caches exactly as Lean's**, cleared after every declaration, never
   shared between declarations, environments or workers; a test mode turns
   them off and must give the same verdicts.
5. **What waits for phase 5:** computing with data types (recursors),
   number and string literals, projections, quotients, and the eta rule
   for structures. Until then a declaration that needs them is
   *unsupported*, as today; and a constant that merely has one of the names
   Lean's kernel treats specially (`Nat.succ`, `Nat.add`, …) makes the
   answer *unknown*.

**Evidence.** Fifty cases run with the pinned Lean 4.35.0 on every
`make check` (`tests/reference/definitional-equality.lean`): Lean's verdict
on each, and, for the 32 it accepts, *how many times Lean opened each
definition* — which shows which side Lean's lazy strategy opened, not only
the answer. Every prediction of this record about Lean's order was
confirmed. Each row also says what LeanForth must answer.

**Risks.** (1) A copy can still differ from Lean in a detail; the tests
compare not only verdicts but also Lean's unfolding counts, and a
randomized comparison against Lean's kernel is part of the plan. (2) The
switch to free variables touches the inference code written in phase 2.
(3) Lean's procedure can take very long on some proofs; LeanForth then
says *exhausted*, never a verdict. (4) Theorem unfolding keeps all proofs
in memory.

**Recommendation.** Approve the design, with the answers recommended in
[Questions for the owner](#questions-for-the-owner): it is the most direct
way to give Lean's exact verdicts, every rule is a line of Lean's own code,
and the unfolding counts give a sharper test than verdicts alone.

## The same idea in three forms

The row `delta.argument-after-unfolding` of the evidence, written three
ways.

- **Mathematics.** Define *twice*(A) to be A → A. For propositions A and B:
  if k turns a proof of *twice*(A) into a proof of B, then k applied to the
  identity proof (λx. x : A → A) proves B — because *twice*(A) is, by
  definition, A → A.
- **LeanForth** (the [syntax words](../user/LEANFORTH_SYNTAX.md); this text
  was run through `src/author/` on 2026-11-03 and, printed back, gives the
  declarations of the Lean text below — though LeanForth's printer shows
  the arrow `twice A → B` as `∀ (a : twice A), B`, where Lean's `#print`
  shows `twice A → B`; the checker cannot yet unfold `twice`):

  ```forth
  def twice
    Prop explicit: A
    Prop
  :=
    A A ->
  end twice

  theorem useTwice
    Prop explicit: A   Prop explicit: B
    twice A $ B ->  explicit: k
    B
  :=
    k  A explicit: x  x fun  $
  end useTwice
  ```

- **Lean** (accepted by Lean 4.35.0):

  ```lean
  def twice (A : Prop) : Prop := A → A
  theorem useTwice (A B : Prop) (k : twice A → B) : B := k (fun x => x)
  ```

To check `k (fun x => x)`, Lean compares the argument's type `A → A` with
the type `k` expects, `twice A`. They are not written the same; neither is
a proof; `twice A` starts with a definition, `A → A` does not, so Lean
opens `twice` once, gets `A → A`, and the two are equal. The table records
Lean's count: `dqTwice:1`.

## The referee

Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (the
`lean --githash` of the pinned toolchain). The C++ kernel is not in the
toolchain, so its files were read from
`raw.githubusercontent.com/leanprover/lean4/<commit>/src/` on 2026-11-03;
SHA-256 of each under [Reproduction](#reproduction). `type_checker.cpp`,
`type_checker.h`, `declaration.h`, `declaration.cpp`, `environment.cpp`,
`inductive.h`, `quot.h`, `kernel_exception.h`, `expr_eq_fn.*`,
`instantiate.cpp` and `level.cpp` are byte for byte the files ADR 0003,
ADR 0011 and its Amendment 1 cite. Line numbers below refer to these files;
"tc" is `src/kernel/type_checker.cpp`. The Lean-side files are the
toolchain's own `src/lean/Lean/Environment.lean` and `Declaration.lean`.
The folder `src/kernel/` at this commit has no `equiv_manager.*`: Lean
4.35.0 has no union-find cache (see [Caches](#caches)).

## Lean's procedure, function by function

### Where comparisons are made

`is_def_eq(t, s)` is called only on terms the kernel has already checked,
always with the *inferred* type on the left and the *expected* one on the
right (ADR 0003 Amendment 1, evidence item 3):

| Caller | Comparison | Failure |
| --- | --- | --- |
| `infer_app` (tc 173–187) | argument's type, function's domain | `appTypeMismatch` |
| `add_definition`, `add_theorem`, `add_opaque` (`environment.cpp` 184–186, 204–206, 218–220) | value's type, declared type | `declTypeMismatch` |
| `infer_let` (tc 213–220) | value's type, the `let`'s declared type | `letTypeMismatch` |
| inside the procedure | `is_def_eq_binding` (domains, bodies), `is_def_eq_app` (functions, arguments), proof irrelevance (the two statements), eta (`t` against the expanded `s`) | — |

Two more places reduce without comparing: `ensure_sort_core` and
`ensure_pi_core` (tc 62–83) call `whnf` when a type is not visibly a
`Sort` or a `Π`, and fail with `typeExpected` or `funExpected`; `is_prop`
(tc 383–389) calls `ensure_sort(infer_type(e))` and tests the level with
`normalizes_to_zero`.

### Structural equality (`==`)

`operator==` on terms is `is_equal` (`expr_eq_fn.h` 14–16,
`expr_eq_fn.cpp` 123–125), which ignores binder names and binder
annotations (98–103) but **compares a `let`'s non-dependence flag** (109)
and an `mdata` node's data (72–75); levels are compared structurally
(`sort_level(a) == sort_level(b)`, 53, and per constant, 81–84). Every
kernel cache uses this equality for its keys (`expr_maps.h` 15,
`std::equal_to<expr>`; pairs: `expr.h` 164–166).

### `whnf_core`: reduction without unfolding (tc 468–551)

- **Already normal** (473–488): bound variables, `Sort`, `Π`, `λ`,
  constants, literals, and free variables that are not `let` variables
  are returned as they are. `mdata` is looked through (478–479).
- **Cache** (490–493, 547–549): results are cached only when neither
  `cheap_rec` nor `cheap_proj` is set.
- **Beta** (511–524): for `f a₁ … aₙ`, `f` is reduced first with
  `whnf_core`; if it is a `λ`, as many leading `λ`s as there are arguments
  are instantiated **at once** (`instantiate(body, m, args)`), the
  remaining arguments re-applied, and the result reduced again. If `f`
  reduced to something else, the application is rebuilt and reduced again
  (537–539).
- **Zeta** (542–544): `let x := v; b` becomes `b[v/x]`, reduced again; a
  `let` *variable* in the local context is replaced by its value
  (`whnf_fvar`, 409–417; `is_let_fvar`, 456–463).
- **Iota and quotients** (525–536): if the head did not change,
  `reduce_recursor` (393–407) tries quotient reduction (`quot_reduce_rec`,
  only once `Quot` is initialised) and recursor reduction
  (`inductive_reduce_rec`, `inductive.h` 76–120), which puts the major
  premise into `whnf` (93) — *phase 5*.
- **Projections** (504–510): `reduce_proj` (444–454) reduces the
  structure with `whnf_core` (`cheap_proj`) or `whnf` and takes the field
  of a constructor application (`reduce_proj_core`, 420–441) — *phase 5*.

### `whnf`: with unfolding (tc 706–743)

Easy cases as above (708–722; `λ` and constants are *not* easy here), then
the `whnf` cache (724–727), then a loop (729–742): `whnf_core`; then
`reduce_nat` (672–703) — `Nat.succ` of a literal and fourteen binary `Nat`
operations on literals, *phase 5* — and otherwise `unfold_definition` of
the head; stop when neither applies, and cache the result. Note that
`whnf`'s `reduce_nat` runs whether or not the term has free variables.

### Delta: which constants unfold

- `is_delta` (tc 555–563): the head is a constant found in the
  environment whose `has_value()` holds and which is given as many
  universe arguments as it has parameters.
- `constant_info::has_value(allow_opaque = false)` (`declaration.h`
  466–468) is **true for definitions and theorems**, false for opaque
  declarations, axioms, inductive types, constructors, recursors and the
  quotient constants. So **theorems unfold**; opaque declarations and
  axioms never do; recursors and `Quot.lift`/`Quot.ind` reduce only by
  their own rules (iota, quotient reduction).
- `unfold_definition_core` (565–586) returns the value with the universe
  arguments substituted (`instantiate_value_lparams`, `instantiate.cpp`
  256–264; the stored value itself when there are no universe arguments or
  parameters) and caches it in `m_unfold` when there are universe arguments
  (573–579). It records the unfolding for kernel diagnostics (570–572),
  which is how the evidence counts it. `unfold_definition` (589–602)
  re-applies the arguments.
- **Hints** (`declaration.h` 15–54; `declaration.cpp` 24–49, 294–299):
  `opaque`, `abbrev` or `regular h`. A *theorem's* hint is always `opaque`
  (`get_hints` returns the opaque hint for anything that is not a
  definition). The kernel takes a definition's hint as given; it does not
  recompute heights (`add_definition`, `environment.cpp` 160–190, never
  reads them; the elaborator computes `regular (h + 1)` from the tallest
  definition the value uses, as `get_max_height`, `declaration.cpp`
  193–209, does for the C++ helpers). Rows `delta.inverted-heights` and
  `delta.equal-heights` give a definition a wrong height and Lean accepts
  it: heights steer the search, they are not checked.
- **Elaborator attributes are not kernel opacity.** `@[irreducible]`,
  `@[reducible]` and `@[implemented_by]` live in the elaborator; the kernel
  still unfolds such a definition (row `whnf.irreducible-definition`). And
  Lean's *own front end* reports a theorem as having no value unless asked
  (`ConstantInfo.value?`/`hasValue`, `Lean/Declaration.lean` 483–500, with
  `allowOpaque := false`): that is the elaborator's view, and probably the
  source of the earlier belief that theorems never unfold. The kernel's
  `has_value` differs.

### `is_def_eq` and the order of `is_def_eq_core`

`is_def_eq(t, s)` (tc 1209–1214) calls `is_def_eq_core` and, on success
only, records the pair in the success cache. `is_def_eq_core` (1132–1207)
tries, in this order, and stops at the first decisive answer:

| # | Step | Lines | Decides |
| --- | --- | --- | --- |
| 1 | `quick_is_def_eq(t, s)` | 1135–1136 | see below |
| 2 | `s` is the constant `Bool.true` and `t` has no free variables (or eager mode): `whnf(t)` is `Bool.true` | 1142–1146 | yes only (*phase 5*, name-matched) |
| 3 | `t_n = whnf_core(t, cheap_proj)`, `s_n` likewise; if either changed, `quick_is_def_eq(t_n, s_n)` | 1155–1161 | yes or no |
| 4 | proof irrelevance on `t_n`, `s_n` | 1163–1164 | yes or no when `t_n` is a proof |
| 5 | `lazy_delta_reduction(t_n, s_n)`, which updates both | 1166–1168 | yes or no |
| 6 | both the same constant with equivalent levels | 1170–1172 | yes only |
| 7 | both the same free variable | 1174–1175 | yes only |
| 8 | both projections of the same field: `lazy_delta_proj_reduction` | 1177–1182 | yes only (*phase 5*) |
| 9 | `whnf_core` with full projection reduction; if either changed, start again on the results | 1185–1188 | — |
| 10 | `is_def_eq_app`: same number of arguments, functions and all arguments equal, in order | 1191–1192 | yes only |
| 11 | eta: `try_eta_expansion` both ways | 1194–1195 | yes only |
| 12 | structure eta: `try_eta_struct` both ways | 1197–1198 | yes only (*phase 5*) |
| 13 | string literal against `String.ofList …` | 1200–1201 | yes or no (*phase 5*) |
| 14 | unit-like types | 1203–1204 | yes only (*phase 5*) |
| 15 | otherwise | 1206 | **no** |

**`quick_is_def_eq`** (802–826): *yes* if `t == s` or the pair succeeded
before (`succeeded_before`, 927–937); for two `λ`s or two `Π`s,
`is_def_eq_binding`'s answer; for two `Sort`s, level equivalence
(`is_def_eq(level)`, 781–787: `is_equivalent`, ADR 0011 Amendment 1); two
`mdata`s compare their contents; two literals their values; otherwise
undecided.

**`is_def_eq_binding`** (752–779): walks both telescopes while both are
binders of the same kind; a domain pair that is not `==` must be
`is_def_eq` (else *no*); the bound variable gets the *right* operand's
domain, or the placeholder constant `dontcare` (772, 1286) when neither
body uses it; then the bodies (ADR 0003, Amendment 1, B1–B2).

**`is_def_eq_app`** (878–895): `get_app_args` on both; functions first,
then the counts, then arguments left to right, stopping at the first
unequal pair.

### Proof irrelevance (tc 899–906)

`t_type = infer_type(t)` (inference without checking); if `is_prop(t_type)`
— the type of `t`'s type is `Sort l` with `l` zero for every assignment of
the parameters (`normalizes_to_zero`) — the answer is
`is_def_eq(t_type, infer_type(s))`, **yes or no**: when `t` is a proof,
nothing else is tried (no unfolding, no eta). Only `t`'s side is tested; if
`t` is not a proof the step is undecided even when `s` is one. Rows:
`proof-irrelevance.same-statement` (accepted),
`.statement-after-unfolding` (accepted; the statements `dqTwice A` and
`A → A` are equal only after unfolding), `.not-proofs` (the same shape over
a `Type`: rejected), `.any-sort` (`A : Sort u` is a proposition only when
`u = 0`, so `h k : A` are not known proofs: rejected).

### Lazy delta reduction (tc 959–1075)

`lazy_delta_reduction` (1055–1075) loops:

1. `is_def_eq_offset` (1043–1052): both `Nat.zero` or literal 0, *yes*;
   both a successor (`Nat.succ x` or a nonzero literal), compare the
   predecessors with `is_def_eq_core`, *yes or no* (*phase 5*,
   name-matched).
2. If neither side has free variables (or eager mode): if `reduce_nat`
   computes `t_n`, compare the result with `s_n`; else if it computes
   `s_n`, compare `t_n` with it (1060–1066; *phase 5*).
3. One `lazy_delta_reduction_step`; continue, or return its answer.

`lazy_delta_reduction_step` (966–1023), with `d_t = is_delta(t_n)` and
`d_s = is_delta(s_n)`:

| Situation | What Lean unfolds |
| --- | --- |
| neither unfolds | stop: *undecided* (`DefUnknown`); `is_def_eq_core` goes on at step 6 with the partly unfolded terms |
| only `t_n` unfolds | `s_n` instead, if it is an application of a projection that `whnf_core` reduces (`try_unfold_proj_app`, 950–957; *phase 5*); otherwise `t_n` |
| only `s_n` unfolds | symmetrically |
| both; `compare(hint t, hint s) < 0` | `t_n` |
| both; `> 0` | `s_n` |
| both; `= 0` | both — but first, if both are applications of **the same declaration** (`is_eqp` of the two `constant_info`s) with a **regular** hint, and this pair has not failed before, compare the universe arguments (`is_equivalent`) and the arguments (`is_def_eq_args`, 830–838: **last argument first**); all equal: *yes*; otherwise record the pair in the failure cache and unfold both |

`compare` (`declaration.cpp` 24–49): two regular hints — the greater
height unfolds, equal heights both; two hints of the same other kind —
both; different kinds — never the `opaque` side first, otherwise the
`abbrev` side first. Each unfolded side goes through
`whnf_core(…, cheap_proj)` (983, 990, 995, 997, 1013–1014); then
`quick_is_def_eq` on the pair answers *yes*, *no*, or continue
(1017–1021).

What the evidence shows (unfold counts of accepted rows):

| Row | Left (inferred) | Right (claimed) | Lean unfolded |
| --- | --- | --- | --- |
| `delta.abbrev-first` | `dqTwice A` (height 1) | `dqAbbr A` (abbreviation) | `dqAbbr` once |
| `delta.higher-first` | `dqTwice A` (1) | `dqHigh A` (2) | `dqHigh` once |
| `delta.equal-heights` | `dqTwice A` (1) | `dqSame A` (1) | both, then `dqTwice` again: `dqSame` 1, `dqTwice` 2 |
| `delta.inverted-heights` | `dqTwice A` (1) | `dqLow A` (claims 0) | `dqTwice` first (uselessly), then `dqLow`, then `dqTwice` again |
| `delta.opaque-hint-last` | `dqTwice A` (1) | `dqOpq A` (opaque hint) | the same: the opaque-hinted side waits |
| `delta.same-head-arguments` | `dqTwice ((fun T => T) A)` | `dqTwice A` | nothing: the arguments are equal by beta |
| `delta.same-head-arguments-differ` | `dqFst A B` | `dqFst A A` | `dqFst` twice: the arguments differ, both unfold to `A` |
| `delta.same-head-abbrev` | `dqAbbFst A B` | `dqAbbFst A ((fun T => T) B)` | `dqAbbFst` twice: no argument test for abbreviations |
| `delta.same-head-levels-differ` | `dqLift.{0} A` | `dqLift.{1} A` | `dqLift` twice: different universe arguments, equal values |
| `delta.chain` | `dqC0 A` (1) | `dqC5 A` (6) | `dqC5` … `dqC1` once each, never `dqC0` |

Rows `delta.same-head-arguments-differ` and `delta.same-head-levels-differ`
are the warning for any shortcut: the same head with different arguments,
or with different universe arguments, is **not** a reason to answer *no*
while the head can unfold (contrast
`delta.same-head-levels-differ-opaque`, rejected: an opaque declaration
never unfolds, so there the levels decide).

### Eta (tc 841–853; `type_checker.h` 94–96)

`try_eta_expansion(t, s)` tries `t` a `λ` and `s` not, then the reverse:
`s`'s type is put into `whnf`; if it is a `Π` with domain `D`,
`fun x : D => s x` is compared with the `λ` by `is_def_eq`. Eta is tried
only at step 11, after lazy delta has unfolded both sides and `is_def_eq_app`
failed. Rows: `eta.lambda-in-claim`, `eta.lambda-in-proof` (both orders),
`eta.after-unfolding` (`dqApp A B f` unfolds to `f`, then eta),
`eta.two-binders` (eta applied twice through the recursion),
`eta.wrong-function` (rejected).

### `let` and inference (tc 125–230)

`infer_let` (208–230) checks the declared type is a type and the value's
type equals it (`letTypeMismatch`, row `let.wrong-value`), then adds a
*local definition* (a free variable with a value) and infers the body;
the result is abstracted back over the `let` variables
(`m_lctx.mk_pi(fvars, r, true)`) after `cheap_beta_reduce`
(`instantiate.cpp` 211–230). `infer_lambda` (125–142) likewise
`cheap_beta_reduce`s the body's type. The `let` variable is transparent
to comparisons through `whnf_fvar` (row `let.variable-unfolds`: in
`let T := A; (fun x : T => x) h`, `A` against `T` succeeds by zeta). A
`let` in a claim is reduced by `whnf_core` at step 3 (row `let.in-claim`).

Inference has two modes (`infer_type_core`, 325–358): *checking* (as for a
declaration) and *infer-only* (`infer_type`, 360–362: no argument types
compared, universe levels not checked; `infer_app` instantiates all
arguments at once, 188–205). Proof irrelevance, eta and `is_prop` use
infer-only; each mode has its own cache (332–334, 356).

### Metadata

`mdata` nodes are transparent: `whnf_core` and `whnf` look through them
(478–479, 712–713), inference infers the contents (339), `quick_is_def_eq`
compares the contents (812–813), but `==` also compares the data. Lean's
exporter writes none unless asked; LeanForth keeps refusing them
(*unsupported*, U2) until an export needs them.

### Caches

The cache state is one `type_checker::state` (`type_checker.h` 25–49):

| Cache | Key → value | Filled | Used |
| --- | --- | --- | --- |
| `m_infer_type[2]` | term → type, one per mode | `infer_type_core` 356 | 332–334 |
| `m_whnf_core` | term → `whnf_core` result | 547–549, only without `cheap_*` | 490–493 |
| `m_whnf` | term → `whnf` result | 733, 739 | 724–727 |
| `m_unfold` | constant with universe arguments → its instantiated value | 578 | 574–576 |
| `m_success` | unordered pair of terms shown equal | `is_def_eq` 1211–1212, via `cache_success` 939–944 | `quick_is_def_eq` 804, via `succeeded_before` 927–937 |
| `m_failure` | unordered pair whose same-head argument test failed | 1009, via `cache_failure` 920–925 | 1004, via `failed_before` 908–918 |

- **Keys are compared with `==`**, so binder names and annotations do not
  matter; the pair caches store each pair once in hash order and look up
  both orders when the hashes tie, so a success for `(t, s)` also answers
  `(s, t)`.
- **There is no union-find and no general failure cache.** Older Lean
  versions had an equivalence manager; 4.35.0 replaced it, and
  `type_checker.h` 33–39 says why: "`is_def_eq` is a sound but incomplete
  semi-decision procedure and is therefore not transitive, so taking a
  transitive closure of successful pairs would make its result depend on
  evaluation order". The failure cache serves only the same-head argument
  test.
- **Lifetime: one declaration.** `add_definition`, `add_theorem` and
  `add_opaque` each build one `type_checker` (`environment.cpp` 181, 196,
  215) for the declared type, the value and the final comparison; it is
  destroyed after the check. So no cache crosses a declaration or an
  environment. Within the declaration, the caches serve the type and the
  value alike: in row `sort.after-unfolding` Lean needs `whnf(dqProp)` in
  the type and again in the value, and unfolds `dqProp` once.
- **Why the caches cannot change a verdict in Lean.** The header's
  argument (33–39): kernel terms have no metavariables, and free variables
  are globally unique with fixed types, so `is_def_eq`, `whnf`,
  `whnf_core` and inference are functions of their arguments. One
  exception: the *eager* flag (`m_eager_reduce`, set by an argument of the
  form `eagerReduce _ _`, tc 168–183) changes steps 2 and 5.2 but is not
  part of the success cache's key — *phase 5*, and name-matched.

### Names the kernel matches by name

`Nat.zero`, `Nat.succ` and fourteen `Nat` operations (tc 37–52,
1287–1302), `Bool.true` (29, 1283), `String.ofList` (1104, 1303) and
`eagerReduce` (30, 1285) are recognised **by name**, whatever the
environment says those constants are. In Lean's own library they are the
real constructors and functions, and the rules are correct. In an
environment that defines such a name itself, they misfire: rows
`names.nat-succ-matched-by-name` (a user `Nat.succ` that ignores its
argument: Lean compares `Nat.succ A` with `Nat.succ B` by comparing `A`
with `B` and rejects a claim that is true by unfolding) and
`names.nat-zero-becomes-a-literal` (Lean turns `Nat.succ Nat.zero` into
the literal `1`, whose type `Nat` does not exist, and fails with
`unknownConstant Nat`); the same declarations under other names are
accepted. Recorded as BL-4 in [BEYOND_LEAN.md](../project/BEYOND_LEAN.md).
*Follow-up (2026-11-05, agent LE; plan tasks 5.2.3 and 4.2.5):* a lookup
that throws inside Lean's `is_def_eq` ends the check with Lean's
exception, never a no: the typer's `infer_constant` (N1, L1), structure
eta's and unit-like types' `env().get` (`try_eta_struct_core`,
`is_non_rec_structure`; `defeq.fs` `lf-dq-named`) and `infer_proj`'s
(`infer-proj.fs`). `mixed-convert.fs` tells Lean's no from such an
exception (`lf-mixed-convert-no?`), and `lf-minfer-verdict` keeps the
exception's own diagnostic. Rows `names.nat-zero-becomes-a-literal` and
`names.bool-true-looked-up-by-eta` (`Nat.beq Nat.zero Nat.zero` computes
`Bool.true`, which the file lacks) give Lean's `unknownConstant`.

### Theorems: G5 answered

1. **Lean's kernel unfolds theorems.** `is_delta` accepts them
   (`has_value`, `declaration.h` 466–468); their hint is `opaque`
   (`declaration.cpp` 294–299), so in lazy delta reduction they are opened
   last, and `whnf` opens them like any definition (row `whnf.theorem`).
   ADR 0006's "Axioms, theorems and opaque declarations must not be
   unfolded" and plan task 4.1.1's wording describe the elaborator's
   default view, not the kernel.
2. **Where it changes a verdict: proofs that data depends on (phase 5).**
   Reducing a recursor puts its major premise into `whnf`
   (`inductive.h` 93), which opens a theorem there. Row
   `theorem.unfolded-by-recursor`: `And.rec … dqAnd` reduces to `True`
   only after Lean opens the theorem `dqAnd` (counts `And.rec:1`,
   `DefEq.dqAnd:1`), so the declaration is accepted; with a variable proof
   in its place (`theorem.variable-proof-stuck`) the recursor is stuck and
   Lean rejects. The same mechanism reduces `Acc.rec` in definitions by
   well-founded recursion (not among the rows).
3. **In phase 4's scope it cannot change a verdict** (an argument, tested
   by the rows but not proved): a theorem applied to arguments is always a
   proof; step 4 (proof irrelevance) decides every comparison whose left
   side is a proof before lazy delta runs, and every route by which Lean
   answers *yes* keeps the two sides' types equal, so lazy delta can meet
   a theorem only when comparing a non-proof with a proof, where Lean's
   answer is *no* either way. The kernel profile also found no theorem
   unfolded while checking `Init`, `Std` and a Mathlib slice
   ([profile](../development/measurements/lean-kernel-profile-2026-11-02/README.md#summary)).
4. **Decision:** LeanForth unfolds theorems exactly as Lean does, from
   phase 4 on, so that phase 5 needs no change. Every theorem's proof stays
   in memory (ADR 0016, "Dropping theorem proofs after their check", stays
   not adopted): dropping proofs would need a way to bring a proof back
   when a recursor needs it.

### Lean's own limits

The kernel stops with `deterministicTimeout` (heartbeats, counted by
allocation), `deepRecursion` (`scope_rec_depth` in every recursive
function) or `excessiveMemory` (`environment.cpp` 287–295). They are not
comparable with LeanForth's fuel (ADR 0011, *Outcomes*); neither side's
limit is ever a verdict.

## Decision (proposed)

### Q1 Port, not approximate

LeanForth implements Lean's functions above, each as one module or group
of words named after it, keeping Lean's order of steps and its operand
order. Each answers **yes**, **no**, or a failure: *unknown* (a deferred
feature, Q8), *exhausted* (fuel) or *full* (room). A *no* is Lean's *no*:
the caller reports Lean's exception for the step (`declTypeMismatch`,
`appTypeMismatch`, `letTypeMismatch`, `typeExpected`, `funExpected`) as
*rejected*. Consequences for ADR 0011, once this is implemented and gated:

- **K1 (unfolding), K2 (proof irrelevance) and K3 (eta) go**: the port
  decides those cases as Lean does.
- **D1–D5, S1, S2, S4 and F1 are subsumed**: each was a sufficient
  condition for Lean's *no*; the port computes Lean's answer itself, with
  `whnf` (with unfolding) in `ensure_sort` and `ensure_pi`. The rejection
  analysis (`lf-minfer-apart` and the words before it in
  `src/kernel/mixed-infer.fs`) is retired with them; during the switch it
  stays as a cross-check that must never disagree with the port's *no*.
- **K4–K6 stay** (levels that cannot be computed; an undecided
  dependency; Lean's level-sharing case), and **K7 is new** (Q8).
- **A1** reads: every step succeeded by the port.

An *unknown*, *exhausted* or *full* anywhere inside the procedure ends the
whole comparison with that outcome: the port cannot know which way Lean's
branch went, so it never continues as if the sub-step had answered *no*
(for example in the same-head argument test or in `is_def_eq_app`).

### Q2 Free variables inside a check (locally nameless)

When a check enters a binder (inference of `λ`, `Π`, `let`;
`is_def_eq_binding`; eta), it creates a **free variable**: a scratch node
with ADR 0016's free-variable tag and a number unique within the check,
whose type (and, for a `let`, value) is entry *n* of the check's local
context, an array in the context record. Bodies are opened with
`instantiate_rev`, results closed again with `abstract` (Lean's
`mk_pi`/`mk_lambda`). This replaces the binder-domain stack and the shifts
of today's inference (`lf-ijob-domains`, `lf-minfer-shift`). Reasons: a
term with free variables means the same thing wherever it appears, so a
cache keyed by the node is sound without a context in its key (Lean's
argument, above); `has_fvar` (steps 2 and 5.2, `is_def_eq_offset`) is the
node's data bit; and the free-variable identity is what makes
`is_def_eq_binding`'s choice of the right-hand domain (ADR 0003, B2)
literal. The variable's binder name and annotation are kept for printing
only.

*Note (plan task 4.2.2a, review rvD2A F2):* as implemented, inference
does not copy each opened body: it reads a source node *under its scope*
(a loose bound variable `k` is the scope's free variable `k` places from
the top), which gives the types of Lean's opened term without making it.
So a source node is not a closed term there: a hash-consed `#0` shared by
two depths stands for different free variables. The argument above holds
for the closed terms inference makes and gives back, not for the source
nodes it reads: an inference cache (Q10) must be keyed by the opened term
(a closed copy) or by the pair (node, scope), never by the source node or
its skeleton alone. Only closed scratch terms may be cached by node.

### Q3 Structural equality: Lean's `==`, by skeletons

Hash-consed node numbers (ADR 0016) include binder names, annotations and
`let` names, which Lean's `==` ignores. Every node gets, on first use, a
**skeleton**: the node number of the same term with binder names and
annotations erased (the `let` non-dependence flag and every other field
kept), memoised per tier (input skeletons computed once at load, scratch
ones per check). Then `t == s` is "same skeleton", one comparison. Every
cache key and the success and failure caches use skeletons, so a hit in
Lean is a hit in LeanForth. A cached result may carry the other term's
binder names, exactly as in Lean; names matter only to the printer.

### Q4 `whnf_core` and `whnf`

Ports of tc 468–551 and 706–743 with the easy cases, the caches, beta with
all leading `λ`s instantiated in one pass, zeta for `let` terms and `let`
variables, and the `cheap_proj` flag. Iota, quotient reduction,
projections and `reduce_nat` are the deferred routes of Q8: the port
returns *unknown* where Lean would try them on an input that could reach
them (a recursor, quotient constant or projection at the head; a
special name), never a guess.

### Q5 Delta, hints and declaration kinds

- `is_delta` reads the head constant's declaration from the node's
  payload (ADR 0016 C4) within the check's snapshot (ADR 0012 E3): a
  definition or a **theorem** that the snapshot holds as accepted, with as
  many universe arguments as parameters.
- Opaque declarations (plan task 4.2.6: imported, checked as
  `add_opaque` does — name, parameters, type, value against type — and
  published) never unfold; axioms remain *unsupported* until the allowlist
  (phase 5); inductive types, constructors and recursors remain
  *unsupported*.
- The environment record keeps each definition's hint from the export and
  `opaque` for a theorem (ADR 0012 E2, `decl-hint`, already so); `compare`
  is a port of `declaration.cpp` 24–49.
- `unfold_definition` returns the stored input value when the constant has
  no universe arguments (no copy, as Lean), otherwise the value
  specialised by ADR 0011 Amendment 1's level substitution, memoised per
  check (`m_unfold`).

### Q6 Lazy delta reduction

A port of tc 959–1075 with the step table above: the same-declaration
test is "same environment slot" (Lean's `is_eqp` on two `constant_info`
objects, which the environment returns once per name, `Environment.lean`
282–285); the argument test compares the last argument first, as
`is_def_eq_args` does; the failure cache (Q10) serves it. Steps 1–2 of the
loop and `try_unfold_proj_app` are deferred routes (Q8).

### Q7 Eta, proof irrelevance, `let`

- **Eta:** `try_eta_expansion` both ways, at step 11, with infer-only
  inference and `whnf` of `s`'s type; the new `λ` takes the `Π`'s binder
  name, domain and annotation.
- **Proof irrelevance:** step 4, with infer-only inference of `t_n`;
  `is_prop` is `ensure_sort(infer_type(·))` and `normalizes_to_zero`
  (already in `src/kernel/level-value.fs`, ADR 0011 fact 6).
- **`let`:** the importer stages `letE` (ADR 0016 C1 has its record),
  inference ports `infer_let` (with `letTypeMismatch`), and comparisons get
  zeta from Q4. A `let`'s non-dependence flag is kept and compared by `==`
  (Q3) but changes nothing else, as in Lean.

### Q8 What stays unknown or unsupported until phase 5

| Lean route | Lines | Phase 4 |
| --- | --- | --- |
| Recursor (iota) and quotient reduction in `whnf_core` | 525–536 | never reached: recursors and `Quot` constants are unsupported declarations, so a declaration using one is *unsupported* (U1, K5) |
| Projections: `reduce_proj`, step 8, `try_unfold_proj_app` | 504–510, 1177–1182, 950–957 | projections are an unsupported term form (U2) |
| Structure eta (step 12), unit-like (step 14) | 856–872, 1120–1130 | need a structure in the environment: none can be (U1). The port still runs them as Lean does — unit-like's `whnf(infer_type(t))` can unfold definitions, which counts and costs fuel — and they answer *no*, as Lean does in such an environment |
| Literals: `reduce_nat`, `is_def_eq_offset`, string expansion (steps 5.1, 5.2, 13), `quick_is_def_eq` on literals | 672–703, 1043–1066, 1104–1117, 821–822 | literals are unsupported forms (U2) |
| Name-matched constants: `Nat.zero`, `Nat.succ`, the fourteen `Nat` operations, `Bool.true` (step 2), `String.ofList`, `eagerReduce` | 29–52, 1142–1146, 1283–1303 | **K7, new:** a `whnf` or comparison that meets one of these constants at a head where Lean's rule would look at it answers *unknown* (rows `names.*`) |

Rule **K7** keeps LeanForth from reproducing Lean's name-matched rules
half-way before phase 5 ports them exactly (with literals and `bignum`). Since plan task 4.2.2d K7 is
narrowed to where Lean's rules compute or decide: `reduce_nat` answers
*unknown* only where it computes a literal (its arguments' whnf are
`Nat.zero`), and `is_def_eq_offset`, which needs no literal for two
`Nat.succ` applications, is ported (so `names.nat-succ-matched-by-name`
gives Lean's `declTypeMismatch`).
In an imported Lean library these names are constructors and recursive
functions, which are unsupported in phase 4 anyway, so K7 matters only for
environments that define the names themselves.

**Since plan task 5.2.3 (2026-11-05, experimental) K7 computes.**
Natural-number literals are leaves (`core/literals.fs`: one cell, or the
limbs of `lib/bignum.fs` in the context's slab); a literal's type is the
constant `Nat`; `whnf_core` leaves it; `reduce_nat` computes Lean's
fifteen operations by name on literals and `Nat.zero`, whether or not the
term has free variables, as Lean's `whnf` does (`kernel/reduce-nat.fs`;
only lazy delta, 1060, and the `Bool.true` step, 1142, test `has_fvar`;
review rvCONV B1 corrected an invented test here); iota turns a literal major
premise into `Nat.zero` or `Nat.succ n`; `quick_is_def_eq` answers no for
two different literals; `is_def_eq_offset` takes the literal 0 and
`Nat.zero` as zero and a literal above 0 as a successor; lazy delta
replaces a side `reduce_nat` computes by its value. Lean's fixed refusal
(`get_count_arg`: `Nat.pow`, and `Nat.shiftLeft` of a nonzero number, by
2^32 or more) rejects (diagnostic 92) and lifted diagnostic 86;
`LEAN_NAT_MAX_SIZE` (2^30 bits, a setting) is a resource (full,
diagnostic 93). Because whnf may refuse, block positivity puts every
field's type in whnf, as `check_positivity` does. String literals and
let terms stay unsupported (U2). Evidence: the table's 5.2.3 rows give
Lean's verdict or a pending mark (strings, let terms, K2), among them
`lit.pow-count-too-big` (rejected) and `lit.pow-direct` (two limbs);
`Nat.add_zero`'s export: 29 of 29 checks accepted.

### Q9 Fuel

One budget per declaration check (`lf-check-budget`, ADR 0011 *Fuel*)
pays for everything, so every loop ends:

| Loop | Charge |
| --- | --- |
| `is_def_eq_core`, `whnf_core`, `whnf`, `infer_type_core` entered | 1 each (a cache hit too) |
| a beta contraction, a zeta step | 1, plus one per node visited by the instantiation |
| a delta step (`unfold_definition`) | 1, plus one per node visited by a level substitution (none when memoised) |
| a lazy delta step | 1 (plus its unfoldings) |
| `is_def_eq_binding` per binder pair; `is_def_eq_args` per argument | 1 |
| skeleton computation | one per new node |

Out of fuel is *exhausted*; out of frames, room or local-context entries
is *full*; neither is ever a verdict or cached. Because caches save work,
a run with caches off can exhaust where a run with them on does not; the
comparison of the two (Q10) is made with fuel enough for both, and a
fuel sweep (test plan) checks that less fuel only ever turns a verdict
into *exhausted*.

### Q10 Caches

| LeanForth cache | Lean's | Key | Value | Notes |
| --- | --- | --- | --- | --- |
| inferred types, two modes | `m_infer_type[2]` | skeleton of the opened (closed) term, or (node, scope) | node | only completed inferences; never a source node alone, which is read under the scope (Q2 note) |
| `whnf_core` | `m_whnf_core` | skeleton | node | only without `cheap_*`, as Lean |
| `whnf` | `m_whnf` | skeleton | node | |
| unfolding | `m_unfold` | constant node (name, interned level list) | node | only with universe arguments, as Lean |
| successes | `m_success` | unordered skeleton pair | — | filled only where `is_def_eq` returns *yes*; looked up only in `quick_is_def_eq`; both orders |
| argument-test failures | `m_failure` | unordered skeleton pair | — | filled and read only by the same-head argument test |

Rules:

1. **Exactly Lean's caches, filled and read where Lean fills and reads
   them.** For the memo caches (types, `whnf`, `whnf_core`, unfolding)
   this is only speed, since they memoise functions. For the success cache
   it is also exactness: Lean answers `(s, t)` from a success on `(t, s)`,
   so if Lean's `is_def_eq` were ever asymmetric its verdict would depend
   on the cache; copying the cache copies that dependence. No union-find,
   and no general failure cache (Lean has none; adding one would be a
   change only if `is_def_eq` were not a function — kept out on
   principle).
2. **Only definite results.** A computation that ended *unknown*,
   *exhausted*, *full* or *invalid* stores nothing; a stored *yes* or
   result node is final.
3. **Lifetime: one declaration check**, type and value together, as
   Lean's `type_checker`. The scratch roll-back between the type and the
   value (ADR 0011, *Implementation* 2.2.3) moves to the end of the check,
   with caches on or off, so that entries never point at freed nodes and
   both modes use the same room (with the compact store's growing scratch
   tier, ADR 0016 C5, this costs memory, not outcomes); every cache is
   emptied by advancing its epoch when the check ends (ADR 0016 C3, C4).
4. **Never shared**: caches live in the context record (ADR 0009); no
   entry crosses a check, an environment or a worker. ADR 0012 E3's
   permission to keep successes across checks is *not* used in phase 4:
   Lean does not do it, and it would need its own argument (that
   `is_def_eq` is a function of its arguments and of the constants they
   reach, unchanged as the environment grows) and its own gate.
5. **Switchable and counted.** A test mode turns all six off; every cache
   counts hits and misses (the kernel profile could not measure Lean's).
   With caches off the verdicts must be identical on every corpus (plan
   task 4.2.7); a difference would be a finding about Lean's procedure,
   recorded in BEYOND_LEAN.md, and the cache-on answer — Lean's — stands.

### Q11 The derivation log

ADR 0013's catalogue gains, as an additive amendment (codes unused in its
catalogue today; 20–22 are taken by `instantiate`, `shift` and
`instantiate-levels`):

| Code | Rule | Inputs a, b | Result | Premises |
| --- | --- | --- | --- | --- |
| 7 | `let` (inference) | the `let` | its type | the type's and value's types, `defeq` |
| 14 | `delta` | the term, its head's slot | the unfolded term | `instantiate-levels` when the constant has universe arguments |
| 15 | `zeta` | the `let` (or the `let` variable) | the reduct | `instantiate` |
| 16 | `lazy-step` | left, right | 1 left unfolded, 2 right, 3 both | its `delta` steps |
| 17 | `same-head-arguments` | left, right | 1 equal, 0 not | `level-eq` and `defeq` per argument |
| 18 | `proof-irrelevance` | left, right | 1 equal, 0 not | the two statements' inference and their `defeq` |
| 19 | `eta` | the `λ`, the other term | 1 equal | the other's type, `whnf`, `defeq` |
| 23 | `cache-hit` | left, right | 1 | none: "shown equal at step n", the log's own memo giving n when the earlier step is in the log |

`defeq` (12) gains a result: 1 for *yes*, 0 for *no* (a *no* is ordinary
control flow inside the procedure; the check fails only where a caller
turns it into an exception). `whnf` (10) lists its `beta`, `zeta` and
`delta` steps. The printer's "by definition of f" (plan task 4.4.3) reads
`delta` records. Logging stays off unless asked (ADR 0013 D1): a proof by
computation can take tens of thousands of unfoldings (123,490 in one
`Std` declaration, per the kernel profile), far beyond the 1,024 records of
a phase-2 log, which then truncates (L3) without changing the verdict.

### Q12 Speed: one thread comparable to Lean

Lean's kernel spends about 40% of its time substituting (`instantiate`
and friends, with a hash map allocated per call: 14–16% alone), 21–23%
allocating and freeing, 21–25% in hash tables and 5–8% looking constants up
by name; the logical rules take under 6%
([profile](../development/measurements/lean-kernel-profile-2026-11-02/README.md#2-time-shares-by-family)).
Inside definitional equality, `whnf_core` is called most from lazy delta
(18–23% of all time) and from the start of `is_def_eq_core` (13–18%). The
design aims at each:

1. **Substitution.** One reusable memo per context for `instantiate`,
   `instantiate_rev` and `abstract`, keyed by (node, offset), cleared by
   epoch (ADR 0016 C4); nodes whose loose-variable range or free-variable
   bit shows they cannot change are returned before any lookup (Lean does
   the same test, `instantiate.cpp` 16, 22–23); beta instantiates all
   leading `λ`s in one walk (as Lean); a definition without universe
   parameters unfolds to its stored value with no copy.
2. **Allocation.** The scratch tier is a region reset once per check: no
   reference counts, no freeing of single nodes, no cache destructors
   (Lean: 21–23% plus 5.5–6.7%).
3. **Hash tables.** Open addressing on 32-bit node numbers for every
   cache, epoch-cleared; hash-consing with one probe per new node (ADR
   0016 C3); `==` is a skeleton comparison instead of a recursive walk
   (Lean: 7–8% structural equality); no re-sharing pass per theorem (Lean:
   5–6%), since the input is hash-consed once at load.
4. **Lookups.** Constants are resolved at load (ADR 0016 C4): `is_delta`,
   inference of a constant and unfolding need no name lookup (Lean: 5–8%).
5. **Avoiding re-instantiation.** The unfolding cache keyed by the
   interned constant node (Lean's `m_unfold`) and the level-substitution
   memo keyed by (node, level list) answer repeated unfoldings of the same
   constant at the same levels. Note (2026-11-10, step S0 of the
   compact-store plan, plan task 6.5.5; [kernel] review pending): one
   level substitution (`mixed-level-substitute.fs`, `level-substitute.fs`)
   and one level normalization (`level-normalize.fs`) no longer cost the
   whole store per call (68% of the check time on a 1M-line `Init`
   prefix): a call marks what it reaches with a new stamp instead of
   erasing a column, and builds only the reached nodes, sorted, so in the
   same order as before. The result, which must equal Lean's
   `instantiate_lparams` (`instantiate.cpp`), every verdict, every fuel
   count and the trial digests are unchanged; the memo itself is still to
   come.
6. **Measuring.** Plan task 4.2.7 reports time per distinct node and cache
   hit rates on the phase-4 corpus next to Lean's 3.0–3.3 µs per distinct
   node (`TimedReplay.lean`, same machine); the owner's goal is one-thread
   speed as close to Lean's as possible (OWNER_DECISIONS.md, *Speed goal*).
   The compact-store prototype's 0.4–0.5 µs per substitution step
   (`gforth-fast`) is the right order of magnitude, not yet a result.

## Lean's functions and their LeanForth counterparts

| Lean (tc lines) | LeanForth today | ADR 0014 |
| --- | --- | --- |
| `whnf_core` 468–551 | `mixed-beta.fs`: beta only, one argument per step, de Bruijn | port (Q4): beta (all arguments), zeta, `let` variables; deferred routes *unknown* (Q8) |
| `whnf` 706–743 | none (no unfolding) | port (Q4, Q5) |
| `is_delta`, `unfold_definition*` 555–602 | none | port (Q5); theorems unfold |
| `ensure_sort_core`, `ensure_pi_core` 62–83 | `mixed-head.fs` rigid tests, rules S1/S2/S4/F1 | port with `whnf` (Q1) |
| `infer_*` 101–358 | `mixed-infer.fs`, binder stack, checking mode only | port both modes with free variables (Q2); `infer_let` (Q7) |
| `quick_is_def_eq` 802–826, `==` | `mixed-convert.fs` structural walk after beta | skeletons (Q3), success cache (Q10) |
| `is_def_eq_binding` 752–779 | `mixed-convert.fs` (ADR 0003 Amendment 1, B1–B2) | port with free variables |
| `is_def_eq_proof_irrel` 899–906 | none (K2) | port (Q7) |
| `lazy_delta_reduction*` 959–1075 | none (K1) | port (Q6) |
| `is_def_eq_app`, `is_def_eq_args` 828–895 | `mixed-convert.fs` children | port |
| `try_eta_expansion` 841–853 | none (K3) | port (Q7) |
| `try_eta_struct`, `is_def_eq_unit_like`, strings, offsets, `reduce_nat` | none | Q8 |
| `is_def_eq(level)` 781–799 | `level-compare.fs` (`is_equivalent`, ADR 0011 Amendment 1) | unchanged |
| caches (`type_checker.h` 25–49) | none | Q10 |
| rejection analysis | `mixed-infer.fs` (`lf-minfer-apart`) | retired after the switch (Q1) |

## Evidence

`tests/reference/definitional-equality.lean`, its table
`definitional-equality.tsv` and script `definitional-equality-check.sh`,
run by `make reference-definitional-equality` (part of `make check`, about
one second). Each case is a kernel declaration added with `addDeclCore` to
a scratch environment with kernel diagnostics on (or `Kernel.whnf`), so
the file's own environment is untouched. The run fails unless Lean's
verdict and unfold counts are the recorded ones, the LeanForth columns
never contradict Lean, and the ADR 0014 column equals Lean's verdict on
every row whose rule is not a deferral (K5, K7, U1, U2).

| Group | Rows | Lean | ADR 0011 column | ADR 0014 column |
| --- | --- | --- | --- | --- |
| `delta.*`: heights, abbreviation and opaque hints, same head, levels, a chain, failures after unfolding | 15 | 12 accepted; `declTypeMismatch` ×2 (`levels-differ-opaque`, `wrong-after-unfolding`), `appTypeMismatch` ×1 | unknown (K1), one unsupported (opaque) | Lean's verdict |
| `sort.*`, `pi.*`: a type or function type only after unfolding | 4 | 2 accepted, `typeExpected`, `funExpected` | unknown | Lean's verdict |
| `opaque.*`: never unfolds; checked like a definition; a definition twin | 4 | 2 accepted, `declTypeMismatch` ×2 | unsupported / unknown | Lean's verdict |
| `whnf.*`: definition, `@[irreducible]` definition, theorem, opaque | 4 | unfolds ×3, stays | n/a | Lean's answer |
| `theorem.*`: a recursor opens a theorem; a variable proof stays stuck | 2 | accepted (`And.rec:1,DefEq.dqAnd:1`), `declTypeMismatch` | unsupported | unsupported (U1, phase 5) |
| `eta.*`: both orders, after unfolding, twice, a wrong function | 5 | 4 accepted, `declTypeMismatch` | unknown (K3) | Lean's verdict |
| `proof-irrelevance.*` (two added 2026-11-05, task 4.2.5: proofs of different statements as a definition's arguments) | 6 | 3 accepted, `declTypeMismatch` ×3 | unknown ×4, rejected ×2 (D3) | Lean's verdict |
| `let.*` (three added 2026-11-05, task 4.2.3: a type that is a let term, a chain, a type that is no type) | 7 | 5 accepted, `letTypeMismatch`, `typeExpected` | unsupported (U2) | Lean's verdict |
| `names.*`: Lean's name-matched `Nat` rules in an environment that defines the names | 4 | `declTypeMismatch`, `unknownConstant Nat`; twins accepted | unknown / unsupported | unknown (K7) for the two; Lean's for the twins |
| `later.*`: structure eta, unit-like, `Nat` literal, quotient (re-checked Lean elaborations) | 4 | accepted ×4 | unsupported | unsupported (phase 5) |

In all, 50 rows: 32 accepted (each with its counts), 14 failures, 4
`whnf` answers (52 since 2026-11-05: 33 accepted, 15 failures, 4; 55
with task 4.2.3's three `let.*` rows: 35 accepted, 16 failures, 4).
Measured 2026-11-03 with the pinned Lean, all as recorded;
`make test` and `make check` (Gforth 1.0.0, Lean 4.35.0) passed with the
table wired in.
Planted faults in scratch copies (`.claude/work/DQ/bin/faults.sh`, not in
git), each caught: a wrong count, a wrong verdict, an ADR 0014 answer
contradicting Lean, an ADR 0014 *unknown* on a row Lean decides, an
abbreviation's hint changed to regular (counts change), an opaque
declaration made a definition (verdict changes), a deferred row given a
definite answer, and the theorem made to "stay"; a changed table row fails
the script's byte comparison.

This is evidence about Lean, not LeanForth: no LeanForth code implements
ADR 0014 yet. The ADR 0011 column is the specification under the approved
rules (not run against LeanForth here); turning this table into a LeanForth
differential is plan task 4.3.1.

## Implementation tasks (plan 4.2.1–4.2.7)

Each is [kernel] code through the gate in `AGENTS.md`, in this order:

| Task | Content | Done when |
| --- | --- | --- |
| 4.2.1 Level equality | Lean's `is_equivalent`, `mk_max`, `mk_imax` (ADR 0011 Amendment 1, implemented 2026-11-03) | its gate is passed; nothing more for phase 4 |
| 4.2.2a Free variables | Q2: free-variable nodes, the local-context array (types, `let` values), `instantiate_rev`/`abstract`; inference moved onto them without behaviour change | the phase-2/3 tables give identical outcomes; randomized differential of inference against the code before |
| 4.2.2b Skeletons and quick check | Q3; `quick_is_def_eq`, `is_def_eq_binding`, `is_def_eq_app` and `is_def_eq_args` ports | unit tests; binder-domain table unchanged |
| 4.2.2c `whnf_core`, `whnf`, delta | Q4, Q5 (theorems unfold, opaque never; hints; `m_unfold`); `ensure_sort`/`ensure_pi` through `whnf` | verdicts of the `sort.*`, `pi.*` and `whnf.*` rows |
| 4.2.2d Lazy delta and `is_def_eq_core` | Q6 and the step table; deferred routes and K7 (Q8); the retirement of K1 and the rejection analysis (Q1), with the cross-check during the switch | verdicts of the `delta.*`, `opaque.*` and `names.*` rows; the K1 rows of the earlier tables |
| 4.2.2e Log | Q11's records for delta, lazy steps and the argument test | golden log of `delta.argument-after-unfolding` |
| 4.2.3 `let` | importer stages `letE`; `infer_let`; zeta (Q7) | `let.*` rows |
| 4.2.4 Eta | Q7, with infer-only inference | `eta.*` rows |
| 4.2.5 Proof irrelevance | Q7 | `proof-irrelevance.*` rows; ADR 0011's `proof-irrelevance-twin` row becomes *accepted* |
| 4.2.6 Opaque declarations | import, `add_opaque` check, publication; never unfold | `opaque.*` rows |
| 4.2.7 Caches v1 | Q10: six caches, skeleton keys, per-check lifetime, epoch reset, counters, off switch; speed report (Q12) | verdicts identical with caches off on every corpus; every accepted row's unfold counts equal Lean's with caches on (some, such as `sort.after-unfolding`, need the `whnf` cache) |

Then 4.3.1 (this table as a LeanForth differential, plus the randomized
one) and 4.3.2 (the unknown rate).

### Progress

**4.2.2a, implemented 2026-11-03 and 2026-11-04 (agent D2A), reviewed
by rvD2A (2026-11-04: no way found to accept what Lean or the code before
rejects; F1-F5 corrected below); its [kernel] gate awaits the owner's
approval.** What changed:

- *Free variables and the local context*
  (`src/core/local-context.fs`): a free variable is a term node of tag
  `lf-tag-fvar` whose number is its entry in the check's local context, a
  heap store in the checker context holding the node (with its
  identity), its type and, for a `let` variable, its value. Inference
  empties it when a job starts, and when it discards scratch it drops the
  entries whose nodes went with it (`lf-lctx-drop`; review F3: before,
  entries grew with every binder opened, 32,767 for a 15-node DAG), so a
  number may be taken again; a node is a live free variable only when its
  own entry names it with its current identity, which every audit
  (`lf-cterm-check`) requires, so a discarded node never names the new
  entry. Its capacity is a per-context setting; full is *full*, never ok.
- *Lean's substitutions* (`src/kernel/mixed-open.fs`): `instantiate`,
  `instantiate_rev`, `abstract` and `mk_pi`, ports of `instantiate.cpp`
  15–39 and 99–118, `abstract.cpp` 14–32 and `local_ctx.cpp` 93–125, with
  Lean's `update_*` rule (a node whose children are unchanged is kept).
  Without Lean's cached loose-variable range and free-variable flag, the
  passes visit unchanged subterms and pay fuel for them (Q12 plans the
  data and a memo); `mk_pi` of a `let` variable is *unsupported* until
  4.2.3.
- *Inference* (`src/kernel/mixed-infer.fs`) computes closed types only,
  as Lean does. It enters the binders of a telescope of λs or Πs one at a
  time, each as `infer_lambda` and `infer_pi` treat it: the domain must
  be a type (S2); the binder then gets a free variable whose type is the
  domain closed with the free variables around it (`instantiate_rev`),
  kept on the job's *scope*. Source terms are read under the scope (a
  loose bound variable `k` is the scope's free variable `k` places from
  the top), which infers exactly Lean's opened body without copying it
  first, and keeps each binder one inference step with its source node as
  subject, as the derivation log (ADR 0013) records it. A free variable's
  type is its entry's (`infer_fvar`); an application's argument is closed
  and put into the Π body with Lean's `instantiate`; a Π's type is
  `Sort (mk_imax u v)`. The instantiate no longer runs
  `lf-mixed-instantiate`'s audit of its two graphs (review F5): the body
  is a type inference made or audited input holds, the argument an
  audited source node closed by mixed-open (which checks each leaf's
  shape, liveness and child order), and every comparison that can lead to
  acceptance audits both of its graphs (`lf-minfer-compare`, through
  `lf-mixed-convert-keeping`). Because source nodes are read under the
  scope, a source node is no closed term: a future inference cache must
  be keyed by the opened term or by (node, scope) (Q2 note, Q10; review
  F2). A chain of λs gets `mk_pi` of its free variables
  over the innermost body's type, built once from the inside out: the
  body's type abstracted over the chain's free variables, the Π of each
  source domain around it, and at the chain's top the loose bound
  variables of outer binders closed. This equals Lean's result, since a
  source domain abstracted after `instantiate_rev` is the domain itself;
  the review proved the two equal node for node, apart from
  `cheap_beta_reduce`; making `mk_pi` per λ instead would cost nodes
  quadratic in a chain's
  depth (composition's value would no longer fit the 64-term store of
  `check-declaration`'s `value-room` case). The binder-domain stack and
  the shift of a bound variable's domain are gone. ADR 0011's rejection
  analysis keeps its own binders (D4) as bound variables, and closes a
  term with their free variables when P2 infers it. Not yet ported:
  `cheap_beta_reduce` of a λ body's type (tc 140), which changes inferred
  types and so comes with 4.2.2c.
- Inference discards scratch it no longer needs (a domain's and an
  argument's inference, a Π's) so that the 64-term default store still
  holds every table case; this must go when the caches of Q10 keep
  scratch until the check ends.
- *The derivation log* copies a free variable as the bound variable it
  stands for at the record's depth (each entry records its binder's
  depth), so logs hold bound variables only and print as before. A
  `variable` step has no `shift` premise any more: composition's log is
  51 steps, the 65 of ADR 0013's table without its 14 shifts, every
  formula and outline line the same (`tests/present/outlines.golden`,
  compared modulo step numbers with the code before).

Evidence: see the agent report of 2026-11-04 (D2A) and the figures here.
Every differential target of `make check` gives the same answers. A
capacity sweep of the first-checker and binder-domain tables (term stores
of 64 to 80 nodes in steps of 2, 96, 128, 4,096; 1,092 rows each) differs
from the code before only where the code before ran out of room:
`compare.eta-under-beta-domain`, `compare.lambda-beta-domain-different-body`
and `decl.lambda-in-argument-wrong-body` now give the table's answer at
64 nodes, so the binder-domain table has no known difference left.
The first randomized differential against main at `87f0f79`
(`.claude/work/D2A/difftrial.fs`; seed 20261103, 20,000 terms, 134,991
runs: 42,101 ok, 80,025 rejected, 12,865 unknown) found no difference in
outcome, diagnostic code, D-rule mask or inferred type, but it tested
little of what changed (review F1): its random terms are mostly ill typed,
and of its well-typed ones few contain an application and none a λ
argument (50 of 1,534 typed terms in 3,000 cases had an application), so
it never reached the chain closing or the argument closing: the planted
fault `infer-chain-unclosed` gave no difference there.
The typed-term trial, adapted from the review's generator,
`tests/core/infer_typed_trial.py` with `tests/support/infer-trial.fs`,
makes well-typed terms with parameters, polymorphic variables, `id.{0/1}`,
λ arguments and dependent λ chains as arguments under binders (a quarter
mutated), and checks every unmutated case's inferred type against a
simple named-term model, exactly. Seed 1 (2,000 cases): 1,323 λ arguments
under binders, 921 of them dependent, 362 chains, 1,027 well-typed cases,
all equal to the model. Old against new (main `147fde8` against this
change, `--compare`): seeds 1 and 2 at ample fuel, 16,613 runs, all
identical; seed 3 (fuel below 3,000) and seed 4 (a store of the input plus
up to 120): only runs that ran out of fuel or room in one tree differ,
and unknown against rejected. Calibration, each planted fault in a copy:
`infer-chain-unclosed` 193 of the 1,027 cases differ from the model,
`infer-arg-unclosed` (an argument not closed) 405, `infer-domain-unclosed`
(a domain not closed) 1,000, `infer-abstract-innermost` 989,
`infer-chain-top-ignored` 1,020, `infer-imax-zero` 28. With too little
fuel or room the first differential's only differences, 124 and 519,
were *unknown* against *rejected* too. The
derivation log's outlines of every pinned export and broken copy are
those of the code before, step numbers aside. Unit tests of the local
context, the four ports and
a λ argument under a binder (`tests/core/mixed-instantiate.fs`,
`tests/core/mixed-infer.fs`), the local context's drop on the review's
DAG (`tests/core/infer-deep.fs`) and mixed-open's recovery after a THROW
(`tests/core/mixed-instantiate.fs`, `tests/core/mixed-beta.fs`:
`lf-mixed-rebuild-reset` now resets all four rebuilding passes, review
F4); 25 planted faults in `tests/mutants/faults.toml` for this task: 24
caught, and `rej-p2-open-term` a known equivalent (P2 inferring an open
term of the analysis under the scope infers its closed copy; the closing
stays, for closed cache keys).

**4.2.2b and 4.2.2c, implemented 2026-11-04 (agent U4); their [kernel]
gate awaits an independent review and the owner's approval.** What
changed:

- *Lean's `whnf_core`, `whnf`, `is_delta` and `unfold_definition`*
  (`src/kernel/whnf.fs`), in Lean's order, as frame steps on the
  caller's frames record (no depth limit, plan task 6.2.0): beta takes
  all leading λs at once (Lean's `instantiate`, `mixed-open.fs`), zeta
  for `let` variables (none occur before 4.2.3), and an unchanged head
  that is no λ goes to the **iota hook** `lf-whnf-iota ( app frames --
  ... frames next )`, Lean's `reduce_recursor`: the hook's visit ends
  with `( reduct outcome frames 0 )`, `-1 ok` for no rule, and may ask
  for `lf-whnf-call` and `lf-whnf-core-call` visits on the same frames
  (the module header documents it for plan task 5.2.1b; the default
  answers *unknown*, diagnostic 81, for a recursor at the head). Delta
  unfolds a definition or a **theorem** (G5) the check's snapshot holds,
  given as many universe arguments as it has parameters: its value with
  the arguments substituted (the stored value itself without any, as
  Lean); opaque declarations, axioms, inductive types, constructors and
  recursors never. Where Lean's `reduce_nat` would look by name (K7),
  *unknown* (diagnostic 82, plan task 5.2.3); outside a check (the
  signature index's constants) a constant at the head of `whnf` is
  *unknown* (K1, diagnostic 64). `cheap_beta_reduce` (`instantiate.cpp`
  211–230) is ported, and `infer_lambda` applies it to the innermost
  body's type (tc 140). An argument with a loose bound variable (terms
  that ADR 0011's analysis and `check-block.fs` compare under their own
  binders) is put under a λ one at a time by `mixed-instantiate.fs`,
  which lifts it, as Lean's `instantiate` does with `lift_loose_bvars`.
- *`ensure_sort` and `ensure_pi` through `whnf`* (`mixed-infer.fs`,
  tc 62–83): a type that is no visible Sort (Π) is put in `whnf`, and one
  that is still none is Lean's `typeExpected` (`funExpected`), rejected
  with the diagnostic codes of S1, S2, S4 and F1, which these ports
  replace. The rows `sort.*` and `pi.*` give Lean's verdict; so do the
  first checker's `pi-body.needs-unfolding` (accepted) and `-wrong`
  (rejected), `constant.function-type-behind-definition` and
  `constant.sort-behind-definition` (accepted), and a binder domain whose
  type is a β-redex (definition-table case 0/4, until then a known
  *unknown*).
- *Lean's `==`* (`expr_eq_fn`) is `lf-expr-equal` (`mixed-compare.fs`),
  a structural walk: the term store keeps no binder names or annotations,
  so it is name-insensitive by construction. The skeletons of Q3
  (hash-consed nodes, `==` as one comparison) come with the caches of
  plan task 4.2.7, which need them as keys; until then `==` costs one
  unit of fuel per node visited (Q12).
- *`quick_is_def_eq`, `is_def_eq_binding`, `is_def_eq_app`,
  `is_def_eq_args` and the steps of `is_def_eq_core` LeanForth has*
  (`src/kernel/defeq.fs`): (1) `quick_is_def_eq` decides yes or no;
  (2) the `Bool.true` test is skipped (it only says yes; K7, 4.2.2d);
  (3) `whnf_core` of both sides and `quick_is_def_eq` again; then the
  steps that only say yes: (6) the same constant with equivalent universe
  arguments, (7) the same free variable, (10) `is_def_eq_app`. Where none
  says yes the answer is *unknown* (proof irrelevance 4.2.5, lazy delta
  4.2.2d, eta 4.2.4, structure eta and unit-like types 5.2.2 may decide
  there). Skipping steps 4 and 5 is sound for a yes only under
  conditions: steps 6, 7 and 10 say yes only for terms equal up to β and
  universe equivalence (ADR 0003's argument, on which conversion has
  always rested), *and* Lean's step 5 could not have gone elsewhere first.
  *Interim guard (review rvU4 B1, 2026-11-04):* the second condition was
  missing, and LeanForth accepted six declarations Lean rejects. Lean's
  lazy delta loop first asks `is_def_eq_offset` and `reduce_nat`, which
  read `Nat.zero` as the literal 0 and compute `Nat` operations by name,
  so Lean may need a type `Nat` the environment lacks. Now a head Lean
  matches by name (K7) is *unknown* before steps 6 and 10 (diagnostic
  82), and so is a head that unfolds, unless both sides are applications
  of the same declaration with a regular hint, whose arguments Lean
  compares first (diagnostic 64). The six declarations and their twins
  are rows `k7.*` of the inductive table (`inductive-expected.lean`, from
  an empty environment), with `k7.whnf-sort` for K7 in `whnf`; three
  planted faults (`rv-k7-off`, `dq-k7-guard-off`, `dq-unfold-guard-off`)
  are caught by them. Task 4.2.2d's lazy delta replaces the guard. `is_def_eq_binding` gives each binder a
  free variable of the right side's domain (B2); where Lean uses its
  placeholder `dontcare` (neither body uses the variable) no later term
  mentions it, so the free variable LeanForth always makes gives the same
  terms.
- *Conversion* (`mixed-convert.fs`) is the port after its audits: yes is
  *ok*; Lean's no is still reported *unknown*, with `lf-mconvert-apart`
  set, and ADR 0011's analysis decides rejections until 4.2.2d retires it
  (the port's no is its cross-check). A rejection analysis that runs out
  of fuel or room is now *exhausted* or *full*, not *unknown* (ADR 0008;
  agent CLI2's finding: `impliesSelf` was *unknown* at every fuel from 151
  to 280, and is now *exhausted* below 230, the fuel its whole check
  takes, and *unknown* from there, as before).
- Not yet as Lean, with no verdict depending on them: Lean's caches
  (4.2.7), the unfold counts of kernel diagnostics (4.2.7, 4.3.1), the
  log's `delta` records (4.2.2e). The inductive type's telescope and
  positivity in `check-block.fs` still use their β-only stand-in
  (`lf-blk-left?`), which task 5.2.1b replaces with `whnf.fs`'s
  `lf-whnf-on`.

Evidence (2026-11-04, Gforth 1.0.0, Lean 4.35.0; details in the agent
report): `make test-definitional-equality-differential` (new, part of
`make check`) runs the table's rows that declare something or ask for
`whnf` end to end (44 of 50; `definitional-equality-terms.lean` prints
them for the first checker's driver, `tests/support/whnf-probe.fs`
probes `whnf`; the 6 rows that name Lean's own library wait for phase
5): the 8 `sort.*`, `pi.*` and `whnf.*` rows give Lean's answer except
`whnf.opaque`, *unsupported* until 4.2.6 holds opaque declarations, and
no row contradicts Lean (4 accepted, 4 rejected, 3 unfolds, 22 unknown,
11 unsupported). Unit tests: `tests/core/defeq.fs`, `tests/core/whnf.fs`.
Old against new (main `b20d9a7`): conversion on random terms without
definitions (seeds 1–8, 32,987 comparisons: 26,631 ok, 6,356 unknown)
identical at ample fuel, where a planted fault (`is_def_eq_app` without
its arguments) gives 53 differences; the typed-term trial of inference
(seeds 11 and 12, 20,575 runs at ample fuel) identical, and at low fuel
or little room the only differences are *exhausted* or *full* against
*ok*, or the analysis's *unknown* now *exhausted*, *full* or *rejected*.
27 new planted faults (`tests/mutants/faults.toml`): 24 caught, 2 known
equivalents (`dq-binding-left-domain`, `infer-not-pi-aside-rejects`)
and 1 gap (`whnf-iota-hook-silent`, closed by 5.2.1b's iota rows); 10
re-targeted at the new code, 9 caught and `rej-p2-open-term` equivalent
as before; the faults of the retired head tests of S1 and F1 deleted
with them, and `rej-d4-left-domain` and `rej-after-exhaustion` now known
equivalents (the reasons are in the list).

**4.2.2d, implemented 2026-11-04 (agent U4); its [kernel] gate awaits an
independent review and the owner's approval.** What changed:

- *The whole of `is_def_eq_core`* (`src/kernel/defeq.fs`), in Lean's
  order, each step a frame step: (2) `Bool.true` by name, `whnf` of the
  left side when it has no free variable (or in eager mode); (4) whether
  the left side is a proof (`is_prop` of its type, through a *typer*
  that inference lends the comparison: Lean's `infer_type` in infer-only
  mode, `lf-minfer-typed`), *unknown* when it is one (K2, diagnostic 87,
  task 4.2.5); (5) lazy delta reduction, below; (6), (7), (10) as
  before; (8), (9) and (13) need projections or literals (U2) and change
  nothing; (11) exactly one side a λ, *unknown* (K3, 88, task 4.2.4);
  (12) a constructor of a non-recursive structure with its parameters
  and fields, and (14) a left side whose type's whnf is a non-recursive
  structure whose constructor has no field, *unknown* (89, task 5.2.2);
  (15) Lean's **no**. Conversion reports the no as *rejected*; the
  caller records its step's rule (59 `appTypeMismatch`, 60
  `declTypeMismatch`, check-block's 69), a bare conversion 90.
- *Lazy delta reduction* (tc 959–1075): each round one unit of fuel;
  `is_def_eq_offset` ported (two `Nat.succ` applications, by name,
  compare their arguments — Lean's rule, also for a user's `Nat.succ`,
  BL-4); `reduce_nat` while neither side has a free variable: *unknown*
  only where it computes a literal (its arguments' whnf are `Nat.zero`;
  K7 narrowed, as N1 asked: on `Nat.succ n` with `n` a variable it gives
  nothing, and iota takes the constructor; the same narrowing in
  `whnf`); then the step: `is_delta` of each side, hints compared as
  `declaration.cpp` 24–49, the same declaration with a regular hint and
  two applications first compares universe arguments and arguments
  (last first), each unfolded side through `whnf_core`, then
  `quick_is_def_eq`. Lean's failure cache only skips an argument test
  that would fail again; it comes with the other caches (4.2.7). The
  interim guard of review rvU4 B1 is gone: lazy delta does what it
  approximated, and the same rows (`k7.*`) prove it.
- *Retired*: ADR 0011's rejection analysis (D1–D5 with P1–P4,
  `lf-minfer-apart` and the words before it, about 230 lines of
  `mixed-infer.fs`) and K1 inside a check. Its white-box pairs now pin
  the port's answers (`tests/core/definite-rejection.fs`). Inference
  "aside" is Lean's infer-only mode (an application's argument neither
  inferred nor compared). Outside a check (the signature index, which
  holds no values) a constant at a head of lazy delta is a *doubt*: the
  comparison goes on for a yes, and a no is *unknown* (K1, 64).
- *Cross-check during the switch* (the analysis kept beside the port in
  one WIP commit, `lf-xc-on`; scratch harnesses in `.claude/work/U4/`):
  the Lean tables (first checker, binder domains, universe scope and
  many, depth, dependencies, definitional equality, their fed copies) 78
  pairs the analysis showed apart, all rejected by the port, and 5 the
  port alone rejects (`constant.needs-unfolding-wrong`,
  `depth2000.lam-wrong`, `delta.wrong-after-unfolding`,
  `delta.argument-wrong-after-unfolding`: Lean rejects each); the
  inductive table 3 and 3 (`unit.bool-not-unit-like`,
  `unit.bool-variables`, `unit.pair-of-units`: Lean `declTypeMismatch`);
  the typed-term trial (seeds 1 and 2, 5,000 cases) 7,090, all rejected
  by the port; the 2,000 checker trials of the digest 39,931 agreements
  and 1,362 pairs the port ran out of fuel on (the analysis had fuel of
  its own). No pair the analysis showed apart was accepted or left
  unknown by the port.
- *Evidence* (Gforth 1.0.0, Lean 4.35.0): the definitional-equality
  differential carries reducibility hints (`HINT` on a definition's
  line) and hierarchical names, and its `delta.*`, `opaque.*` and
  `names.*` rows give Lean's verdict, except the five that need an
  opaque declaration (`opaque.never-unfolds`,
  `opaque.declaration-accepted`, `opaque.declaration-wrong-value`,
  `delta.same-head-levels-differ-opaque`,
  `names.nat-zero-becomes-a-literal`, with its twin): *unsupported*
  until 4.2.6. The K1 rows of the first checker
  (`constant.needs-unfolding` accepted, `-wrong` rejected, and
  `constant.uses-an-undecided-declaration` accepted) and of the binder
  domains (two accepted, two rejected) give Lean's verdict; so do the
  inductive rows that waited for 4.2.2d (`params.constructor-binder-defeq`,
  `after.annotated-binders-left-out-then-use-rec`, `iota.bool-true-wrong`,
  `iota.list-hypothesis-wrong`, `iota.bool-stuck`), `k7.with-free-variable`
  and the new `k7.rec-on-succ-variable`. `names.nat-succ-matched-by-name`
  is now Lean's `declTypeMismatch` (offset ported). Planted faults: see
  `tests/mutants/faults.toml` (`dq-*`, `rv-k7-off`); the faults of the
  retired analysis are deleted with it.

**4.2.4 and 4.2.5, implemented 2026-11-05 (agent PE, branch
`pe-proof-irrel-eta`); their [kernel] gate awaits an independent review
and the owner's approval.** K2 and K3 go:

- *Step 4, proof irrelevance* (tc 899–906, called at 1163): when the
  left side is a proof (Lean's `is_prop` of its type, as before), the
  typer infers the right side's type (a free variable's type directly,
  Lean's `infer_fvar`) and `is_def_eq` of the two types, a child visit
  on the frames, is the answer, yes or no; nothing else is tried.
- *Step 11, eta* (tc 841–853, `type_checker.h` 94–96, called at 1194):
  when exactly one side is a λ, the other side's type (typer, or a free
  variable's type; a Sort's or a Π's type is a Sort) is put in `whnf`;
  a Π of domain `D` gives the new node `fun x : D => other x` (Lean's
  binder name and annotation are not stored: `==` ignores them), and
  `is_def_eq(λ, new)` (λ on the left, as Lean in both orders), a child
  visit, answers yes; a no, or a type that is no Π, goes on to step 12.
- Fuel: each child visit one unit (frame-admit), the typer and `whnf`
  on the frames' fuel as before; a failure (exhausted, full, unknown,
  invalid) ends the comparison with it, never as an answer. The new
  nodes stay for the caller to discard, as every comparison's.
- Without a typer (a bare comparison, only unit tests) steps 4 and 11
  stay doubts: 87 and 88 now mark only that (DIAGNOSTICS.md); a check
  always has a typer and never gives them.
- *Evidence* (Gforth 1.0.0, Lean 4.35.0): the definitional-equality
  differential's `eta.*` (5) and `proof-irrelevance.*` (6, two new:
  `.different-statements`, Lean `declTypeMismatch`, where step 4's no
  decides the argument test and the unfolded statements differ, and
  `.different-statements-unfold`, accepted, `dqForget:2`) give Lean's
  verdict and are now required to; 46 rows run. First-checker rows
  `composition.proof-irrelevance` (still *full* at the 64-node default,
  accepted at large capacities and fed), `type-identity.proof-irrelevance-twin`,
  `type-identity.eta-twin`, `poly-identity.proof-irrelevance-imax`,
  `-max-zero`, and binder-domain rows `compare.domain-proof-irrelevance`,
  `compare.eta-under-beta-domain`: accepted (Lean accepts); inductive
  row `k7.nat-is-prop`: rejected (Lean `declTypeMismatch`); CLI
  `tests/cli/irrelevance.ndjson` accepted. Nothing moved to accepted
  that Lean rejects. Planted faults `dq-eta-*`, `dq-proof-*` (8), all
  caught.

**4.2.3, implemented 2026-11-05 (agent LT, branch `lt-let-zeta`); its
[kernel][import] gate awaits an independent review and the owner's
approval.** `let` terms (Q7) leave U2:

- *Representation* (`src/core/let-terms.fs`): Lean's `letE x T v b` is a
  let leaf (its `nonDep` flag, which Lean's `==` compares; binder names,
  which it ignores, are dropped) applied to `v`, then to `fun x : T => b`.
  So every structural pass (instantiate, abstract, shift, level
  substitution, scope, audit) treats `T` and `v` at the let's depth and
  `b` one binder deeper, as Lean's do, with no new binary tag; the passes
  that treat `letE` specially recognise the outer application. The audit
  checks the leaf's fields; a leaf elsewhere, or a let whose second
  argument is no λ, is invalid where a pass interprets it. (Since
  compact-store plan step S5, parts 4-5, 2026-11-11: a let is a binary
  node of its own, `LET(v, fun x : T => b)`, its tag the `nonDep` flag,
  read in place from the export's `letE` record; ADR 0016's note.) The feed
  stages `letE` records so (`import/feed.fs`); the first importer
  (`checker-input.fs`) still makes the U2 leaf, as for projections.
- *Spine*: `get_app_fn` stops at a let (`mixed-head.fs`), so a let at
  the head of an application is the head.
- *`infer_let`* (tc 208–230; `mixed-infer.fs`): a chain of lets in one
  visit, as Lean's loop; while deciding, `T`'s Sort (`typeExpected`, S2's
  code 56) and `is_def_eq(type of v, T)` (`letTypeMismatch`, new code
  94); then a let variable of the local context (type and value closed),
  the body one binder deeper, its type through `cheap_beta_reduce` and
  closed as `mk_pi(fvars, r, true)` (`local_ctx.cpp` 93–125,
  `mk_binding` with `remove_dead_let`): innermost first, a variable the
  type does not mention dropped, any other wrapping it in a let
  (`nonDep` false, `mk_let`'s default). Infer-only mode skips both
  checks, as Lean.
- *Zeta* (tc 542–544; `whnf.fs`): a let is its body instantiated with
  its value, reduced again; a let at an application's head is reduced
  first (514), then beta or the arguments applied again. `whnf_fvar`
  (409–417) was in place since 4.2.2a. `is_def_eq` needs nothing else:
  `quick_is_def_eq` leaves `Let` undecided and `whnf_core` (step 3)
  removes it.
- *Evidence* (Gforth 1.0.0, Lean 4.35.0): the definitional-equality
  table's `let.*` rows, now required to give Lean's verdict (7: the four
  of the table, accepted ×3 and `letTypeMismatch`, and three added and
  Lean-checked: `let.dependent-body`, whose type is a let term,
  `let.chain`, `let.type-not-a-type`, `typeExpected`); first-checker row
  `identity.let` accepted (was *unsupported*; Lean accepts) at all three
  capacities and fed. The inductive rows `lit.div-by-zero` and `lit.gcd`
  get past their lets but stay pending, now *unknown*: `eq_of_heq`
  needs K-like reduction of `Eq.rec` on a proof that is no constructor
  (`to_cnstr_when_K`, diagnostic 81), plan task 5.2.1c. Planted faults
  `let-*` (18), all caught.

## Test plan

1. **This table as a LeanForth differential** (4.3.1): a terms file prints
   the 50 cases for LeanForth (as `binder-domains-terms.lean` does); every
   row outside the deferrals must give Lean's verdict and exception kind,
   and every accepted row **Lean's unfold counts** (LeanForth counts
   unfoldings per constant the way Lean's diagnostics do, recursor
   reductions included); deferred rows *unknown* or *unsupported*.
2. **Earlier tables**: the first checker's 69 rows, the 22 binder-domain
   rows and the 49 universe-scope rows re-run; only the K1–K3 rows may
   change, each to Lean's verdict: 11 of the 69 (9 to *accepted*,
   `constant.needs-unfolding-wrong` and `pi-body.needs-unfolding-wrong` to
   *rejected*) and 6 of the 22 (4 *equal* or *accepted*, 2 *apart* or
   *rejected*).
3. **Randomized differential against Lean's kernel**: seeded generators of
   small environments — definitions with random hints (honest, equal and
   inverted heights, abbreviations, opaque hints), theorems, opaque
   declarations — and of declarations whose check compares random closed
   and open terms (binders, applications, `let`, eta-expanded and
   beta-expanded forms, proofs and non-proofs); Lean's verdict and counts
   from `addDeclCore`, and `Kernel.isDefEq` in both orders; seeds,
   counts and the outcome mix recorded; zero disagreements required.
4. **Unit tests per ported function** in `tests/core/`, reaching every
   step of the `is_def_eq_core` table and every row of the lazy-step
   table, each outcome (yes, no, unknown, exhausted, full).
5. **Caches**: every corpus with caches on and off (identical verdicts);
   hit and miss counters; no entry survives a check (a planted stale
   entry from another context or an earlier check is never read); the
   success cache answers both orders.
6. **Fuel sweeps**: for every row, budgets from 0 upwards give
   *exhausted* until the verdict appears and never another verdict.
7. **Planted faults** (`tests/mutants/faults.toml`): hints compared the
   wrong way; abbreviation not first; opaque hint not last; the argument
   test skipped, done for abbreviations, or done first-argument-first
   (counts change); an opaque declaration unfolded; a theorem not
   unfolded (caught by `whnf.theorem`, and in phase 5 by the recursor
   rows); eta in one order only; proof irrelevance tested on `s`; a `let`
   variable opaque; a non-symmetric success cache; caches kept across
   checks. Each must fail a test.

## Amendment 1: the caches as built (plan task 4.2.7, 2026-11-05, proposed)

Status: proposed; [kernel] gate owed (review, owner). Code:
`src/kernel/caches.fs`, hooks in `whnf.fs`, `defeq.fs`, `mixed-infer.fs`,
`mixed-convert.fs`, `mixed-open.fs`.

**What is cached** — Lean 4.35.0's `type_checker::state` (Q10), filled
and read where Lean fills and reads it: inferred types per mode
(`m_infer_type[infer_only]`, tc 332–334, 356), `whnf_core` (490–493,
547–549, also at each recursive call), `whnf` (724–739), `m_unfold`
(573–579), successes (804, 1211; both orders) and same-head failures
(1004–1009). 4.35.0 has **no equivalence manager** (`type_checker.h`
33–39: `is_def_eq` is not transitive); none is added. Also Lean's cached
node data (`loose_bvar_range`, `has_fvar`): the `has_loose_bvars` and
`has_fvar` walks are answered from it, `instantiate` and `abstract` skip
unchanged subterms as `replace` does (instantiate.cpp 103, abstract.cpp
19), and `==` holds at once for one skeleton.

**Keys** — Q3's skeletons, computed per check in a table instead of per
tier: a node's skeleton is its tag with its children's skeletons, or for
a leaf the data `mixed-compare.fs`'s `==` compares (bound-variable index,
free-variable node, level syntax by skeleton, constant name and
universe-argument skeletons, literal value, projection name and index,
let flag); a literal of several limbs keys by its own node. Equal
skeletons imply Lean's `==`; the converse can fail only for such
literals and for equal names with two numbers (a miss, never a false
hit). An inferred type's key adds the scope (Q2 note): 0 for a node
without loose bound variables, else the identity of the scope's
innermost free variable, which fixes the scope; a chained lambda (whose
type is not closed) is not cached. The pair caches take closed terms
only. Values are nodes checked by identity: a discarded node misses.

**Invalidation** — every table empties when a check begins and when an
inference job starts (a new local context: an inductive block starts
several without discarding scratch). A node whose leaf is a free
variable not live in this job, a malformed bound variable or an unknown
tag has no skeleton, so the passes meet it uncached and fail as before.

**Why sound** — each cached function is a function of its key within one
snapshot and one local context (Q10's argument); only definite results
are kept (no *unknown*, *exhausted*, *full*, *invalid*, *rejected*);
pair caches run only with a typer, so the doubt record cannot arise, and
a failure is kept only without doubt. Scratch is kept until the job ends
while the term, level and reference stores have ample room (2^18, 2^14,
2^16 records); a smaller store discards as before, so tests that measure
room are unchanged.

**Fuel** — entering a pass costs one unit as before, a hit too, and a hit
ends it; a miss costs nothing extra (the wrapper's unit is given back);
lookups, skeletons and node data cost nothing, like Lean's hashes and
node flags. Skipped walks and subterms are no longer charged, so a check
needs less fuel; less fuel still only ever gives *exhausted* (or
*unknown* for a dependency out of fuel).

**Off** — with the derivation log on (a hit would skip logged steps:
plan task 4.2.7b, log it as Q11's rule 23), outside a check, and under
`false lf-caches-enable` (tests). Off reproduces the previous checker
exactly (Init's first 50,000 lines: identical verdicts and total fuel).

**Evidence** — caches on and off give identical verdicts on all 285 NDJSON
fixtures (2,010 declarations) at fuel 2,000,000 and on Init's first
50,000 lines (1,230 declarations: 1,216 accepted, 14 unknown, both); a
randomized fuel run (seed 4207, fuel below 3,000) gave no verdict other
than the final one, *exhausted* or *unknown*; eight planted faults (mode
ignored, tables never emptied, success kept on a no, Sort skeleton
without its level, skip one binder early, scope ignored, value identity
unchecked, dead free variable kept) are all caught. Init's first 50,000
lines at the default fuel: 971 accepted, 251 unknown, 8 exhausted before;
1,164 accepted, 63 unknown, 3 exhausted after.

**Review rvCACHE and rvCONV L1 (2026-11-10, fixes FX1)** — a bound
variable whose loose count would overflow a cell (index at least
`max-n 2/ 1-`) gets no skeleton, so every pass meets it uncached (L1;
unreachable today, as the audit bounds every index by its binders);
inference looks up and keeps only nodes it may read
(`lf-minfer-source?`), so a node it refuses stays refused (L2); and
`is_def_eq_core`'s direct calls (`is_def_eq_offset` 1049, lazy delta's
`reduce_nat` 1062 and 1064, `is_def_eq_unit_like` 1129) open the
comparison itself (`lf-dq-core-call`), so the success cache keeps only
what `is_def_eq` keeps (1211; rvCONV L1). Planted faults: universe
arguments, projection index and literal value left out of a key are
caught by `tests/core/check-block.fs`'s `cache.*` and literal rows; a
free variable keyed by entry number, pair caches over open terms and a
keep threshold of 0 are listed as gaps in `tests/mutants/faults.toml`
(no test reaches a discard, an open pair met twice, or a store between
the run's live nodes and all it makes); a failure kept with doubt is
equivalent (no doubt arises where the pair caches work).

**Resource gap (rvCACHE L3; a temporary gap, never a verdict)** — kept
scratch (until the job ends, while a store has the room above) and the
extra frame each cached visit or `whnf_core` tail step opens can make a
check *full* where the uncached run decides. Plan task 4.2.7c (to be
added to the plan) closes it: on *full* with scratch kept, discard the
kept scratch, empty the tables and retry the job uncached.

**Outside a job (rvCACHE L4)** — step 12 of a block's check
(`inductive-recursor.fs`, `lf-rcr-whnf`) runs `whnf` outside any
inference job, on the tables and local context the last job left. The
argument above ("within one local context") still holds there: the
recursor builder's terms have no free variable (fields are read under
binders, as loose bound variables), so no key it meets names a free
variable of that context, and `whnf` of such a term is a function of the
term in the snapshot — the only typer-dependent steps, K and iota's
structure eta, need a closed major premise and an inference job
(`iota.fs`), and answer *unknown* elsewhere.

## Amendment 2: shared terms cost their nodes, not their paths (agent EX, 2026-11-10, proposed)

**Finding.** The 17 declarations of `Init`'s first 1,000,000 export lines
that ended *exhausted* at 2,000,000 fuel (36% of all fuel; the official
checker accepts the prefix in 5.8 s) are `omega`-style proofs of a few
thousand nodes shared along up to 2^40 paths. None ran out in `is_def_eq`
or in the projection steps: all 17 ran out in LeanForth's own audits
(U2, V1 and the structural check), which visited each path. With those
fixed, the next walls were `mixed-open.fs` (each pass rebuilt a shared
node once per path, so the result lost the sharing too), inference's
loose-variable scan, and the level substitution of a constant without
universe arguments.

**Ported** (each a Lean step that keeps the work per node):
1. *Audits per node.* Lean keeps a node's loose bound variables and its
   free-variable flag in the node (`expr.cpp` 102–105, `lean_expr_mk_data`)
   and reads them in constant time (`check_no_metavar_no_fvar`,
   `environment.cpp` 87–100; `infer_type_core`'s `has_loose_bvars`,
   `type_checker.cpp` 326). LeanForth's U2, V1 and structural walks keep
   per-term marks (a run number and the depth it was reached at,
   `constant-term-boundary.fs`): a node is checked again only at a smaller
   depth; a repeated visit costs its own unit. The outcome and the first
   failure found are those of the per-path walk (a node is skipped only
   when its whole subterm was checked at a depth no greater).
2. *Substitution per node and offset.* Lean's `replace` keeps each shared
   node's result per offset for the rest of the call (`replace_fn.cpp`
   16–40); `instantiate`, `instantiate_rev` and `abstract` use it
   (`instantiate.cpp` 15–39, 99–118; `abstract.cpp` 14–32).
   `mixed-open.fs` keeps every binary node's result for the pass in a term
   column (one offset per node, its last: met at another, it is rebuilt).
   This is Q12 item 1 in part (the memo is per pass, not per context).
3. *`loose_bvar_range` read, not scanned.* Inference's count of the scope
   variables a term needs (`lf-minfer-loose`) takes the caches' node data
   when they are on (`caches.fs`, `lf-ci-range`).
4. *`instantiate_type_lparams` without universe arguments* returns the
   stored type itself (`instantiate.cpp` 251–252), as `whnf.fs` already
   did for values; with the derivation log on the substitution still runs
   (same term), so the log keeps its step.

**Evidence.** `tests/cli/sharing.lean`: pinned Lean accepts `sharedAnd`
(2^40 paths) and `sharedBeta` (shared under two offsets) and rejects
their wrong twins (`appTypeMismatch`); LeanForth before: `sharedAnd`
*exhausted* (its twin too); after: Lean's verdicts, 61,647 fuel.
Planted faults `ex-*` in `tests/mutants/faults.toml`, all caught.

**A constant with universe arguments** (review rvPSE M1, agent FX7,
2026-11-11, [kernel] gate open). The level substitution's source audit
(`mixed-level-substitute.fs`) and its level walk (`level-substitute.fs`)
now check a node and push its children only at its first visit in a walk;
a repeat costs its unit. The checks read only the node, never the path or
depth. Lean's `instantiate_lparams` rebuilds a shared node once per offset
(`instantiate.cpp` 236–253, `replace_fn.cpp` 16–40); its level walks have
no cache (`level.cpp` 247–277). `tests/cli/sharing-universe.lean`: pinned
Lean accepts `sharedAndU.{u}` (2^40 paths, `u` in every leaf) and
`useU := sharedAndU.{0}` and rejects two wrong twins (`declTypeMismatch`);
LeanForth before: `useU` *exhausted*; after: Lean's verdicts, 8,419 fuel.
Planted faults `fx7-*`, all caught.

**Left (plan task 6.5.5).** Inference still closes each application
argument with all the scope's free variables, where Lean instantiates a
binder's body once, and every comparison audits both types in full; on
the Array.Extract `omega` proofs this costs 10–20 million fuel (9 of the
17). Both are 6.5.5's "work linear in a term's depth". (The first is
Amendment 3's, 2026-11-11.)

## Amendment 3: substitution as Lean's replace, node facts from the data word, inferred types keyed by the opened term (agent S6A, 2026-11-11, proposed)

Status: proposed; [kernel] gate owed (review, owner's approval of the fuel
model below). Plan task 6.5.5, parts (a), (d) and (e) of compact-store
plan step S6 (`.claude` plan row S6; parts (b) and (c) are elsewhere).
Code: `src/kernel/replace-memo.fs` (new), `mixed-open.fs`,
`mixed-shift.fs`, `mixed-instantiate.fs`, `mixed-beta.fs` (reset only),
`whnf.fs`, `mixed-infer.fs`, `caches.fs`. Lean's files at the referee
commit `eb6cafb7`.

**Ported.**
1. *Replace* (`replace_fn.cpp` 16–40; `instantiate.cpp` 15–37, 99–118;
   `abstract.cpp` 14–32; `expr.cpp` 448–463). Every substitution
   (instantiate, instantiate_rev, abstract, lift_loose_bvars, and the
   single-binder instantiate that beta uses) keeps a binary node's result
   per node and offset for the rest of the call, in one table per pass and
   context (`replace-memo.fs`, ADR 0016 C4's substitution memo; keys are
   identities, values checked by identity), and gives a node back
   unvisited when its data word (ADR 0016 C1) shows the function returns
   it: loose range at most the offset (`instantiate.cpp` 22, 103;
   `expr.cpp` 455), or no free variable for abstract (`abstract.cpp` 19);
   a lift by 0 is the term itself (`expr.cpp` 449); a node whose children
   come back unchanged is kept (update_app, update_binding). A node whose
   word names a free variable is kept unvisited by instantiate only on the
   caches' memo, which knows a free variable only while it is live (as
   since step S3), so a dead one is still refused. Lean keeps only shared
   nodes' results; keeping every one changes work, never a result.
2. *Node facts read, not scanned.* has_loose_bvars, has_fvar (`whnf.fs`)
   and loose_bvar_range (`mixed-infer.fs`'s count of the scope variables a
   term needs) read the data word, with or without the caches; a node
   without data asks the caches' memo, then is walked.
3. *Inferred types keyed by the opened term.* Lean infers the term that
   infer_lambda, infer_pi and infer_let instantiated with their free
   variables and keys its type by that term (`type_checker.h` 26–30,
   `expr_map` with ==; `type_checker.cpp` 125–171, 208–230, 332–334, 356),
   so a term that names only outer binders hits under any inner one.
   LeanForth reads source nodes under the scope (Q2); the key of an open
   node is now the skeleton of its copy closed with the scope (before: the
   node with the scope's innermost free variable, which missed under every
   new binder: agent DX measured 2.8–11.5 times Lean's inferences on the
   exhausted roots of `Init`). The closing is remembered per scope for the
   job: a closing under the whole scope is a function of the scope, which
   its innermost free variable names (each binder makes a new one;
   identities never repeat), so `lf-instantiate-scope` stamps its results
   with that identity and a later closing under the same scope finds them,
   at its root for no fuel. Inference closes an application's argument
   after inferring it, so the argument's subterms were closed already: no
   argument is closed in full again. As Lean's infer_pi opens a whole chain
   (144–166), an inner Pi of a chain is neither looked up nor kept (inner
   λs were not, Amendment 1); a loose bound variable is not keyed (its
   type is its entry's, 93–99). A closing that runs out of fuel or room
   ends the visit so; any other failure leaves the node uncached. While a
   check keeps no scratch (a small store: `lf-caches-keep?`) open nodes are
   not keyed.

**Fuel model** (Q9, changed by design; the owner approves it at the
gate). A substitution visit costs one unit, as before; a node given back
by its data word or by the memo ends its visit for that unit, so a call
expands each node at most once per offset ("a unit per distinct node per
call", plus one per edge into an expanded node); a closing found
remembered at its root costs nothing, as do memo lookups and keeps, the
data-word reads that replace the scans (Lean's flags and hash lookups cost
no steps); the closing of an open node for its key is paid as any
substitution (Lean's instantiate when it opens a binder). Less fuel can
still only give *exhausted* or *unknown*, never another verdict.

**Why sound.** Within a call the substitution is fixed, so a result is a
function of node and offset; across calls only closings stamped by a live
innermost free variable share entries, and the closing of a node at an
offset with the scope's innermost n' variables equals its closing with
the whole scope whenever n' covers its loose range (inference passes
exactly that, `lf-minfer-needed`). A memo entry is used only while its
key node and its result keep the identities kept with them. The inferred-
type key is Lean's: types are functions of the closed term within one
local context, and every table is emptied when a job starts (Amendment 1).

**Evidence.** `make test` and `make check` on the final commit (all
Lean-compared tables: the same verdicts). Planted faults: 16 new
(`s6a-*`: memo without offset or stamp, value identity unchecked, a skip
reaching the offset in each pass, a skipped free variable, abstract
skipping, no lift at all, one stamp for every scope, has_fvar or
has_loose_bvars misread, a loose count one short, a key failure dropped)
and 7 stale ones re-targeted, all 23 caught. Checker trials (2,000 × 300;
trial digest `902a42ce549d` → `670bff75d128`, as fuel is folded in; outcomes
ok 1,166,038 → 1,168,012, exhausted 476,867 → 474,875, invalid +1,
unknown +20, rejected −3): 1,482 trials keep their outcome mix; the 518 that change move only
between *exhausted* and *ok* except 39, and in each of those 39 the first
call that differs went from *exhausted* to *ok* (36) or *unknown* (3) on
the same store, the rest following from the different store; no trial
has more *exhausted*. `Init`'s first 1M lines (`check --fast
--no-manifest`, default fuel): 8,672 → 8,695 accepted, 518 → 501 unknown,
12 → 6 exhausted, every move to *accepted* (Lean's verdict); fuel
202,224,048 → 161,723,424 (1,751 declarations use more, at most 8.6%
more, 5,880 less); check CPU 163 → 159 s. All of `Init` (`check --fast
--no-manifest --resources`, default fuel): 54,556 → 55,587 accepted,
4,703 → 3,735 unknown, 90 → 27 exhausted; 65 *exhausted* and 966
*unknown* (a dependency out of fuel) are now accepted, Lean's verdict,
and 2 that were *unknown* for a dependency now run themselves and run out
of fuel (`Array.cons_lex_cons`'s private lemma, `Std.Iter.step_flatMapAfterM`);
no other move; fuel 1,521,467,121 → 1,187,033,444 (8,864 declarations use
more, at most 9% more, 41,923 less); check CPU 1,384 → 1,147 s; peak
memory 1,280 → 1,098 MB.
`_private.Init.Data.Array.Extract.0.Array.extract_append._proof_1_1`
(blocks about 3,290 unknowns, agent DX): 21,299,931 → 15,767,375 fuel
(cut of its dependencies, `--fuel 60000000`): 6.3 M of it is the
per-conversion audit (`lf-mcompare-roots`, plan row S6 (c)), and with the
check's scratch room raised from 2^20 to 2^22 terms (`feed.fs`, not
changed here) it needs 9.0 M: past about 786,000 scratch nodes the caches
stop keeping (`lf-caches-keep?`), and its comparisons rise from about
21,000 to 533,000. `make test-depth-deep-differential` (six rows 10,000
deep, fed; Lean's verdicts before and after): 162 s → 6.1 s.

**Left.** The audits at every comparison and rebuild (S6 (c), agent S6C),
`instantiate_lparams` per node (S6 (b)), Lean's == by hash (agent DX's
finding 2), and the check's fixed scratch room above (a temporary gap:
*exhausted* where Lean decides; plan task 6.2.2 removes the fixed 2^20-term
scratch room, as it does `feed-term-room`).

## Amendment 4: each node audited once per check (compact-store plan step S6 (c), agent S6C, 2026-11-11, proposed)

Status: proposed; [kernel] gate owed. It changes LeanForth's own
fail-closed defence, not a rule of Lean's: no typing, reduction or
conversion step changes, and every verdict that moves is an *exhausted*
that becomes Lean's.

**Finding.** After Amendment 2 the structural audit (`lf-cterm-check`,
`src/core/constant-term-boundary.fs`) checked each node once per *audit*,
and audits run at every comparison (both roots, `lf-mcompare-roots`),
every rebuilding pass (`lf-rebuild-audit`: shift, instantiate, beta),
every universe substitution's source, every inference job's preflight and
every V1 (`lf-constant-term-scope`, which also walked the scope). Lean's
kernel runs none of them: its terms are well formed by construction and
it reads `loose_bvar_range` and `has_fvar` from each node (`expr.h`;
`infer_type_core` 326, `check_no_metavar_no_fvar`). On `Init` at main
dbc39ad 28 of the 95 roots that ran out of fuel stopped inside the
structural audit and 5 inside the level-scope check it runs per constant
(Mathlib 1/6: 51 and 11 of 321); in the stuck `Init` roots the audits took
25-41% of the fuel, nearly all of it the per-comparison audits (agent DX,
`.claude/work/DX/REPORT.md`).

**Decision: keep every audit, drop the repetition.**
1. *A memo per check.* While the memo is on, a node reached by an audit
   run that ends ok is kept as checked in its marks unit, as (epoch,
   identity); a later audit in the same epoch pushes no kept child and a
   kept root costs no fuel. Two epochs: the closed one, for nodes without
   a free variable (the data word's bit clear), and the open one, for
   nodes with one; a node without a data word is never kept. Both are new
   numbers from the run counter (never a run's own number) when a check
   begins (`lf-check-begin`), when the memo turns on, when the counter
   wraps, and when one of the generations the audit reads differs from
   those the closed epoch captured (term, level, reference and name
   stores, literal limbs, string bytes, the parameter context); the open
   one alone when the local context's generation moves (inference empties
   it for each job). The memo is on in a check of the checked environment
   (`lf-whnf-env?`, where the caches are), off elsewhere, so unit tests and
   probes audit as before; `lf-audit-memo!` sets it (tests).
2. *V1 from the data word.* After the structural audit, a root whose data
   word shows no free variable and a loose range at most the depth passes
   (`lf-cts-word?`); any other root (out of scope, a free variable, no
   data word) takes the scope walk as before, so its verdict, diagnostic
   and fuel are unchanged.
3. *U2 from the data word.* A root with a data word holds no unsupported
   leaf (such a leaf has none, nor has any node above it); a root without
   one takes the walk (`lf-check-forms-word?`).
4. `lf-cref-reset` advances the reference store's generation, as term and
   level resets do (it set the count alone).

Not changed: every call site of the audit (the declaration's entry audit
where input enters, conversion, the rebuilding passes, inference's
preflight, universe substitution, whose own graph check plan step S4
retires); the level-scope check is not memoised by itself (its calls
inside the term audit go with the term memo; level comparison's and
level value's own calls stay per call, measured at 0.4% of the fuel of
the stuck root below).

**Why no node reaches a rule unaudited.** A pass reads a root only after
an audit of it returned ok in this check. That audit either walked it or
found it kept. A node is kept only by a run that ended ok, and such a run
checked every node it reached and reached every child of every node it
visited, except children kept themselves; by induction over the epoch's
runs every kept node's whole graph was checked in this epoch. It stays
checked because nothing the audit read can change within the epoch:
- *The node and its children.* Records are never written after they are
  made (`terms.fs`; only the test fault words of
  `tests/support/store-faults.fs` write fields); a rollback gives back a
  suffix (store marks, the joint scratch marks of step S1), so the
  children of a live node, which come earlier, are live and the same; an
  index given back and made again has a new identity (serials never
  rewind), and a unit counts only with its node's identity.
- *Stamps* of a constant or symbolic Sort are written when the node is
  made.
- *References and levels* a node names are made before it, so a joint
  rollback that gives them back gives the node back; level-only rollbacks
  (`level-substitute.fs`, `level-normalize.fs` on failure) give back only
  levels their own pass made, which no live term names; a reset advances
  the store's generation, which starts a new epoch.
- *The parameter context, names, literal limbs and string bytes*: every
  change advances a generation (the slabs only grow within a context).
- *Free variables*: liveness depends on the local context. A node with
  one is kept in the open epoch, which ends with the local context's
  generation; within one job an entry goes only with its node
  (`lf-lctx-drop` at a scratch rollback), so a live node's free variables
  stay live.
A run that does not end ok keeps nothing. V1 and U2 read data words that
`terms.fs` computes from the children when a node is made, never from
input (ADR 0016 C8), and that equal Lean's `loose_bvar_range` and
`has_fvar`. With the entry audit's U2 and V1 removed, the malformed
inputs of `tests/core/check-declaration.fs` still end *invalid* or
*unknown*, never accepted (inference and the other audits meet them).

**Fuel.** A kept root costs nothing and a kept child is not visited; V1
and U2 of a root with a data word cost nothing; every failure costs as
before. A check needs less fuel, so only *exhausted* (or *unknown* for a
dependency out of fuel) can become a decided verdict.

**Evidence.** `make test` and `make check`. On top of Amendment 3 (main
3578de5 against the merge, `check --fast --no-manifest`, default fuel
2,000,000): full `Init` 55,587 → 55,750 accepted, 27 → 16 exhausted,
3,735 → 3,583 unknown; all 163 moves are to Lean's verdict (Lean accepts
all of `Init`): 11 declarations that ran out of fuel and 152 that were
unknown only through such a dependency are accepted, none moved away and
no accepted declaration uses more fuel (list:
`.claude/work/S6C/init-moves2.txt` of the agent's worktree); fuel
1,187,033,444 → 791,610,006 (−33%); whole run's CPU 1,175 → 1,073 s
(`gforth-fast`, a loaded machine); peak resident memory 1,072 → 1,051
MB. The first 1M lines: 8,695 → 8,696 accepted, 6 → 5 exhausted
(`Array.extract_append._proof_1_3` accepted), fuel 161,723,424 →
109,613,586 (−32%), check CPU 147.9 → 147.7 s, peak memory 302 → 313 MB
(the run's list of reached nodes). `Array.extract_append._proof_1_1`,
which blocks most of `Init`'s remaining unknowns, with its dependencies
alone (DX's cut, fuel 40M): 15,767,375 → 8,368,183 (Amendment 3's
measurement put 6.3M of it in the per-comparison audits); still above
the default 2,000,000. Over that cut the audits now take 5% of the fuel
(633,132 of 12,531,033), `==` 6.5%, the level-scope checks of level
comparison 4.8%. The 2,000 checker trials: `670bff75d128` →
`056b65372109`, re-baselined; 1,989 trials differ, each trial's later
random choices following the fuel left (ok 1,168,012 → 1,171,229,
invalid 356,575 → 357,089, exhausted 474,875 → 467,820, unknown 405,130
→ 407,009, rejected 90,014 → 91,459, full 4 → 4).

Measured first on main b4c6935 (before Amendment 3). The first 1M lines of `Init`
(`check --fast --no-manifest`, default fuel 2,000,000): 8,672 → 8,674
accepted, 12 → 10 exhausted, 518 unknown, the two moves to Lean's verdict
(`Array.extract_append._proof_1_2`,
`Array.extract_append_extract._proof_1_2`), no other verdict moved; fuel
202,224,048 → 145,072,524 steps (−28%); check CPU 170.7 → 162.2 s;
peak resident memory 323 → 331 MB (the run's list of reached nodes).
Full `Init` (same command, against main b4c6935): 54,556 → 54,920
accepted, 90 → 52 exhausted, 4,703 → 4,377 unknown; all 364 moves are to
Lean's verdict (Lean accepts all of `Init`): 38 declarations that ran out
of fuel and 326 that were unknown only through such a dependency are
accepted, none moved away (list:
`.claude/work/S6C/init-moves.txt` of the agent's worktree); fuel
1,521,467,121 → 1,107,410,988 (−27%); check CPU 1,385.8 → 1,332.1 s
(−4%, `gforth-fast`, a loaded machine); peak resident memory 1,279 →
1,275 MB. Four of the stuck roots
of `Init` with their dependencies alone (DX's cuts, fuel 20M):
`WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix` exhausted
before, accepted with 18,453,088 after (over its cut the audits' fuel
5,685,126 → 263,483, the level-scope checks' 1,750,591 → 82,839);
`Array.extract_append_extract._proof_1_1` 17,824,836 → 10,787,727;
`IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'`
13,430,006 → 8,847,858; `Std.Iter.step_flatMapAfterM` 13,103,450 →
8,300,367 (all still above the default 2,000,000). The 2,000
checker trials (`scripts/trial-digest.sh`): `902a42ce549d` →
`f3019867dbc3`; 1,989 trials differ because each trial's
later random choices follow the fuel left (outcomes over all trials: ok
1,166,038 → 1,169,256, invalid 356,574 → 357,087, exhausted 476,867 →
469,809, unknown 405,110 → 406,991, rejected 90,017 → 91,463, full 4 →
4). Planted faults `s6c-*` in `tests/mutants/faults.toml` (12: a unit
taken without its identity, a failed run that keeps, a free variable's
node in the closed epoch, the local context or the generations ignored,
the memo on outside a check, no child pushed, a reference reset without
its generation, no new epoch per check, V1 passing a free variable or one
binder too many, U2 passing a root without a data word), all caught; the
nine earlier faults on the audits' code re-run, all caught.

**Left.** Lean's `==` checks pointer identity at every pair, rejects at
once on different hashes and caches pairs (`expr_eq_fn.cpp` 44-58);
`lf-expr-equal` checks identity only at its roots and walks the rest (13-20%
of the stuck roots' fuel before Amendment 3, DX; 6.5% of the cut above):
a follow-up, as a structural hash needs room the 16-byte record lacks (a
column or step S4's interning). The level-scope check that level
comparison and level value run on both levels per call (4.8% of the cut)
could keep its own memo per level node in the same way; levels are not
hash-consed before step S4. `instantiate_lparams` per node is step S6 (b).

## Amendment 5: == at every pair, caches keyed by node (compact-store plan step S4, agent S4, 2026-11-11, proposed)

Status: proposed; [kernel] gate owed. Code: `src/kernel/mixed-compare.fs`
(`lf-expr-equal`), `src/kernel/caches.fs`,
`src/kernel/mixed-level-substitute.fs`, `src/kernel/level-compare.fs`;
the storage side is ADR 0016's S4 note. No typing, reduction or
conversion rule changes; every verdict that moves is an *exhausted* (or
an *unknown* behind one) that becomes Lean's.

**Ported.**
1. *Lean's `==` at every pair* (`expr_eq_fn.cpp` 44-58, `apply`): one
   node is equal at once (`is_eqp`), at the root and at every child
   pair; two nodes whose data words (ADR 0016 C1: loose range, the
   parameter and free-variable bits and the depth, each a function of
   the term's structure as Lean's hash is) are known and differ are
   apart at once (Lean's `hash(a) != hash(b)`); a pair met before in the
   call is not walked again (Lean's per-call `check_cache`: had it
   differed, the call would have ended); two constants of one interned
   reference, or two Sorts of one hash-consed level, are equal at once
   (`is_eqp` on the name and levels). None of these is pushed, so none
   costs a unit. Before, `lf-expr-equal` checked identity only at its
   roots and walked the rest (6.5% of the fuel of a stuck root after
   Amendment 4, agent S6C).
2. *Caches keyed by node* (Amendment 1's keys). With levels hash-consed
   and references interned (ADR 0016's S4 note), equal constants and
   Sorts are one node, so a node's number is its class under `==` and
   the result caches key a node by its identity; the skeleton memo and
   its key table are retired. Lean's node facts are the data word; the
   memo left checks only, for a node whose word names a free variable,
   that every free variable in it is live in this job (Amendment 1's
   dead free variable). Two nodes that are `==` but not one node (made
   while sharing was off, two literals of one value, a constant or Sort
   made again because its stamps no longer held) are two keys: a miss
   where Lean hits, never a false hit. Step S3 measured that keying by
   node before this step lost 142 accepted declarations on the first 1M
   lines of `Init`; after it none is lost (below).
3. *`instantiate_lparams`' `has_param_univ` test* (`instantiate.cpp`
   232-237, the skip at line 236): universe substitution neither audits nor rebuilds a term
   whose data word shows no universe parameter; it is its own image.
4. *Level comparison's scope checks per level*: in a check, a root
   level found in scope is kept with its identity and the parameter
   context's generation (a column of the level store) and is not walked
   again while both hold (Amendment 4's note: 4.8% of a stuck root).

**Why sound.** `==`: a node is equal to itself; data words are computed
from the children when a node is made (never read from input, C8) and
are equal for equal structure, so a difference proves a difference; the
pair set only skips pairs already being compared in the same call; a
constant's interned reference fixes its name and levels, a Sort's
hash-consed level fixes its level. Keys: a cached function is a
function of its argument within one job (Amendment 1), and a node's
identity names exactly one node, never reused. `has_param_univ`: a term
without universe parameters is unchanged by the substitution, and its
levels need no check against the formals (none is a parameter); the
graph audit still runs on the whole root. Level memo: a level's graph
never changes while its identity holds, and every change of the
parameter context advances its generation.

**Fuel.** Fewer units: a pair answered at once, a skipped term, a kept
level cost none. Less fuel can only turn *exhausted* (or *unknown* for a
dependency out of fuel) into a decided verdict.

**Evidence.** See ADR 0016's S4 note: the first 1M lines of `Init` and
all of `Init` before and after, every move to Lean's verdict; `make
check`; planted faults `s4-eq-*`, `s4-cache-key-stale-node`,
`s4-fvmemo-children-live`, `s4-mls-*`, `s4-lcmp-memo-*`, all caught.

## Amendment 6: an argument put into a closed Pi body is not closed; a closed key's facts from its data word (agent PF, 2026-11-11, proposed)

Status: proposed; [kernel] gate owed. Code: `src/kernel/mixed-infer.fs`
(`lf-minfer-put-closed`), `src/kernel/caches.fs` (`lf-copy-id`). No
typing, reduction or conversion rule changes; the type inferred is the
same node as before; every verdict that moves is an *exhausted* that
becomes Lean's.

**Finding** (the Lean Kernel Arena's seven `good/perf` tests that
LeanForth gave up on; `.claude/work/PF/ROOTCAUSE.md`). Lean's `infer_app`
types `f a` as the function type's Pi body instantiated with `a`
(`type_checker.cpp` 187), and `instantiate` gives back a body whose
`loose_bvar_range` is 0 at once, never reading `a` (`instantiate.cpp` 22:
`s >= get_loose_bvar_range(a)`): every non-dependent arrow. LeanForth reads
`a` under the scope (Q2) and closed it with the scope's free variables
before every such substitution (Amendment 3's closing). The closing it had
made for `a`'s cache key is remembered only while the replace memo keeps
it (at most 2^20 entries, `replace-memo.fs`); on a large term the memo is
emptied first and `a` was closed again, its whole size. On the arena's
`let-ladder` (2,000 `let`s, each `x + (let …)`) that was 18,826,994 of
38,983,499 units. Separately, the key of each closed copy was found by the
free-variable memo's walk of the whole copy (`lf-term-facts`), checking
that its free variables are live: no fuel, but 24.9 of 65.4 s on the same
test after the first change.

**Ported.**
1. *An argument for a closed body is not closed.* When the Pi body's data
   word (ADR 0016 C1) shows no loose bound variable, the substitution runs
   with the argument as it is, keeps the body by its data word for one
   unit, and never reads the argument (no loose bound variable remains to
   put it for); a body with a free variable is checked for live free
   variables as before. A dependent body, or one without a data word, gets
   the closed argument as before.
2. *A closed key's facts from its data word.* The identity and bits of the
   copy a closing just made for an inferred-type key (`lf-ci-copy`) are
   read from its data word, as Lean reads `has_fvar` from the node. The
   walk is not needed there: a closing that succeeded holds only live free
   variables (the scope's, live while their binders are open; the leaves
   it visited, each checked; nodes the hook kept, found live; and memo
   results made in this job, which inference empties when a job starts,
   whose free variables are older than they are and go only by a scratch
   rollback that takes the results too). Every other caller of
   `lf-term-facts` keeps the walk.

**Fuel.** Item 1: the closing's units are no longer spent; the
substitution's one unit stays. Where a later closing of a larger term
would have found the argument's closing remembered, it visits the
argument itself instead, for what the closing here would have cost; no
declaration measured below needs more. Less fuel can still only give
*exhausted* or *unknown*, never another verdict. Item 2 changes no fuel.

**Evidence.** `tests/core/mixed-infer.fs`: a closed body costs one unit
(six with the closing), a dependent one gets `id A x` closed; the `poly`
case's fuel 49,937 → 49,938 left. `tests/core/check-declaration.fs`: the
`sweep-unfolding` case accepted from 60 units (62).
`tests/core/infer-deep.fs`: in a 64-node store the deepest `f (f … c)`
that infers grows from 27 to 54 applications, as no argument is copied
(Lean makes none either). The pinned fuel of
`mixed-definition-probe.fs`, `tests/cli/leanforth.fs` (`inductive.ndjson`
518 → 508) and the report digests of `tests/cli/test_leanforth.py` (11
re-pinned) move with it: compared with main, every report is the same but
for fuel, 97 declarations use less and none more. `tests/cli/shared-depths.lean`
P3: the arena's let-, beta- and app-ladders at n = 48, with bad twins
pinned Lean rejects (letTypeMismatch, declTypeMismatch, appTypeMismatch);
LeanForth agrees, memo on and off, and `shared_depths.py` bounds the good
rows' fuel. Planted faults `pf-put-always-closes`,
`pf-put-dependent-unclosed` and `pf-copy-id-one-key`, caught; the earlier
faults on the code changed (`infer-arg-unclosed`,
`s6a-infer-key-failure-ignored`, `cache-dead-fvar`,
`s4-fvmemo-children-live`, `cache-identity-unchecked`,
`cache-scope-ignored`, `s4-cache-key-stale-node`) re-run, all caught. Arena `let-ladder` (`check --fast`,
fuel 400M): accepted with 38,983,499 → 20,072,078 units, check CPU
85.9 → 66.9 s (item 1) → 39.9 s (both), peak memory 1,291 → 866 MB; at
the default 20,000,000 it is still *exhausted*: what is left is Lean's
own `instantiate_rev` of each `let` body, Θ(n²) (ROOTCAUSE.md, cause C2,
a question for the owner about the fuel budget). Arena `beta-ladder`
(fuel 400M, accepted, 28,078,156 → 28,074,156 units): check CPU 61.8 →
40.9 s, peak memory 1,111 → 804 MB. Agent DX's cuts of two `Init` roots
(default fuel, both accepted before and after):
`WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix` 554,047 →
552,473 units, `Vector.extract_append._proof_1` 4,394,015 → 4,374,321;
check CPU the same (2.1 s; 15.9 → 16.1 s).
The 2,000 checker trials (`scripts/trial-digest.sh`): `f78118062cf9` →
`e96c47672b69` with item 1 (item 2 changes nothing there); 1,980 trials
differ, and in every one the first call that differs keeps its outcome
(what differs is the fuel left or the store's counts: the closed argument
is no longer made), the rest following from the fuel left (outcomes over
all trials: ok 1,175,302 → 1,175,500, invalid 367,209 → 367,046,
exhausted 457,164 → 457,203, unknown 406,080 → 405,983, rejected 88,851 →
88,877, full 4 → 1).

**Default fuel** (owner, 2026-11-11, on PF's question). The command
line's fuel per declaration is 100,000,000 (`src/cli/leanforth.fs`,
`cli-default-fuel`; it was 20,000,000): Lean's own kernel takes 20-91
million of the same steps on the arena's Θ(n²) tests, which no change
that follows Lean lowers. Both changes bump the verdict version to 3
(ADR 0020 D3; `src/kernel/verdict-version.fs`; 2 was step SN5's), so
every older snapshot is refused as stale (or labelled stale with
`--snapshot-stale-ok`), and the golden snapshot fields
(`tests/cli/golden-snapshots`) are written again: only the header's
verdict version and fuel setting and 99 slots' fuel moved, all to less.

## Amendment 7: a check's fuel independent of the other records of the tier (agent PF, review rvSN4 B1, 2026-11-11, proposed)

Status: proposed; [kernel] gate owed. Code: `src/import/feed.fs`
(`feed-enter`, `feed-merge`), `src/core/terms.fs`
(`lf-term-input-binder-first`, `lf-term-input-binder-merged?`,
`lf-term-findable?`), `src/core/levels.fs`
(`lf-level-findable?`), `src/core/level-scope.fs` (`lf-lscope-reached`),
`src/core/constant-term-boundary.fs` (`lf-audit-reached?`,
`lf-audit-level-reached?`), `src/kernel/check-declaration.fs`
(`lf-check-findable`, `lf-check-level-findable`). No typing, reduction or
conversion rule changes: every change decides only which node, of nodes
that are equal, stands for a term or level, never what it is.

**Finding** (review rvSN4 B1). Amendment 5 keys the caches by node and
lets `==` and the memos answer by identity, relying on hash-consing to
make a node's number its class. A check's fuel then depended on which
other records the tier held, so a declaration checked against a snapshot
(ADR 0020 D5) could use other fuel than in a fresh check, and a verdict
near the fuel budget could differ (the review's p7: `Implies` *exhausted*
fresh, *accepted* against a snapshot, at fuel 35). Three causes, found in
turn on Mathlib's first 1M lines against `Init`'s snapshot (agent SN4:
2,151 of 13,023 declarations with other fuel):
1. *Binder names.* Two input binders that differ only in a binder name
   (or binder information, which Lean's `==` ignores too) were two
   nodes, and the binder table gave a binder a check makes the first
   record of the class in the whole tier, another declaration's or the
   snapshot's.
2. *Earlier nodes found by hash-consing.* A term a pass makes was given
   any equal node made before the check (an input node, or a copy the
   importer made), whichever declaration it belongs to; such a node is
   never rolled back while a store node is, and the caches and memos
   keyed by the store node then miss. So `Membership.mem` took 400 fuel
   in `Init`'s export and in a cut of the Mathlib prefix, 396 in the whole
   prefix (records after it in the file changed it).
3. *Earlier levels*, likewise: a level a pass makes was given the
   importer's equal level, which keeps level comparison's scope memo
   (Amendment 5, item 4) across a pass's rollback; `Equiv.trans._proof_1`
   took 8,589 fresh and 8,583 against the snapshot.

**Change.**
1. The importer's first pass enters each binder read in place in the
   binder table as before; a binder whose tag and children equal one
   entered before it is marked to copy instead, and its copy is that
   earlier binder; its parents are copied too and are the tier's records
   of those fields when there are some. So each `==` class of input
   binders, and every node above one, is one node. Not with a binder hook
   (the print command keeps every binder's own name to print it, so its
   checks share as before and may use a little more fuel than `check`'s;
   `print` writes no snapshot). Lets likewise (review rvRS F2, agent
   FXR, 2026-11-12): Lean's `==` compares a `letE`'s type, value, body
   and `nonDep` flag but not its name (`expr_eq_fn.cpp` 104-109, SHA-256
   `7feb30ca…07c`, read again), so a let read in place whose tag (the
   `nonDep` flag) and leaf fields (its value and lambda) equal a let
   entered before it is copied, and its copy is that earlier let; the
   first pass now enters every other let's leaf, so that a later let
   finds it. Before, only binders were merged: of two lets differing in
   their names only the first was findable by its fields, and rule 2
   declined it when it was another declaration's, so `B` of
   `tests/cli/let-b.lean` took 295 fuel fresh and 302 against the
   snapshot of `let-zd.lean` (`Zd := let x : Nat := 0; x`). A parallel
   check's worker, which reads
   the source's input in place (shared input, ADR 0016 S8), marks the
   same binders to copy -- those whose class the source's binder table
   holds another binder for -- and so makes the source's copies; without
   that its input's fingerprint was not the source's, no worker could be
   made and `--jobs` ran one declaration at a time (found when main's
   shared input was merged into this work, before any run used both);
   for lets, those whose fields the source's leaf table holds another
   let for.
2. In a check (the audit memo on, Amendment 4), hash-consing gives a node
   made before the check -- below the input's term mark -- only once the
   check has reached it: an audit of this check's epoch kept it.
   Otherwise a new store node is made, as in an export without that
   record. Nodes made in the check are given as before; outside a check
   (the importer's feed) every node is.
3. Levels likewise: a level made before the check (but the zero level) is
   given only once a scope check of this check found it in scope (a
   column of the level store with its identity and the closed epoch).

**Why sound.** Each rule only declines to give an equal node and makes a
new one with the same fields, as a smaller export or a store without
sharing would; hash-consing "only saves room and time: a missing entry
costs a duplicate, never a verdict" (`terms.fs` header, ADR 0016 C8).
The binder merge gives a term an `==`-equal binder, which Lean's kernel
cannot tell apart. What a check reaches, and so what it is given, depends
only on its declaration and the declarations it reads, in the same order,
so its fuel does too.

**Fuel.** Rule 1 shares more (less fuel); rules 2 and 3 share less with
records the check never reached (more fuel): all of `Init` (default fuel, against pf-perf's batch 1): 59,349 accepted before and after, fuel 659,257,764 → 661,501,419 (+0.34%), 48,397 declarations with more (at most +19.7%: `String.lt_irrefl` 680 → 814) and 5 with less; Mathlib's first 1M lines fresh (against rule 1 alone): 13,023 accepted, fuel 68,235,044 → 68,731,666 (+0.73%, at most +29.8%: `self_mem_nhdsWithin` 2,151 → 2,792). Verdicts move
only from or to *exhausted* near the budget; none moved on `Init` or the
prefix.

**Evidence.**
- `tests/cli/cross_snapshot.py` (in `make check`, through
  `tests/cli/export-check.sh`): nine fixtures, each checked fresh and
  against a snapshot of each of the other eight, 72 pairs: every
  declaration's verdict and fuel the same (before: unfold's `Implies`
  34 → 38, nested `PProd`/`Prod` +6, sharing's `And` +6); and since
  review rvRS the let pair, `let-b` and `let-zd` each against the
  other's snapshot (before the let merge: `B` 295 → 302). Lets in a
  parallel check: `Jobs.test_workers_share_merged_lets`
  (`tests/cli/jobs/gen.py lets 20`, twenty lets equal but for their
  names: workers made). Planted faults `fxr-let-class-split` and
  `fxr-let-worker-unmerged` are caught.
- The review's p7 (`.claude/work/PF/b2/p7`): fresh and against the
  snapshot both give `Implies` accepted with 34 and `impliesSelf`
  exhausted.
- `tests/core/check-declaration-ndjson.fs`: a let's lambda and a later
  lambda of the same type and body are one node; with the audit memo on,
  an input lambda, and the importer's level `succ 0`, are given back only
  after an audit (a scope check) of this epoch reached them.
- `tests/cli/jobs/renamed20.ndjson` (`gen.py renamed`: binders equal up
  to their names, below new copies): the Jobs tests give the same output
  serially and with workers, and the workers are made.
- Planted faults `pf-binder-class-split`, `pf-findable-always`,
  `pf-findable-held-any-epoch`, `pf-level-findable-always`,
  `pf-level-reached-no-mark`, `pf-shared-merge-missed` (all caught) and
  the re-targeted `s5-feed-binders-not-entered`.
- Mathlib's first 1M lines (`.claude/work/SN4/ml1m.ndjson`) fresh and
  against `Init`'s snapshot written by this build (verdict version 4;
  `.claude/work/PF/b4`, and again on the merge with the shared input,
  `PF/b5`, with the same fuel per declaration): every one of the 13,023
  declarations has the
  same verdict and fuel (1,108 taken, 11,571 checked on taken slots, 344
  checked alone), the same counts and exit status, total fuel 68,731,666
  in both (2,151 differed at SN4, 1,292 with rule 1 alone, 7 with rules 1
  and 2). The 5,231 names in both `Init`'s export and the prefix use the
  same fuel fresh in each (931 differed with rule 1 alone; `Init` was
  checked with 8 workers, the prefix with one).
- The golden snapshot fields of the ten guarded exports
  (`tests/cli/golden-snapshots`) are written again with verdict version 4.

## Amendment 8: resource limits per check, fuel and memory (agent MB, 2026-11-11, proposed)

Status: proposed; no typing, reduction or conversion rule changes, and
without the new option no outcome, fuel count or diagnostic changes (no
verdict-version bump). Code: `src/core/scratch-meter.fs` (new),
`core/terms.fs`, `core/levels.fs`, `core/constant-references.fs`,
`kernel/caches.fs` (one charge each where a record is made),
`kernel/check-declaration.fs` (`lf-check-scratch`, `lf-check-over`),
`cli/leanforth.fs`, `cli/check-run.fs` (the workers' copy),
`cli/check-json.fs`; diagnostic 101.

**Why** (owner, 2026-11-11: more fuel for the night's Mathlib run). Q9's
fuel bounds a check's time; nothing bounded its memory but the heap. The
workers of `check --jobs N` share one process, and its `ulimit -v`, so
with more fuel one huge check could take the memory the other workers'
checks need, and those would end *full*: new differences from Lean that
no rule causes.

**Decision.** Two resource limits per check, both LeanForth's own, never
Lean verdicts (Lean's kernel has neither; its `LEAN_NAT_MAX_SIZE` aside,
Q8): *fuel* (Q9; `--fuel N`), and since this amendment *memory*
(`check --memory-per-check MB`, default none). A check whose scratch --
the term nodes, levels and constant references it makes above the
input's marks, with their universe arguments (and, since review rvRS,
the shadows of the references it is given but has not reached, and the
limbs and bytes of the literals it makes), its local context and its
result caches' entries, all of which it gives back or empties when it
ends -- would pass MB × 2^20 bytes stops *full*, the outcome the heap's
refusal gives (ADR 0008): never accepted, its dependants unknown as after
any *full*, its diagnostic code 101 with the bytes asked for and the
limit. The input, the stage, the checked environment and the walks'
frame stacks are not counted.

- *Counted, not measured.* Each record counts a fixed number of bytes,
  upper bounds on a 64-bit host of its record, identity, side columns
  and two table slots (96 per term node, 176 per level, 64 per reference
  plus 16 per universe argument, 64 per cache entry, 48 per local-context
  entry; `tests/core/check-declaration.fs` checks the bounds against the
  stores). The heap's own sizes depend on what earlier checks grew in the
  same worker; counts do not, so a check under a limit gets the same
  outcome serially, with `--jobs` and in every run (big2, the same
  theorem after big in one worker, asks for exactly big's bytes). The
  heap holds more than the count: stores and tables grow by doubling,
  and the walks' stacks and memos are not counted. On the doubling
  export a check that needed 11 and 44 MB by the count (`double 14`,
  `double 16`) grew the process by 14 and 59 MB, about 1.3-1.4 times;
  the command line's manual says to allow twice.
- *Cheap.* A new record is charged against a credit; only when the
  credit runs out is the whole scratch read (a sum over five stores, two
  slabs and eight tables) and the credit set to what is left below the
  limit. Every refusal comes from a reading. *Exact* since review rvRS
  F4: a record is charged just before it is made, never one found
  shared, and with no other charge between (a local-context entry after
  its node), so a check is refused exactly when a record would take its
  scratch past the limit. Before, a term or level was charged before the
  lookup that might find it, so a reading could refuse one record below
  the limit, and local-context entries were counted by readings but never
  charged, so a check could pass its limit unrefused between readings.
- *Where it stops.* A term, level or reference past the limit is refused
  as a full store refuses it, and the check's passes end *full* as
  before. A cache entry past it is a miss (as when the heap refuses one),
  so the check may go on; it ends *full* all the same
  (`lf-check-over`), whatever it found. Once a check passes the limit,
  every later charge of that check is refused.
- *Not an approximation of Lean.* Like *exhausted*, a *full* from the
  limit is never a verdict; the check would need more memory, which
  `--memory-per-check MB` gives. The known resource gap rvCACHE L3
  (Amendment 1: scratch kept for the caches until the job ends) makes
  a check reach the limit sooner than an uncached run would; plan task
  4.2.7c closes it.

**Evidence.** The doubling export (`tests/cli/jobs/gen.py double 12`:
`big` unfolds 2^12 - 1 definitions; Lean accepts it) is *full* with
`--memory-per-check 1` and 2, accepted with 4 or none; with `--jobs 2`
`big` is full while the small theorems beside it are accepted, the same
text as serially (`tests/cli/test_leanforth.py`, `MemoryPerCheck`). The
composition case is full under every limit below 1,680 bytes (1,664
before the exact count of review rvRS F4) and accepted from there on,
never before (a sweep in steps of 16, `tests/core/check-declaration.fs`;
at 1,679 it asks for exactly 1,680); the doubling export from 1 to 5 MB
likewise, each limit the same text with `--jobs 3`. Six planted faults are caught
(`tests/mutants/faults.toml`, `mb-*`): the limit never armed (both
tests), the workers without it, a passed check ending with what it
found, a reading without the scratch, and (`mb-capacity-not-count`) a
reading of the stores' capacity instead of the records made.
All of Lean's `Init` (59,349 declarations; `gforth-fast`, `--jobs 8`, a
10-core machine other agents loaded) with `--memory-per-check 4000` gives
every verdict line of main's run without the option (93a993f), all
59,349 accepted, the same fuel in all (659,257,764 steps) and the same
ten declarations that used the most; the check phase's CPU time 1,410 s
against main's 1,387 s (+1.7%, within the load's noise: its wall time
was 273 s against 353 s), peak resident memory 2,323 MB against 2,302 MB.

**Corrections (review rvRS, agent FXR, 2026-11-12).** Three claims
above did not hold; no outcome, fuel count or diagnostic without the
option changed in fixing them (all of `Init` below), so no verdict-version
bump.
1. *Same outcome in every export* (F1). Rules 2 and 3 of Amendment 7
   gate terms and levels, not references: `lf-cref-intern` gave any
   equal reference made before the check uncharged, so a check counted
   other bytes fresh, against a snapshot and in an export with more
   declarations (the reviewer's probe: full fresh, accepted in the
   others). Gating references as rule 2 gates terms (a new record for
   one not reached) moved fuel (`Zd` of `let-zd.lean` 106 → 109): code
   compares constants by their reference's number, and interning makes
   that number a reference's class. So the reference is still given, and
   a reference made before the check that an audit of this check has not
   reached (a constant node holding it checked in today's closed epoch,
   `lf-cref-reach`, as levels' `lf-level-reach`) gets a *shadow*: a new
   record of the same fields in the context's store, charged, counted by
   the reading, given back by rollbacks, and entered in the interning
   table, where a later find meets it and gives its original at no cost
   -- the room a fresh export without that record would take
   (`constant-references.fs`, "Shadows"). Evidence:
   `MemoryPerCheck.test_snapshot_pair` (`gen.py refs 2800`: `B` full
   asking for 1,048,608 bytes fresh, against the snapshot of `refsz`,
   and in `refsbz` serially and with `--jobs 2`; before: 1,048,640 in the
   others); the reviewer's probe (1000 × 60): full with 1,048,768 in all
   three (fuel 4,373,027 unchanged); planted faults `fxr-cref-gate-off`
   and `fxr-cref-unshadowed`.
2. *The scratch* (F3). Literal limbs and string bytes a check made were
   neither counted nor given back (the reviewer: five 2 MB literals
   accepted under 1 MB, the process 28 → 47 MB, +10 MB per such check for
   the run). Now `lf-input-end` marks the two slabs with the stores,
   `lf-input-rollback` gives them back after every check, each limb (1
   cell) and byte (1 char) is charged where it is claimed, and the
   reading counts them above the marks. Not counted: the arenas in which
   `reduce-nat.fs` computes (one operation's, freed when it ends; Lean
   bounds `pow` at 2^24 bits, ADR 0015, but a product may reach 2^30
   bits), and a literal's limbs given back by a rollback within a check
   (only lowering the scratch: the slab keeps them until the check
   ends). Evidence: `tests/core/check-declaration.fs` (a literal of 200
   limbs and a string of 2,000 bytes refused under 1,000 bytes, one of
   100 limbs allowed; the slabs back at their marks after the rollback;
   the reading counts a literal's limbs with its node); planted faults
   `fxr-limbs-uncharged`, `fxr-bytes-uncharged`, `fxr-slabs-kept`,
   `fxr-slabs-unread`.
3. *Never a refusal below the limit* (F4): see *Cheap* above. Evidence:
   the composition case's threshold (1,680) and, with fake readings, a
   term and level found shared given with room for less than a record
   while a new one is refused; a local-context entry refused with room for
   its node and one byte less than itself; planted faults
   `fxr-term-charged-found`, `fxr-level-charged-found`,
   `fxr-local-uncharged`.

**Gate.** A [kernel] change only in where a check stops for a resource:
no rule is touched, and no limit is set unless the option is given. It
needs the owner's approval of this summary and an independent review of
the change (AGENTS.md, review gates) before it counts as reviewed.

## Amendment 9: an application typed aside from its spine's head (agent R5, 2026-11-11, proposed)

Status: proposed; [kernel] gate owed. Written as Amendment 8 on branch
`r5-roots`; renumbered 9 at the merge with agent PF's Amendment 7 (verdict
version 4) and agent MB's Amendment 8; this amendment is verdict version 5.
Code: `src/kernel/mixed-infer.fs` (`lf-minfer-spine` and the words
before it; `lf-minfer-binary`). No typing, reduction or conversion rule
changes: the type given back is the same term, the whnf calls are the same
calls on the same terms; every verdict that moves is an *exhausted* that
becomes Lean's.

**Finding** (`.claude/work/R5/ROOTCAUSE.md`: the six Mathlib declarations
that exhausted 100,000,000 units). Lean's `infer_app` in infer-only mode
(`type_checker.cpp` 188-205), the mode of every inference a comparison
asks for (proof irrelevance, eta, unit-like types), takes the arguments of
`f a₁ … aₙ` at once: it infers the head `f` alone, walks its type's Pi
bodies without instantiating while they are visible Pis, and puts the
arguments since the last such point in by one `instantiate_rev` where a
type is no visible Pi (then `ensure_pi_core`) and at the end. LeanForth
typed the spine one application node at a time, each node's type the
function's Pi body instantiated with one argument: every argument cost a
pass over the rest of the telescope (Θ(n²) visits for a spine whose type
names its binders, Lean's Θ(n)), and every prefix `f a₁ … aₖ` was looked
up and kept in the inferred-type cache. On `AlgebraicGeometry.Proj.awayι_comp_map`
these passes were 23.9M of the first 100M units (1,779,077 calls), on two
other roots 13-17%.

**Ported.** In aside mode an application's spine is collected (the
arguments, outermost first, on a growable stack of the job,
`lf-minfer-spine-cells`, above those of the spines being typed around it:
a whnf's iota may type aside again), its head is inferred (keyed, as
`infer_type_core(f, true)` keys it), and Lean's loop runs on the head's
type: a visible Pi gives its body; otherwise the pending arguments are put
in at once (`lf-instantiate-rev`), the result is put in whnf when it is no
Pi (`lf-minfer-pi-parts`: else unknown, as before aside) and gives its
body; last, the pending arguments are put in. An argument read under the
scope is closed first when the type's loose range can name it (Lean's
`instantiate` never reads the others; Amendment 6 for one argument). The
prefixes are neither typed nor keyed, as in Lean. Checking mode (Lean's
`infer_only = false`, one node at a time, 173-187) is unchanged. The
derivation log (ADR 0013) records no step for a spine typed aside, as for
every visit aside; before, each application typed aside logged one
instantiate step without formulas (`tests/present/outlines.golden`:
`Nat.add_zero`'s log 263 → 245 steps, only those 18 gone).

**Why sound.** Instantiation keeps a visible Pi a Pi, so the points where
Lean's loop instantiates are the points where the node-at-a-time typing
found no visible Pi, and both put the same whnf calls on the same terms;
putting k arguments in at once gives the term that k single substitutions
give (`instantiate_rev`'s definition, mixed-open.fs). The stack's cells
are read by index after anything that may grow it; each spine gives its
cells back when its type is known or refused, and a job starts with none.

**Fuel.** One pass per point instead of one per argument, and no visit,
lookup or key per prefix: fewer units for long dependent spines. Where a
prefix's type was found in the cache before, the spine now types it from
its head, as Lean does, which can cost more (two Mathlib roots below, and
some declarations of `Init`). Fuel only bounds work: a run with a
different count can only be *exhausted* (or *unknown* behind one) where
the other decides, never give another verdict. Verdict version 5 (ADR
0020 D3).

**Evidence.** `tests/cli/shared-depths.lean` P4: proof irrelevance types
two 48-argument spines aside (`Spine.h 0 … 0`, `Spine.h₂ 0 … 0`); pinned
Lean accepts `spinegood` and rejects `spinebad` (appTypeMismatch), and
LeanForth agrees, memo on and off; `shared_depths.py` bounds the good
row's fuel (15,749 units, 25,063 before). Its two exports are pinned
(`tests/core/check-declaration-cases/spine-{good,bad}.ndjson`,
`test_leanforth.py` PINNED). Every pinned report of `test_leanforth.py`,
compared with the tree before: the same but for fuel, 34 declarations less
and none more; the golden snapshot fields: 23 slots' fuel less, nothing
else moved. The checker trial digest stays `e96c47672b69`. Planted faults
`r5-spine-one-short`, `r5-spine-visible-pi-ignored`, `r5-spine-order` and
`r5-spine-unclosed`, all caught; the 37 earlier faults of
`mixed-infer.fs` behave as listed (36 caught, 1 known equivalent). Mathlib
roots, each checked alone against a snapshot of its dependencies with
`--fuel 1000000000` (`.claude/work/R5/ROOTCAUSE.md`), all accepted before
and after, units before → after:
`AlgebraicGeometry.Proj.awayι_comp_map` 219,483,113 → 211,894,547 (check
CPU 656 → 521 s, peak memory 8,641 → 5,397 MB);
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare.biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply`
99,751,907 → 88,024,288 (peak 4,820 → 3,338 MB);
`CategoryTheory.instIsIsoIndCoimageImageComparison` 233,897,724 →
226,013,339; `PresheafOfModules.freeObj._proof_2` 188,314,434 →
187,856,617; `PadicInt.coe_adicCompletionIntegersEquiv_apply` 133,650,976
→ 137,151,657 and `Polynomial.iterate_derivative_derivative_mul_X`
165,018,370 → 167,077,182 (more: prefixes no longer cached, as in Lean);
check CPU 2-21% less on each. All of `Init` (`check --no-manifest --json
--jobs 4`, default fuel): 59,349 accepted before and after, no other field
of any declaration moved; fuel 659,257,764 → 652,726,907 (−0.99%), 31,418
declarations less, 27 more (at most +0.17% each).

## Amendment 10: Lean's infer-only typing, what it skips and what it throws (agent CK, plan task 4.2.7d, 2026-11-12, proposed)

Status: proposed; [kernel] gate owed (review rvKN finding 3, owner
approval of the task on 2026-11-12). Verdict version 9. Code:
`src/kernel/mixed-infer.fs` (`lf-minfer-lam` and the words before it,
`lf-minfer-not-type`, `lf-minfer-not-pi`), `src/kernel/infer-proj.fs`
(`lf-iproj-bad`), `src/kernel/defeq.fs` (`lf-dq-typeish?`).

**Lean's rules** (`type_checker.cpp` of 4.35.0, `.claude/work/lean-src`).
`infer_type` (360-362) is `infer_type_core(e, true)`, the mode of every
inference `is_def_eq` and the reductions ask for: `is_def_eq_proof_irrel`
(899-905, step 1163) infers `t`'s type for any `t`, a Pi included, then
`is_prop` of it (383-389, `ensure_sort` of its type); `try_eta_expansion_core`
(841-853) the other side's; `try_eta_struct_core` (856-872) both;
`is_def_eq_unit_like` (1120-1130) `t`'s and `s`'s; K and structure eta in
iota (`inductive.h` 31-75) the major premise's. In that mode
`infer_lambda` (125-142) types no domain (131-133), `infer_let` (208-230)
neither the type nor the value (215-221), `infer_app` (188-205) no
argument; but `infer_pi` (144-166) still makes each domain and the body a
type (`ensure_sort_core`, 151 and 158), `infer_app` still makes each
function type a Pi (`ensure_pi_core`, 199) and `infer_proj` (247-292)
still tests the structure (`invalid_proj_exception`). Each failure throws,
and nothing in `type_checker.cpp` catches a kernel exception: the
declaration is rejected (`environment.cpp` 292-298). Such a failure needs
an ill-typed term, which in a checked declaration only reduction makes:
beta putting a variable `h : True ∧ True` where `⟨⟩` stood, say, so that
`F h` (an `And.rec` on `h`, which no rule reduces: Lean eta-expands no
proposition, `inductive.h` 71) stays where `F ⟨⟩` reduced to a Pi.

**Before.** LeanForth's inference aside (the typer) typed every
lambda's domain as while deciding (a domain Lean never types could fail),
answered *unknown* where Lean throws typeExpected, funExpected or
invalidProj (review rvKN 3), and `defeq.fs` took a Pi to be a type at
steps 4, 11 and 14 without asking the typer -- the answer Lean gets ("not
a proof") but not Lean's exception when the Pi is ill-typed: `pibad`
below, which Lean rejects, was **accepted**.

**Ported.** (1) Aside, a lambda's domain is closed and opened as the next
binder at once, with no inference, Sort rule or scratch mark (lets were
already so). (2) `lf-minfer-not-type` and `lf-minfer-not-pi` reject in
both modes (S2/S4 and F1, the codes of the deciding path), and so does
`lf-iproj-bad` (J2). (3) With a typer, a Pi is typed at steps 4, 11 and
14 as Lean types it; without one (a bare comparison outside a check,
which decides no declaration) it is still taken as a type. A Sort, and a
free variable whose type is a Sort, still are: Lean's typing of them
cannot fail. What stays unknown aside: a whnf that cannot follow Lean
(K1 outside a check, K5, K7, iota pending), as while deciding.

**Why Lean's.** Each rejection aside is at the call where Lean's
infer-only typing throws, on the same term (the typer's call sites are
Lean's `infer_type` calls in the same steps and order, ADR 0014 Q1 and the
defeq port), with Lean's exception kind; a failed typing is never kept
(the caches keep only *ok*, `caches.fs`), and a typer's *rejected* passes
through `defeq.fs`, `iota.fs` and conversion as an exception, never as
Lean's no (`lf-mixed-convert-no?` false), so no failure cache entry is
made. Outside a check a rejection aside, like `lf-dq-sorted`'s before it,
passes even when an earlier step left a doubt; no declaration is decided
there.

**Fuel.** Fewer units where a lambda typed aside had a large domain, more
where a Pi is now typed at steps 4, 11 or 14. Verdict version 9 (ADR 0020
D3).

**Evidence.** `tests/cli/shared-depths.lean` P5 (10 rows `io-*` and
`p5all`, the ten in one export; the theorems are named `InferOnly.appbad`
and so on): pinned Lean and the official checker reject `appbad`
and `lambad` (funExpected), `pibad` (typeExpected) and `projbad`
(invalidProj) and accept `appgood`, `pigood`, `lam2good`, `lamgood`,
`letgood` and `projgood`; LeanForth, memo on and off, now agrees on all
(before: `appbad`, `lambad`, `projbad` and `lamgood` unknown, `pibad`
accepted). `p5all` is `tests/core/check-declaration-cases/infer-only.ndjson`
(`test_leanforth.py` `ExitCodes.test_1_infer_only`, per declaration, and
PINNED). Aside in `tests/core/definite-rejection.fs`: rejected
(funExpected), unknown (K1) and a lambda with an ill-typed domain typed.
Planted faults (`tests/mutants/faults.toml`): `infer-not-pi-aside-unknown`,
`infer-not-sort-aside-unknown`, `infer-lam-aside-domain`,
`infer-let-aside-checks`, `dq-pi-untyped`, `iproj-bad-aside-unknown`,
all caught; `rej-f1-off` and `infer-chain-never` re-targeted, caught;
`infer-not-pi-aside-rejects` (an equivalent of the old rule) retired.
Every pinned report of `test_leanforth.py`: the same but for
`unfold.ndjson`'s `impliesSelf`, 65 → 68 fuel (step 4 types `A → A`);
the golden snapshots: that slot's fuel only; `shared_depths.py`'s bounded
rows 13,250, 18,060 → 18,056, 13,157 → 13,160 and `spinegood` 15,749 →
15,894, all below their bounds. All of `Init` (`check
--no-manifest --json --jobs 2`, default fuel, against main `390197d`'s
report): 59,349 accepted before and after, every field of every
declaration the same but fuel; fuel 654,546,896 → 654,719,715 (+0.03%),
5,873 declarations more (at most +13.8%, `Sum.liftRel_subrelation_lex`;
+334 units at most, the `*.instLinearOrderPackage` instances) and 3,647
less (at most −3.3%); 650 s wall, 0.86 GB peak.

## Note: the projection steps (plan task 5.2.2, 2026-11-10)

The Q8 row "Projections: `reduce_proj`, step 8, `try_unfold_proj_app`"
is closed: `defeq.fs` runs steps 8 and 9 (1177–1183, 1185–1188;
`lazy_delta_proj_reduction` 1084–1102, sharing lazy delta's step) and
`try_unfold_proj_app` (950–957) where only one side unfolds, and steps 3
and lazy delta's unfoldings run `whnf_core` with `cheap_proj` (`whnf.fs`
keeps the mode; `caches.fs` keeps no `m_whnf_core` entry of a cheap
visit, as Lean, 547). `is_def_eq_app` and `is_def_eq_args` use Lean's
`is_app` and `get_app_fn`: a projection (`Expr.proj`, here the
application of a projection leaf; since compact-store plan step S5,
parts 4-5, a node of its own over the leaf and the term, ADR 0016's
note) is no application. Evidence, rows and
the `Init` counts: ADR 0015, "The comparison's projection steps".
[kernel] code; review gate owed.

## Consequences

- **ADR 0003**: its candidate algorithm and Amendment 1 become one part of
  the port (`is_def_eq_binding`).
- **ADR 0006**: "theorems must not be unfolded" is corrected: theorems
  unfold last (G5, answered here).
- **ADR 0011**: K1–K3 go, D1–D5, S1, S2, S4 and F1 are subsumed, K7 is
  added (Q1, Q8); its *Equal* becomes "the port answers *yes*".
- **ADR 0012**: E2's `decl-hint` and kept theorem values are used; E3's
  cross-check cache reuse is not used in phase 4 (Q10 rule 4); a new
  declaration kind, opaque.
- **ADR 0013**: the catalogue grows by codes 7, 14–19 and 23 and `defeq`
  gains a result (Q11), an additive amendment.
- **ADR 0016**: free-variable nodes and skeletons are used; theorem
  proofs stay in memory.
- **Plan**: task 4.1.1's wording ("theorems … never unfold") is
  corrected; 4.2.2 splits into 4.2.2a–e.
- **BEYOND_LEAN.md**: row BL-4 (name-matched `Nat` rules).

## Rejected alternatives

- **Extend the cautious rules** (more *unknown* cases, more sufficient
  conditions for *no*). Every extension is another argument that Lean
  would agree, and *unknown* where Lean decides is a gap the owner does not
  accept. The port answers what Lean answers, with Lean's code as the
  specification.
- **A complete decision procedure** (normalise both sides fully and
  compare). It would accept what Lean rejects (BL-4's rows, BL-1's levels)
  and be exponentially slower on proofs by computation.
- **Theorems never unfold** (ADR 0006's proposal). Verdict-neutral in phase
  4 but wrong for recursors on proofs in phase 5
  (`theorem.unfolded-by-recursor`), and needless: the proofs are in memory
  anyway.
- **Keep de Bruijn indices and a binder stack.** Then every cache key
  would need the binder context, and a cached result could not be reused
  under another context; Lean's caching argument would not carry over.
- **Name-sensitive keys (plain node numbers).** Simpler, but a hit in Lean
  could be a miss in LeanForth, which changes unfold counts and, should
  Lean's procedure ever be asymmetric, verdicts.
- **A union-find (equivalence-closure) cache**, as in older Lean versions.
  Lean 4.35.0 removed it because it made results depend on evaluation
  order (`type_checker.h` 33–39).
- **Share caches across declarations** now. Faster for large libraries,
  but Lean does not, and it needs its own soundness argument and gate.
- **Port the name-matched `Nat` rules now.** They produce literals, which
  need the big-number library and phase 5's literal support to stay exact.

## Questions for the owner

**G5. Should LeanForth unfold theorems?**
Lean's kernel does, after everything else; in phase 4 it makes no
difference to any verdict (by the argument above), but in phase 5 some
proofs only check because Lean opens a theorem's proof (row
`theorem.unfolded-by-recursor`). *Recommendation: yes, exactly as Lean*,
and keep every proof in memory as you already decided for ADR 0016. The
alternative (never unfold) is simpler only today and would be wrong later.

**Q-A. Replace the cautious rules by a copy of Lean's procedure?**
Today LeanForth answers *unknown* whenever unfolding, eta or "any two
proofs are equal" might matter, and has extra rules to say *rejected*
safely. *Recommendation: yes, replace them* by the copy described here,
once it passes its gate: it gives Lean's exact verdicts, including Lean's
reasons, and every rule is a cited line of Lean's code. The old rules stay
as a cross-check during the switch.

**Q-B. Name bound variables like Lean does (free variables) inside the
checker?** *Recommendation: yes.* It is how Lean's caches stay correct,
and it makes the copy line-for-line comparable with Lean's code. It means
reworking the phase-2 inference code first, without changing any answer.

**Q-C. Copy Lean's caches exactly, one declaration at a time, and no
sharing between declarations for now?** *Recommendation: yes.* Exact
copies keep the verdicts and even the unfolding counts identical to
Lean's; sharing between declarations could come later as a separate,
argued speed-up.

**Q-D. Answer *unknown* when a constant has one of the names Lean's
kernel treats specially (`Nat.succ`, `Nat.add`, `Bool.true`, …) until
phase 5?** In Lean's own library these are never a problem; only a file
that defines such names itself would see it. *Recommendation: yes*, and
record Lean's behaviour as BL-4.

**Q-E. A speed target?** *Recommendation:* report time per distinct node
and cache hit rates from task 4.2.7 on, next to Lean's 3 µs per node on
the same machine, and aim for within twice Lean's time on one thread
before phase 6, with parallel checking then going beyond it.

## Reproduction

```sh
make reference-definitional-equality
LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  bash tests/reference/definitional-equality-check.sh
curl -fsSL -o type_checker.h \
  https://raw.githubusercontent.com/leanprover/lean4/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/kernel/type_checker.h
curl -fsSL 'https://api.github.com/repos/leanprover/lean4/contents/src/kernel?ref=eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
```

SHA-256 of the files read (at commit `eb6cafb7…`, 2026-11-03). Already
recorded by ADR 0011 and its Amendment 1, unchanged:
`src/kernel/type_checker.cpp` `26eae5eb…df4e`, `type_checker.h`
`251e5910…35b0`, `declaration.h` `eb9c497b…a51`, `declaration.cpp`
`1d4751c0…454`, `environment.cpp` `0930ff37…0b2`, `inductive.h`
`61bd4153…98a`, `quot.h` `17105c83…243`, `kernel_exception.h`
`58facd4e…24c`, `instantiate.cpp` `42527c96…916a`, `expr.cpp`
`cb02c189…c592`, `level.cpp` `7cb927c6…fc25`; ADR 0003 Amendment 1:
`expr_eq_fn.h` `ad010ccb…f3b`, `expr_eq_fn.cpp` `7feb30ca…07c`. Read for
this record:
`src/kernel/expr.h`
`9e8e953ce70ed056458659cdaabc96c0d2784e9a2ac5552357df0b9150571260`,
`src/kernel/expr_maps.h`
`9407344e004017991dbcd91bde689aa78be2e012254899c49aafc2f531272f2d`,
`src/kernel/environment.h`
`95e9b7aad9f138830197972c1812ca206317dae059ace9b7815674beec8500ed`,
`src/kernel/inductive.cpp`
`ad549d9a85bf75ea0405cd84f2c6759651c193474f7865ffc823d1467a79c7d6`,
`src/kernel/quot.cpp`
`500621538bfa97cd63ebf0c4b0e111b69232f5d4fa34aa56b5f6482599782627`,
`src/kernel/instantiate.h`
`82c29aeb56dfbdb68fc0266df21805a891c28b4c4ed9032e70602e709b532264`,
`src/kernel/replace_fn.cpp`
`2edfa1721059dbb570ba99746f2cd60d1d691071523c129a12b3b9414972ac67`,
`src/kernel/replace_fn.h`
`6b3a850ce10b5646a8d40011ff228f6d3223dc9a79136417bc586588d1aa8e76`,
`src/kernel/abstract.cpp`
`64d90a1d952b8c67fa382b820f7dc3173735c5300d80a946e1ebf4952875fcc2`,
`src/kernel/local_ctx.cpp`
`cc34d02060a8a98118550f5f75c81b51cd05765a455819ed2a1cb2963b4ee7f7`,
`src/kernel/expr_cache.h`
`99fa32315261934532693eeeac05b979ea3ce7419d42e521a70f02f2eea7d2b2`,
`src/kernel/expr_cache.cpp`
`2c1ee712926341b8e1950c15992a764c1c12e26d115a1a2d6e933bf0976438e0`,
`src/kernel/expr_sets.h`
`e17ecdf51f54fd58331e8e6f02429f3abc5ea030aca3849f07d86167ffd5e7cb`,
`src/kernel/for_each_fn.cpp`
`0c50dd26164830b35407ad1ff3dc3c02b4e612b1621f064bbbb3e786c34898d7`,
`src/runtime/sharecommon.cpp`
`2726b9384e4bbfe078983d1c62438bedd622c18aacf0196c24d3d397acadb622`,
`src/util/lbool.h`
`db705d9d3b62927452d66deb08d4bc2a2f62242013d08e4c8e0039f82a1b249f`;
the toolchain's `src/lean/Lean/Environment.lean`
`6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43` and
`Declaration.lean`
`1cf2f06d848086f165b3df0afe494924ae26aaea248d5e0135d5efc2d588948f` (as
ADR 0011 records). The GitHub listing of `src/kernel/` at the commit has
no `equiv_manager.*` and no `instantiate_mvars.*` (both return 404; the
kernel has no metavariables to instantiate).
