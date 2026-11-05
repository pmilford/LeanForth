# ADR 0014: Definitional equality as Lean's kernel decides it

Status: task **4.2.2a implemented and approved** [kernel] by the owner on 2026-11-04 ([decisions](../project/OWNER_DECISIONS.md#free-variables-approved-2026-11-04)); **4.2.2b and 4.2.2c implemented** 2026-11-04, their gate pending (see [Progress](#progress)); 4.2.2d–e next. **Accepted** by the owner on 2026-11-03 (G5 and Q-A to Q-D as recommended; Q-E: within twice Lean's one-thread time before phase 6, then close the gap, by algorithms first — [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)). Previously: **proposed**, 2026-11-03 (plan task 4.1.1, with the sections task
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
half-way before phase 5 ports them exactly (with literals and `bignum`).
In an imported Lean library these names are constructors and recursive
functions, which are unsupported in phase 4 anyway, so K7 matters only for
environments that define the names themselves.

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
   constant at the same levels.
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
| `proof-irrelevance.*` | 4 | 2 accepted, `declTypeMismatch` ×2 | unknown ×2, rejected ×2 (D3) | Lean's verdict |
| `let.*` | 4 | 3 accepted, `letTypeMismatch` | unsupported (U2) | Lean's verdict |
| `names.*`: Lean's name-matched `Nat` rules in an environment that defines the names | 4 | `declTypeMismatch`, `unknownConstant Nat`; twins accepted | unknown / unsupported | unknown (K7) for the two; Lean's for the twins |
| `later.*`: structure eta, unit-like, `Nat` literal, quotient (re-checked Lean elaborations) | 4 | accepted ×4 | unsupported | unsupported (phase 5) |

In all, 50 rows: 32 accepted (each with its counts), 14 failures, 4
`whnf` answers. Measured 2026-11-03 with the pinned Lean, all as recorded;
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
  there). Skipping steps 4 and 5 is sound for a yes: steps 6, 7 and 10
  say yes only for terms equal up to β and universe equivalence, which
  Lean finds equal whatever route it takes (ADR 0003's argument, on which
  conversion has always rested). `is_def_eq_binding` gives each binder a
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
