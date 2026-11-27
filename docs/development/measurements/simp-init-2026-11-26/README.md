# What Init's one-line simp proofs use (2026-11-26)

This measurement decides what goes into simp group 4, the first plain `by-simp`. The plan is in
`.claude/work/briefs/simp-group-4-architect.md`, section 1, "Measurement" and "Numbers that decide".
Pinned Lean re-ran every one-line `simp` proof of `Init` with all of `Init` imported. For each proof the
run recorded what the proof used: lemmas, simprocs, discharges, binder congruence, `_simp_N` helpers,
casts, reduction steps and bracket items. No LeanForth code ran; this is the Lean side of the future
`reference-simp-init` harness.

## How it was run

- Machine: WSL2 (Linux 6.18.58.1-microsoft-standard-WSL2), 10 cores. Date: 2026-11-26. Branch
  `simp-init-measure`, based on main `b2ecdbc6`.
- Lean: the pinned toolchain binary, `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit
  eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`. No elan proxy was used and nothing was
  downloaded. The script finds its toolchain from the running binary (`IO.appDir`), never from `PATH`.
- Commands (there is no make target yet; the implementing group adds `reference-simp-init`):

```sh
ulimit -u 500
T=.tools/elan/toolchains/leanprover--lean4---v4.35.0
$T/bin/lean --run tests/front/simp-init.lean > OUT.ndjson   # optional argument: a module prefix
python3 tests/front/simp_init_summary.py OUT.ndjson \
    --export .claude/work/IM/init.ndjson --src $T/src/lean
```

- Run time: 5.2 s wall for the Lean run. That covers interpreting the script, importing `Init`, and two
  simp runs per theorem. The first simp runs took 626 ms in total. The summary took 1.1 s, most of it
  reading the export.
- Output: one NDJSON line per theorem, 651 lines, not committed (SHA-256 `16b289e2…f3f8fa` for this
  run; the `ms` fields change from run to run). The export used for H was `.claude/work/IM/init.ndjson`,
  SHA-256 `c1b2071a…59a179`.

## What is counted

The script imports `Init` alone (not `Lean` or `Std`), so the default simp set, simprocs and `@[congr]`
lemmas are Init's.

It reads Init's theorems through `findDeclarationRanges?` and the module's source file under the
toolchain's `src/lean/`. A theorem counts when the text after the first `:=` outside brackets is, on one
line, `by simp`, `by simp [..]` (no `]` inside) or `by simp only [..]`. The text before that `:=` must
hold no `where` and no `|`. These are the shapes `docs/design/TACTIC_SIMP.md` counted with grep, so `at`,
`using`, config and `(disch := ..)` are left out.

For each theorem the script:

1. introduces as many binders as the stored value has leading lambdas (`introNP`);
2. elaborates the tactic text with Lean's own `mkSimpContext`, in the theorem's namespace, plus the
   module's top-level `open`s;
3. runs `Simp.main` on the target with the default methods. A counter wraps the discharger, and
   `wellBehavedDischarge` stays true, so caching acts as it does in the tactic;
4. closes the goal when the result is `True`, as `simpTargetCore` does.

Time-box: the default 200,000 heartbeats and the default maximum recursion depth, per theorem.

| | count |
|---|---:|
| TACTIC_SIMP.md's grep lines (`simp` 279, `simp [..]` 619, `simp only` 17) | 915 |
| measured theorems (`simp` 190, `simp [..]` 450, `simp only` 11) | 651 |
| **N**: measured `simp` / `simp [..]` | **640** |
| **L**: N closed by Lean's re-run | **636** |
| N not closed: harness errors ("failed to retrieve match equations … after realization" for a private matcher of another module; `Nat.fold_succ`, `any_succ`, `all_succ`), maximum recursion depth (`Fin.castSucc_eq_zero_iff`) | 3 + 1 |
| L whose term equals Init's stored value | 382 (60.1%) |

Why N is less than 898: the grep counts lines, and 264 of the 915 grep lines are not top-level
theorems. The summary classes them:

- 214 are inside a declaration: `have`, `calc` steps, structure fields, `obtain`, `replace`;
- 29 are `instance` fields;
- 10 are a macro's template (`$typeName`);
- 3 are `def`, 1 `example` and 1 `grind`;
- 6 are lines the classifier calls theorems: 2 `replace` lines and 2 continuation lines of an
  `obtain` inside proofs, 1 `le_refl a := by simp` field, and `and_false_eq` in `Init.Simproc`, the
  one top-level theorem the harness missed.

## Numbers that decide (shares of L = 636)

| | what | theorems | share | rule (architect) |
|---|---|---:|---:|---|
| D | at least one discharge attempt (192 attempts, 44 succeed, in 44 theorems) | 94 | 14.8% | ≥ 15%: the discharger stays in group 4 |
| S | Core ite/dite (`reduceIte` 6, `reduceDIte` 8) | 14 | 2.2% | > 5%: actions in group 4 |
| S | UInt/SInt (`reduceNeg`, `reduceToInt`, `reduceToNat`, `reduceEq`, `reduceLT`) | 40 | 6.3% | |
| S | Int | 4 | 0.6% | |
| S | Nat `reducePow` | 4 | 0.6% | |
| S | Nat literal arithmetic, Nat Diff family, `reduceCtorEq`, Fin, Char, String, BitVec, List, Array | 0 | 0% | |
| H | uses a `_simp_N` helper the export does not declare (any `_simp_N` helper: 239, 37.6%) | 142 | 22.3% | ≥ 10%: helpers lead group 5 |
| B | binder congruence (`forall_congr`, `implies_congr`, `funext`); other kinds or a nested `funext`: 0 | 35 | 5.5% | |
| Dep | a `.congr_simp` lemma and a cast in the same term (any `.congr_simp`: 19, 3.0%; any cast: 9, 1.4%) | 7 | 1.1% | |
| R | reduceStep's projection, matcher/iota or let steps (detected by the ablation below) | 14 | 2.2% | |
| U | `simp [f]` with `f` a definition | 60 | 9.4% | |
| P | a bracket item needing preprocessing | 183 | 28.8% | |
| | P: a `←` item | 152 | 23.9% | |
| | P: a hypothesis that is not an equation | 12 | 1.9% | |
| | P: `[*]` | 13 | 2.0% | |
| | P: a term item (`foo (f := f)`) or a non-equation theorem | 6 | 0.9% | |
| | `@[congr]` lemmas other than `ite_congr` (`exists_prop_congr` 2, `Vector.mk_congr` 2, `dite_congr` 1, Array's four 1 each) | 9 | 1.4% | |

Bracket items over L: 204 equation theorems, 152 `←` equation theorems, 65 definitions, 38 equation
hypotheses, 13 `*`, 12 other hypotheses, 5 terms, 1 non-equation theorem and 1 unresolved.

How each flag is computed:

- D, S and the used set come from the run: the discharge counter, and `usedTheorems`, where a name that
  `Simp.isSimproc` knows is a simproc.
- B, Dep, H, `@[congr]` and casts come from the constants of the closed proof term. Casts are `cast`,
  `Eq.rec`, `Eq.ndrec`, `HEq`, `Eq.recOn` and `Eq.casesOn`. `Eq.mpr` and `Eq.mp` are listed in the
  NDJSON but not counted as casts.
- R comes from an ablation: the same tactic re-run with `-iota -proj -zeta`. A theorem counts in R when
  that re-run fails or gives a different term.
- U and P come from the bracket items, each resolved in the theorem's context.

## What a first `by-simp` without x would lose (theorems of L)

| x | theorems | share | only blocker |
|---|---:|---:|---:|
| bracket preprocessing (P) | 183 | 28.8% | 78 |
| left-out helpers (H) | 142 | 22.3% | 41 |
| the discharger (D) | 94 | 14.8% | 24 |
| unfolding (U) | 60 | 9.4% | 39 |
| UInt/SInt simproc actions | 40 | 6.3% | 24 |
| binders (assumed built) | 35 | 5.5% | — |
| Core ite/dite simprocs (assumed built) | 14 | 2.2% | — |
| reduceStep proj/matcher/iota/let (R) | 14 | 2.2% | 2 |
| `@[congr]` other than `ite_congr` | 9 | 1.4% | 1 |
| casts | 9 | 1.4% | 0 |
| Int simprocs | 4 | 0.6% | 2 |
| Nat `reducePow` | 4 | 0.6% | 0 |

**K estimate: 276 of L (43.4%), 276 of N = 640.** This is an estimate from the flags, not a LeanForth
run. It is the number of theorems that need none of the features left unbuilt. The features assumed
built are:

- rewriting with the default set and `rfl` lemmas;
- congruence as on main: `ite_congr` through `@[congr]`, and realized `.congr_simp` without casts;
- binders as on main: arrow, `∀` and a one-binder `fun`;
- the Core ite/dite simprocs and Nat literal arithmetic.

Everything else counts as a blocker: the discharger (any attempt), `reduceCtorEq` and every other
simproc family (guard only), left-out helpers, R, U, P, other `@[congr]` lemmas and casts. The "only
blocker" column gives what each one feature would add to K on its own.

Top 15 lemmas, by the number of theorems of L that use each:

| lemma | uses | lemma | uses |
|---|---:|---|---:|
| `eq_self` | 445 | `Lean.Omega.LinearCombo.coordinate_eval` | 10 |
| `iff_self` | 104 | `List.not_mem_nil` | 10 |
| `ne_eq` | 67 | `BitVec.neg_inj` | 10 |
| `not_false_eq_true` | 67 | `BitVec.neg_eq_zero_iff` | 10 |
| `Nat.zero_lt_succ` | 18 | `BitVec.xor_eq_zero_iff` | 10 |
| `implies_true` | 16 | `BitVec.not_inj` | 10 |
| `Std.le_refl` | 11 | `BitVec.ne_not_self` | 10 |
| `Lean.Omega.IntList.get_cons_zero` | 10 | | |

Term sizes (tree nodes, sharing not counted): median 305, maximum 2,701. Every term is under the
script's 20,000-node limit, so every line carries its S-expression, printed by
`tests/front/s2-proofs.lean`'s printer extended with `proj`, `let`, `mdata`, string literals and free
variables. Levels that are not numerals print as Lean prints them, for example `u_1 + 1`.

## Limits of the method

- **The reference is Lean's re-run, not Init's stored proofs.** 40% of the re-run terms differ from the
  stored ones, because those were proved with their own module's smaller simp set.
  Local `attribute [local simp]` settings and `section`-scoped `open`s are not reproduced. The `open`s
  the script uses are every top-level `open` line before the theorem, so some may already be out of
  scope.
- **"Uses x" is not "needs x".** Lean might reach a different term without x. Because K is node for
  node against Lean's term, any use counts against it.
- **D counts attempts at every depth**, including nested discharges, and attempts in branches simp
  later abandons.
- **R is detected only when switching the steps off changes the result.** Every R step is a definitional
  step and leaves no constant in the term. A step whose result was later rewritten to the same term
  would not show.
- **Dep is approximate:** a `.congr_simp` lemma and a cast in the same term. The kinds of the congruence
  lemma's arguments were not read.
- **H is a name check only:** a `_simp_N` constant of the term that the export does not declare.
- **The family table is by name prefix.** `nat-diff` is a name containing `Diff`; `nat-pow-dvd` is
  `reducePow` and `reduceDvd`.
- **Bracket kinds come from the item text.** An item with a space or a parenthesis counts as a term.
- **The theorem list is from source ranges.** It misses one-liners inside other declarations and
  macro-generated theorems (see "Why N is less than 898").

## The harness: `make reference-simp-init` (simp group 4, pass 3)

The measurement's Lean side is now the harness's: `tests/front/simp-init.lean` also prints each
theorem as LeanForth text (`lf`: binders `v1 .. vk` with their kinds, the statement in postfix,
`by-simp` or `by-simp[ ' NAME .. ]`, `<-` after a reversed item) or why it cannot be written
(`lf_why`), and its statement's S-expression (`type`). `tests/front/check_simp_init.py` runs every
text through `tests/front/simp-init.fs` (Init's export and its format-4.1 data read once, each
text run by the authoring words on Gforth 1.0, the word that refused read from the backtrace of
the first unsupported throw), then checks the texts that ran with `bin/leanforth check` against
Init's snapshot (one file, `elab-dump.fs`'s `cli-dump`), and compares every accepted theorem's
type and value with Lean's statement and re-run term, node for node. `make reference-simp-init`
(`tests/front/simp-init.sh`: Init exported, its 4.1 data written, the Lean side run) is part of
`make daily` only, after `make parallel-init` (the snapshot); without the snapshot a user's run
says SKIPPED, a recorded one fails.

```sh
ulimit -u 500
make reference-simp-init GFORTH=.tools/gforth/bin/gforth \
    LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean   # INIT_EXPORT=... to reuse an export
```

Run of 2026-11-26, branch `simp-group-4-p3`: 2 min 33 s wall with `INIT_EXPORT` (the export
exists; 14 s of it the 4.1 data, 14 s the Lean side, the rest the two LeanForth passes).

**K = 57 of N = 640** accepted with terms equal to pinned Lean's re-run node for node (L = 636);
54 before the dsimp scan of pass 3, step 4. **0 accepted with a different term; 0 accepted where
Lean's re-run fails.** 2 more were accepted with a statement LeanForth elaborates differently from
Lean's (the dumped types differ: a numeral whose type the printed text does not fix), never
counted.

| | theorems |
|---|---:|
| N | 640 |
| cannot be written as LeanForth text | 247 |
| written | 393 |
| K: accepted, term node for node Lean's | 57 |
| U: not supported yet (error 99 at `by-simp`) | 320 |
| refused before `by-simp` (the statement: errors 131 coercion 5, 117 instance of a function type 4, 139 2, 73, 126, 121 1 each) | 14 |
| accepted, statement elaborated differently (not counted) | 2 |

U by reason (the word that refused):

| reason | theorems | group |
|---|---:|---|
| a bracket theorem with `<-` (Lean's auxiliary lemma, `mkAuxLemma`) | 145 | other (bracket) |
| a rule whose statement is no Eq (a `_simp_N`-style helper, slice SL3d) | 47 | other |
| unification (isDefEq) not supported | 32 | other |
| a perm lemma (acLt), and 3 perm tests of compound terms | 24 | other |
| a bracket definition or simproc (unfold) | 20 | unfold |
| a simproc family, guard only | 20 | simproc family |
| congruence (`congr.fs`: argument kinds 15, a refusal 1) | 16 | other |
| a conditional rule (the discharger) | 6 | conditional rule |
| matcher, recursor or projection (reduceStep) | 5 | matcher |
| dsimp of a dependent argument | 2 | other |
| a left-out helper reached in candidate order | 2 | left-out helper |
| recorded keys not the statement's (no_index) | 1 | other |

Why 247 cannot be written: universe parameters 161 (natural form has no universe words yet), a
binder of a sort (`Prop`, `Type`) 39, numerals whose type only an ascription fixes 20, a `∀` or `→`
in the statement 13 and in a binder 4, the bracket item `*` 4, Lean's harness errors 4, an
unresolved item 1, a string literal 1.

### After the review's fixes (2026-11-26, branch `simp-group-4-fix`)

The same command on the fix round's head (rebased on main `b892c993`; `INIT_EXPORT=.claude/work/IM/init.ndjson`,
`INIT_SNAPSHOT=.claude/work/parallel-init/init-1.lfsn`, pinned Lean 4.35.0, Gforth 1.0.0; about 3 min wall). Two
things changed in the harness (review of simp group 4, M2 and B1): `simp-init.lean` prints each statement a
second time in Lean's syntax and elaborates it, so a text whose statement pinned Lean reads otherwise is not
written; and a statement LeanForth elaborates differently is a BUG. Three fixed cases
(`tests/front/simp-init-cases/`: `pb_shr_shr`, `pb_shr_shr_eq`, `pb_shr_at`, which pinned Lean proves with
`BitVec.reduceShiftRightShiftRight`) run beside the texts and must answer 99; the data's 341 simproc records must
be `tests/front/simp-data/init-simprocs.fs`'s.

**K = 57 of N = 640** (L = 636), as before. **0 accepted with a different term, 0 accepted where Lean's re-run
fails, 0 accepted with another statement**; the three cases 99.

| | theorems |
|---|---:|
| N | 640 |
| cannot be written as LeanForth text | 255 |
| written | 385 |
| K: accepted, term node for node Lean's | 57 |
| U: not supported yet (error 99 at `by-simp`) | 316 |
| refused before `by-simp` (errors 117 4, 131 4, 139 2, 73 1, 121 1) | 12 |
| accepted, statement elaborated differently (a BUG) | 0 |

U by reason: a bracket theorem with `<-` 145, a rule whose statement is no Eq 47, unification (isDefEq) 32, a
perm lemma 21 and 3 perm tests of compound terms, a bracket definition or simproc 20, a simproc family's guard
16 (20 before: their texts are now among those not written), congruence 16 (argument kinds 15, a refusal 1),
the discharger 6, matcher, recursor or projection 5, dsimp of a dependent argument 2, a left-out helper 2, no_index
keys 1. Cannot be written: universe parameters 161, a binder of a sort 39, numerals whose type only an ascription
fixes 20, a `∀` or `→` in the statement 13 and in a binder 4, **a printing Lean reads as another statement 8**
(new: `Int.Nonneg.natCast` and `Vector.range'_one`, the two the review found, and 6 that LeanForth refused or
did not support before), the item `*` 4, Lean's harness errors 4, an unresolved item 1, a string literal 1.

What this says for the next groups: the `<-` item on a theorem is the largest single blocker (Lean
builds an auxiliary lemma at the call; LeanForth would declare it itself), then rules that need
Lean's preprocessing into Eq helpers, then the defeq engine's own refusals. The left-out helpers
the architect's plan feared (`Nat.succ_ne_self`'s `Eq Nat * *` keys) block 2 here: Init's export
holds most of them; the simp slice of the unit tests lacks many more.
