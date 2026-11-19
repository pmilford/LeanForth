# LeanForth's own libraries: the elaborator library and the simp and rewriting library

Design (2026-11-18), revised after its architecture review (section 10); nothing built. Plan row PD20 of
[PLAN_DRAFT.md](../project/PLAN_DRAFT.md) and the owner's decision of 2026-11-18: LeanForth-specific libraries in
PD20's order, the first two being (1) an **elaborator library** and (2) a **simp and rewriting library**, designed
with their interactions with the tactic library and the tactics. Builds on [TACTIC_PLUGINS.md](TACTIC_PLUGINS.md) (the
tactic library), [SIMP_DATA.md](SIMP_DATA.md) (simp's data, slices SP1a-SP4, S7, S8),
[MATHLIB_FRONT.md](MATHLIB_FRONT.md) (MF) and [FE2_TERMS.md](FE2_TERMS.md) (FE2), and does not repeat them. Lean
references are to pinned Lean 4.35.0's `src/lean/Lean/`. Every size marked *estimate* is one; every measurement names
its command in appendix C. Appendices: A and B the two libraries' public words and Lean functions, C measurements, D
which tactic calls what, E the words used here (read it first if a term is new), F libraries 3-8 of PD20.

## For the owner (one page)

**What a library is here.** A set of public Forth words, each a port of one named Lean function (same choices, same
order, same resulting term), that several tactics and the term front end call, so that no tactic keeps a private
copy. The tactic library (term builders, binders, goal operations) is the first; this design adds two more.

**Library 1, the elaborator library.** Turning what the user wrote into a Lean term: inserting hidden (implicit)
arguments, unifying, passing the expected type down, finding instances, and, new, inserting coercions. What exists is
the S1/S2 core, about a third of appendix A's Lean functions by Lean lines (*estimate*: about 1,100 of 2,900;
`elab-term.fs`, `elab-app.fs`, `elab-pending.fs`, 1,691 lines): elabTerm, the instance calls, synthesis, binop% and
most of elabAppArgs. Most of the rest is FE2's (binders, `fun`, `let`, implicit lambdas, postponement, field
notation). What is missing is (a) its face for tactics: today the tactics reach it through a hook in the declaration
glue; (b) a registry of term forms, so the many forms of FE2 can be written in separate files at the same time; (c)
one saved state across the layers, so a failed attempt is undone everywhere; (d) coercions (plan FE4).

**Library 2, the simp and rewriting library.** Rewriting a goal with equations: the index that finds candidate
lemmas fast (a "discrimination tree"), the proof records `simp` builds step by step, stepping inside functions and
binders ("congruence"), and `rw`'s motive. Today its pieces sit inside other files: `rw`'s core inside the `rw`
tactic, the index inside the instance table. The simp core does not exist. `simp`, `rw`, `norm_num` and `ring_nf` all
call it; `ring` and `omega` do not need it.

**What changes for a user, by slice.** First (package LA): `rw [← h] at h2`, rewriting with an "if and only if"
lemma, and side goals left by a rule, each node for node Lean's. Then `simp only [...]` (SP1b, in two parts, the
second rewriting under binders), coercions such as `n + i` with `n : Nat`, `i : Int` (FE4a), and FE2's statements.

**Six changes to the tactic library, all in package LA** (section 4.2): one saved state across Meta, Term and Tactic;
library words that can be re-entered (simp calls itself); the elaboration hook replaced by library words; a shared
reader for rule lists and `at h`; frames freed when a word throws; a public depth scope. Each is small today and
costly later.

**Sizes (estimates).** Library 1 grows by about 1,000 lines of Forth in LA and FE4a, plus about 2,300 in FE2's slices
(about 1,200 Lean lines: binders, implicit lambdas, postponement, overloads, fields, `runTactic`); library 2
by about 4,000 (LA's part, the index, SP1b, SP1c), each with tests about as large. Measured yardstick: 1.3-2.1 file
lines of Forth per Lean line ported (appendix C); SIMP_DATA's SP1b figure (1,400 with tests) is
about 37% of this design's (3,700).

**Recommendation.** Approve the layers and the two scopes; build package LA first, beside MF2 and S3; then SP1b, FE4a
and FE2's forms in parallel (section 6). Seven questions (section 9); the review's findings in section 10. Terms are
defined in appendix E.

## 1. The layers

### 1.1 Today (`main` at `c8cd00dd`, 55 files, 17,297 lines; branch `tactic-lib-a2ii` adds 845)

| Layer (Lean) | Files in `src/front/` | Lines |
| --- | --- | ---: |
| Data readers (elaboration data, library decoding, environment view) | `elab-data`, `elab-keys`, `lib-decode`, `meta-env` | 2,826 |
| `Meta` core | `mvars`, `lctx-views`, `instantiate`, `offset-walk`, `beta-inst`, `dag-walk`, `term-find`, `term-eqv`, `meta-spine`, `meta-config`, `whnf`, `unfold`, `defeq`, `defeq-delta`, `assign-check`, `level-*` (5), `infer`, `prop-quick`, `fun-info`, `nat-offset`, `meta-check`, `kabstract` | 6,606 |
| `Meta` index and instance search | `discr-keys`, `instances`, `synth` | 1,611 |
| Generated definitions | `constructions`, `ctor-idx`, `cases-several`, `expr-remap` | 1,005 |
| Tactic library (`Meta/AppBuilder`, `Meta/Basic`) | `meta-must`, `app-builder`, `telescope` | 550 |
| `Elab.Term` (the elaborator) | `elab-pending`, `elab-app`, `elab-term`, `elab-decl` | 1,691 |
| `Elab.Tactic`, reader, goals, hand-over | `reader`, `syntax`, `tactic-syntax`, `tactic-run`, `tactic-basic`, `tactic-induction`, `tactic-rewrite`, `goals`, `goal-print`, `step-log`, `handover` | 3,008 |
| On `tactic-lib-a2ii` (in flight): goal layer, registry, glue | `meta-tactic/{goal,apply,assumption,constructor}`, `tactic-api`, `tactic-core`, `tactics/*` | 652 in new files |

### 1.2 Where the eight libraries sit, and which way calls go

```
 tactics/*.fs   (one file per tactic; mostly calls)                         Elab.Tactic
   │   tactic-run, tactic-api, tactic-core: runner, registry, (4) goal and proof-state library
   ├──► (1) elaborator library, tactic face  (Elab/Tactic/ElabTerm.lean)
   ├──► (2) simp and rewriting library: Elab face (rule lists, simp arguments)
   │          │
   │          ▼
   │     (2) core: Simp.Result/Step, visit, congruence, rewrite?, simp sets     Meta.Tactic
   │     goal layer meta-tactic/: apply, assumption, constructor, rewrite, simp's goal words
   │          │                       (3) numerals: called by (2)'s simprocs, norm_num, ring, omega
   ▼          ▼
 (1) elaborator library, Term core (elab-*.fs, FE2's forms, coercions)           Elab.Term
   │          │
   ▼          ▼
 tactic library: meta-must, app-builder, telescope                               Meta/AppBuilder, Basic
   ▼
 Meta core (+ discr-tree.fs, the shared index; synth; transform.fs)             Meta
   ▼
 (7) data readers: elab-data, lib-decode, meta-env (one access layer later)
 (6) Lean printing: used by every layer for messages, never calling back.  (5) test library: tests only.
 (8) verified programs: src/program/, apart from the front end.
```

Rules: (2)'s Meta core does not call (1); (2)'s Elab face does (rules and bracket lemmas are terms the user wrote).
(1) never calls the tactic runner except through one hook, `lf-elab-run-tactic`, for `by` inside a term (Lean's
`runTactic`, SyntheticMVars.lean:474, which imports `Elab.Tactic.Basic`). The discrimination tree is Meta core, shared
by instances (1) and simp (2), as in Lean (`Meta/DiscrTree`).

### 1.3 What already is library 1 or 2 under another name, and what is buried

| Evidence (file:line on `main` unless said) | Is | Library |
| --- | --- | --- |
| `elab-term.fs` (elabTerm, elabType, binop%), `elab-app.fs` (elabAppArgs), `elab-pending.fs` (synthesizeSyntheticMVars, default instances, mkInstMVar) | the Term core, complete for S1/S2's forms | 1 |
| `elab-decl.fs:143-152` `edc-tac-elab`, set into the hook `lf-tac-elab` declared at `tactic-basic.fs:139-142` | Lean's `Tactic.elabTerm` (ElabTerm.lean:45), buried in the declaration glue | 1 (tactic face) |
| `elab-decl.fs:155` registers the Term pending list with the Tactic runner's `tac-state:` | Term.SavedState, kept only at the Tactic layer | 1 |
| `tactic-core.fs` `lf-tac-elab-for-apply` (branch `tactic-lib-a2ii`) | `elabTermForApply` (ElabTerm.lean:265) | 1 (tactic face) |
| `elab-term.fs:138, 197`: `case`s over the seven syntax kinds it elaborates | Lean's term-elaborator table (`elabUsingElabFns`, TermElabM.lean:1691); every FE2 form would edit it | 1 |
| `elab-app.fs:237`, `elab-term.fs:268, 358, 474`: error 131 | the four places Lean inserts a coercion (ensureHasType, binop%'s analyze and applyCoe, ensureType) | 1 (FE4) |
| `tactic-rewrite.fs:120-213` (`lfw-telescope` to `lfw-proof!`) | `MVarId.rewrite` (Meta/Tactic/Rewrite.lean:28): telescope, matchEq?, kabstract, motive, its checks, `congrArg` proof, inside the `rw` tactic | 2 |
| `tactic-rewrite.fs:107-111` (a rule naming a definition: 99), `:146` (Iff: 99), `:124-125` (instance binder: 99), `:200-203` (rule metavariables left: 99) | Lean's equation theorems, `propext`, `postprocessAppMVars`, new goals: not ported | 2 / 1 |
| `instances.fs:358-490` (`it-node-new` … `it-walk`) | a complete discrimination trie, private to instances | 2 (shared index) |
| `kabstract.fs` (161 lines), `discr-keys.fs` (`mkPath`), `app-builder.fs` (`mkCongrArg`, `mkEqTrans`, `mkEqMPR`) | public already; library 2 uses them | 2 |
| `nat-offset.fs:105` `lf-meta-nat-lit`, `elab-term.fs` `et-num` (elabNumLit) | numerals | 3 |

## 2. Library 1: the elaborator library

**Scope.** Lean's `Elab.Term` for the forms LeanForth reads, and its tactic face, `Elab/Tactic/ElabTerm.lean`. The
Lean functions, with where each stands, are in appendix A. Instance search itself (`synth.fs`, Meta/SynthInstance)
stays Meta core; the elaborator's calls to it (`mkInstMVar`, `synthesizeInstMVarCore`, default instances) are library
1.

**Public words** (stack effects in appendix A.1). Existing outcome words stay: `lf-elab-term`, `lf-elab-ensuring`,
`lf-elab-type`, `lf-elab-ensure`, the `lf-elab-app-*` activations, `lf-elab-inst-mvar`, `lf-elab-synth-core`,
`lf-elab-synthesize`, `lf-elab-with-synth`. LA adds the form registry `lf-term-elab:`, the Term saved state
(`lf-term-commit-when`) and the tactic face, which throws: `lf-tac-elab-term`, `lf-tac-elab-ensuring`,
`lf-tac-elab-for-apply` (moved), `lf-tac-collecting-goals`, `lf-close-main-goal-using`. FE4a adds `lf-coerce`,
`lf-coerce-to-fun`, `lf-coerce-to-sort` and `lf-elab-mk-coe`; FE2's words (FE2_TERMS §5.5) become registered forms.

**Data structures.** The syntax store (`syntax.fs`); application activations and their slabs on frames
(`elab-app.fs`); the pending list with windows and the first-error record (`elab-pending.fs`); binop trees
(`elab-term.fs`); new: the form registry (an `lib/xt-table.fs` table by syntax kind, a chain per kind tried newest
first, as the tactic rows); the Term part of the saved state (pending window, first error, later FE2c's postponed
list).

**Needs.** From the Meta core: whnf, isDefEq, inferType, instantiateMVars, synth, the environment view. From the
tactic library: `lf-mk-app-m` (binop%), telescopes (default instances). From the data: instances, default instances,
reducibility, binder kinds (FE1c-bk), and, for FE4a, the `coe_decl` tag that `expandCoe` reads (Coe.lean:21-29), which
no data format carries yet (question 6; `Init/Coe.lean:135-254` tags ten declarations). No kernel word: the kernel
checks the finished term only.

**Outcomes.** Lean's errors keep their codes (125-139, FE2's 140-199) and stay invalid; a form or case not ported is
unsupported (99, 131-139), never accepted; fuel gives exhausted, no room full. The tactic face throws with the outcome
in the code (`meta-must.fs`), so unsupported never turns into a Lean error.

**Size** (*estimates*, file lines of Forth at the measured 1.9 per Lean line, appendix C; tests about as large): LA's
part about 450 (240 Lean lines: the tactic face, saved state, the registry) plus moving the seven kinds; FE4a about
570 (300 Lean lines). FE2 keeps its own design's sizes.

## 3. Library 2: the simp and rewriting library

**Scope.** Lean's `Meta/DiscrTree` (queries), `Meta/KAbstract`, `Meta/Tactic/Rewrite`, `Replace`,
`Meta/Tactic/Simp/*`, `Meta/CongrTheorems`, `Meta/ACLt` and `Meta/Transform`; its Elab face is
`Elab/Tactic/Rewrite.lean`, `Elab/Tactic/Location.lean` and `Elab/Tactic/Simp.lean`'s argument reader (`elabSimpArgs`,
`mkSimpContext`), which `simp`, `simp_all`, `simpa`, `norm_num` and `field_simp` share. Appendix B lists the
functions.

**Public words** (all throw, as Lean's MetaM; stack effects in appendix B.1), by group: the index (`lf-dt-insert`,
`lf-dt-get-unify`, `lf-dt-get-match`, `lf-dt-get-match-extra`); rewriting (`lf-meta-rewrite`,
`lf-goal-replace-local-decl`, `lf-rw-rules`, `lf-with-location`); results (`/simp-result`, `lf-simp-trans`,
`lf-simp-congr-arg`, `-congr-fun`, `-congr`, `-congr-args`, `lf-simp-proof`, `lf-simp-add-lambdas`); the traversal
(`lf-simp`, `lf-dsimp`, `lf-simp-methods`); lemmas (`lf-simp-rewrite?`, `lf-simp-try-theorem`,
`lf-simp-discharge-default`); congruence (`lf-congr-simp?`, `lf-simp-try-congr-thm`); simp sets (`lf-simp-set-new`,
`lf-simp-set-add-const`, `lf-simp-preprocess`, `lf-ac-lt`); goal words (`lf-simp-target`, `lf-simp-local-decl`,
`lf-simp-goal`); simprocs (`lf-simproc:`); the Elab face (`lf-simp-elab-args`).

**Data structures.** `Result` and `Step` records on frames; the simp context (configuration as `Simp.Config`, sets,
congruence lemmas) and methods (pre, post, discharge as execution tokens, so `norm_num1` plugs its `derive` in as
Lean's does, Mathlib `NormNum/Core.lean:220-248`); Lean's `State` as it is (Types.lean:248-255): three caches in one
state shared by the whole call, nested discharges included (`cache` term to result, `congrCache`, `dsimpCache`;
`lib/memo.fs` tables), the used-theorems list and the step count; a discharge runs with the cache preserved and the
used list put back (`withPreservedCache`, Rewrite.lean:45-47), nesting capped by `maxDischargeDepth`
(Rewrite.lean:40); new local lemmas get a fresh cache (`withFreshCache`, Main.lean:270, 287). Simp sets are
discrimination trees with `lib/htab.fs` maps by name and origin. The traversal runs on `lib/frame.fs` frames, no host
recursion; a nested simp call pushes its own frames on the same shared state, as Lean's does. SP1b-i ports the state
and the cache; SP2b the discharge rules.

**Needs.** From the Meta core: whnfCore, isDefEq, inferType, instantiateMVars, `fun-info.fs` (extended with Lean's
`ParamInfo` dependency fields for `getCongrSimpKinds`), `meta-config.fs` (transparency and `simpGlobalConfig`), a
throw-safe rebuild walk (`transform.fs`, section 4.2 item 5), `lf-with-new-depth` (`withNewMCtxDepth`,
Simp/Rewrite.lean:179, 188, 257, Main.lean:586) and `lf-meta-at` for `withSimpContext`'s `withReducible`
(Types.lean:963-966). From the tactic library: `mkCongrArg`, `mkEqTrans`,
`mkEqMPR`, telescopes, `mkLambdaFVars`; new builders `mkCongr`, `mkCongrFun`, `mkFunExt`, `mkPropExt`, `mkImpCongr`,
`mkForallCongr`, `mkOfEqTrue`, `mkEqTrue` (AppBuilder.lean:255, 232, 598, 602, 669, 678, 636, 648) with their first
callers. From the data: format 4 (SIMP_DATA §3) through SP1a's reader. From the hand-over: helper theorems (Lean's
`mkAuxLemma`) for `preprocess`, built once by S4's services. No kernel word.

**Outcomes.** Lean's errors (`simp made no progress`, rw's "did not find instance of the pattern" 215) invalid with
Lean's text; a simp lemma left out of the export, an unported simproc that matches, a `@[congr]` form not ported:
unsupported, never skipped (SIMP_DATA question 3); fuel exhausted; room full. A wrong data record can only change the
route or fail; the kernel checks the proof.

**Size** (*estimates* at 1.9 file lines per Lean line; tests about as large): LA's part about 320 new (170 Lean lines)
plus about 100 moved; the index's queries about 170 (90 Lean); SP1b about 2,100 (1,100 Lean: Types 315, Main 400,
Rewrite 300, lemma intake 45); SP1c about 1,330 (700 Lean: congruence 385, preprocess 72, perm and acLt 215).

## 4. Who calls whom

### 4.1 Each planned tactic is mostly calls (appendix D has the full Lean call lists)

| Tactic | Elaborator library (1) | Simp and rewriting (2) | Tactic library and goal layer | Others |
| --- | --- | --- | --- | --- |
| `rw` | rules by `lf-tac-elab-term`, side goals by `lf-tac-collecting-goals` | `lf-rw-rules`, `lf-with-location`, `lf-meta-rewrite`, `lf-goal-replace-target-eq`/`-local-decl`, kabstract | telescopes, `mkEqSymm`, `mkPropExt`, `synthAppInstances` | then `rfl` (`lf-tac-eval`) |
| `simp`, `simp only`, `dsimp` | bracket terms (`lf-simp-elab-args`) | `lf-simp`, `lf-dsimp`, sets, congruence, `lf-simp-target`, `lf-simp-local-decl` | builders, `mkLambdaFVars` | simp data (7), simprocs (3) |
| `norm_num` | — | `lf-simp` with norm_num's methods; the default set | builders | `derive`, `IsNat`/`IsInt`/`IsRat` (3); its table (7) |
| `ring` (`ring1`), `ring_nf` | — | `ring_nf` only: `lf-simp` with ring's evaluation as a simproc | `mkAppM`, synth (`CommSemiring`) | normal form `ExSum` (3); `first` (4) |
| `omega` | — | — | `falseOrByContra`, `getLocalHyps`, `mkDecideProof` | linear combinations, Int literals (3); helper theorem (hand-over) |
| `decide` | — | `zetaReduce` on `transform.fs` (shared with dsimp) | `mkDecide`, `mkDecideProof`, `closeMainGoalUsing` | — |
| `apply`, `exact`, `refine` | `lf-tac-elab-for-apply`, `lf-tac-elab-ensuring`, `lf-tac-collecting-goals` | — | `lf-goal-apply`, `lf-close-main-goal-using` | — |
| `constructor` | — | — | `lf-goal-constructor` | — |
| `cases`, `induction` | targets and `using` by `lf-tac-elab-term` | — | `ElimApp`, `evalAlts` (`meta-tactic/elim.fs`); later `cases`, `subst`, `injection` | eliminators (7) |

### 4.2 Changes to the present tactic library, flagged now

1. **One saved state across the layers.** Today `lf-commit-when` (`meta-must.fs:93`) restores only the metavariable
   context, and the Term pending list is saved only by the Tactic runner's `tac-state:` (`elab-decl.fs:155`). Lean has
   a saved state per layer (Meta/Basic.lean:479, TermElabM.lean:225, Tactic) and the elaborator's own attempts
   (`observing`, overloads, coercions) restore the Term part. Change: a registry
   `lf-state: ( save-xt back-xt layer -- )` in `meta-must.fs`; `tac-state:` becomes its Tactic-layer use;
   `lf-term-commit-when` restores Meta and Term. Now, because every new tactic file registers its state through
   `tac-state:`.
2. **Library words can be re-entered.** `meta-tactic/apply.fs` says "one apply runs at a time"; `kabstract.fs` keeps
   one record `kab`. Lean's simp calls itself (its discharger, congruence hypotheses), `norm_num`'s `derive` recurses,
   Mathlib's `gcongr` and `positivity` nest `apply`. Rule: a library word keeps its working record on a frame stack
   (as `elab-app.fs` does); one not yet re-entrant detects re-entry and answers unsupported. Change `apply.fs`'s
   record in LA, once `tactic-lib-a2ii` has merged. (The Meta core's leaf calls, finished before the next starts, may
   stay as they are.)
3. **The elaboration hook goes.** `lf-tac-elab` (`tactic-basic.fs:139`, set at `elab-decl.fs:152`) becomes the word
   `lf-tac-elab-term` of library 1's tactic face (`elab/tactic-term.fs`), with `lf-tac-elab-for-apply` moved there
   from `tactic-core.fs`. `tactic-core.fs` already requires `elab-term.fs`, so the hook only hides the dependency.
4. **A shared reader for rule lists and locations.** `by-rw[` has its own reader (`tactic-syntax.fs:232-240`). `simp`,
   `simp_rw`, `norm_num [..]`, `field_simp` and `ring_nf at h` need the same list with `←` (later `-name`, `*`, `↓`)
   and `at h`/`at *` (Lean's `rwRuleSeq`, `simpArgs`, `location`). Change: a "rule list" shape with a location suffix,
   in the registry's shape records (TACTIC_PLUGINS §3.2), before any of those words is added.
5. **Frames freed when a word throws.** No throwing word may run inside a `dw-run` walk (`dag-walk.fs:149`,
   `meta-must.fs:34`). `dsimp`, `zetaReduce` (S3) and `expandCoe` (FE4a) are Lean's `Meta.transform`
   (Transform.lean:98, 179) with callbacks that throw. The rule is wider than walks (`meta-must.fs:31-37`: also
   defeq's machine, synth's search and the elaborator's frames), and simp's own traversal frames will be such code.
   Change: every frame stack a library word opens is freed on both paths (a CATCH at its entry word); the reuse pass's
   planned rebuild walk is written so in `transform.fs`, S3 building it first, and simp's frames from SP1b-i.
6. **A public, throw-safe depth scope.** Simp tries lemmas and congruence theorems in a new metavariable depth
   (`withNewMCtxDepth`, Simp/Rewrite.lean:179, 188, 257; Main.lean:586); today only `app-builder.fs`'s private
   `abm-deeper` (`:224-226`) opens one under throws. Change: `lf-with-new-depth ( i*x xt -- j*x )` in `meta-must.fs`,
   `abm-deeper` on it, in LA.

Not changes, but rules for both libraries: their state lives in their own frame records, never in a tactic's step
record (32 cells, `tactic-run.fs:173`); `mkAuxLemma` (AuxLemma.lean:43) is one word in `handover.fs`, built by S4's
services and reused by SP1c.

## 5. Files every branch collides on, and a layout for parallel work

**Measured** (commits on `main` since 2026-11-14 touching each file, appendix C): `tests/mutants/faults.toml` 57,
`Makefile` 22, `whnf.fs` 16, `tactic-run.fs` 12, `tactic-rewrite.fs` 10, `meta-env.fs` 10, `lib-decode.fs` 8,
`kabstract.fs` 8, `tests/coverage-baseline.json` 8. TACTIC_PLUGINS (a1) already turns the build and test files into
per-file pieces (`faults.d/`, pattern rules, sorted JSON Lines). **Planned** collisions, by file and slice:

| File | Slices that would edit it |
| --- | --- |
| `elab-data.fs` (1,534 lines, 65 globals) | FE1c-bk (in flight, `data-bk`), SP1a's reader, FE2f (structures) |
| `instances.fs` | MF2, the trie's move (DT), FE3 |
| `app-builder.fs` | a2-iii (in flight), S3 (`mkDecide`), LA (`mkPropExt`), S4 (Int literals), SP1b (congruence builders) |
| `elab-term.fs`, `elab-app.fs` | LA (registry), FE4a (coercions), FE2a-e, FE1c-bk |
| `fun-info.fs`, `meta-config.fs` | SP1b/SP1c (FunInfo, `Simp.Config`), FE1c-bk |
| `handover.fs` | S4's services, SP1c (helper theorems) |
| `whnf.fs`, `defeq.fs`, `unfold.fs` | MF3a, MF3b, S3 (the unfold trace for decide's diagnosis) |

**Layout.** No mass move of existing files: a move breaks every branch in flight. New files go into folders owned by
one library: `src/front/elab/` (library 1: `tactic-term.fs`, `coe.fs`, and FE2's forms as `elab/forms/*.fs`, one per
Lean term elaborator, registered with `lf-term-elab:` as tactics are), `src/front/simp/` (library 2: `types.fs`,
`congr.fs`, `main.fs`, `rewrite.fs`, `theorems.fs`, `config.fs`, `args.fs`, `simprocs/*.fs` one family each),
`src/front/meta-tactic/` (goal words, including `rewrite.fs` from LA), `src/front/num/` (library 3, later); new Meta
services as new files (`discr-tree.fs`, `transform.fs`), never inside `mvars.fs`, `whnf.fs` or `meta-env.fs`.
[FRONT_LAYERS.md](../development/FRONT_LAYERS.md) records which existing file belongs to which library.
**File claims:** at most one open branch at a time per shared file of the table above, listed in the Now list of
`PROJECT_PROGRESS.md`; a slice's design names the shared files it claims. With these, two or three agents can work at
once: one on library 1's forms, one on library 2, one on the Meta core or a tactic.

## 6. Slices

Each ends in a command a user can run, lands with its first caller, carries its tests (the seven classes, planted
faults, terms compared node for node with pinned Lean) and documentation. Sizes are Forth file lines, *estimates*.
Proofs are shown in Lean's spelling for brevity; the test files are written in LeanForth (the language reference's
words, `by-rw[`, `by-exact`, …) beside their pinned-Lean twins.

| Slice | Command at the end (`bin/leanforth check --env init.ndjson --elab-data init.elab.ndjson FILE.lf`, or a slice of `Init` holding the lemmas named) | Contains | Forth + tests | Gates | Needs |
| --- | --- | --- | ---: | --- | --- |
| **LA** the elaboration API and the rewrite library | a file with `rw [← h] at h2`, `rw [Nat.lt_iff_add_one_le]` (an Iff rule, `propext` in the axiom report), `rw [Nat.sub_add_cancel]` leaving the side goal `m ≤ n` closed by `exact h`: accepted, node for node Lean's; wrong twins exit 4 with Lean's texts; every S1/S2 dump byte-identical | §4.2 items 1-4 and 6; `elab/tactic-term.fs`; the form registry with the seven kinds moved; `meta-tactic/rewrite.fs` (moved from `tactic-rewrite.fs`, plus `symm`, Iff, instance binders, new goals); `replaceLocalDecl`; locations | 1,000 + 900 | [parser]: `at`, `←`, no other text changes meaning | a2-ii, a2-iii merged; S2's done-check fixes merged (the baseline dumps are then a done state) |
| **MF2+DT** | MF2's command (MATHLIB_FRONT §8) | MF2; the trie moved to `discr-tree.fs` with insertion that replaces in place, `instances.fs` on it (taken from SP1a's row, so `instances.fs` is edited in one slice) | 600 + 400 | MF2's | `names-index` (merged) |
| **SP1a** (reader) | SIMP_DATA's SP1a | format 4 read and checked; no longer the trie's move (now MF2+DT) | per SIMP_DATA less the move | [import]/[format] approved | the tool (`simp-data-tool`), FE1c-bk merged |
| **SP1b-i** simp core | `by-simp-only[ Nat.add_zero ]` proves `n + 0 + 0 = n` and `f (n + 0) = f n`; `by-simp-only[ ]` on a goal it cannot change failing with Lean's "simp made no progress" | Result, Step, congrArgs with automatic congruence, `getMatch`/`getMatchWithExtra` (with their first caller, moved from SP1a), `rewrite?` and `tryTheorem?` for unconditional Eq lemmas, the cache, `simpTarget`, `applySimpResult`, `of_eq_true` | 1,250 + 900 | [parser] (`by-simp-only[`) | LA, MF2+DT, SP1a |
| **SP1b-ii** under binders | `(fun x => x + 0) = (fun x => x)` and `(∀ x, x + 0 = 1) ↔ (∀ x, x = 1)` by `by-simp-only[ Nat.add_zero ]` | `simpLambda` (funext), `simpForall`, `simpArrow`, `simpLet`, `simpProj`, `dsimp` on `transform.fs`, `rfl` lemmas without proof steps | 850 + 700 | — | SP1b-i, S3's walk |
| **FE4a** coercions | `theorem t (n : Nat) (i : Int) : n + i = i + n := by rw [Int.add_comm]` accepted, the statement `↑n + i = i + ↑n` node for node Lean's; `#check` lines of `Int.natCast_add` | `coerce?`, `coerceSimple?`, `expandCoe`, to-function, to-sort, `mkCoe`, the four 131 sites | 570 + 600 | [parser]; [format] for the `coe_decl` tag (question 6) | LA, S3's walk |
| **SP1c** | SIMP_DATA's SP1c: `↔`, `¬`, `←`, hypotheses, through `if` | `mkCongrSimp?`, `@[congr]`, `preprocess` with helper theorems, `isPerm`, `acLt` | 1,330 + 1,000 | [parser]; helper theorems as S4 decides | SP1b-ii, S4's services |

Then SP2a, SP2b, SP3, SP4, MF3a, MF3b, S8a1, S7, S8a2 and S8b as SIMP_DATA and MATHLIB_FRONT order them; FE2's S5 and
S6 as FE2_TERMS cuts them, each form a file on the registry.

**SIMP_DATA's estimates.** On the measured yardstick SP1b is about 3,700 lines with tests, not 1,400, and SP1c about
2,300, not 1,200 (about 37% and 52%): hence SP1b's two parts, each about the size of a tactic-library piece.

**Order and parallel work** (recommended; at most three front-end agents at a time, no shared file twice):

1. Now, in flight: a2-ii and a2-iii (`tactic-lib-a2ii`), SP1a's tool (`simp-data-tool`), FE1c-bk (`data-bk`). MF2 can
   start (`names-index` is on main) but is not in flight; it becomes MF2+DT.
2. After a2-ii/a2-iii and S2's done-check fixes merge: **LA** ∥ **MF2+DT** ∥ **S3** (`by-decide`, which builds
   `transform.fs`). Disjoint files: LA claims `elab-term.fs`, `elab-decl.fs`, `tactic-rewrite.fs`, `tactic-syntax.fs`,
   `meta-must.fs`; MF2+DT `instances.fs`; S3 `app-builder.fs` (LA adds `mkPropExt` after S3, or in its own section)
   and `whnf.fs`'s trace hook. The front reuse pass's follow-ups (plan 9.4.8n: `meta-spine.fs`, `meta-check.fs`,
   `instantiate.fs`, `term-eqv.fs`) claim none of LA's files and may run beside it; the next front reuse pass waits
   for LA where it would touch `tactic-rewrite.fs`, `elab-*.fs` or `tactic-syntax.fs`, since LA moves code out of
   them.
3. Then **SP1b-i** ∥ **FE4a** ∥ **S5's first forms** (binders, `fun`, `∀`) on the registry; SP1a's reader before
   SP1b-i.
4. Then **SP1b-ii** ∥ **S4's services** (helper theorems, `getLocalHyps`, Int literals: library 3's design first) ∥
   **MF3a**; then **SP1c** ∥ S5's other forms ∥ MF3b; then SP2a onwards.

How they interleave with what is planned: S3 and S4 keep their plan rows and use the libraries; MF2 absorbs the trie's
move (SIMP_DATA's SP1a row amended in this branch); FE2's sub-steps FE2a-e become forms on the registry (FE2d after
FE4a, both in `elab-app.fs`); FE3's remaining part (classes and instances declared in text) is not needed for
statements about ℝ (MATHLIB_FRONT §5) and can follow FE4a (question 7).

## 7. Reuse

**Used:** `lib/frame.fs` (all traversals), `lib/memo.fs` (simp's cache, per-lemma checks), `lib/htab.fs` (sets by
name, lemmas by origin), `lib/sort.fs` (stable descending priority sort, SIMP_DATA §1), `lib/slab.fs`, `lib/runs.fs`
(goal lists), `lib/xt-table.fs` (the form registry, simprocs), `lib/module.fs` (private wordlists); in the front end
`meta-must.fs`, `app-builder.fs`, `telescope.fs`, `kabstract.fs`, `discr-keys.fs`, `fun-info.fs` (extended),
`elab-pending.fs`'s window, `synth.fs`, `handover.fs`, `offset-walk.fs` (under `transform.fs`), the goal layer.
**New:** `discr-tree.fs` (moved, not copied), `transform.fs` (S3), `elab/tactic-term.fs`, `elab/coe.fs`, the form
registry, the state registry, `simp/*.fs`, `meta-tactic/rewrite.fs`. No new `src/lib` library: all are Lean's layers.
**Copies replaced:** the hook body `elab-decl.fs:143-152`; `tactic-core.fs`'s `lf-tac-elab-for-apply` (moved); the
rewrite core `tactic-rewrite.fs:120-213`; the trie `instances.fs:358-490`; the `case` dispatch `elab-term.fs:138,
197`; the four 131 refusals (FE4a); every later private copy is a review finding (AGENTS.md "Reuse first").

## 8. Risks

1. **Moves change terms.** Each moved word calls what Lean calls there; acceptance requires byte-identical dumps and
   goldens of every S1/S2 file before and after LA, and unchanged fuel counts.
2. **Sizes.** The simp core is long in Lean too; the estimates here are about twice SIMP_DATA's. Checked after SP1b-i
   against what was written (Forth lines per Lean function), as the owner asked on 2026-11-17.
3. **Hidden shared state.** A library record re-entered silently corrupts a nested call. Mitigation: §4.2 item 2's
   rule, a re-entry test per library word simp reaches, and a planted fault that shares a record.
4. **Coercions earlier than planned.** FE4a turns refusals (131) into terms; each is compared with pinned Lean, and
   a statement Lean would coerce differently stays unsupported.
5. **Merges with work in flight** (`tactic-lib-a2ii`, `simp-data-tool`, `data-bk`): LA starts after a2-ii/iii merge;
   SP1a's reader after `data-bk`.
6. **Layers drift back.** A tactic writing a private Meta copy again; the architect role checks FRONT_LAYERS.md and
   the tactic plug-in check keeps tactic branches confined.

## 9. Questions for the owner

1. **Approve the layers and the two libraries' scope** (section 1.2: the elaborator library is Lean's term elaborator
   plus its face for tactics; the simp and rewriting library is Lean's `rw` and `simp` machinery, with the lemma index
   shared with instance search)? *Recommendation: yes.* It is Lean's own split, so a port stays a port.
2. **Make the six tactic-library changes of section 4.2 in package LA (item 5's walk in S3), before more tactics
   are written?**
   *Recommendation: yes.* Today about ten tactics use the present interface; after `simp`, `norm_num` and the
   combinators, each change would touch dozens of files.
3. **Package sizes:** packages of about 1,500-2,500 lines of Forth with their tests, one agent each, a command at
   the end (LA about 1,900; SP1b in two parts of about 2,150 and 1,550)? *Recommendation: yes.* Larger than before, as
   you asked; SP1b whole (about 3,700) would be too long for one review round.
4. **A registry of term forms, as for tactics,** so FE2's forms are separate files written in parallel?
   *Recommendation: yes.* Otherwise every FE2 branch edits the same dispatch in `elab-term.fs`; [parser] question:
   nothing written today changes meaning (byte-identical dumps).
5. **File claims and new folders:** one open branch at a time per shared file (section 5's table), new files in
   `elab/`, `simp/`, `num/`, and no mass move of existing files? *Recommendation: yes.* It removes the collisions you
   noted without breaking work in flight.
6. **A new [format] approval: the `coe_decl` tag.** Coercions unfold the declarations Lean marks `coe_decl`
   (`Coe.coe`, `CoeT.coe` and eight more in `Init/Coe.lean`), a mark the export lacks. Add it as one more value of the
   data's `tag` record, checked like the others, in the next format the tool writes? This is an addition to format 4
   as you approved it, so it needs its own approval. *Recommendation: yes.* It can only make a coercion unfold as
   Lean's does; the kernel checks the result. (Separately, and not a question: FE2_TERMS.md's structure records,
   planned as format 4 before simp's format 4 was approved, are renumbered format 5 in this branch.)
7. **Order, with one change to an approved slice:** LA ∥ MF2+DT ∥ S3; then SP1b-i ∥ FE4a ∥ FE2's first forms; library
   3's design before S4's services; coercions (FE4a) before the rest of FE3; and the discrimination tree's move out of
   `instances.fs` taken from SP1a into MF2 (so that file is edited once), its two lookups going to SP1b-i, their first
   caller? *Recommendation: yes.* Statements about real numbers need coercions far sooner than classes declared in
   LeanForth text; each slice still ends in a command compared with pinned Lean.

## 10. Review

Architecture review of `baeb2568` (2026-11-18, "ready after fixes", 7 findings, all taken):

| # | Finding | Answered in |
| --- | --- | --- |
| 1 | library 1 is not 70% built: the S1/S2 core, about a third by Lean lines | owner page; library 1's growth now counts FE2's share |
| 2 | the trie's move was in both SP1a (approved) and MF2+DT | section 6 (MF2+DT and SP1a rows), SIMP_DATA.md's SP1a row amended, question 7 |
| 3 | question 6 reopened an approved format | question 6 is now its own `coe_decl` approval; FE2_TERMS.md's structures renumbered format 5 |
| 4 | missing API: a public depth scope, frames freed on throw beyond walks, Lean's simp state and caches | section 4.2 items 2, 5, 6 (all in LA); section 3's data structures and needs |
| 5 | order against the progress file: MF2 not in flight; S2 not done; the reuse passes | section 6 order step 1-2 and LA's needs |
| 6 | SIMP_DATA's SP1b is about 37% of this estimate, not half | owner page; section 6 |
| 7 | main text too long | word list and libraries 3-8 moved to appendices E and F |

## Appendix A. Library 1: public words and Lean functions

### A.1 Public words (outcome words unless marked "throws")

| Word ( stack ) | Lean (file:line) | State |
| --- | --- | --- |
| `lf-elab-term ( node expected -- term outcome )` | `elabTerm` (TermElabM.lean:1908) | exists |
| `lf-elab-ensuring`, `lf-elab-type`, `lf-elab-ensure ( e expected -- e outcome )` | `elabTermEnsuringType` 1918, `elabType` 1980, `ensureHasType` 1334 | exist; FE4a adds the coercion |
| `lf-elab-app-new`, `lf-elab-app-term+`, `lf-elab-app-syntax!` | `elabAppArgs` (App.lean:1351) and its state machine | exist; FE2d extends |
| `lf-elab-inst-mvar`, `lf-elab-synth-core`, `lf-elab-synthesize ( mode -- outcome )`, `lf-elab-with-synth ( xt mode -- outcome )` | `mkInstMVar` 1954, `synthesizeInstMVarCore` 1232, `synthesizeSyntheticMVars` (SyntheticMVars.lean:611), `withSynthesize` 678 | exist |
| `lf-term-elab: ( xt kind -- )` | the `builtin_term_elab` attribute and `elabUsingElabFns` (TermElabM.lean:637, 1691): an elaborator per syntax kind, the newest tried first | LA |
| `lf-term-commit-when ( i*x xt -- j*x flag )`, `lf-term-observing` | `Term.saveState`/`restore` (417, 420), `observing` 574 | LA |
| `lf-tac-elab-term ( node expected postpone? -- e )` throws | `Tactic.elabTerm` (ElabTerm.lean:45), replacing the hook | LA |
| `lf-tac-elab-ensuring ( node expected postpone? -- e )` throws | `Tactic.elabTermEnsuringType` 51 | LA |
| `lf-tac-elab-for-apply ( node -- e )` throws | `elabTermForApply` 265 | moved in LA |
| `lf-tac-collecting-goals ( xt tag -- e goals )` throws | `withCollectingNewGoalsFrom` 142, with `getMVarsNoDelayed` (CollectMVars.lean:42) | LA |
| `lf-close-main-goal-using ( xt -- )` throws | `closeMainGoalUsing` 85 | LA (planned in a2-ii) |
| `lf-coerce ( e expected -- e' outcome )`, `lf-coerce-to-fun`, `lf-coerce-to-sort`, `lf-elab-mk-coe` | `coerce?` (Meta/Coe.lean:274), `coerceSimple?` 93, `expandCoe` 44, `coerceToFunction?` 100, `coerceToSort?` 114, `mkCoe` (TermElabM.lean:1294) | FE4a |
| FE2's words (`lf-elab-binders`, `lf-elab-fun`, `lf-elab-let`, `lf-elab-postpone`, …) | FE2_TERMS §5.5 | S5, S6, each a registered form |

### A.2 Lean functions and their Forth words

Lean 4.35.0 file:line; Lean lines are code lines of the definition and its private helpers (approximate where
marked ~); "exists" names the file. Forth estimates use 1.9 file lines per Lean line (appendix C).

| Lean function | File:line | Lean lines | Forth word | State | Forth (est.) |
| --- | --- | ---: | --- | --- | ---: |
| `elabTerm`, `elabUsingElabFns` | TermElabM.lean:1908, 1643-1700 | ~80 | `lf-elab-term`, `lf-term-elab:` | exists; registry in LA | 110 |
| `useImplicitLambda`, `elabImplicitLambda` | TermElabM.lean:1771-1907 | ~135 | FE2c | FE2 | per FE2 |
| `postponeElabTerm`, `tryPostpone` | TermElabM.lean:1636, 1370 | ~60 | `lf-elab-postpone` | FE2c | per FE2 |
| `ensureHasType`, `mkCoe` | TermElabM.lean:1334, 1294 | ~70 | `lf-elab-ensure`, `lf-elab-mk-coe` | exists without coercion; FE4a | 130 |
| `mkInstMVar`, `synthesizeInstMVarCore` | TermElabM.lean:1954, 1232 | ~70 | `lf-elab-inst-mvar`, `lf-elab-synth-core` | exists (`elab-pending.fs`) | — |
| `synthesizeSyntheticMVars`, `synthesizeUsingDefault`, `withSynthesize` | SyntheticMVars.lean:611, 215, 678 | ~160 | `lf-elab-synthesize`, `lf-elab-with-synth` | exists | — |
| `runTactic` | SyntheticMVars.lean:474 | ~70 | `lf-elab-run-tactic` (hook) | FE2h | per FE2 |
| `Term.SavedState`, `saveState`, `restore`, `observing` | TermElabM.lean:225, 417, 420, 574 | ~60 | `lf-state:`, `lf-term-commit-when`, `lf-term-observing` | LA | 110 |
| `elabAppArgs` and its state machine | App.lean:563-1420 | ~600 | `lf-elab-app-*` | exists (no `@`, named, eta, optParam) | — |
| `elabAppFn`, `mergeFailures` (overloads) | App.lean:2060, 2190 | ~150 | — | FE2/FE3, when overloads appear | 290 |
| `elabAppLVals` (field notation) | App.lean:1843-1925 | ~80 | `lf-elab-field` | FE2f | per FE2 |
| `binop%`, `binrel%` (`toTree`, `analyze`, `applyCoe`, `toExprCore`) | Extra.lean:183-564 | ~300 | in `elab-term.fs` | exists; `applyCoe`'s coercion in FE4a | 60 |
| `coerce?`, `coerceSimple?`, `expandCoe`, `coerceToFunction?`, `coerceToSort?` | Meta/Coe.lean:274, 93, 44, 100, 114 | ~170 | `lf-coerce`, `lf-coerce-to-fun`, `lf-coerce-to-sort` | FE4a (monad lifts later) | 320 |
| `Tactic.elabTerm`, `elabTermEnsuringType`, `runTermElab` | Elab/Tactic/ElabTerm.lean:45, 51, 31 | ~50 | `lf-tac-elab-term`, `lf-tac-elab-ensuring` | hook today; LA | 95 |
| `closeMainGoalUsing` | ElabTerm.lean:85 | 15 | `lf-close-main-goal-using` | LA | 30 |
| `withCollectingNewGoalsFrom`, `elabTermWithHoles`, `getMVarsNoDelayed` | ElabTerm.lean:142, 200; CollectMVars.lean:42 | ~70 | `lf-tac-collecting-goals`, `lf-tac-elab-with-holes` | LA | 135 |
| `elabTermForApply` | ElabTerm.lean:265 | 17 | `lf-tac-elab-for-apply` | `tactic-core.fs` (a2-ii); moved in LA | — |
| Binders, `fun`, `∀`, `let`, `have`, `show`, ascription, `sorry`, `▸` | Binders.lean:258-745; BuiltinNotation.lean:114-457 | ~700 | FE2_TERMS §5.5 | S5, S6 | per FE2 |

## Appendix B. Library 2: public words and Lean functions

### B.1 Public words (all throw)

| Group | Words ( stack ) | Lean | Slice |
| --- | --- | --- | --- |
| Index | `lf-dt-insert ( tree keys n v -- )`, `lf-dt-get-unify`, `lf-dt-get-match ( tree e -- addr n )`, `lf-dt-get-match-extra ( tree e -- addr n )` | `insertCore` (DiscrTree/Basic.lean:176), `getUnify` (Main.lean:567), `getMatch` 483, `getMatchWithExtra` 489 | MF2+DT; the two matches with SP1b |
| Rewrite | `lf-meta-rewrite ( goal e heq symm? -- new proof goals )`, `lf-goal-replace-local-decl ( goal fvar new h -- goal' )`, `lf-rw-rules ( i xt -- )`, `lf-with-location ( loc xt-hyp xt-target -- )` | `MVarId.rewrite` (Rewrite.lean:28), `replaceLocalDecl` (Replace.lean:76), `withRWRulesSeq` (Elab/Tactic/Rewrite.lean:117), `withLocation` (Location.lean:58) | LA |
| Result and Step | `/simp-result` (term, proof or none, cache flag), `lf-simp-trans ( r1 r2 -- r )`, `lf-simp-congr-arg ( f r -- r )`, `lf-simp-congr-fun ( r a -- r )`, `lf-simp-congr ( r1 r2 -- r )`, `lf-simp-congr-args ( r args n -- r )`, `lf-simp-proof ( r -- h )`, `lf-simp-add-lambdas ( r fvars n -- r )` | Simp/Types.lean: `Result` 25, `mkEqTrans` 47, `mkCongrArg` 603, `mkCongrFun` 598, `mkCongr` 608, `congrArgs` 649, `getProof` 560, `addLambdas` 942 | SP1b |
| The traversal | `lf-simp ( e ctx methods -- r )`, `lf-dsimp ( e ctx -- e' )`, `lf-simp-methods ( pre post discharge -- m )` | `Simp.main` (Main.lean:749), `simpLoop` 677, `visitFn` 531, `congr` 637, `simpLambda`/`simpForall`/`simpArrow`/`simpLet` 299-470, `dsimp` 776, `Methods` (Types.lean:424) | SP1b |
| Lemmas | `lf-simp-rewrite? ( e set rfl-only? -- r flag )`, `lf-simp-try-theorem ( e thm -- r flag )`, `lf-simp-discharge-default` | `rewrite?` (Simp/Rewrite.lean:207), `tryTheorem?` 187, `synthesizeArgs` 58, `dischargeDefault?` 637 | SP1b (Eq, no hypotheses); SP2b (discharger) |
| Congruence | `lf-congr-simp? ( f n -- thm flag )`, `lf-simp-try-congr-thm` | `mkCongrSimp?` (CongrTheorems.lean:387), `trySimpCongrTheorem?` (Main.lean:586) | SP1c |
| Simp sets | `lf-simp-set-new`, `lf-simp-set-add-const ( set name post? inv? prio -- )`, `lf-simp-preprocess`, `lf-ac-lt ( a b -- flag )` | `SimpTheorems` (SimpTheorems.lean:599), `mkSimpTheoremsFromConst` 453, `preprocess` 319, `isPerm` 292, `acLt` (ACLt.lean:200) | SP1b (bracket constants); SP1c (preprocess, perm) |
| Goal words | `lf-simp-target ( goal ctx m -- goal' \| 0 )`, `lf-simp-local-decl`, `lf-simp-goal` | `simpTarget` (Main.lean:796), `applySimpResult` 807, `simpLocalDecl` 866, `simpGoal` 874 | SP1b; SP2b |
| Simprocs | `lf-simproc: ( keys post? xt "Lean.name" -- )` | `Simprocs` (Types.lean:417) | SP2a fixes it |
| Elab face | `lf-simp-elab-args ( i -- ctx simprocs )` | `elabSimpArgs`, `mkSimpContext` (Elab/Tactic/Simp.lean:554-580) | SP1b (brackets), SP2a (default set) |

### B.2 Lean functions and their Forth words

| Lean function | File:line | Lean lines | Forth word | State | Forth (est.) |
| --- | --- | ---: | --- | --- | ---: |
| `insertCore`, `insertVal`, `insertAux` | DiscrTree/Basic.lean:125-179 | ~55 | `lf-dt-insert` | private in `instances.fs:358-430`; MF2+DT | moved + 40 |
| `getUnify` | DiscrTree/Main.lean:567 | ~40 | `lf-dt-get-unify` | private in `instances.fs:444-490`; MF2+DT | moved |
| `getMatchLoop`, `getMatch`, `getMatchWithExtra` | DiscrTree/Main.lean:438-520 | ~90 | `lf-dt-get-match`, `-extra` | SP1b-i | 170 |
| `mkPath`, `getKeyArgs` | DiscrTree/Main.lean:329, 350 | ~250 | `lf-dt-path`, `lf-dt-key` | exists (`discr-keys.fs`); match mode in SP1a | — |
| `kabstract` with `toHeadIndex`, `headNumArgs` | KAbstract.lean:30; HeadIndex.lean:55-115 | ~85 | `lf-meta-kabstract` | exists | — |
| `MVarId.rewrite` | Meta/Tactic/Rewrite.lean:28-104 | 73 | `lf-meta-rewrite` | in `tactic-rewrite.fs:120-213`; LA moves it and adds `symm`, Iff, instances, new goals | moved + 60 |
| `replaceTargetEq`, `replaceLocalDecl` | Replace.lean:21, 76 | ~50 | `lf-goal-replace-target-eq`, `-local-decl` | first on a2-ii; second LA | 65 |
| `elabRewrite`, `rewriteTarget`, `rewriteLocalDecl`, `withRWRulesSeq` | Elab/Tactic/Rewrite.lean:25-133 | ~100 | `lf-rw-rules` | partly in `tactic-rewrite.fs`; LA | 120 |
| `expandLocation`, `withLocation` | Elab/Tactic/Location.lean:32, 58 | ~45 | `lf-with-location` | LA | 85 |
| `Result`, `mkEqTrans`, `getProof`, `mkEqMPR`, `mkCongr*`, `mkImpCongr`, `congrArgs`, `addExtraArgs`, `addLambdas`, `addForalls` | Simp/Types.lean:25-56, 560-680, 919-975 | ~315 | `/simp-result`, `lf-simp-*` | SP1b | 600 |
| `Step`, `andThen`, `mkEqTransResultStep`, `Methods`, `pre`, `post` | Simp/Types.lean:316-460 | ~80 | `lf-simp-methods` | SP1b-i | 150 |
| `visitFn`, `congrDefault`, `congr`, `simpApp`, `simpStep`, `cacheResult`, `simpLoop`, `simpImpl`, `main` | Simp/Main.lean:531-750 | ~190 | `lf-simp` | SP1b-i | 360 |
| `simpProj`, `simpLambda`, `simpArrow`, `simpForall`, `simpLet`, `simpHaveTelescope` | Simp/Main.lean:299-470 | ~170 | (inside `lf-simp`) | SP1b-ii | 320 |
| `dsimp`, `dsimpImpl`, `Meta.transform`, `zetaReduce` | Simp/Main.lean:516, 776; Transform.lean:98-219 | ~140 | `lf-dsimp`; `transform.fs` | S3 (walk), SP1b-ii | 270 |
| `simpTarget`, `applySimpResult`, `simpLocalDecl`, `simpGoal` | Simp/Main.lean:781-912 | ~110 | `lf-simp-target`, `-local-decl`, `-goal` | SP1b-i (target), SP2b | 210 |
| `rewrite?`, `tryTheoremCore`, `tryTheorem?`, `rewritePre`, `rewritePost` | Simp/Rewrite.lean:115-300, 389-400 | ~200 | `lf-simp-rewrite?`, `lf-simp-try-theorem` | SP1b-i (Eq, unconditional) | 380 |
| `synthesizeArgs`, `discharge?'`, `dischargeDefault?`, `dischargeUsingAssumption?` | Simp/Rewrite.lean:32-108, 576-650 | ~150 | `lf-simp-discharge-default` | SP2b | 285 |
| `mkSimpTheoremsFromConst`, `mkSimpTheoremCore`, `mkSimpTheoremKeys` | SimpTheorems.lean:396-473 | ~65 | `lf-simp-set-add-const` | SP1b-i | 125 |
| `preprocess`, `isPerm`, `isRflProof` | SimpTheorems.lean:319, 292, 232 | ~130 | `lf-simp-preprocess` | SP1c | 250 |
| `acLt` | ACLt.lean:14-203 | ~190 | `lf-ac-lt` | SP1c | 360 |
| `getCongrSimpKinds`, `mkCast`, `mkCongrSimpCore?`, `mkCongrSimp?` | CongrTheorems.lean:178-391 | ~200 | `lf-congr-simp?` | SP1c | 380 |
| `mkSimpCongrTheorem`, `trySimpCongrTheorem?`, `processCongrHypothesis` | SimpCongrTheorems.lean:56; Main.lean:552-636 | ~185 | `lf-simp-try-congr-thm` | SP1c | 350 |
| `elabSimpArgs`, `mkSimpContext` | Elab/Tactic/Simp.lean:554-580 and helpers | ~300 | `lf-simp-elab-args` | SP1b-i (brackets), SP2a | 570 |
| Simprocs (built in) | Meta/Tactic/Simp/BuiltinSimprocs/ | 2,112 | `simp/simprocs/*.fs` | SP2a, SP3 | per SIMP_DATA |

## Appendix C. Measurements

**The yardstick: Forth lines per Lean line, ported code already written.** Forth code lines exclude comments and blank
lines (`grep -v '^\s*\\' FILE | grep -cv '^\s*$'`); Lean lines count the definitions and helpers named, without
comments or blank lines (`sed -n A,Bp FILE | grep -v '^\s*--' | grep -cv '^\s*$'`); file lines by `wc -l`.

| Port | Lean lines | Forth code | Code per Lean | Forth file lines | File per Lean |
| --- | ---: | ---: | ---: | ---: | ---: |
| Builders, telescopes, throwing faces (a2-i; [FRONT_LAYERS.md](../development/FRONT_LAYERS.md) table) | 301 | 234 | 0.78 | 550 (three files) | 1.8 |
| `MVarId.apply` and helpers (`meta-tactic/apply.fs`, branch `tactic-lib-a2ii`; Apply.lean:1-232) | ~170 | 135 | 0.8 | 218 | 1.3 |
| `kabstract` with HeadIndex (`kabstract.fs`) | ~85 | 89 | 1.05 | 161 | 1.9 |
| `rw` and `MVarId.rewrite` (`tactic-rewrite.fs`; Rewrite.lean:28-104, Elab/Tactic/Rewrite.lean:25-77) | 119 | 165 | 1.4 | 251 | 2.1 |

So 0.8-1.4 code lines and 1.3-2.1 file lines per Lean line; this design estimates with 1.9 file lines (traversals and
tactic logic weigh most in libraries 1 and 2) and tests about as large as the file. SIMP_DATA §8 used 1.2 lines
with tests.

**Other commands.** Line counts: `wc -l src/front/*.fs` on `main` `c8cd00dd` (17,297). Words and style:
`python3 scripts/forth-metrics.py src/front/*.fs` (4,770 words, 81 globals; `elab-data.fs` 65 of them). Files touched:
`git log --since=2026-11-14 --format= --name-only main -- src/front src/author/errors.fs src/main.fs Makefile
tests/mutants/faults.toml tests/coverage-baseline.json src/cli/check-lf.fs | sort | uniq -c | sort -rn`. Who requires
whom: `grep -l "require ./FILE" src/front/*.fs` per file. Branch `tactic-lib-a2ii`: `git diff --stat
main...tactic-lib-a2ii -- src` (23 files, 845 lines added). Lean function lines: `grep -n "def NAME"` in pinned Lean's
`src/lean/Lean/`.

## Appendix D. Lean call lists of the tactics, one level down

| Tactic (Lean) | Lean calls → LeanForth word |
| --- | --- |
| `rw` (Elab/Tactic/Rewrite.lean, Meta/Tactic/Rewrite.lean) | `withRWRulesSeq`, `withLocation` → LA; `Tactic.elabTerm` → `lf-tac-elab-term` (LA); `MVarId.rewrite` → `lf-meta-rewrite` (LA); `forallMetaTelescopeReducing` → exists (`telescope.fs`); `kabstract` → exists; `postprocessAppMVars` → a2-iii; `getMVarsNoDelayed` → LA; `mkEqSymm` → exists; `propext` by `mkConst` → `mkPropExt` (LA); `replaceTargetEq` → a2-ii; `replaceLocalDecl` → LA; `rfl` after → `lf-tac-eval` |
| `simp only` (Elab/Tactic/Simp.lean, Meta/Tactic/Simp/) | `mkSimpContext`, `elabSimpArgs` → SP1b-i; `Simp.main` → `lf-simp`; `getMatchWithExtra` → SP1b-i; `isDefEq`, `instantiateMVars`, `whnfCore` → exist; `mkCongr`, `mkCongrFun`, `mkFunExt`, `mkImpCongr`, `mkOfEqTrue` → SP1b; `mkCongrSimp?` → SP1c; `simpTarget`, `applySimpResult` → SP1b-i; `mkAuxLemma` → S4's services |
| `norm_num1` (Mathlib NormNum/Core.lean) | `Simp.main` with methods → `lf-simp`, `lf-simp-methods`; `derive`, extension lookup (`getMatch`, Core.lean:106) → `lf-dt-get-match` + library 3; `IsNat.to_eq` builders → library 3 |
| `ring1` (Mathlib Ring/Basic.lean:596) | `synthInstance` → exists; `NormNum.derive` → library 3; `isDefEq` at reducible (atoms) → exists; `mkAppM` → exists; `first` → library 4 |
| `omega` (Elab/Tactic/Omega/Frontend.lean) | `falseOrByContra`, `getLocalHyps` → S4's services; `mkDecideProof` → S3; Int literals and linear combinations → library 3; `mkAuxLemma` → S4's services |
| `decide` (Elab/Tactic/Decide.lean) | `zetaReduce` → `transform.fs` (S3); `mkDecide`, `mkDecideProof` → S3; `closeMainGoalUsing` → LA |
| `exact`, `apply`, `refine` (ElabTerm.lean:100, 282, 207) | `elabTermEnsuringType`, `elabTermForApply`, `withCollectingNewGoalsFrom` → LA; `MVarId.apply` → a2-iii; `closeMainGoalUsing` → LA |
| `constructor` (Constructor.lean:23) | `whnfR`, `MVarId.apply` under `observing?` → exist / a2-iii |
| `cases`, `induction` (Induction.lean, Meta/Tactic/Cases.lean) | `ElimApp`, `evalAlts` → `meta-tactic/elim.fs`; `Tactic.elabTerm` for targets → LA; `MVarId.cases`, `subst`, `injection` → goal layer, FE5 |

## Appendix E. Words used here

- **Term, type, metavariable.** A term is Lean's data for an expression; its type is another term. A *metavariable*
  is a hole in a term, to be filled later (by unification, an instance search or a tactic).
- **Elaboration.** Turning written text into a complete term. *Implicit arguments* are those the user does not
  write (`@id Nat 3` written `id 3`); the elaborator inserts a metavariable for each. The *expected type* is the type
  the context wants; passing it down lets the elaborator fill holes earlier. *Unification* (`isDefEq`) makes two terms
  equal by filling metavariables. *Instance synthesis* finds a value for a class argument (`Add Nat`).
  A *coercion* is a conversion Lean inserts when types differ (`↑n : Int` for `n : Nat`).
- **Layers.** Lean's code is in layers: `Meta` (terms, whnf, isDefEq, inferType), `Elab.Term` (the term
  elaborator), `Meta.Tactic` (operations on one goal), `Elab.Tactic` (tactics as the user writes them). A lower layer
  never calls a higher one, except through a named hook.
- **Outcome word, throwing word.** LeanForth's Meta core returns an outcome (ok, invalid, unsupported, exhausted,
  full); the tactic library's words throw on failure as Lean's do (`meta-must.fs`); the throw code keeps the outcome.
- **Discrimination tree.** An index from a term's shape (its *keys*) to stored values, used to find the instances or
  simp lemmas that may apply to a term without trying all of them.
- **Simp lemma, simp set, simproc.** An equation `simp` may use left to right; a named collection of them; a built-in
  procedure that rewrites (`2 + 3` to `5`).
- **Simp.Result and Simp.Step.** `Result` is a new term with a proof that it equals the old one (or no proof, when
  they are equal by definition). `Step` says what to do next with a result: stop, visit its parts, or continue.
- **Congruence.** Turning proofs about parts into a proof about the whole (`a = b` gives `f a = f b`); *under
  binders*, inside `fun x => …` or `∀ x, …`, which needs `funext` or `forall_congr`.
- **Motive.** In `rw`, the function `fun _a => target-with-_a` whose two applications are the old and new goal.
- **Frame.** A record on a heap stack, which LeanForth uses instead of host recursion (`lib/frame.fs`).

## Appendix F. Libraries 3-8 of PD20

**(3) Numerals and arithmetic normal forms.** Literals and `OfNat`/`OfScientific`, Int and rational arithmetic with
proofs, polynomial normal forms. First caller: S4's services (Int literals for `omega`), then `norm_num`'s `IsNat`,
`IsInt`, `IsRat` and `derive` (S8a1) and `ring`'s `ExSum` (S7); `Nat` simprocs (SP2a) call its evaluation. Absorbs
`nat-offset.fs`'s literal (`:105`), `elab-term.fs`'s `elabNumLit`, `lib/bigint.fs`'s first caller. Design: next,
before S4's services start.

**(4) Goal and proof-state library.** Combinators (`first`, `try`, `<;>`, `all_goals`), focusing, backtracking, error
messages as Lean words them. First caller: slice (b) of TACTIC_PLUGINS, then `ring` (`first | ring1 | ring_nf`).
Absorbs `tactic-run.fs`'s focus, saved states and choice points (`:322-541`), the step record. Design: with (b),
before S7; it uses §4.2 item 1's state registry.

**(5) Pinned-Lean comparison library (tests).** Run a text in pinned Lean and in LeanForth, compare terms node for
node, make wrong twins, cache Lean's runs. First caller: LA's and SP1b's tests. Absorbs `tests/author/lean_terms.py`
and the runners each written per slice (`check_defeq.py` 648 lines, `check_meta.py` 555, `check_whnf.py` 516,
`check_s2.py` 397, `check_tactics.py` 346 …). Design: now, small; Python, no gate.

**(6) Lean-printing library.** Names, terms, goals and messages as Lean prints them. First caller: simp's messages
and, later, `simp?` and `Try this` (PD11). Absorbs `present/term-printer.fs` and its `print-*.fs`, `goal-print.fs`,
the message words of `tactic-basic.fs:193-278` and the error terms of `elab-pending.fs`. Design: before SP2a.

**(7) Library-data access layer.** One reader for the snapshot, elaboration data and simp data, lazy by class or
branch. First caller: SP2a/SP4's lazy simp branches on Mathlib. Absorbs `elab-data.fs` (1,534 lines, 65 globals),
`lib-decode.fs`, `meta-env.fs`'s data side, MF2's lazy checks. Design: with MATHLIB_FRONT's load design (its question
4), after MF2's profile.

**(8) Verified-programs library.** Stack-effect and memory models for the parked V2-V4 path (`src/program/`). First
caller: V2. Design: when V2 restarts; it shares nothing with the front end's libraries.
