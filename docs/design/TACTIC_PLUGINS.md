# Tactic plug-ins on a tactic library

Design (2026-11-17), revised after its design review and the front end's architecture review of 2026-11-18 (section
11); nothing built. Two owner requests: each tactic in its own files, registering itself, so several can be built at
once (2026-11-17); and tactics as 100% Lean-compatible ports *of function* on a shared tactic library, never line-by-line
transcriptions, most of a tactic's code being library calls (2026-11-17). Lean references: pinned Lean 4.35.0's
`src/lean/`. Appendices: A measurements, B Lean notes, C codes, D the library's public words, E the Lean call lists,
F Lean's layers in LeanForth.

## For the owner (one page)

**What changes.** Today a tactic is spread over shared files (its word, spelling, reader, row, codes, Lean name,
schema, faults, `Makefile`, baselines: `by-rfl` alone is in nine), and each tactic wrote its own private copies of what
Lean keeps in a library: building a constant 5 times, an application 4 times, "close over these variables"
(`mkLambdaFVars`) 4 times, "open a binder with a new local" 7 times. Afterwards there is a **tactic library**, Lean's own
layers as public Forth words: term builders (`mkEq`, `mkEqRefl`, `mkCongrArg`, `mkAppM`), binder helpers (telescopes,
`withLocalDecl`, `mkLambdaFVars`), goal operations (`MVarId.apply`, `assumption`, `constructor`, `replaceTargetEq`) and
throwing versions of the Meta words. A tactic is then new files only, mostly calls: `by-constructor` is about 25 lines,
`by-apply` 50, `by-decide` about 200 (section 7). It registers itself when it loads, as Lean's tactics do.

**What a user sees.** Nothing until new tactics arrive: the same words, proofs, errors and step log. A dump of every
word, code, message and tactic row, and every `check` of the S1/S2 proofs, must be byte-identical before and after.

**What it buys.** Of the 18 front-end branches of 2026-11-12 to 2026-11-17, 18 edited `faults.toml`, 17 the `Makefile`,
16 the coverage baseline, 12 `src/main.fs`, 11 `author/errors.fs` (appendix A1); a new tactic then edits none of these.
And a Lean function is ported once: a fix to `mkCongrArg` or `MVarId.apply` serves every tactic.

**Risks.** (1) Replacing working copies by library calls can change terms: each site calls what Lean calls there, and
the dumps and goldens must stay identical. (2) Two error styles meet: the library throws, the Meta core returns
outcomes; the bridge (section 2.1) keeps every refusal a refusal. (3) The big tactics stay big: `simp`, `ring` and
`norm_num` are long case analyses in Lean too; the library saves about 15-20% there, not pages.

**Recommendation.** Approve: (a1) test and build plumbing; (a2) in three pieces, each about 1,500 lines of Forth with
tests: (a2-i) the library, (a2-ii) the registry with every existing tactic on it, (a2-iii) the goal layer with
`by-apply`, `by-assumption`, `by-constructor`; then S3, S4's services and (b) the combinators in parallel. Three
decisions are yours (section 10).

## 1. Lean's layers, and the rule

Lean writes its tactics on layers (appendix F): `Meta` (whnf, isDefEq, inferType, instantiateMVars: public in
LeanForth today), `Meta/AppBuilder` and `Meta/Basic` (term builders, telescopes, `mkLambdaFVars`: private copies or
absent), `Meta/Tactic` (`MVarId.*` goal operations: private or absent), `Elab/Tactic` (the elaborators that read syntax
and call the layers below, filed by syntax kind and tried newest first; one runs another through `evalTactic`). **The
rule:** a tactic file holds only Elab-level code; every Lean function it calls from `Meta/*` or `Elab/Tactic/Basic` is
a public library word. A design or brief lists those calls (its *Lean call list*, appendix E) and names for each the
word that exists (file:line), the word (a2) adds, or the word the slice itself adds to the library.

## 2. The tactic library

Word lists with stack effects are in appendix D. Library words throw on failure, as Lean's do; the Meta core keeps its
outcomes. Sizes are Forth lines without tests.

**2.1 `src/front/meta-must.fs` (about 70; (a2-i)).** `lf-must: ( xt "name" -- )` makes a throwing face of an outcome
word (`' lf-meta-whnf lf-must: lf-whnf!`); `lf-meta-catch ( i*x xt -- j*x outcome )` lets outcome code call throwing
words; `lf-commit-when ( xt -- flag )` is Lean's `commitWhen` (mark the metavariable context, CATCH, roll back on a
throw or a false flag); `lf-with-goal ( i*x goal xt -- j*x )` runs xt in the goal's context (Lean's
`MVarId.withContext`). **Fail-closed:** the throw code is `-4200 - outcome`, so CATCH gives 0 only when xt finished,
the catch hands back the same outcome (unsupported never becomes rejected, never ok), any other code passes on
untouched, and `lfr-meta-code` (`tactic-run.fs:294`) stays the one mapping to an authoring error. Every `with-` word
restores on both paths. **No throwing word may run inside a `dw-run` walk** (`dag-walk.fs:109`), whose heap memo and
stack are freed only on a normal return: builders call walks, never the reverse; the load-time header of each library
file says which of its words throw.

**2.2 `src/front/app-builder.fs` (about 350; (a2-i) with the words it has callers for).** Lean's `mkConst`, `mkApp`,
`mkAppN` and `Meta/AppBuilder.lean`: `lf-mk-const`, `lf-mk-app`, `lf-mk-app-n`, `lf-mk-eq`, `lf-mk-eq-refl`,
`lf-mk-eq-symm`, `lf-mk-congr-arg`, `lf-mk-eq-mpr`, `lf-mk-expected-prop-hint`, `lf-mk-nat-lit`; levels pass on the
stack, never through the runner's global `trun-pair`. It replaces the 5 constant builders and 4 application builders
(`tactic-run.fs:443-463`, `nat-offset.fs:75-107`, `elab-term.fs:115-126`, `lib-decode.fs:294`) and the rewrite's
hand-built `Eq`, `id` hint, `Eq.mpr` and `congrArg` terms (`tactic-rewrite.fs:192-213`). Each site calls what Lean calls
there (`Rewrite.lean` uses `mkApp6 congrArg`, `Replace.lean:21-32` uses `mkEq` and `mkExpectedPropHint`), so terms stay
node for node. `lf-mk-app-m` and `lf-mk-app-opt-m` (implicit arguments by isDefEq, instances by `lf-synth-instance`)
come with their first caller, (a2-iii); `mkDecide`, `mkDecideProof`, `mkExpectedTypeHint` with S3; `mkEqTrans`,
`mkCongr`, `mkCongrFun`, `mkOfEqTrue`, `mkEqTrue` with the simp core.

**2.3 `src/front/telescope.fs` (about 200; (a2-i) for the tactic copies).** `lf-with-local-decl`,
`lf-forall-telescope`, `lf-lambda-telescope`, `lf-forall-meta-telescope-reducing`, `lf-mk-lambda-fvars`,
`lf-mk-forall-fvars`; the last two name binders from the view and port `elimMVar`'s delayed case once. They replace
the tactic files' mkLambdaFVars copies (`tactic-run.fs:561-588`, `tactic-basic.fs:239-250`, `tactic-induction.fs:
250-257`) and telescope (`tactic-rewrite.fs:112-126`), and the local at `tactic-rewrite.fs:182`, which Lean scopes with
`withLocalDeclD` and LeanForth never drops: `lf-with-local-decl` cuts the local context back (`lf-lctx-drop`,
`core/local-context.fs:139`) on both paths. The Meta files' six binder-local copies (`defeq.fs:348`, `meta-check.fs:84`,
`fun-info.fs:144`, `infer.fs:291`, `whnf.fs:453`, `elab-decl.fs:114`) move to the library in the reuse pass (section 8).

**2.4 The goal layer, `src/front/meta-tactic/` (about 350).** Lean's `Meta/Tactic`: `goal.fs` (`lf-goal-assign-checked`,
`lf-goal-replace-target-eq`, `lf-goal-replace-target-defeq`, `lf-goal-refl`, `lf-goal-intro-n`), `rewrite.fs`
(`lf-goal-rewrite`), `elim.fs` (`ElimApp` and `evalAlts`, shared by `induction` and `cases`), all from today's tactic
files, in (a2-ii); `apply.fs` (`lf-goal-apply` with `lf-synth-app-instances`, `lf-get-mvars-no-delayed`, Lean's
parent tags and new-goal order, `throwApplyError`'s texts), `lf-goal-assumption`, `lf-goal-constructor` (an apply per
constructor under `lf-commit-when`), in (a2-iii).

**2.5 Elab glue, `src/front/tactic-core.fs` (about 40 plus the moved message words).** `lf-lift-meta-tactic ( xt -- )`
(Lean's `liftMetaTactic`: the main goal to xt, its new goals in its place), `lf-close-main-goal-using`,
`lf-with-main-context`, Lean's `throwTypeMismatchError`, the message words and the step record `tb`
(`tactic-basic.fs:110-201`). A goal-operation tactic is then one line: `' lf-goal-assumption lf-lift-meta-tactic`.

## 3. The plug-in interface

**3.1 Registration.** `tac-shape-plain lf-tactic: by-decide constant tac-k-decide` `( shape "spelling" -- kind )`,
then `lf-tactic-lean!`, `lf-tactic-plan!`, `lf-tactic-action!`, each `( … kind -- )`. Rows are allotted in the
dictionary through a table of 1024 kinds; the S1/S2 kinds keep 1-11 (`tactic-dump.fs:47` relies on them). For a new
spelling `lf-tactic:` adds the reserved word and the `LF-WORDS` word (kernel form: error 72); for every kind it sets a
reader made for kind and shape (`lf-tac-reader ( kind shape -- xt )`). A row holds a chain of run words: `lf-tactic-also!`
adds one tried first, as Lean tries newer elaborators first, under `lf-tac-try`, so the last one's error is reported
(Basic.lean:216-223). `lf-tac-eval ( i kind -- )` runs a kind's chain (`by-rw[` runs `by-rfl` so). Error 80 prints the
row's plan text; the existing rows keep "FE1g-N".

**3.2 Shapes** are records: an argument reader (none, a term, a name, a header `TAG NAMES... =>`, several terms),
suffix readers (a location `at h`, `Location.lean:58`; a configuration `+kernel`; rule modifiers `←`), a body kind
(none, `|` alternatives, values to `]`, a tactic block to `by-end`) and the flags `block?`, `bracket?`,
`holds-alternatives?`, which the structural checks read instead of kind numbers (`tactic-syntax.fs:190, 208, 290`,
`tactic-run.fs:414-416`). Today's six shapes are built from exactly the readers `lft-w-*` (`tactic-syntax.fs:221-276`).
A new body kind is core work in its own branch; `by`, `end`, `|`, `=>`, `by-end`, `]` stay the block grammar.

**3.3 Alternatives** are the API's: `lf-tactic-alt! ( xt parent-kind -- )`, and the `|` row dispatches on its
parent's kind, so `cases ... with` reuses them without editing induction's file.

**3.4 What a tactic file provides:** its registrations, each run word `( i -- )` built from library calls; its Lean
call list in its header; helpers in its own private wordlist (`lib/module.fs`), no hook writes (`is`, `defer!`),
setters only for its own kinds; step-record fields checked at load (`lf-tac-work-fits`); state in checker-context
records (ADR 0009); its codes (3.5); "not supported yet" for every case it does not port, never a silent success. It
requires only `tactic-api.fs` (which loads the library), other tactics' files and `src/lib/`. A Lean library function no
word ports yet goes into the library file of its layer, never into the tactic file.

**3.5 Error codes, one at a time.** `lfa-code: ( n outcome c-addr u "name" -- )` defines the constant with its
message; the load aborts on a number registered anywhere. The catalogue (`errors.fs:246-490`) becomes a chain; all
existing codes stay in `errors.fs`; ranges are a planning rule (appendix C). `tests/author/check_author.py` dumps the
whole catalogue and checks it against `LEANFORTH_WORDS.md` and each tactic's user page.

**3.6 Combinators (service (b)).** `first` (`BuiltinTactic.lean:631`), `try`, `<;>`, `all_goals`
(`Init/Tactics.lean:445, 451, 358`) need a handler frame in the runner: it saves at open and, on an authoring THROW
inside the block, restores and goes to the next alternative. Mathlib's `ring` is `first | ring1 | ring_nf`, so (b)
precedes S7.

**3.7 Trust.** Everything here is untrusted; only the kernel decides. The guards stay outside tactics and library: the
record checked before any step runs (`tactic-run.fs:407-432`), unsolved goals at a block's end, holes refused at the
hand-over (code 74), the kernel's check, and its axiom report, which names `sorryAx` for any goal closed by `sorry`,
recorded as an open part or not. Default rows fail closed (80); the throwing bridge keeps outcomes (2.1).

## 4. Test and build files (all in (a1))

- **Faults:** `scripts/mutants.py` reads `faults.toml` and every `tests/mutants/faults.d/*.toml` as one list; new and
  moved tactic and library faults go to `faults.d/`; the rest of `faults.toml` splits per folder later, at a quiet point.
- **Makefile:** targets found from files: the silent-load check over `$(wildcard src/front/*.fs src/front/tactics/*.fs
  src/front/meta-tactic/*.fs)` (instead of `Makefile:1018-1034`), each `tests/front/tactics/*/test.fs` and `check.py`
  by a pattern rule; one pattern row in `tests/test-classes.txt`.
- **Loading:** `src/main.fs` and `cli/check-lf.fs` load the generated `src/front/tactics/all.fs`, one sorted `require`
  per tactic, `merge=union` in `.gitattributes`, refused unless sorted, unique and complete.
- **Baselines:** coverage, quality and duplicates as JSON Lines, one sorted entry per line, `merge=union`; loaders refuse
  duplicate keys or unsorted lines; coverage's `runs` floor written only on request; `scripts/baseline-lines.py`
  converts, and is re-run on either side of a conflict with a branch in flight.

## 5. Slices

**(a1) Test and build plumbing** (section 4, `scripts/check-tactic-plugins.py`; full tier as it changes scripts).
Acceptance: the same faults listed, baselines read back to the same maps, `make test` running the same targets.

**(a2-i) The library** (2.1-2.3; about 620 lines of library, 500-700 of unit tests): the words with their callers in
today's code: the rewrite, rfl, sorry and the runner's closing (`tactic-run.fs:553-591`) on the builders and
telescopes; `nat-offset.fs`'s literal, `elab-term.fs`'s and `lib-decode.fs`'s builders replaced; behaviour
byte-identical. Unit tests compare each builder's terms with pinned Lean's (`check_meta.py`'s method).

**(a2-ii) The registry and the moves** (3.1-3.5, 2.4's moved cores, 2.5; about 600 changed lines, 400 of tests): every
existing tactic in `tactics/` on the library (`rfl.fs`, `exact.fs`, `intro.fs`, `sorry.fs`, `induction.fs`,
`rewrite.fs`, `case.fs`); the step log and `tactic-dump.fs` read the rows; the tactic files' 15 duplicate groups fixed;
the schema widened (decision 1); the check enforced; the guide `ADDING_A_TACTIC.md` (planned), with the Lean call list
as a rule and `tactics/rfl.fs` as template. Acceptance: `tests/front/tactic-registry.fs` dumps the catalogue, the
`LF-WORDS` and reserved lists and the rows; it and `bin/leanforth check --env tests/front/s2-slice.ndjson --elab-data
tests/front/s2-slice.elab.ndjson --steps -` on every S1/S2 `.lf` file are byte-identical; moves reviewed with
`git diff -M --color-moved`; faults and baseline lines re-keyed with per-file sums unchanged.

**(a2-iii) The goal layer with its first callers** (2.4's new words, `lf-mk-app-m`, `lf-mk-app-opt-m`; about 450 of
library, 100 of tactics, 600-800 of tests and pinned-Lean cases): `by-apply`, `by-assumption`, `by-constructor` (each a
new word: its own [parser] question). Command: `bin/leanforth check` on their acceptance files, accepted, with Lean's
errors for the wrong ones.

**(b) Combinators** (3.6), beside the tactics, before S7. **Shared edits that remain:** a language-reference row and a
`docs/README.md` line per tactic; plan rows (by whoever merges); a new body kind, option or library word, in its own
branch or in the library file of its layer.

## 6. Reuse

Used: `lib/xt-table.fs`, `lib/module.fs`, `lib/context.fs`, the runner's rows and `lf-tac-try`, `lfa-syntax` and
`lfa-natural!` (`author/groups.fs:180-186`), the catalogue's record words, `lf-meta-const-at` (`meta-env.fs:264`, the
core under `lf-mk-const`), `lf-meta-abstract` and `lf-meta-instantiate1` (`instantiate.fs:226, 217`), `lf-lctx-drop`,
`lf-mctx-mark`/`-rollback`/`-commit` (`mvars.fs:500-503`, under `lf-commit-when`), `lf-synth-instance`. Replaced: the
copies listed in 2.2-2.4. New: the library files of section 2 and the registry words of section 3, each with callers in
its slice. No new `src/lib/` library: these are LeanForth's Lean layers, not general tools.

## 7. What can then run in parallel, and sizes

After (a2-iii): **S3 (`by-decide`), S4's services branch** (helper theorems in the hand-over, `handover.fs`, codes 78-79;
the canonicalizer; `falseOrByContra`; Int literals; the opt-in flag) **and (b)**; `by-omega` after its services;
`simp`'s data design now (its [import] gate is the long pole). Sizes on the library (Forth lines without tests;
appendix E lists the calls):

| Tactic | Review's estimate | This design's | Where we differ |
| --- | --- | --- | --- |
| `by-decide` | 200 + 130 library | 150-200 + 130 library | agree; the library part (`mkDecide`, `mkDecideProof`, `mkExpectedTypeHint`, `zetaReduce`, an unfold trace for the diagnosis) assumes the reuse pass's offset walk exists; without it `zetaReduce` costs about 60 more. `+kernel` waits for S4's helper theorems |
| `by-apply` | 50 + 220 | 50 + 220 | agree; the 220 sit in (a2-iii) |
| `by-constructor` | 25 + 30 | 25 + 30 | agree; in (a2-iii) |
| simp-only core | 1,700-1,900 + 400 | same | agree; its own design |

Tests are extra and usually as large as the code. Decision procedures stay about 1.0-1.1 Forth lines per Lean line.

## 8. Fit with the front end's reuse pass

The pass (plan 9.4.8k's front items) works where the duplicates are (instantiate 31 groups, beta-inst 27, mvars 23,
constructions 21, elab-data 20; appendix A3), and should be organised around one offset rebuild walk (Lean's
`Expr.replace` and `Meta.transform`), which `zetaReduce` and `dsimp` also need. It takes the Meta files' binder-local
copies onto `telescope.fs` once (a2-i) has merged. (a2-i) touches `nat-offset.fs`, `elab-term.fs` and `lib-decode.fs`
for three builder sites: coordinate those with the pass (one of them merges first, the other rebases). New Meta services
go in new files, not in `mvars.fs`, `whnf.fs` or `meta-env.fs` (8-9 branches each).

## 9. Gates

No kernel, import or certificate change. **[parser]:** no existing `.lf` text changes meaning (identical dumps,
reading goldens, `check_tactics.py`'s pinned-Lean messages); `by-apply`, `by-assumption`, `by-constructor` in (a2-iii),
and each later tactic word, are their slices' own [parser] questions. **[format]:** decision 1, in (a2-ii).

## 10. Decisions for the owner

1. **Widen the step log's schema once, in (a2-ii)** (`tactic-steps-1.schema.json:124-150`): names matching
   `^[a-z][a-z0-9_]*[?!']*$`, any non-blank word, the current names listed by `leanforth capabilities`; every log so far
   stays valid. Recommendation: yes.
2. **A lighter test tier for tactic-only branches, once the check enforces confinement:** the front end's targets, all
   `.lf` end-to-end runs and the S1/S2 goldens, not the kernel and import suites; the daily full run is the safety net.
   Recommendation: yes.
3. **Order:** (a1), (a2-i), (a2-ii), (a2-iii); then S3, S4's services and (b) together; `simp`'s data design now.
   Recommendation: yes.

## 11. Reviews

**Design review, 2026-11-17** ("ready after fixes", 15 findings, all accepted, checked against `tactic-rewrite.fs:239`,
`tactic-induction.fs:373` and Lean's source): (1) single codes, 3.5; (2) the Meta/Elab split, `lf-tac-eval`, 2.4, 3.1;
(3) the check and the moves before parallel work, 5; (4) chains, 3.1; (5) combinators, 3.6; (6) shape records, 3.2;
(7) `lf-tactic-alt!`, 3.3; (8) 1024 kinds, 3.1; (9) private wordlists, 3.4; (10) `tactic-dump.fs`, `all.fs`, S4's flag,
4, 5, 7; (11) the dumps, 5; (12) no `skip` example, 5; (13) `lfa-code:`, 3.5; (14) plan text, 3.1; (15) `sorryAx`, 3.7.
**Architecture review, 2026-11-18**: its finding holds: the first revision's "API layer" mostly relocated code, and
S3 and `apply` do need services that do not exist (`mkAppOptM`, `forallMetaTelescopeReducing`, `synthAppInstances`,
`getMVarsNoDelayed`, `zetaReduce`; checked in `Meta/AppBuilder.lean:402`, `Meta/Basic.lean:1791`,
`Meta/Tactic/Apply.lean:40`, `Meta/CollectMVars.lean:42`, `Meta/Transform.lean:198`). Its recommendations 1-6, 8 and 10
are sections 2, 5, 7 and appendices D-F; 7 and 9 are section 8. Beyond the reviews: the test and build files (4).

## Appendix A. Measurements

### A1. Shared files by number of front-end branches

Branches: fe1, fe1d, fe1e1, fe1c-lnorm, fe6a, fe1c-2, fe1f, fe1g1, fe1g2, fe1c-3, s1-meta, s1-meta-b, s1-synth,
s1-synth-b, s2-unfold, s1-elab, s2-tactics (merged 2026-11-12 to 2026-11-14) and s2-finish (`bb13df16..s2-finish-2`).
Per merge on `main`: `git diff --name-only $(git merge-base P1 P2) P2`; a branch merged several times counts once. The
design reviewer's recount over 19 merges agrees; most of these branches are Meta or elaboration-data work.

| Branches | Source file | Branches | Test, build or doc file |
| --- | --- | --- | --- |
| 12 | src/main.fs | 18 | tests/mutants/faults.toml |
| 11 | src/author/errors.fs | 17 | Makefile |
| 9 | src/front/mvars.fs, src/README.md | 16 | tests/coverage-baseline.json |
| 8 | src/front/whnf.fs, src/front/meta-env.fs | 15 | docs/project/PLAN_DRAFT.md |
| 7 | src/front/infer.fs | 10 | tests/forth-quality-baseline.json |
| 6 | front/term-eqv, nat-offset, meta-spine, elab-data, defeq; cli/check-lf.fs | 9 | docs/programming/LEANFORTH_WORDS.md |
| 5 | front/tactic-basic, meta-config, fun-info; cli/leanforth.fs | 7 | tests/front/whnf.fs, docs/user/COMMAND_LINE.md, PROJECT_PROGRESS.md |
| 4 | front/tactic-run, instantiate, instances, handover, discr-keys | 6 | tests/front/front.fs, defeq.fs, check_defeq.py, duplicates-baseline.json |

### A2. Where each existing tactic lives (on `s2-finish-2`)

Common to all: `print-forth.fs:91-92`, `tactic-run.fs:256-262` and `:314-318`, `schemas/tactic-steps-1.schema.json:
124-150`, `LEANFORTH_WORDS.md:156-158` and `:436-499`, `LANGUAGE_REFERENCE.md:951-961`; tests `tactic-syntax.fs`,
`tactic-dump.fs:23-28, 47`, `tactics.golden`, `Makefile:1018-1065`; faults naming tactic-syntax 18, tactic-run 21,
tactic-basic 13, tactic-induction 6, tactic-rewrite 6, step-log 2. Calls between tactics: `tactic-rewrite.fs:239` runs
rfl (`tactic-basic.fs:359`); `tactic-induction.fs:373` runs intro (`:267`); `tactic-induction.fs:271` uses
`tactic-basic`'s private `lfb-popped` and `tb`.

| Tactic | words.fs | tactic-syntax.fs: kind, reader, meaning | run | codes (errors.fs lines) | step-log.fs |
| --- | --- | --- | --- | --- | --- |
| `by-rfl` | 194 | 85, 226, 340 | tactic-basic.fs 322-359, 363 | 97 (153, 403) | 96 |
| `by-exact` | 196 | 86, 228, 342 | tactic-basic.fs 269-320, 362; elab-decl.fs:152 | 95, 96, 98 (151-154, 399-405) | 96 |
| `by-intro:` | 197 | 87, 241-255, 343 | tactic-basic.fs 203-267, 361 | 94 (150, 397) | 97 |
| `by-sorry` | 195 | 94, 227, 341 | tactic-run.fs 434-470; report 611-630 | none of its own | 94 |
| `by-induction`, `-with` | 192, 198 | 88-89, 229-230, 208, 291, 344-345 | tactic-induction.fs 406-409; tactic-run.fs 414-416 | 205-213 (209-215, 473-480) | 94 |
| `\|` | 203 | 90, 286-288, 347 | tactic-induction.fs 407 | reader's 83, 85 | 93 |
| `by-case:` | 193 | 91, 289-291, 346 | none yet (error 80) | 210, 211 kept | 93 |
| `by-rw[`, `by-rewrite[` | 200-201 | 92-93, 190, 231-239, 350-352 | tactic-rewrite.fs 243-244 | 215-220 (216-221, 481-489) | 97-98 |

### A3. Duplicate groups (`tests/duplicates-baseline.json` on this branch)

167 groups have a member in `src/front/`; 15 involve the tactic files. Per file: instantiate 31, beta-inst 27, mvars 23,
constructions 21, elab-data 20, level-params 13, whnf 11, assign-check 9, elab-pending 8, lib-decode 8, ctor-idx 7,
defeq 7, and 6 each for elab-app, goal-print, infer, elab-term, tactic-run. The architecture review found the builder
and binder copies of 2.2-2.3, which the duplicate checker misses because their shapes differ.

## Appendix B. Lean source notes (pinned 4.35.0, `src/lean/Lean/`)

- `Elab/Tactic/Basic.lean:147` `tacticElabAttribute`; `:191-246` `evalTactic` (newest first, saved state, last error
  reported `:216-223`); `:526` `withMainContext`; `:581` `liftMetaTactic`; `Elab/Tactic/ElabTerm.lean:85`
  `closeMainGoalUsing`, `:100` `exact`, `:302` `apply`, `:326` `constructor`.
- `Meta/AppBuilder.lean`: `mkExpectedPropHint` 29, `mkExpectedTypeHint` 35, `mkEq` 40, `mkEqRefl` 65, `mkEqSymm` 98,
  `mkEqTrans` 110, `mkCongrArg` 212, `mkCongrFun` 232, `mkCongr` 255, `mkAppM` 345, `mkAppOptM` 402, `mkEqMPR` 447,
  `mkDecide` 570, `mkDecideProof` 574, `mkOfEqTrue` 636, `mkEqTrue` 648.
- `Meta/Basic.lean`: `mkFreshExprMVar` 907, `mkForallFVars` 1174, `mkLambdaFVars` 1180, `forallTelescope` 1595,
  `lambdaTelescope` 1694, `forallMetaTelescopeReducing` 1791, `withLocalDecl` 1835; `Util/MonadBacktrack.lean:50`
  `commitWhen`, `:77` `observing?`; `Meta/CollectMVars.lean:42` `getMVarsNoDelayed`; `Meta/Transform.lean:198`
  `zetaReduce`; `LocalContext.lean:672` `getLocalHyps`; `MonadEnv.lean:64` `matchConstInduct`.
- `Meta/Tactic/`: `Refl.lean:25`, `Intro.lean:147`, `Rewrite.lean:28` (calls `forallMetaTelescopeReducing`, `kabstract`,
  `check`, `withLocalDeclD`, `getLevel`, `mkApp6 congrArg`, `postprocessAppMVars`, `getMVarsNoDelayed`, `mkEqSymm`,
  `mkEq`), `Replace.lean:21` (`mkEq`, `mkExpectedPropHint`, `Eq.mpr`), `Apply.lean:40` `synthAppInstances`, `:108`
  `appendParentTag`, `:169` `MVarId.apply`, `Assumption.lean:26`, `Constructor.lean:23`, `AuxLemma.lean:43`;
  `Elab/Tactic/FalseOrByContra.lean:38`; `Elab/Tactic/Decide.lean:24-157`.
- Combinators: `first` `Elab/Tactic/BuiltinTactic.lean:631`, `skip` `:289`; `Init/Tactics.lean` `try` 445, `<;>` 451,
  `all_goals` 358, `rfl`'s three `macro_rules` 477-482. Mathlib `NormNum/Core.lean:73-78` and `Ring/Common.lean:8-9`.

## Appendix C. Code planning (a rule for designs, not a load check)

Existing (`errors.fs:30-54`, staying there): 1-73 words and reading; 74-79 elaboration and hand-over (78-79 S4's helper
theorems); 80-99 the runner, reader and first tactics; 100-139 Meta, instances, elaboration; 140-199 FE2; 200-224
unfolding, induction, case, rewriting; 225-229 the step log; 230-249 FE5; 250-269 decide; 270-299 omega. Planned:
300-339 simp, 340-359 norm_num, 360-379 ring, 380-389 apply, assumption, constructor, 390-399 combinators, 400-419
cases, 420-429 have, 430-439 calc; 440 on free.

## Appendix D. The tactic library's public words

All throw on failure unless marked `outcome`; "a2-i", "a2-ii", "a2-iii" or a slice name says when each arrives.

| File | Word ( stack ) | Meaning (Lean) | When |
| --- | --- | --- | --- |
| meta-must.fs | `lf-must: ( xt "name" -- )` | a throwing face of an outcome word | a2-i |
| | `lf-meta-catch ( i*x xt -- j*x outcome )` | run throwing code from outcome code | a2-i |
| | `lf-commit-when ( xt -- flag )` | `commitWhen`: keep the changes only on true | a2-i |
| | `lf-with-goal ( i*x goal xt -- j*x )` | `MVarId.withContext` | a2-i |
| | `lf-whnf! lf-whnf-r! lf-infer! lf-defeq! lf-instantiate! lf-level!` | throwing faces of `whnf.fs:835, 846`, `infer.fs:348, 360`, `defeq.fs:961`, `mvars.fs:828` | a2-i |
| app-builder.fs | `lf-mk-const ( c-addr u lvl1..lvln n -- e )`, `lf-mk-const0`, `lf-mk-const1` | `mkConst` | a2-i |
| | `lf-mk-app ( f a -- e )`, `lf-mk-app-n ( f a1..an n -- e )` | `mkApp`, `mkAppN` | a2-i |
| | `lf-mk-eq ( a b -- e )`, `lf-mk-eq-refl ( a -- h )`, `lf-mk-eq-symm ( h -- h' )` | `mkEq`, `mkEqRefl`, `mkEqSymm` | a2-i |
| | `lf-mk-congr-arg ( f h -- h' )`, `lf-mk-eq-mpr ( h p -- e )` | `mkCongrArg`, `mkEqMPR` | a2-i |
| | `lf-mk-expected-prop-hint ( h p -- h' )`, `lf-mk-nat-lit ( u -- e )` | `mkExpectedPropHint`, `mkNatLit` | a2-i |
| | `lf-mk-app-m ( c-addr u a1..an n -- e )`, `lf-mk-app-opt-m ( c-addr u x1..xn mask n -- e )` | `mkAppM`, `mkAppOptM` | a2-iii |
| | `lf-mk-decide ( p -- e )`, `lf-mk-decide-proof ( p -- h )`, `lf-mk-expected-type-hint ( e t -- e' )` | `mkDecide`, `mkDecideProof`, `mkExpectedTypeHint` | S3 |
| | `lf-mk-eq-trans`, `lf-mk-congr`, `lf-mk-congr-fun`, `lf-mk-of-eq-true`, `lf-mk-eq-true` ( h h -- h ) / ( h a -- h ) / ( h -- h ) | `mkEqTrans`, `mkCongr`, `mkCongrFun`, `mkOfEqTrue`, `mkEqTrue` | S4 services (trans), simp core |
| telescope.fs | `lf-with-local-decl ( i*x type name bi xt -- j*x )` | `withLocalDecl`; xt gets the fvar; the local dropped on both paths | a2-i |
| | `lf-forall-telescope ( i*x type xt -- j*x )`, `lf-lambda-telescope` | `forallTelescope`, `lambdaTelescope`; xt gets fvars n and the body | a2-i |
| | `lf-forall-meta-telescope-reducing ( type max -- mvars bis n body )` | `forallMetaTelescopeReducing` | a2-i |
| | `lf-mk-lambda-fvars ( e fvars n -- e' )`, `lf-mk-forall-fvars` | `mkLambdaFVars`, `mkForallFVars` (elimMVar's delayed case) | a2-i |
| meta-tactic/goal.fs | `lf-goal-assign-checked ( goal e -- )` | `checkedAssign` | a2-ii |
| | `lf-goal-replace-target-eq ( goal new h -- goal' )`, `-defeq ( goal new -- goal' )` | `replaceTargetEq`, `replaceTargetDefEq` | a2-ii |
| | `lf-goal-refl ( goal -- )`, `lf-goal-intro-n ( goal names n -- fvars n goal' )` | `MVarId.refl`, `introN` | a2-ii |
| meta-tactic/rewrite.fs, elim.fs | `lf-goal-rewrite ( goal e h -- new h' goals )`, `lf-elim-app`, `lf-eval-alts` | `MVarId.rewrite`, `ElimApp`, `evalAlts` | a2-ii |
| meta-tactic/apply.fs | `lf-goal-apply ( goal e -- goals )`, `lf-synth-app-instances ( mvars bis n -- )`, `lf-get-mvars-no-delayed ( e -- mvars n )` | `MVarId.apply`, `synthAppInstances`, `getMVarsNoDelayed` | a2-iii |
| | `lf-goal-assumption ( goal -- )`, `lf-goal-constructor ( goal -- goals )` | `MVarId.assumption`, `constructor` | a2-iii |
| tactic-core.fs | `lf-lift-meta-tactic ( xt -- )`, `lf-close-main-goal-using ( xt -- )`, `lf-with-main-context ( i*x xt -- j*x )` | `liftMetaTactic`, `closeMainGoalUsing`, `withMainContext` | a2-ii |
| | `lf-throw-type-mismatch ( e type expected -- )`, `tb`, `lf-tac-step-run`, the message words | `throwTypeMismatchError` | a2-ii (moved) |

Unchanged and listed by `tactic-api.fs`: the runner's goals, blocks, choice points and records (`tactic-run.fs:322-541`),
`lf-goal-new`, `lf-replace-main`, `lf-goal-clear`, `lf-goal-rename` (`goals.fs:59-140`), `lf-mvar-new` (`mvars.fs:280`),
`lf-meta-const-fresh` (`:319`), `lf-meta-instantiate-forall` (`whnf.fs:862`), `lf-meta-fun-info`, `lf-meta-is-prop`
(`fun-info.fs:210, 106`), `lf-synth-instance` (`synth.fs:682`), `lf-meta-kabstract` (`kabstract.fs:159`),
`lf-meta-check` (`meta-check.fs:142`), `lf-meta-at`, `lf-meta-with` (`meta-config.fs:87-92`), `lf-elab-ensuring`
(`elab-term.fs:530`), the `lf-tac-elab` hook (`elab-decl.fs:152`). The reader pieces `lft-tactic`, `lft-term-step`,
`lft-given`, `lft-header`, `lft-opened`, `lft-done` (`tactic-syntax.fs:219-276`) are exported for shapes.

## Appendix E. Lean call lists

Each row: the Lean function a port calls (one level below the tactic) and its public word: "exists" (file:line),
"a2-x" (added by that piece of (a2)) or the slice that adds it to the library. The guide makes this list a rule.

| Port | Lean calls → LeanForth word |
| --- | --- |
| S3 `decide` (`Decide.lean:24-157`) | `instantiateMVars` → exists `mvars.fs:828`; `zetaReduce` → S3, on the offset walk; `hasFVar` → exists `meta-spine.fs:88`; `hasMVar` → exists as `lf-term-holds?` with a test (`term-find.fs:42`); `closeMainGoalUsing` → a2-ii; `mkDecide`, `mkDecideProof`, `mkExpectedTypeHint`/`mkExpectedPropHint` → S3 / a2-i; `synthInstance` (inside `mkDecide`) → exists `synth.fs:682`; `withAtLeastTransparency .default whnf` → exists `lf-meta-at` + `whnf.fs:835`; `mkConst`/`mkApp3` → a2-i; `mkAuxLemma` (`+kernel`) → S4 services; the diagnosis (`blameDecideReductionFailure`, unfolded-instance trace) → S3, a whnf trace hook in a new file |
| S4 services (`FalseOrByContra.lean:38`, `Assumption.lean`, `AuxLemma.lean:43`) | `whnfR` → exists `whnf.fs:846`; `intro1`/`intro1P` → a2-ii `lf-goal-intro-n`; `applyConst` → a2-iii `lf-goal-apply`; `exfalso` → S4 (`Apply.lean:286`); `Decidable.byContradiction`/`Classical.byContradiction` by `mkConst` → a2-i; `synthInstance` → exists; `getLocalHyps` → S4 (`LocalContext.lean:672`), on `lctx-views.fs`; `mkAppM`, `mkDecideProof`, `mkEqTrans`, `mkEqSymm` → a2-iii / S3 / S4 / a2-i; Int literals → S4, beside `lf-mk-nat-lit`; `mkAuxLemma` → S4 (hand-over helper theorems) |
| `apply` (`Apply.lean:169-232`) | `withContext` → a2-i `lf-with-goal`; `checkNotAssigned` → a2-iii; `inferType` → exists; `getExpectedNumArgs`, `forallMetaTelescopeReducing` → a2-i; `isDefEq` → exists `defeq.fs:961`; `postprocessAppMVars`, `synthAppInstances` → a2-iii; `instantiateMVars` → exists; `appendParentTag`, `getMVarsNoDelayed`, `reorderGoals` → a2-iii; `throwApplyError` → a2-iii |
| `constructor` (`Constructor.lean:23-40`) | `whnfR` → exists; `matchConstInduct` → a2-iii (from `tactic-induction.fs:155`); `observing?` → a2-i `lf-commit-when`; `MVarId.apply` → a2-iii; `mkConst` with the type's levels → a2-i |
| simp-only core (`Meta/Tactic/Simp/Main.lean`, `Types.lean`, `Rewrite.lean`) | `instantiateMVars`, `isDefEq`, `whnfCore` → exist; `mkCongr`, `mkCongrArg`, `mkCongrFun`, `mkEqTrans`, `mkEqMPR`, `mkOfEqTrue`, `mkImpCongr`, `mkExpectedTypeHint` → a2-i / simp core; `mkLambdaFVars`, `mkForallFVars`, `withLocalDecl`, `forallTelescope`, `forallMetaTelescopeReducing` → a2-i; `getMatchWithExtra` (`DiscrTree/Main.lean:489`) → simp core, on `discr-keys.fs`; `mkCongrSimp?` (`CongrTheorems.lean:387`) → simp core; `reduceMatcher` → exists (`whnf.fs`); `synthesizeArgs` (instances, `isDefEq`) → a2-iii `lf-synth-app-instances` |

## Appendix F. Lean's layers in LeanForth (the architecture review's table (a), counts of Lean functions)

| Lean layer | Public today | Private in a feature file | Absent |
| --- | --- | --- | --- |
| Lean.Meta (incl. AppBuilder, Basic) | 21 (whnf, isDefEq, inferType, instantiateMVars, mkFreshExprMVar, mkConst, kabstract, check, synthInstance, ...) | 10 (mkEq, mkExpectedPropHint, the congrArg term, mkLambdaFVars/mkForallFVars, forallMetaTelescopeReducing, matchEq?, matchConstInduct, ...) | 16 (mkAppM, mkAppOptM, mkEqRefl, mkEqSymm, mkEqTrans, mkCongr, mkCongrFun, mkEqMPR, mkDecide, mkOfEqTrue, telescopes, withLocalDecl, zetaReduce, getLocalHyps, commitWhen, ...) |
| Meta.Tactic (MVarId) | 3 (clear, rename, unchecked assign) | 7 (intro, refl, rewrite, replaceTargetEq, ElimApp/evalAlts, checkedAssign, withContext) | 9 (apply, assumption, constructor, cases, revert, subst, exfalso, getMVarsNoDelayed, synthAppInstances) |
| Elab.Term | 7 | 3 | binders, let/have/show (FE2), classes (FE3) |
| Elab.Tactic | 7 | 2 (closeMainGoalUsing, throwTypeMismatchError) | 6 (liftMetaTactic, first, try, `<;>`, all_goals, withLocation) |

After (a2): the 10 private Meta functions and the 7 private MVarId functions are public library words; of the absent,
(a2) adds mkEqRefl, mkEqSymm, mkEqMPR, the telescopes, withLocalDecl, commitWhen, mkAppM, mkAppOptM, apply, assumption,
constructor, getMVarsNoDelayed, synthAppInstances, liftMetaTactic; the rest arrive with S3, S4, (b), simp and FE5.
