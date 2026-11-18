# Whole-code Forth review, second pass: src/front Meta and elaborator files (s2-finish-2)
**Range:** whole files at `s2-finish-2` = `3e5f95b4` (merge-base with main `3b8f8bf9`; the first pass read `cb12814d`); not a diff review.
**Findings: 17.** BLOCKS: 4 (N1-N4). Reuse pass: 8 (F8-F12, F1+, B6, D2). Note: 5 (N5-N9).
**What was run:** read-only, on a `git archive` scratch copy. Three Gforth 1.0.0 probes and one planted fault, all in that copy. Tools: `forth-metrics.py`, `check-duplicates.py`, `check-lib-callers.py`. No suite was run. This AI review does not replace the owner's human review.

## For the owner (plain language)
- Nothing here lets a wrong proof through: every path still ends at the hand-over check and the kernel.
- **N1.** Instance search turns on an "approximate unification" setting and never turns it off. Later unification then answers "unsupported" where Lean answers "no" and carries on. A probe shows the setting left on. The fix is a few lines.
- **N2.** Three places look for an old form of `Sort` that the front end no longer makes. As a result, "is this a type?" and "is this Prop?" are always answered no. The second makes LeanForth do something Lean deliberately avoids. A probe shows both. Fix: one shared word for each test.
- **N3** settles the first pass's open doubt. A library declaration that cannot be decoded is read as "no such constant", and so is treated as "not a class" or "does not reduce" instead of "unsupported". Fix: one line.
- **N4.** A failed pass over pending instance problems loses them. This matters once `try`/`first` (FE5) catch errors; it belongs with the first pass's C2.
- prop-quick's bound-variable rule, the first pass's other doubt, matches pinned Lean exactly. No cache is keyed on too little.
- **Coverage:** 26 files read whole (about 10,900 lines). 14 small files remain (list at the end).

## 1. Correctness and fail-closed behaviour
**N1 (BLOCKS: a difference from Lean; fails closed).**
- **Where:** assign-check.fs:65-69 keeps ctxApprox in the register `ac-approx`. defeq.fs:950 `de-config` sets it at every isDefEq, and nothing restores it.
- **How it leaks:** synth.fs:679-684 runs with ctxApprox on. defeq.fs:413 `de-nested` (synthPending inside isDefEq) restores `df`, de-frames and de-cells, but not this register.
- **Consequence:** the rest of the outer isDefEq checks assignments with ctxApprox on. `ac-other` (:100) and `ac-mvar-spine?` (:141) then answer unsupported where Lean's checkAssignment fails and its caller goes on (first-order approximation and the later cases).
- **Probe:** set `false lf-meta-ctx-approx!`, then synthesize `Add Nat` (setup of tests/front/synth.fs). It prints `before synth: 0`, `after synth: -1`, while the configured `lf-defeq-flags lf-defeq-ctx and` is `0`.
- **Fault:** removing `lf-defeq-ctx or` from synth.fs:680 `sy-flags` survives tests/front/synth.fs (exit 0).
- **Fix:** delete the register and `lf-meta-ctx-approx!`, and read the scoped configuration where it is used: `: ac-approx? ( -- flag ) lf-defeq-ctx lf-meta-flag? ;`. Add a test (synthPending inside isDefEq, then an out-of-scope assignment answers false) and a fault.

**N2 (BLOCKS: a difference from Lean).** Three words compare with `lf-tag-sort` (1): elab-term.fs:516 `et-is-type?`, elab-app.fs:372 `ea-prop?`, and tactic-induction.fs:129 `lfi-sort?` (same cause). Every front-end Sort is `lf-tag-symbolic-sort` (6): lib-decode.fs:278 makes them so, and so does infer.fs:128 via `lf-hterm-sort`.
- **Probe:** `nat lf-infer` gives tag 6; `et-is-type?` of Nat gives `0 0`; `ea-prop?` of Prop gives `0`.
- **Effects:**
  - ensureType (:524) always runs isDefEq(type, Sort ?u): an extra level metavariable and budget, but the same answer.
  - propagateExpectedType (:377) propagates an expected Prop, which Lean refuses on purpose (App.lean:594). Elaboration can then fail or differ where Lean succeeds.
  - Prop's hint in `lfi-sort?` never shows.
- **Fix (F9):** two words in core/tagged-sort-boundary.fs, used at all eight sites:
  - `lf-sort? ( t -- flag )` for either tag;
  - `: lf-prop? ( t -- flag ) dup lf-tag-symbolic-sort lf-term-tag? if lf-term-first@ lf-level-tag@ lf-level-tag-zero = else drop false then ;`.
- **Tests:** no fault covers the three words, and no test pins them (a fault that fixes them would survive).

**N3 (BLOCKS: fails closed with a different outcome; settles instances.fs:199-200).** meta-env.fs:201 `me-decoded` passes lf-libdec-decl's outcome on as it is.
- **Cause:** lib-decode answers invalid not only for a missing declaration but also for malformed tier data:
  - a rules tuple that is not a multiple of `/rule-items` (:567);
  - an unknown level tag (:264);
  - a kind with no entry (:505-509);
  - a sunfold parameter out of range (:406).
- **Callers that read invalid as "unknown constant" (11):** instances.fs:199 `it-unknown`; whnf.fs:241, 510, 656, 709; defeq.fs:251; infer.fs:161; fun-info.fs:84; unfold.fs:162; elab-term.fs:120, 349.
- **Effect:** a corrupt declaration becomes "not a class", "stuck" or error 103 instead of unsupported. Instance search may then pass a candidate over and pick another, which gives a different term (the kernel still checks it). meta-spine.fs:13-17 documents the opposite.
- **Fix:** `: me-decoded ( d -- d outcome ) dup lf-libdec-decl nip dup outcome-invalid = if drop outcome-unsupported then dup ok? 0= if nip no-result then ;`. Add a test with a stage whose rules are cut short, and a fault.

**N4 (BLOCKS FE5, with C2).** elab-pending.fs:285-310: `ep-take` cuts the window before resuming, and on any failure `ep-abandon` cuts ep-scratch too.
- **Effect:** the window's instance problems are lost; problems already filled keep their assignments. Today every failure ends the declaration. Under `lf-tac-try` the restored goals would go on without their pending problems.
- **Fix:** restore the window from ep-scratch before cutting it in `ep-abandon`, and add the pending list to C2's `tac-state:` chain. Add a test and a fault.

**Notes.**
- **N5.** Local free variables made with `lf-lctx-local` are never dropped: whnf.fs:452 `wc-new-h`, infer.fs:289-296, meta-check.fs:83. Memory only; views are unaffected. fun-info.fs:210 and defeq.fs:955 drop theirs (architecture review recommendation 2, `with-local-decl`).
- **N6.** whnf.fs:737 `wc-sstuck` calls `lf-whnf-stuck` inside a running whnf, which overwrites wc-args, wc-margs, wc-data and wc-fault. It is safe at that resume point, but undocumented. Give ws-* its own slabs.
- **N7.** elab-data.fs:1469 `elab-bind!` truncates with `min`, so 64 correct digits followed by extra text are accepted on their prefix. Refuse `u <> 64`.
- **N8.** prop-quick.fs never looks through an annotation (Lean's `.mdata _ e`), so it answers undef; this fails closed. Otherwise it matches InferType.lean:368-388: letE keeps n, `.bvar` only at n = 0, checkProp through outParam, isNeverZero before isZero.
- **N9.** Hooks set without chaining: elab-pending.fs:201 and :206-208, synth.fs:713-714 (first-pass B3, `fresh-hook:`).

**Caches (against Meta/Basic.lean).** whnf, isDefEq, inferType and getFunInfo keep none (defeq.fs:71). meta-check's memo lasts one call, keyed by node, as Lean's checkCache. Synthesis keys on (type with out-parameter wildcards, synthPendingDepth), used only without local instances: Lean's (localInsts, type, depth); results holding metavariables are refused (121) before caching; cleared by epoch. lib-decode is keyed by store generations, instances.fs by elab-generation.

**Performance (one line each, not measured).**
- dag-walk.fs:109-112 allocates and erases a memo the size of the whole term store per walk, so per occurs check in every `lf-mvar-assign` (mvars.fs:357) and per instantiateMVars.
- mvars.fs:683 scans every metavariable per instantiateMVars.
- fun-info.fs:134 re-reads tier kinds per parameter, which is quadratic.
- nat-offset.fs:75 looks up its names again for every literal.

## 2. Factoring (extends F1-F7)
- **F8.** The "unknown constant" test is written 11 times (N3's sites). One word replaces it: `lf-meta-const-known ( const -- d true outcome | false outcome )`, which turns invalid into `false ok` and passes every other outcome on.
- **F9.** Sort and Prop tests at 8 sites. Besides N2's three wrong copies, whnf.fs:279, discr-keys.fs:181, fun-info.fs:178 and prop-quick.fs:100/153 write the both-tags test by hand. F3's `tag-set:` would have made the wrong copies impossible.
- **F1+.** elab-term.fs:303-341 `et-am-*` (mkAppM's walk) is a fifth forallMetaTelescope copy. It reads binder kinds with `lf-menv-kind@` and makes a metavariable per binder.
- **F10.** Dotted-name OR chains: nat-offset.fs:124-141 (16 `lf-meta-app-of?` calls in 5 words) and meta-env.fs:339-357 (architecture review L1). Replacement: a table of (arity, name) and `lf-meta-app-in? ( t table -- flag )`.
- **F11.** Records used as registers between consecutive words:
  - whnf.fs:133 `wc-src`, set right before `wc-apply` (:182);
  - `wc-e`, `wc-head` and `wc-data` (:364, :464);
  - infer.fs:100 `if-from`;
  - elab-term.fs:103-111 `et-am`;
  - elab-app.fs:91-94 `ea-rt`, `ea-rk` and `ea-rn`.

  Frames that save an activation's registers (defeq's, whnf's) are justified by the no-host-recursion rule; these are not.
- **F12.** `lf-elab-meta` appears 61 times in elab-term, elab-app and elab-pending, 36 of them followed by `ok-then?`: the architecture review's `meta-catch`/`must:`.

## 3. Module boundaries
- **B6 (reuse pass). elab-pending.fs mixes four layers.**
  - The trace (:156-201).
  - Error recording and positions (:166-191; every elab file uses them).
  - The pending list (:224-310).
  - Default instances with frames (:328-522).

  Split into `elab-errors.fs`, `elab-trace.fs`, `elab-pending.fs` and `elab-defaults.fs`. nat-offset.fs:98-116's mkNatLit and mkNatAdd belong in the architecture review's app-builder.fs.
- `lf-meta-ctx-approx!` is a public setter of a configuration copy: remove it (N1). defeq-delta uses defeq's private de-* words (architecture review Q5); whnf's `lf-whnf-stuck` shares the machine's private slabs (N6).
- **Public words named by no test: about 57** (grep over tests/): elab-pending 10; lib-decode 9 (`lf-libdec-find`, `-value`); meta-spine 9 (`lf-meta-spine`, `-apply-all`); meta-env 7 (`lf-menv-proj-class?`, `-rec-arg`); discr-keys 5; nat-offset 4 (`lf-meta-nat-lit`, `-cleanup-offset`); elab-app 3; elab-term 2; unfold 2 (`lf-unfold-step`); six files 1 each.

## 4. Documentation (D2), and the layer map
- **Headers that are wrong:**
  - meta-spine.fs:13-17 (N3);
  - assign-check.fs:41 says "Lean's Meta.Config"; the value is a stale copy (N1);
  - elab-term.fs:40-43: ensureType's isType step never fires (N2);
  - whnf.fs:93-97 does not say that `lf-whnf-stuck` shares wc's slabs (N6);
  - infer.fs:64-68 says the context "only grows", but fun-info and defeq drop their entries.
- **Layer map (Lean functions each file ports; header lines give the details):**
  - whnf: whnfCore, whnfCoreAtDefEq, whnf, unfoldDefinition?, getStuckMVar?, whnfR/D, whnfForall, instantiateForall.
  - unfold: getUnfoldableConst?, unfoldDefault, deltaBetaDefinition, unfoldProjInst?.
  - defeq: isDefEq, isDefEqGuarded. defeq-delta: isDefEqDelta.
  - infer: inferType, getLevel, getDecLevel. prop-quick: isPropQuick, isProofQuick. fun-info: getFunInfoNArgs, isProp. meta-check: Meta.check. assign-check: checkAssignment, mkLambdaFVars.
  - mvars: the MetavarContext, mkFreshExprMVar(At), mkConstWithFreshMVarLevels, assign, instantiateMVars, exprDependsOn, saveState, withNewMCtxDepth.
  - instantiate: instantiate1, abstract, headBeta. beta-inst: instantiateBetaRevRange. nat-offset: evalNat, isOffset?, mkOffset, mkNatLit, toCtorIfLit, cleanupNatOffsetMajor.
  - level-defeq: isLevelDefEq. term-eqv: Expr.eqv, etaExpanded?, consumeTypeAnnotations. meta-env: canUnfoldDefault/AtMatcher, getMatcherInfo?, getProjectionFnInfo?. lib-decode: getConstInfo (library). elab-data: the data reader (no Lean counterpart).
  - discr-keys: mkPath, getUnifyKeyArgs. instances: getUnify, getInstances, getDefaultInstances, isClass?.
  - synth: synthInstance?, trySynthInstance, synthPending.
  - elab-term: elabTerm, elabType, elabNumLit, binop%/binrel%. elab-app: elabAppArgs, ensureHasType. elab-pending: synthesizeSyntheticMVars, synthesizeUsingDefault, synthesizeInstMVarCore, mkInstMVar.

## 5. Tests seen from the code
- **No planted fault:** prop-quick.fs (none at all), `et-is-type?`, `ea-prop?`, `ep-step`, `ep-abandon`, `sy-flags`, `sy-cache-hit?`, `de-config`, `de-nested`, `it-unknown`, `mck-fits`, `wc-new-h`.
- meta-check.fs has a single fault, although it gates `rw`'s motive.
- **Planted fault that survives:** synthesis's ctxApprox (N1).
- **Missing tests:** ensureType of a term whose type is a Sort; propagateExpectedType with expected Prop; a malformed run-mode declaration; a failing synthesizeSyntheticMVars step.

## 6. Forth idiom (three translated-Lean spots)
**I4, nat-offset.fs:124-141.** match_expr written as `dup N s" X" lf-meta-app-of? over ... or` in 5 words. Forth form:
```forth
: no-unported? ( t -- flag ) no-unported-ops lf-meta-app-in? ;   \ table of (arity name)
```
**I5, elab-term.fs:303-341.** mkAppM's loop state kept in a 6-field global record (`et-am am-type @` 9 times). Forth form, on F1's telescope:
```forth
: et-app-m ( d max -- type outcome ) swap lf-meta-const-fresh ok-then? 0= if nip no-result exit then ['] et-am-arg lf-meta-telescope ;
```
**I6, infer.fs:189-200.** Lean's `j` held in `if-state if-from`. Forth form: carry it on the stack, `if-enter ( j type i -- j' type' outcome )`, with the loop `0 swap if-n 0 ?do i if-enter ... loop`.

## Reuse searched
- **Tools:** `check-duplicates.py`: "284 baseline groups, none new or grown". `check-lib-callers.py`: OK (bigint allowed, FE1i-4).
- **Searches:** grep over src/ for `lf-tag-sort`; `lf-lctx-local` (8 sites); `lf-lctx-drop` and `lf-view-push` (11); `outcome-invalid =` after a lookup; `ctx-approx`; `slab-index`, `lf-under`, `memo-walk:` and `tag-set:` (none exist yet); the in-/ib- memo words (F2).
- **New** next to the first pass and the architecture review: F8, F9, F10's nat-offset site, F11, F12's count, B6 and the fifth telescope copy.

## Forth style metrics (`forth-metrics.py --words 10`, 26 files)
- 3,126 words: 65% of 1-2 lines, 34% of 3-5, none longer. 76 globals (62 in elab-data's tables), 26 context members.
- 163 deep shuffles; 417 return-stack operations (elab-pending 52, elab-app 39, synth 35, lib-decode 34, mvars 31).

## Files: read whole / in part / not read
- **Read whole (26):** whnf, defeq, infer, unfold, defeq-delta, mvars, lib-decode, elab-data, elab-term, elab-app, elab-pending, synth, instances, discr-keys, meta-env, meta-spine, meta-check, fun-info, instantiate, beta-inst, nat-offset, assign-check, prop-quick, level-defeq, term-eqv, dag-walk.
- **Not read** (I stopped here to keep room for the report): level-map, level-normalize, level-params, level-simp, constructions, cases-several, ctor-idx, expr-remap, lctx-views, goal-print, step-log, term-find, syntax, elab-keys.
- **Uncertainties:** N1's end effect (an outer isDefEq answering unsupported) was traced in the code, not run; N3's malformed tier was not built; level-defeq's "deeper metavariable first" rule was not compared with pinned LevelDefEq.lean.
