# Whole-code Forth review: src/front and src/author on s2-finish-2 (input to the front reuse pass)
**Range:** whole files at `s2-finish-2` = `cb12814d` (merge-base with main `3b8f8bf9`); not a diff review.
**Findings: 26.** Blocks a merge (a difference from Lean, or fail-closed state): 5 (C1-C4, D1). Reuse pass: 16. Note: 5. Read-only. I worked on a scratch copy made with `git archive`, ran one Gforth 1.0.0 probe, and ran `forth-metrics.py`, `check-duplicates.py` and `check-lib-callers.py`. No suite was run. This AI review does not replace the owner's required human review.

## For the owner (plain language)
- Nothing I found lets a wrong proof through. Every path still ends at the hand-over check and then the kernel.
- **One real bug in "try this, else undo it" (C1).** When an attempt fails, the goal list is put back. If the attempt left an inner checkpoint open, its assignments are not undone, and nothing reports it; my probe shows this. Today only `rw`'s closing `rfl` runs inside an attempt, and it never leaves a checkpoint open. `first`, `try` and `<;>` (FE5) would trigger it. The fix is small: undo everything, or stop with an error.
- **The same undo also misses three files' state (C2):** the elaborator's pending list, the open induction blocks and the step log's newest entry. Fix this before FE5.
- **Two small differences from Lean (C3, C4):** `rw` can miss a match on a raw number, and it may fill an instance argument by unification where Lean runs instance search. The first only gives an error; in the second the kernel still checks the proof.
- **The reuse pass should fix 7 causes, not 152 duplicate groups:** a metavariable telescope: 4 copies, one already public; a memoised rebuild walk; a tag-set word; a find-in-slab word; a tactic-error word; a "step into the body" word; a chained start-up hook.
- **Coverage:** I read 11 files whole and 13 in part, about a quarter of the 19,500 lines. whnf, defeq, infer, lib-decode, elab-data, elab-term and synth need a second pass (list at the end).

## 1. Correctness and fail-closed behaviour
**C1 (BLOCKS; the hand-over or the kernel still catches the result).** tactic-run.fs:526-543 with mvars.fs:501-502.
- `lfr-rolled` first cuts trun's slabs and puts back the goal list (`lfr-back`), and only then undoes the trail.
- `lf-mctx-rollback` refuses (invalid) while a newer scope is open. `lf-tac-restore` drops the save anyway, and `lfr-undone`/`lfr-kept` (:539-540) drop the outcome. `lfr-back` (:531) also drops the outcome of `lf-goals!`.
- **Probe** (a copy of tests/front/tactic-run.fs §6): `: spoil-marked lf-mctx-mark 2drop spoil lfa-e-tac-unsolved lfa-fail ;  two-goals ' spoil-marked lf-tac-try`. It gives `code=-4129 g1-assigned=-1 goals=2 marks=2 saves=0`. g1 stays assigned, and `lf-main-goal` then skips it as solved. Two marks leak, so every later change is trailed. The outcome is a hole (error 74) or a wrong term that the kernel rejects.
- **Fix:** Add `lf-mctx-rollback-to ( mark -- outcome )`, which undoes every newer scope too (Lean replaces the whole MetavarContext). Undo the trail first. Make a refusal fatal: `: lfr-undone ( save code -- code ) swap lf-tac-restore lfr-must ;` and the same for `lfr-kept`. Add the probe as a test and plant a fault.
**C2 (BLOCKS FE5; same cause).** `lf-tac-save` covers only trun's slabs. After a caught authoring error, these stay changed:
- the elaborator's window: `lf-elab-synth{` at tactic-rewrite.fs:222 is closed only at :227;
- tind-withs and tind-alts: tactic-induction.fs:316-332 cuts them only on success, and `lfi-closed` throws first at :326;
- trw-mvars;
- trun-entry: tsv has no field for it, so `lfr-frame!` may name a cut log entry.
Fix: `tac-state: ( save-xt restore-xt -- )`, a chain that `lf-tac-save` and `lfr-back` run, plus scoped words that restore under CATCH, as `lf-meta-with` does (meta-config.fs:91), for example `with-elab-synth ( xt mode -- outcome )`.
**C3 (BLOCKS: a difference from Lean; fails closed).** kabstract.fs:74-76: `kab-same` compares a literal head by node identity.
- Authoring runs switch term sharing off (author/runner.fs:234), so two equal literals are distinct nodes and isDefEq is never tried.
- Lean's HeadIndex `.lit` compares values, so the result is "did not find instance" where Lean rewrites.
- Fix: `lf-tag-lit of lf-lit-cell swap lf-lit-cell = endof`, and compare strings by text. Add a pinned-Lean case and a fault.
**C4 (BLOCKS: a difference from Lean; the kernel checks types).** tactic-rewrite.fs:113-116: `lfw-mvar` takes the binder kind from `lf-tac-binder` (tactic-basic.fs:178-180).
- When the kind is unknown, for example on a pi that whnf made at :121-123, it answers explicit. LeanForth then makes a natural metavariable, which isDefEq may fill.
- Lean makes a synthetic one and synthesizes it (postprocessAppMVars), so the two terms can differ.
- Fix: refuse an unknown kind (99), as `lfb-explicit?` does at :214. F1 then removes the cause.
**C5 (reuse pass).** tactic-basic.fs:264-266: `lfb-intro-as` skips `lfb-plain`'s let test.
- A let node is (value, binder(type, body)) (core/let-terms.fs:40-43), so on a let the domain becomes the value and the body becomes the binder node: a wrong term that the kernel rejects.
- Unreachable today: an alternative's fields are pis.
- Fix: `dup lf-let? if lfa-e-tac-form lf-tac-fail then`.
**C6 (note).** tactic-induction.fs:185: `lfi-pos` goes negative for a bvar index at or past `binders`. `tind-motive` then stays 0, and :270 assigns metavariable record 0. Unreachable with closed types; add a check with `0 binders within`.
**C7 (note).** tactic-run.fs:471-473 records the open part before `lf-mvar-assign` can fail. This is harmless only because the failure stops the run; say so in the comment.

## 2. Factoring (causes; the baseline's groups are their symptoms)
**F1 (reuse pass; the cause of C4). One forallMetaTelescopeReducing instead of four:**
- instances.fs:170-190 `lf-inst-telescope` (public, with no caller outside its file);
- elab-pending.fs:379-400 `ep-t-*`;
- synth.fs:402-410 and :537-545;
- tactic-rewrite.fs:112-126.
Each copy takes binder kinds from a different source. The architecture review listed only the rewrite copy. Replacement: `lf-meta-telescope ( type kind-xt mvar-xt -- body outcome )` with `lf-binder-kind-of ( pi src -- kind true | false )`.
**F2 (reuse pass; architecture review recommendation 7). One memoised offset rebuild walk.**
- instantiate.fs:123-150 and beta-inst.fs:75-100 match word for word: entry, hash, rehash, same, hooks, tab, find, image?, ready?, room, claim, keep, top, pop, push, push-if.
- kabstract.fs:100-153 hand-writes the same stacks.
- Replacement: `memo-walk: ( build-xt kids-xt "name" -- )`, which defines `name ( node depth -- image outcome )`. This covers instantiate's 31 groups, beta-inst's 27, mvars' 23 and the annotation trio.
**F3 (reuse pass). Tag-set OR chains, 6 sites:** tactic-run.fs:418-419; kabstract.fs:72-73; prop-quick.fs:63-64, 99-101, 152-154; tactic-basic.fs:204.
- defeq-delta.fs:165-167 and export.fs:253-255 already use `lf-tag-bit` masks.
- Replacement: `tag-set: ( mask "name" -- )`, which defines `name ( term -- flag )`, and `kind-set:` for tactic kinds.
**F4 (reuse pass). Linear search with `?do … unloop exit`:**
- tactic-induction.fs:217-219, :283-285, :287-289, :345-347;
- goals.fs:90 and :131;
- handover.fs:88.
Replacement: `slab-index ( x xt slab from -- i true | false )` in lib/slab.fs.
**F5 (reuse pass). One tactic-error word.**
- The phrase `0 ['] X lf-tac-inline 0 ['] Y lf-tac-detail CODE stop` and its `( xt code -- )` twins `lfb-failed` (tactic-basic.fs:193), `lfw-failed` (tactic-rewrite.fs:96) and `lf-tac-failed` make 14 sites in 3 files.
- Replacement: `tac-error ( inline-xt detail-xt code -- )`.
**F6 (reuse pass). Step-record fields used as registers between consecutive words.**
- tactic-rewrite.fs:205-218 (61 field accesses); `tind-f` and `tind-ftype` at tactic-induction.fs:243-247.
- They go away with the builders (architecture review recommendations 1 and 3).
**F7 (reuse pass). "let or binder → body" re-tested at 5 sites:** prop-quick.fs:76-78, 89-92, 105-107, 126-130 and 162-165, plus `lfi-past` at tactic-induction.fs:180. Replacement: `lf-under ( e -- e' true | e false )`.

## 3. Module boundaries
**B1 (reuse pass). 11 public aliases of private words.**
- tactic-basic.fs:160, 172, 175, 197-199, 286, 325;
- tactic-run.fs:287, 300, 463 (`lf-tac-must`, `lf-tac-app`, `lf-tac-stop`).
Define each word once. tactic-induction.fs:271 still calls the private `lfb-popped`.
**B2 (reuse pass). Mixed layers.**
- tactic-basic.fs mixes the MVarId layer with about 25 printing words (:183-201, :285-312).
- tactic-induction.fs holds about 45 lines of Lean message text.
- tactic-run.fs holds the runner, the term builders (:447-465), the binder closing (:557-595), the step log and the open-part printing.
Split them: runner, step log, and a `tactic-messages.fs` catalogue.
**B3 (reuse pass; load order).** reader.fs:57 sets `lfa-declaration-fresh` without chaining to the previous action, unlike tactic-syntax.fs:149-151 and elab-decl.fs:88-90. A hook set before reader.fs loads would be lost silently. Replacement: `fresh-hook: ( xt -- )`, a chain like `context-setup`, also for `lfa-run-fresh`.
**B4 (reuse pass). 81 public `lf-` words with no caller outside their file:** tactic-run 15 (`lf-tac-save`, `-restore`, `-commit`, `lf-tactic-by`), instances 9, elab-pending 8, lctx-views, meta-config, meta-env and mvars 5 each. Make them private (ADR 0010) or mark them as the test interface.
**B5 (note). Seven "must" words with their own outcome-to-code maps:** tactic-run.fs:295-308, plus `edc-must` and `lfa-must`.
- Move them into architecture review recommendation 3's throwing-outcome file.
- Error codes are still declared twice in errors.fs (`lfa-code:`).

## 4. Comments and documentation
**D1 (BLOCKS, with C1).** tactic-run.fs:49-57 promises that a failed `lf-tac-try` "puts the state back". C1 and C2 disprove that, so state the exact scope of a save.
**D2 (reuse pass).** The word lists are prose: tactic-run.fs:58-96 is 39 lines, and tactic-basic.fs:55-73 is similar. A tactic library needs one line per public word: `name ( effect )` and the Lean function it ports.
**D3 (reuse pass).** kabstract.fs:66-68 states C3's wrong rule. tactic-basic.fs:176-180 does not call "explicit when unknown" a guess. `lf-tac-try` does not give xt's stack effect `( -- )`.
**D4 (note).** Reflowed lines split phrases (tactic-induction.fs:114-116, 191-192, 213-214, 241-242, 302-303), so 2-line words read as 3-5 lines.

## 5. Tests as seen from the code
**T1 (reuse pass). 102 of the 425 public `lf-` words in front and author are named by no test** (some are reached indirectly):
- tactic-run 18 (`lf-tac-in-record`, `lf-front-close`, `lf-tactic-by`, `lf-tac-const2`);
- elab-pending 14;
- tactic-basic 13 (`lf-tac-intro-as`, `lf-tac-rfl-reducible`);
- lib-decode 11;
- meta-spine 11;
- meta-env 7 (`lf-menv-rec-arg`, `-matcher-sizes`, `-dite?`);
- discr-keys 5;
- nat-offset 4.
**T2 (reuse pass). Risky words with no planted fault:**
- `lfr-undone` and `lfr-kept` (C1);
- `kab-same` (C3);
- all of prop-quick.fs, whose isProofQuick drives defeq's proof irrelevance. Suggested faults: `pq-no-proof?` without the pi test, and `pq-sort-zero` turning undef into true;
- `lfr-linked?` and `lfr-alt-right?`;
- the bound check in `lfi-field-kind`;
- `lfh-shaped?`.
No planted fault at all in prop-quick.fs, syntax.fs, author/constants.fs, library.fs or scopes.fs.

## 6. Forth idiom (the three worst)
**I1, prop-quick.fs:162-165.** It tests "lam or let", then tests let again. Forth form:
```forth
: lf-under ( e -- e' true | e false )
  dup lf-let? if lf-let-body true exit then dup lf-term-lam? if lf-term-second@ true exit then false ;
: pq-proof-round ( e -- e' true | lbool outcome false )
  lf-under if true exit then dup lf-term-app? if pq-proof-app else pq-proof-leaf false then ;
```
**I2, tactic-induction.fs:345-347.** A counted loop with `2dup … nip nip unloop exit`, and `i lfi-case` computed twice. Forth form:
```forth
: lfi-name= ( name case -- flag ) tia-name @ = ;
: lfi-case-named ( name -- case )
  ['] lfi-name= tind-alts lfi-top tiw-first @ slab-index 0= if lfa-e-tac-record lf-tac-stop then tind-alts slab-at ;
```
**I3, tactic-run.fs:418-419 and F3's sites.** Chains of `dup X = over Y = or`. Forth form:
```forth
tac-k-by kind-bit tac-k-with kind-bit or tac-k-alt kind-bit or tac-k-case kind-bit or kind-set: lfr-holder?
```

## Reuse searched
- **Tools:** `check-duplicates.py` reports "284 baseline groups, none new or grown". `check-lib-callers.py` is OK (`bigint.fs` allowed under FE1i-4).
- **Searches:** I grepped src/ for the Lean names forallMetaTelescope, forallTelescope, mkLambdaFVars, withLocalDecl and instantiateForall (found in 17 files), and for `lf-inst-telescope`, `slab-claim drop` and dropped rollback/commit outcomes.
- **New** next to the 2026-11-18 architecture review: F1's public copy, F3, F4, F5 and B3. Everything else is a named item of that review or of the 2026-11-17 review.

## Forth style metrics (`forth-metrics.py --words 10`)
- **front (51 files):** 4,678 words; 69% of 1-2 lines, 30% of 3-5, none longer. No locals, 77 globals, 248 deep shuffles, 756 return-stack operations.
- **author (14 files):** 597 words; 70% and 29%, and 3 of 6-10 lines. Split each into a dispatch by kind: build.fs:104 `lfa-copy`, 10 lines; build.fs:191 `lfa-shift-node`, 7 lines; values.fs:101 `lfa-item-term`, 6 lines.
- **Most return-stack operations:** synth 35, lib-decode 34, mvars 31.

## Files: read whole / in part / not read
- **Whole (11):** tactic-run, tactic-basic, tactic-induction (from line 60), tactic-rewrite (from 50), tactic-syntax (from 90), handover, goals, kabstract, prop-quick, elab-decl (from 40), meta-config (from 60).
- **In part (13):** mvars 120-660; defeq header, 380-430 and 900-969; instances 1-40 and 150-205; elab-pending 375-400 and 520-563; elab-data 1-140; meta-env header and tables; synth 1-80; instantiate 120-160; beta-inst 75-100; defeq-delta 160-180; reader 30-70; author/export 120-343; author/errors (structure only).
- **Not read in front (29):** whnf, unfold, infer, lib-decode, elab-term, elab-app, discr-keys, meta-spine, meta-check, fun-info, nat-offset, the six level-* files, constructions, cases-several, ctor-idx, expr-remap, assign-check, dag-walk, lctx-views, goal-print, step-log, term-eqv, term-find, syntax, elab-keys.
- **Not read in author (12):** declarations, groups, scopes, values, words, build, runner, source, namespaces, form, constants, library.
**Uncertainties.**
- Not checked against pinned Lean: prop-quick's bvar rule in isArrowProposition.
- Not checked: whether instances.fs:199-200 `it-unknown` (every invalid treated as "no class") can also swallow a decoding failure.
