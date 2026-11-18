# Forth review: tactic library slice a2-i (branch `tactic-lib`), 2026-11-18

**Range:** `e3c5297a..2e60b49e` (6 commits). **Findings:** 4 BLOCKS, 5 should fix before merge, 6 REUSE PASS (2 reuse, 4 style), 7 notes.
**Verdict: blocking.** F1-F4: new behaviour that no test runs (11 of the 14 never-run blocks are behaviour, not resources; 4 of my 5 extra planted faults survive), and two differences from Lean in mkAppM that are not pinned as gaps. Every term I compared with pinned Lean was equal, so the fixes are tests and gap pins, not rewrites.

## For the owner (plain language)
- It is the library you asked for, at its lowest layer: Lean's term builders (mkEq, mkEqSymm, mkEqTrans, mkCongrArg, mkAppM, ...), telescopes and binder scopes are now shared words. Each builds Lean's term. I checked 22 cases of my own against Lean 4.35.0 and found no wrong term.
- Tactics are not "a few library calls" yet. rw, rfl, intro and induction lost only 1-23 lines each, because the goal layer (Lean's MVarId.intro, rewrite, replaceTargetEq, apply) is still inside the tactic files. That layer is slice a2-ii. The size gain comes there, and in a2-iii for apply and constructor.
- The size figures are roughly fair. The Forth looks shorter partly because it leaves out Lean's error texts. It is longer where Lean's recursion became a frame of named fields.
- What blocks: failure cases that Lean has ("instance not found", "result has metavariables") and the instance-synthesis success path were never run by any test. Two known differences from Lean are refused safely but not yet listed as gaps.
- Gates: no kernel, import, format, parser or bypass change. Some `.lf` text can now elaborate differently, always towards Lean: default instances are tried through definitions that unfold to a function type, closing over binders now beta-reduces binder types, and one trace shows `?α` as Lean does. The kernel still checks every term.

## Findings (most severe first)
1. **BLOCKS: mkAppM's instance synthesis and final check are untested.** `src/front/app-builder.fs:207` (both the not-found `abl-fail` and the found `lf-mvar-assign`), `:210`, `:212` and `:213` never run. The fault "not-found accepted" (`lf-must 0= if abl-fail then` -> `lf-must drop`) and the fault "assignable metavariable not rejected" (`:212` `if abl-fail then` -> `drop`) both survive `check_whnf.py --golden` and `tactic-lib.fs`. `:202:64`/`:203` (whnfD reveals a pi) also never run. Fix: add these build cases to `check_whnf.py`: `mkAppM ``id #[u, k]` (my probe: equal to Lean), `mkAppM ``id #[u, k, k]` (rejected), `mkAppM ``congrArg #[u]` (rejected, "result contains metavariables"; equal). Add `mkAppM ``HAdd.hAdd #[k, k]` (Lean gives `@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k k`) and a case with no instance (rejected) in a harness with elaboration data loaded, so that `lf-synth-instance` is the `lf-meta-synth` hook (S2 slice in `tactic-lib.fs`, or `whnf-slice.elab`). Plant both faults.
2. **BLOCKS: the congrFun fusion test checks nothing.** `tests/front/tactic-lib.fs:220-222` builds an ill-typed `congrFun` (β := Nat) and accepts any failure. It gets -4201 (invalid), not the "instantiate1 lift" gap its comment claims. The fault `abl-from-fun` `rot 4 abl-arg` -> `rot 5 abl-arg` (`app-builder.fs:134`) survives. My well-typed probe (u v : Nat -> Nat, hh : u = v, `congrFun hh 0`) fuses to exactly `mkCongrArg (fun x => Nat.succ (x 0)) hh`, Lean's term. Fix: pin that case's term. Drop the ill-typed one, or pin its outcome.
3. **BLOCKS: the telescope and binding branches with behaviour are untested.** `telescope.fs:169` (a metavariable that sees some but not all of the xs: unsupported) and `:174:25` (e delayed-assigned) need tests. The fault "delayed e treated as open" (`2drop 2drop false` -> `true`) survives. `:83` (an unnamed binder gives the anonymous name) and `app-builder.fs:108` (an input node's binder is left unrecorded) need tests too. Name them in `tactic-lib.fs`: `partial-xs` -> -4205, `delayed-e` -> -4205 (after F5), `anon-binder`, `input-lam` (an export run, before `lf-author-begin`).
4. **BLOCKS (cheap): pin mkAppM's two differences from Lean as listed gaps.** (a) A result with an unassigned level metavariable is unsupported where Lean rejects: `mkAppM ``id #[]` gives Lean "rejected", LeanForth "unsupported". (b) A result containing an outer-depth metavariable is unsupported where Lean returns the term (`:213`, e.g. `mkAppM ``Nat.succ #[?n]`). Both fail closed. List them in `check_whnf.py` with `gap=` and a plan row, as the C4 binder rule is listed.
5. **Should fix: mkLambdaFVars silently leaves metavariables that see the xs.** `tl-elim` (`telescope.fs:193-195`) and `tl-open-mvar?` (`:172-174`) return e unchanged when it is delayed-assigned or holds a nested metavariable whose context contains an x. Lean's elimMVarDeps reverts them. The result then fails later (hand-over 74 or kernel) instead of failing here. This is not a regression (the old copies did the same), but the word now carries Lean's name. Fix: `tl-sees-xs? ( e -- flag )` with `lf-term-holds?` and a predicate "unassigned or delayed metavariable whose view finds an x", then `outcome-unsupported lf-must`. Re-run S1/S2's goldens.
6. **Should fix: the rewrite's local drop has no regression test in rw.** The planted fault `lf-with-local-decl` never drops (`catch r> lf-lctx-drop throw` -> `catch r> drop throw`) survives `tactic-run.fs` and `tactic-basic.fs`. Only the library test sees it. Fix: in `tactic-run.fs`, check that `lf-lctx-count @` is equal before and after a `by-rw[ n ]` run, and plant a fault replacing `lfw-independent`'s `lf-with-local-decl` with a bare `lf-lctx-local`.
7. **Should fix (before a2-ii's first rejecting caller): Lean's builder errors become "not supported yet".** `lfr-meta-code` (`tactic-run.fs:314-316`) maps a library rejected (throwAppBuilderException, throwAppTypeMismatch, "failed to synthesize") to 93, whose outcome is unsupported. `lfw-caught` (`tactic-rewrite.fs:246`) then rethrows it where Lean's `try` catches it. Today no tactic path reaches it. Map outcome-rejected to a Lean-error code (outcome invalid) and test it inside a try.
8. **Should fix: `lf-meta-catch` trusts its cell counts.** `meta-must.fs:64-66`. Probe: `111 222 333 ' two-in 3 1 lf-meta-catch` with a 2-input xt silently ate 111 on the failure path, while the success path ignores the counts. Fix: `depth` at entry; on success, check `depth = d0 - 1 - in + out` (allowing for xt), else `outcome-invalid lf-must`. That catches every wrong count on the success path, which every test runs.
9. **Should fix: the "no throw inside a walk" rule is too narrow and unchecked.** `meta-must.fs:33-36` names only `dw-run`. defeq's machine (`de-saved` stacks around the synth hooks), synth's `sy-enter`/`sy-leave` and the elaborator's frames also free state only on a normal return. Today every library call in outcome code is wrapped (`ep-telescope`, `lf-inst-telescope`, `et-app-m`, `lfr-close`), and no `lf-term-holds?` predicate throws (I traced `lfb-*?`, `lf-tac-hole?`, `abl-assignable?`). Fix: widen the rule's text, and add a plan row for a run-time guard: a `dw-active` depth in `dag-walk.fs` that `lf-must` and `lfa-fail` assert is zero (other agent's file).
10. **REUSE PASS: three copies of Expr.eq?.** `abl-eq`/`abl-alpha`/`abl-lhs`/`abl-rhs` (`app-builder.fs:84-87`), `lfb-eq?`/`lfb-alpha`/`lfb-sides` (`tactic-basic.fs:316-321,336`) and `lfw-sides` (`tactic-rewrite.fs:133-135`). Make public `lf-eq? ( t -- α a b true | false )` and `lf-const-levels ( t -- l1..ln n )` (Expr.constLevels!, replacing `lfb-level`, `tactic-basic.fs:334`).
11. **REUSE PASS: layering.** `app-builder.fs` requires `author/declarations.fs` only for `lfa-intern`. Move name interning below the author layer. `abl-level-zero` (`:64`) belongs in `core/levels.fs`.
12. **Note:** an unknown constant in mkAppM gives invalid (Lean: an ordinary error; `tactic-lib.fs:194` pins invalid), and `lf-meta-synth`'s stuck (16) becomes invalid through `outcome-sane` in `abm-synth`. Both fail closed. Prefer unsupported, or rejected after checking Lean.
13. **Note:** these words have no production caller: `lf-commit-when`, `lf-whnf-r!`, `lf-mk-eq-symm`, `-eq-trans`, `-congr-arg`, `-eq-mp`, `-eq-mpr`. The owner's own library is exempt, but dropping mkCongrFun for the same reason is inconsistent. `lf-commit-when` restores only the metavariable context (Meta's saveState). Uncertain: whether LeanForth keeps other Meta state, such as postponed level constraints.
14. **Note:** `lf-with-local-decl` drops every local made inside xt, not only its own. Dead fvars are detectable (`lf-fvar-live?`), so this is safe, but the header should say that nothing made inside may escape (Lean's metavariables keep their context).
15. **Note:** a pi revealed by whnf takes its binder name from a shared node's record. Probe on `id.{2} Type (Nat -> Nat)`: metavariable `n`, Lean `y`, kind equal. This is the known C4 limit.
16. **Note:** `ea-add` (`elab-app.fs:213`) fixes an old 2-cell result on the full path (untested resource branch).
17. **Note:** `docs/project/PROJECT_PROGRESS.md` has no row for a2-i (coordinator, at merge).

## The 14 never-run blocks (my focused coverage over test-front, -front-e2e, -instances, -elab-data, -author: the same 9 + 5)
| block | what | class | test |
| --- | --- | --- | --- |
| app-builder 108:25 | input node's binder left unrecorded | behaviour | F3 `input-lam` |
| 187:40 | more than 16 instance binders | resource (debt) | - |
| 202:64, 203:1 | whnfD reveals a pi, loop goes on | behaviour | F1 `mkAppM id #[u,k]` |
| 207:52 | no instance: rejected | behaviour | F1 no-instance case |
| 207:66 | instance found and assigned | behaviour | F1 HAdd case |
| 210:18 | result check meets a metavariable | behaviour | F1 `congrArg #[u]` |
| 212:52 | assignable metavariable left: rejected | behaviour | F1 `congrArg #[u]` |
| 213:35 | other metavariable left: unsupported | behaviour (gap) | F4 gaps |
| telescope 83:58 | unnamed binder: anonymous | behaviour | F3 `anon-binder` |
| 165:57 | metavariable without a view | malformed (debt) | - |
| 169:22 | x missing from the metavariable's context | behaviour | F3 `partial-xs` |
| 174:25 | delayed-assigned e | behaviour | F3/F5 `delayed-e` |
| 174:74 | assigned e after instantiate | unreachable (debt) | - |
11 are behaviour (need a test and a fault before the merge); 3 may be recorded as debt.

## Lean fidelity (step 1) and replacements (step 3)
- Same term, same failures, same order: mkEq, mkEqRefl, mkEqSymm, mkEqTrans (refl short-cuts h1 then h2; infer h1, h2; eq? h1 then h2), mkExpectedPropHint, mkCongrArg (isRefl? arity 2, congrArg?/congrFun? arity 6, infer h then f, arrow? before eq?), mkEqMP/MPR (mkAppM, no short-cut, as Lean). One order difference: `abl-congr-plain` takes getLevel of α and β before eq? of hType. It is observable only when getLevel itself fails. mkAppM: fresh levels inside the new depth, implicit and strict-implicit natural, instance synthetic and filled at the end, isDefEq at least default, whnfD then "too many arguments", stop at the last explicit argument. The difference is the final check (F4). The telescope: kinds and names equal to Lean for HAdd.hAdd (self synthetic), congrArg, absurd and Nat.rec; whnf between binders, the body kept from before whnf; maxMVars? not ported (needed for apply).
- `?m.198` -> `?α`: confirmed. Pinned Lean on `tests/front/s1-c17.lean`, line 64: `[Meta.synthInstance] Add ?α`, the userName of instHAdd's binder from forallMetaTelescopeReducing.
- Copies left: synth's `sy-telescope` is getSubgoals (mkForallFVars xs d, every metavariable natural and anonymous) and `sy-pi-whnf` is preprocessArgs (whnf at every step): different Lean functions, correctly kept. nat-offset, defeq, whnf, infer and fun-info are deferred to the reuse pass (FRONT_LAYERS.md).

## Step 5: the tactic files
The best example is induction's motive, from 9 lines to `: lfi-motive ( -- lam ) tb tb-want @ ti tind-target 1 lf-mk-lambda-fvars ;`. intro's closing went from 13 lines to 2. The worst example is rewrite (167 code lines, Lean's MVarId.rewrite plus the elaborator about 110). Thirteen `trw` fields act as registers (`trw trw-x @` about 60 times), and Eq is destructured by hand. The words that remove it come from a2-ii: `lf-goal-rewrite ( goal heq symm? -- new proof mvars )` (MVarId.rewrite), `lf-goal-replace-target-eq ( goal new proof -- goal' )` and `lf-lift-meta-tactic ( xt -- )`. by-rw then becomes about 10 lines. For by-apply (about 50), by-constructor (about 25) and by-decide (about 200), add first:
- the bounded telescope `lf-forall-meta-bounded-telescope ( type d n -- addr n' body )`, collecting metavariables and binder kinds into a slab (Lean's arrays);
- `lf-mk-app-opt-m` and `lf-synth-app-instances`;
- `lf-goal-apply` and `lf-get-mvars-no-delayed`;
- a first-success combinator over `lf-commit-when`, for constructor.

## Forth style
Metrics (`forth-metrics.py --words 10`, 10 files): 1057 words, 70% of 1-2 lines, 29% of 3-5 lines, none longer, no locals. meta-must 21 words (1 deep shuffle); app-builder 67 (9 deep shuffles, 20 return-stack operations); telescope 54 (7 deep shuffles, 26 return-stack operations). check-duplicates: 283 baseline groups, none new (the baseline went down 2). check-lib-callers: clean.
- S1 (REUSE PASS): frame fields used as registers in mkAppM and the telescope (`abm abm-app @ ... abm abm-app !`, `tl tlf-type @ ... !`). Carry the loop state on the stack, as Lean's recursion does: `abm-enter ( app pi x -- app' body ) tuck lf-meta-open lf-must >r lf-mk-app r>`, and `abm-step ( app type -- app' type' )`, with only xs, i and insts in the frame.
- S2 (REUSE PASS): `s" x" lfa-intern abl-named` is repeated 3 times (`:110`, `:132-134`). Use `: abl-named" ( t c-addr u -- t ) lfa-intern abl-named ;` and split `abl-from-fun` into `abl-fun-dom ( h -- α' )` and `abl-fun-lam ( h α' -- f' )`.
- S3 (REUSE PASS): `tl-binding`/`tl-bind-in` take 5 items, and `tl-aux-type` juggles `>r >r ... r> r> rot`. Keep view and xt in `tlb`, set by the public words, and save and restore `tlb` around the recursion: `tl-binding ( e addr n -- e' )`.
- S4 (REUSE PASS): `tle!` relies on `tle-n` and `tle-xs` being adjacent (`2!`). Store the two fields by name.

## Reuse (step 3a)
I searched: LIBRARY_WORDS.md (only `context-catch` is near; it differs); FRONT_LAYERS.md; src/front by shape for mkApp copies (`lf-term-app` with a full check), withLocalDecl copies (`lf-view-push`), mkConst copies (`lf-cref-new`), binder-metavariable copies (`lf-mvar-tag!`), telescopes (`lf-meta-open` loops) and Eq destructuring (`3 s" Eq"`). New: F10 (Eq.?) and F11. The rest are listed in FRONT_LAYERS.md for the reuse pass. No module was started as a copy.

## Probes run (Gforth 1.0.0, pinned Lean 4.35.0, scratch copy of 2e60b49e; no suite re-run)
- Builders: 22 cases of my own against pinned Lean through check_whnf's harness. 18 equal (including the nested and lambda congrArg fusion, `mkAppM congrArg #[u, e]`, `id #[u, k]` and function-typed Eq). 4 differ: `id #[]` (F4); `Eq.trans` is not in the slice (invalid); HAdd (this harness has no synth hook); `absurd #[e, e]` (a defeq gap: `Not (a=b) =?= a=b` is unsupported).
- The telescope against Lean (4 declarations and 1 whnf case); s1-c17 with Lean; congrFun and `lf-meta-catch` probes.
- Faults: the three requested are all caught (mkEqTrans h1/h2 swapped: check_whnf; instance binder made natural: tactic-lib and instances.fs; local kept on a throw: tactic-lib). Five more planted, of which four survive the focused tests: F1 (2), F2, F3. The fifth (`d` kept after whnf) is equivalent.
- Not run: gforth-fast, Gforth 0.7.3, the full tier. My coverage run was focused; part of it overlapped the fault planting in the same scratch tree, but its counts equal the implementer's.
AI review does not replace the owner's required human review of trusted semantics and interfaces.

## Re-check: branch `tactic-lib-2`, range `2e60b49e..71f1f395` (14 commits), 2026-11-18
**Verdict: mergeable.** All four blocking findings and F5-F8 and F10 are fixed as I meant them. I re-planted my five faults that had survived; all are now caught. No finding in this round blocks. Before the merge, the coordinator must add plan rows A-D (and the two below) to the plan; the report only drafts their text. Open: 0 blocking, 3 should fix (planned), 4 notes.

**Findings (1) and (2): fixes and faults.** I re-planted these faults (Gforth 1.0.0, scratch copy of 71f1f395):
- "leftover metavariable not rejected": caught by check_whnf (`congrArg #[u]`: Lean rejected, LeanForth unsupported);
- "not found treated as found": caught by tactic-lib (Append);
- the congrFun `h` index: caught by check_whnf (the congrFun case against Lean);
- "delayed treated as open": caught by tactic-lib (`delayed-e`);
- the rw local never dropped: caught by tactic-run (`rw-locals` 2 -> 4).
The other fixes, checked in the code:
- `lf-eq?` returns α a b in the right order, and the new mkEqTrans, mkCongrArg and Eq.symm term builders build the same terms as before.
- `lfm-want`/`lfm-left` compare absolute stack depths correctly.
- `tl-closed` cannot throw inside its walk: the no-view case is caught before `tle-view` could throw. It clobbers `tle`, but `tl-revert` stores it again after the recursion.

**(2) Instance cases pinned by hand.** I ran pinned Lean 4.35.0 myself (run_meta, pp.all, k : Nat):
- `mkAppM ``HAdd.hAdd #[k, k]` = `@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k k`;
- `Append.append #[Nat, Nat]`: "failed to synthesize Append.{1} Type";
- `HAdd.hAdd #[Nat, Nat]`: "failed to synthesize HAdd.{1, 1, ?u.3} Type Type ?γ".
The hand-pinned values are Lean's. The third case is pinned as unsupported (119), not rejected. The cause is the slice's data leaving a candidate out, not the code, so that is acceptable.
A hand pin is acceptable for now: it cites the Lean command, and I re-ran it. It should become generated once a pinned-Lean harness has instance data. That is a plan row, together with (3).

**(3) Name ID 30: not reproduced, and not possible in a real `check`.**
- **Reproduction tries.** I tried three set-ups:
  - synth.fs loaded after `whnf-builds.fs`;
  - synth.fs loaded inside it;
  - after check_whnf's whole case list.
  In each I traced every `lf-menv-find`/`lf-menv-data-decl` id during `mkAppM HAdd.hAdd #[k,k]`. Every id was the right one: `lfa-intern` "HAdd" = 794 = `menv-name` "HAdd" -> declaration HAdd, and name 30 is List.rec's "rec".
- **Name modes.** `lfa-intern` interns through the current names mode. With a stage fed, that mode is the view over the stage's tier, so its ids are the tier's numbers.
- **The latent hazard.** In fed mode (`lf-menv-stage!`, used only by tests and reference-synth), `lf-menv-find` (`lf-input-newest`) and `elab-decl-of` (`ed-stage stage-find`) index by the raw id.
  - Nothing checks that the names are the view over that same stage. `lf-input-indexed?` exists but is not consulted.
  - `lf-const-name` drops the constant's name generation.
  - So an id from another store, or a stale id, would be used silently.
- **A related defect (outside this branch, test-only).** I reproduced it in the export test harness:
  1. `lfc-elab-read` of another export's data is refused (outcome 1);
  2. after that, `lf-menv-data-decl` of HAdd answers true with a garbage handle.
  This is the most likely kind of state the implementer saw.
- **Real `check` of `.lf` text.**
  - It uses run mode (`lf-menv-library!`). `lbd-tier-name` maps a context name to the library tier part by part, by its text. An id cannot reach another declaration's slot: a name that is not found is unknown.
  - Without `--env`, `Nat` is "unknown name".
  - A mismatched `--elab-data` stops the run: exit 4, "elaboration data of another export", text not checked.
  - So no well-typed wrong constant can come from this path.
- **Is F11 the root?** No. F11 (app-builder requiring `author/declarations.fs` for `lfa-intern`) is layering, not this.
- **Does it block?** No. Add two plan rows (should fix):
  - (E) in fed mode, `lf-menv-find`/`lf-menv-data-decl` refuse as invalid unless `lf-name-viewed?` holds over `me-stage` (and `ed-stage` is that stage);
  - (F) a refused `elab-read` must leave no half-set `ed-stage` (elab-data.fs or check-lf.fs, the author agent's files).
  The implementer should also attach the exact ID-30 reproduction to row E.

**(4) F7, error 96 "Type mismatch".** The behaviour is right: outcome invalid, `try` catches it, as Lean's does, and the test pins 96, 93, 60 and 91. The text misleads for "failed to synthesize" and for AppBuilder's "equality proof expected". No tactic reaches it today. It is acceptable for this merge. Should fix: give AppBuilder's exception its own code before a2-iii's apply errors (plan row; errors.fs).

**(5) Debt blocks.**
- app-builder `192:40` (a 17th instance binder: abl-most): resource. OK.
- telescope `169:57` and `206:29` (a metavariable with no view): malformed record, inside the owner's rule. OK.
- telescope `178:74` (`tl-open-mvar?` on an assigned e): this is neither a resource branch nor a malformed record. It is a defensive branch that cannot run, because `tl-elim` always gets an instantiated e. It has the same standing as tactic-syntax's `lft-bracketed?` entry. Accept it with its stated reason, or test it in one line (`tl-open-mvar?` of an assigned metavariable). Not blocking.

**(6) The meta-check leak.** `lf-meta-check` keeps one local per lambda it enters. That is about one local per rw rule, never in any view and never closed over. So it is a slow resource growth: the local-context store fills sooner on long proofs. It is not a correctness bug. The F6 test pins the count at 2, so plan row C will show when it is fixed. Harmless for the merge.

**(7) Nothing new blocks.** Note: FRONT_LAYERS.md's table does not list `lf-eq?` yet.
**Gates.** No change to [kernel], [import], [format], [parser] or [bypass]: only `src/front` and tests changed. `.lf` text that now elaborates differently, all towards Lean:
- (a) Trace metavariables are named by their binder: `?α`. Evidence: pinned Lean on s1-c17.lean, line 64, `Add ?α`; I re-confirmed it.
- (b) Binder types in mkLambdaFVars/mkForallFVars are head-beta reduced. Evidence: I re-ran pinned Lean; `mkLambdaFVars #[j] j` over `j : (fun y => Nat) k` prints `fun (j : Nat) => j`, as tactic-lib's `lam-j` pins.
- (c) Default instances are tried through definitions that unfold to a pi. No slice case reaches this, so no corpus text changes.
- (d) A metavariable left seeing an abstracted variable is now refused at once (93, unsupported). Before, the term went on and was refused later (hand-over 74 or the kernel). The S1/S2 goldens are unchanged.
- (e) A tactic library rejection inside `try` is caught (96). No current path reaches it.
The kernel still checks every proof term.
**Ran:** five re-planted faults; pinned Lean on the three instance cases and on head-beta; instrumented lookups in three harness set-ups; a mismatched `--elab-data` check. Not run: suites, gforth-fast, Gforth 0.7.3.
