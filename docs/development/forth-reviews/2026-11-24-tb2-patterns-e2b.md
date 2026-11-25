FORTH REVIEW: tb2-patterns-e2b
Range 3c622ac1..8b930bcc (head 8b930bcc). Findings: 1 blocking, 9 not blocking (6 correctness, docs or tests, plus 3 style).
Verdict: merge after fixes. No probe found LeanForth accepting something Lean rejects. Every accepted probe gives Lean's term node for node.

Findings
1. BLOCKING (test class "state and rollback"). src/front/meta-tactic/contradiction.fs:168 `mcd-committed`. I planted a fault that drops `lf-commit-when` (`: mcd-committed ( fvar -- flag ) mcd-split ;`). It survived batch-h2's test.fs and check.py. Rule 6's false path has no test: cases fails with a Lean error, exfalso's assignment is undone and the next local is tried. Block coverage cannot see this because mcd-split is one line with no branch. If a test exists that can reach a rejected `lf-goal-cases` on a type with no constructor and no index, add it to batch-h2 test.fs section 4: the goal must be open afterwards and a later local must close it. If no such test exists, say in the header why the path is unreachable in LeanForth today, keep the commit-when (Lean has it at Contradiction.lean:79-81), and add the fault with an `equivalent =` reason.
2. src/front/pattern-syntax.fs:157-158 `lft-contra-item`. `by-contra: -` answers 84 (a name error), but Lean's `by_contra -` is valid. The word also copies pat-words' handling of `rfl`. Fix: read the item through the same word list, e.g. `2dup pat-words lfa-word-of if nip nip execute drop else lft-given 1 pat-span! then`, so `rfl`, `_` and `-` mean what they mean inside `by-contra[ ]`. Not blocking: `by-contra[ - ]` already works, and the header lists only NAME, _ or rfl.
3. src/front/rcases.fs:248 and :323 (`lf-tac-ported` around `lf-goal-cases` and `lf-goal-generalize`). Every unsupported Meta failure inside those words now answers 99, including one from lf-whnf!, lf-infer! or a store. Before the branch such failures reached the runner as 93 (tactic-run.fs:418). Both mean "not supported" and none can become a negative answer. Still, the text at tactic-run.fs:383-385 should say that every unsupported failure inside the wrapped word is mapped. Not blocking.
4. src/front/meta-must.fs:179-184 `lf-meta-try`. On the false path it does not roll back the metavariable context. That matches Lean's MetaM `try`, and rule 6 gets its rollback from lf-commit-when. Say so in the comment: "nothing undone; wrap in lf-commit-when". Test gap: batch-h2 section 2 and section 3 check only rejected, unsupported and abort. Add the full and invalid outcomes (`' fulld ported -> thrown-full`, and lf-meta-try rethrowing full and invalid). My fault mapping full to 99 was caught only because the heap sweep aborted at test.fs:138. Not blocking.
5. The patterns slice's recipe exists only in commit d43f05f3's message. Record the four commands in the repository, next to the slicer in TESTING_STRATEGY.md or in TACTIC_PATTERNS.md section 5:
   - export-slice.py on the pinned Init export with the roots file;
   - ndjson-reexport.sh;
   - export_manifest.py;
   - export-elab.sh.
   Not blocking: I reproduced the export byte for byte (finding C below).
6. Size: the new files add 4,034,114 bytes (ndjson 3,586,242; elab 445,130; roots 1,630; manifest 1,112). That is a near-copy of decide-slice (3,554,617 + 443,662). Its roots are a strict superset (all of decide's plus 37 more): 1,073 declarations against 1,027. Plan row: move decide's users to patterns-slice and retire decide-slice, or extend decide-slice.roots as ops-c1 did. Not blocking.
7. src/front/pattern-syntax.fs:74. The `pfr-closer` field comment still says "3 or 4 ]"; closer 5 (by-contra[) is missing. Not blocking.

Forth style (`python3 scripts/forth-metrics.py --words 10` on the 10 changed src files)
- Summary: 730 words. 82% are 1-2 lines and 17% are 3-5; none is longer than 5 (longest: 5 lines, mel-type-hint and lfg-decl).
- No missing stack comments, no locals, no line over 90 characters.
- Counts: globals 6, deep shuffles 38, return-stack operations 108.
- No PICK or ROLL. No new long word.
S1. The branch writes the phrase `outcome-unsupported lf-must` 20 times: cases.fs:71-83 (6) and meta-induction.fs:138-300 (14). src/front has 34 copies in all. Name it in meta-must.fs beside lf-made! and lf-found, `: lf-unported ( -- ) outcome-unsupported lf-must ;`, then write `0= if lf-unported then` at each site.
S2. pattern-syntax.fs:118-119 `pfr-end-list` is an IF chain over the magic closers 3, 4 and 5. Use named constants and CASE: `pfr pfr-closer @ case 3 of pfr-top endof 4 of pfr-seq endof 5 of pfr-contra endof endcase`.
S3. tests/support/meta-sweeps.fs:104-116 `sweep-view-at` and `sweep-kept` use raw offsets (`3 * cells`, `2 cells +`). Use `begin-structure /svl field: svl-name field: svl-fvar field: svl-flags end-structure`.
Baseline: by-contra.fs globals 3 to 4 is the new registry row `tac-k-by-contra-pat` (lf-tactic-seq:). It is written at load time, and rows abort once context-sealed? is true (tactic-run.fs:303). Acceptable.
Re-entrancy: no new mutable state in src. meta-sweeps.fs adds `sweep-view` (CREATE) and `sweep-view#` (VARIABLE). sweep-keep-view writes them during tests; it is test support only and never loaded by the checker.

Reuse (searched lib/, FORTH_LIBRARY.md and src/front by name and shape)
- Try-and-catch-rejected sites: elab-term.fs:537 and defeq-delta.fs:180 return outcomes, so they are a different shape. The old inline copy in mcd-try-decide now calls lf-meta-try.
- `lfr-thrown-as?` now also serves lfr-rejected?, which is good. `lf-decl-suffix?` has its one caller.
- check-duplicates.py: "186 baseline groups, none new or grown". check-lib-callers.py: every lib file has a caller or a plan row.
- The duplication is S1 (a phrase without a name) and finding 2. Nothing re-implements a library word.

A. Probes (LeanForth on patterns-slice, `bin/leanforth check` plus the elab-dump term dump). Lean side: pinned Lean 4.35.0 with Batteries' by_contra_core and by_contra macros copied exactly as in batch-h2.lean, the file's header citing Batteries Init.lean:43-60. rintro and rcases are core Lean's.
| probe | LeanForth | Lean |
| p01 `by-contra[ h ]`, goal ¬¬(a=b) | accepted, h : ¬a=b | same term |
| p02 `[ << x y z >> ]`, goal ¬(a=b∧b=a∧a=a) | accepted | same term |
| p03 `[ _ ]` and q01 `by-contra: _` | accepted, hypothesis shown a✝ | same term and goal |
| p04 `[ - ]` then contradiction | 449 | contradiction failed |
| p05 `[ ]`, and two patterns (test) | 474 | (Lean has no such syntax; `k j` is a parse error) |
| p06 `[ h1 \| h2 ]`, goal ¬(a=b) | 99 | accepted (rcases on an Eq, E4) |
| p07 `[ << u v >> ]`, goal a=b∨b=a | 471 "...→ False is not an inductive datatype" | same message |
| p08 goal Nonempty Nat (no Decidable) | Classical.byContradiction; axioms propext, choice, Quot.sound | same term |
| p11 goal True / p01 a=b | Decidable.byContradiction | same |
| p12 goal ¬¬Nonempty Nat | the negation path; no axioms | same term |
| p09 `by-contra: rfl` on a ≤ b | 478 "subst failed: invalid equality proof ... ¬a ≤ b" | same error, so 478 is Lean's answer |
| p10 plain `by-contra`, goal ¬(a=b) | this : a=b | same term |
| q03 `by-contra: -` | 84 | accepted (finding 2) |
| r01 h : False | rule 5 (absurd, of_decide_eq_false) | same term |
| r02 h : id False; r03 h : id Empty | rule 6, False.casesOn / Empty.casesOn after whnfD | same term |
| r04 False∧True; r05 ¬True | rule 5 (decide), not rule 6 | same term |
| r06 (x:Empty)(h:¬True) / r07 reversed | x by rule 6 / h by rule 5 | same term (order follows Lean) |
| r08 (x:Empty) ⊢ x=x; r09 two Empty | first local, Empty.casesOn | same term |
| r10 (h : a≤b)(x : Empty) | 99 | accepted (the indexed local is reached first; E4) |
| batch-h2: True, False∧a=a | 449 | fails |
| batch-h2: a≤b | 99 | fails |
Existing texts, base against branch: the base commit 3c622ac1 was extracted with git archive (the main checkout has moved on to 98f36c00). I ran the six .lf files that use by-contra or by-contradiction (batch-a x-cn-ctor, w-cn, close, x-cn-le; batch-c contra, w-bk) on decide-slice with `--steps -` and the term dump. Both outputs are byte-identical between base and branch. In batch-c test.fs only `by-contra: rfl` changes (99 to 478), and Lean agrees (p09).

B. Outcome layering, traced by hand
- `lfr-thrown-as?` matches only the outcome it is given, so `lf-tac-ported` maps only unsupported to 99. Full (6), exhausted (2), invalid (1) and rejected (4) are rethrown unchanged, and so is any non-Meta code.
- `lf-meta-try` returns false only for rejected; every other outcome is rethrown through lf-must.
- The changed throw sites contain no `rejected` throw (cases.fs, meta-induction.fs, generalize.fs).
- No lf-meta-catch caller reaches those words: tactic-run.fs:930, elab-pending, elab-term and instances only.
- At the tactic layer, `first` and `try` treat 99 and unsupported as non-Lean errors (lf-tac-lean-error?).
- So no refusal can be read as "this rule does not apply". The one gap is finding 1's untested rollback.
- generalize.fs:71 maps invalid to unsupported. That was 99 before as well, so no answer changes.

C. The export and the support code
- I reproduced it from the roots with `export-slice.py ~/.claude/work/IM/init.ndjson $(cat roots)`. That gives 1,073 declarations and 67,044 lines. After ndjson-reexport.sh its sha256 is ade176ae…, equal to the committed file and its manifest, so nothing was hand-edited.
- `bin/leanforth check` verifies the manifest by default. test_ndjson_emit.py round-trips the export. batch-h2 test.fs:26-33 fails if a listed declaration is missing.
- I did not regenerate the elaboration data, which needs a pinned-Lean export-elab run.
- The batch-d to batch-d2 split kept p-change-text unchanged, with the binders written out. Folders are found by the Makefile wildcard.
- sweep-view-anew: resetting before each run stops a refused run's leftovers from affecting later runs. For direct Meta calls, Lean's MetaM keeps state after a throw too, so the old accumulation never tested rollback. The text sweeps still exercise the tactic layer's restore. Low risk. To keep a signal, assert before lf-mctx-reset that the test's own goal was not left assigned.
- mv-any-delay, confirmed at mvars.fs:702 (called from mv-inst-run, :844): every lf-instantiate-mvars call loops over every metavariable declaration (`mv-exprs store-count @ 0 ?do i mv-ready-decl? or loop`), with no early exit. In addition, mv-spine-block (:839) allocates 2 cells per term of the whole term store on each call.
- Fix for a plan row: drop the pre-scan as Lean does. Lean's instantiateMVars looks up a head's delayed assignment only when its walk reaches that head, and mv-delay-rec already checks each head. If the flag stays, keep a count of delayed assignments in the mctx context record (ADR 0009), raised by mv-delay-set and restored by the trail on rollback, and scan only when it is nonzero, stopping at the first ready one.

D. Planted faults (in copies under scratchpad/review-e2b/f1-f4, git archive of 8b930bcc)
- F1, rule 6 also splitting a one-constructor type: caught (test.fs: `true-of … -> 449 true`).
- F2, lf-tac-ported also mapping full to 99: caught (the heap sweep aborted at test.fs:138).
- F3, `by-contra: NAME` dropping the name for `this`: caught (test.fs name check).
- F4, rule 6 without lf-commit-when: survived test.fs and check.py (finding 1).
- A clean copy passes check.py (exit 0).

Not looked at: batch-g test.fs's 90 changed lines in detail; batch-a test.fs on F4; gforth-fast and Gforth 0.7.3; the wording of LANGUAGE_REFERENCE and TACTIC_STATUS; regenerating the elaboration data. No make target, tier or suite was run. Probe files and outputs are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-e2b/ (p/, out/, probes.lean, lean.out, probes-wrong.lean, lean-wrong.out). An AI review does not replace the required human review.

## Resolution

On branch `tb2-patterns-e2b` after its rebase on main `98f36c00` (the reviewed commits `3c622ac1..8b930bcc` are `fe02ab1b..dfbe00b8` there), 2026-11-25:

1. Not testable today, recorded: `0fb3e1db`. No input makes `lf-goal-cases` throw a Lean error (rejected) on a type with no constructor and no index: mkCasesContext?'s "not applicable" is unsupported in cases.fs, meta-induction.fs and revert.fs throw only unsupported, the intro after the revert always meets a pi, and Lean's own induction errors need an index (slice E4); full and exhausted are thrown on and the runner undoes the tactic. contradiction.fs's header says so, the commit-when stays as Lean's (Contradiction.lean:79-81), and the planted fault `rule6-no-commit` is recorded with that reason as `equivalent`.
2. Fixed: `2d860263`. The leaf items `_`, `-` and `rfl` are a word list of their own (`pat-leaves`, `pat-leaf?`), searched by `pat-step` and by `lft-contra-item`, so each means in `by-contra:` what it means inside `by-contra[ ]`. New theorems `bc_clear_word` (`by-contra: -`) and `bc_anon_word` (`by-contra: _`) in batch-h2, node for node pinned Lean's (golden written by `check.py --lean`); test.fs's `by-contra: -` gives 449 where `by-contra: k` closes the goal (Lean: contradiction failed), and argument `pat-clear`. Fault `contra-rfl-as-name` moved, caught.
3. Fixed: `3cfca522` (lf-tac-ported's comment: every unsupported refusal inside the wrapped word, lf-whnf!'s, lf-infer!'s or a store's too, is 99; 93 before; neither a negative answer).
4. Fixed: `3cfca522` (lf-meta-try's comment: nothing undone on false, as Lean's MetaM try; wrap in lf-commit-when; batch-h2's test.fs: `lf-tac-ported` passes full and invalid on, `lf-meta-try` rethrows both).
5. Fixed: `5f472e89` (TESTING_STRATEGY.md, "Test exports cut from Init": the four commands).
6. Planned: plan row 9.4.8v (one test slice of Init: retire decide-slice for its superset, or extend decide's roots).
7. Fixed: `3cfca522` (pfr-closer's comment), then `57ee7bd0` (the closers named).
- S1: `ac545bce` and `2a3f3cd3`. `lf-unported ( -- )` in meta-must.fs beside `lf-made!`, used at 32 of the 34 sites; faults whose text quoted the phrase moved and caught (fe-rfl-non-eq, tb2-replace-holes-taken, tb2-delta-theorem, tb3a-rfl-heq-sides, tb3a-rfl-noneq-unsupported, decide-let-not-zeta, s3a-decide-let-node-unseen, rw-unknown-binder-explicit, lib-elim-tail-unchecked, lib-app-m-other-mvar-taken). `make cover-changed` counts every block on a changed line, so the change brought three older never-run blocks into the branch: app-builder.fs's `abl-closed` refusal is now tested (mkAppM over a metavariable of an outer depth); goal.fs's `mtg-is-eq` (its Eq branch runs only end to end) and constructor.fs's `mco-ctors` (an inductive with no data record, recorded coverage debt) keep `outcome-unsupported lf-must` until their unit tests exist (plan row 9.4.8t).
- S2 and S3: `57ee7bd0` (closers `pc-chev`, `pc-angle`, `pc-one`, `pc-rintro`, `pc-contra` and a CASE, ] with a tuple open its default, 473; meta-sweeps.fs's `/svl` record). Faults `contra-many-patterns` and `rintro-top-as-one` moved, caught.
- C, `mv-any-delay` and `mv-spine-block`: planned, plan row 9.4.8w, with the kernel-speed work's front-end items.
- C, `sweep-view-anew`'s assertion that the test's own goal is not left assigned: the goal is made inside each run and assigned when the run succeeds, so the check needs the run's goal and outcome kept for the reset (more than two lines); left in plan row 9.4.8u.

Baselines the branch sets: the style baseline of `tactics/by-contra.fs` globals 3 to 4 (the registry row `tac-k-by-contra-pat`, accepted above); the coverage baseline reasons of cases.fs and meta-induction.fs renumbered to their lines (`1d81aba2`), no count raised.

## Re-check of the fixes (2026-11-25)

The independent re-check of the fix commits (`dfbe00b8..2c49180f`) judged the "equivalent" record of fault
`rule6-no-commit` and found its reason to hold: exfalso runs outside the try, so the goal is False; without an
index none of Lean's index errors can arise; every other refusal of Meta cases on such a type is unsupported (99),
never Lean's kind of error; a let-bound local is refused at revert. It found no input that reaches the false path
before slice E4. Findings 2 to 7 and S1 to S3 verified (all 32 replacements by `lf-unported` read). One blocking
item, fixed in `6d32b34d`: Forth's word lists find a word whatever the case of its letters, so `by-contra: Rfl` and
`by-rintro[ RFL ]` were read as the `rfl` pattern where Lean names a hypothesis (inside brackets since slice E1;
after `by-contra:` since this round's fix of finding 2); `lfa-exact` (author/runner.fs) now makes a token with an
upper-case letter find no pattern word, with two tests and fault `pattern-word-any-case`. One note, not applied
(the sentence was not found as quoted): contradiction.fs's header should say that revert.fs also throws invalid,
a LeanForth fault, which is thrown on and never returned as false. Verdict: merge once the case fix is in.

