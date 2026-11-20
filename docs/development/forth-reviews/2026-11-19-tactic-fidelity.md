# Forth review: tactic-fidelity, plan 9.4.8l's fidelity items (2026-11-19)

Branch tactic-fidelity, range 11fa22e9..b80169d3 (9 commits); reviewer forth-reviewer (Opus), independent of the implementer.

Findings: 0 high, 1 medium, 8 low (1 blocking: reuse). **Verdict: merge after fixes.**
- B1 must be fixed before the merge. It is a few lines.
- M1 and L1 add two tests. Their text is given below and was run on the head.
- L2 and L3 need plan rows. L4-L8 are small fixes.
- Every claimed change matches Lean 4.35.0's source and my pinned-Lean probes. None turns a refusal into a wrong acceptance (trust section).

## Findings

**B1 (low, blocking: reuse).** `mrf-rel-sides` (meta-tactic/goal.fs:275) is a third copy of an existing two-argument read.
- `no-sides` (nat-offset.fs:143) and `et-type-args` (elab-term.fs:171) have the same body: `dup lf-term-first@ lf-term-second@ swap lf-term-second@`.
- `lf-eq?` (app-builder.fs:99) uses the same phrase on its inner application.
- `mrf-binary?` (:272), "an application of two arguments or more", is the general test that goes with it.
- `check-duplicates.py` misses this: the body is five tokens, under its six-token threshold.
- Fix: put both words in meta-spine.fs, which nat-offset.fs and elab-term.fs already require:
  ```forth
  \ The last two arguments of f .. a b (unchecked: e is such an application).
  : lf-meta-args2 ( e -- a b ) dup lf-term-first@ lf-term-second@ swap lf-term-second@ ;
  \ Whether e is an application of two arguments or more.
  : lf-meta-app2? ( e -- flag ) dup lf-meta-app? if lf-term-first@ lf-meta-app? else drop false then ;
  ```
  Then delete `mrf-rel-sides`, `no-sides` and `et-type-args`, make `mrf-binary?` `lf-meta-app2?`, and write `lf-eq?`'s inner phrase as `lf-term-first@ lf-meta-args2`.

**M1 (medium, tests: outcome classes).** `lf-tac-with-synth`'s failure now goes through `lf-elab-code` (`tcr-synthesized`, tactic-core.fs:156). Only the 125 path is pinned.
- An invalid authoring error is a Lean error that `lf-tac-try-lean` catches.
- So the property that matters is this: an exhausted or unsupported synthesis with no recorded error stops as 138 or 139, keeping its class, never as 125.
- My fault r23b survives tactic-lib.fs. It reports every failure as 125 and keeps the detail:
  `dup ok? 0= if lf-tac-elab-detail drop lfa-e-elab-synth lf-tac-stop then drop`.
- Add this test after the 125 test (tactic-lib.fs:395). It passes on b80169d3 and catches r23b:
  ```forth
  : pend-starved ( -- ) pend-append 0 lf-meta-budget! ;
  T{ lf-elab-pending-reset lf-elab-error-reset ' pend-starved ' lf-tac-with-synth catch nip
     lf-meta-default-budget lf-meta-budget! lf-author-code dup lf-author-outcome
     -> lf-author-throw 138 outcome-exhausted }T
  ```
- Add an unsupported case the same way: stand a word in for `lf-elab-class?` that answers unsupported, and expect 139.
- Add r23b as a fault.

**L1 (low, tests: malformed shape).** `mrf-binary?`'s one-argument branch is never run.
- The tests give it no argument (`fr`) or three (an Eq); nothing gives it one.
- My fault r1 (`if drop true else drop false then`) survives tactic-lib.fs.
- With r1 planted, a one-argument relation reads a constant's fields as an application: WRONG NUMBER OF RESULTS.
- Add this test; it passes on the head and catches r1:
  `T{ s" Nat.succ" lf-mk-const0 fr lf-mk-app rel-code -> -4205 }T`.
- A goal Lean's applyRfl refuses this way is pinned-Lean probe r3 below: `def MyEq (a : Nat) : Prop := a = 0`, `MyEq 1 := by rfl` gives "Expected the goal to be a binary relation".

**L2 (low, Lean difference, a refusal; plan row).** A goal that is not an equation after whnf is refused with 93, both under rfl and under rw's trailing `try (with_reducible rfl)`. Lean's apply_rfl gives an error there, and in rw `try` catches it.
- Reproduced with `bin/leanforth check` on the S2 slice:
  ```
  theorem p_rw_le (a b c : Nat) (he : a = b) (h : b ≤ c) : a ≤ c := by rw [he]; exact h
  ```
  LeanForth stops with 93 at `by-rw[` (goal `b ≤ c`), on the head and on the base. Pinned Lean accepts it.
- `by-rfl` on `a ≤ b` is also 93, where Lean gives "The left-hand side…".
- Now that applyRfl is ported, the gap is small:
  - When eq_refl's whnf is no Eq but its head is a free variable or an inductive other than Iff, HEq and Eq, `exact Iff.rfl` and `exact HEq.rfl` must fail. Run `mrf-apply-rfl` there.
  - Unequal sides are then 97, which `try` catches. Equal sides stay 93 (@[refl] lemmas).
- Also name these in 9.4.8l or FE5; today they are cited as "plan FE5" only in comments, and FE5's row names none of them:
  - Rfl.lean:72-74's binary-relation error;
  - "No `[refl]` lemma registered";
  - the HEq.refl path;
  - the two exact alternatives.

**L3 (low, Lean difference, a refusal; plan row).** reduceNat?'s guard is `lf-menv-nat-name?`, so any `Nat.x` of one or two arguments counts (whnf.fs:559).
- Lean's list (WHNF.lean:1010-1034) has 15 names: `Nat.succ` (unary); `add`, `sub`, `mul`, `div`, `mod`, `pow`, `gcd`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight` (binary).
- Probe: `lf-meta-whnf` of `Nat.le 2 3` answers `-1 unsupported`; Lean's reduceNat? gives none and whnf keeps the term.
- This fails closed, so it is acceptable as a planned item. No row names it yet. Add one, or narrow the guard with a 15-name table.

**L4 (low, docs and tests).** goal-print.fs:38-42 says `lf-with-names` uses "the plain names when the codes find no room or a goal is printing".
- Inside a goal print it uses that goal's names: `gp gp-active @ if drop execute exit then`, as :217-219 and the `hidinside` test say. Fix the header.
- The no-room branch (`gp-codes!` refused) is untested: my fault r6 (`drop true gp gp-active !`) survives goals.fs.

**L5 (low, docs).** meta-must.fs:121-125 says `lf-defeq-elab-at` adds the elaborator's flags to the configuration in force.
- Lean's `setElabConfig` (Elab/Config.lean:61-62) also clears constApprox and quasiPatternApprox, once, when TermElabM starts.
- OR-ing gives the same configuration today: no caller holds those bits, and inside TermElabM a scope's bits stay set in Lean too. Say so.

**L6 (low, requires).** tactic-core.fs:168 uses `lf-with-assignable-opaque` (meta-config.fs) without requiring meta-config.fs. It loads through meta-must.fs. Add `require ./meta-config.fs`.

**L7 (low, tests).** Two more surviving faults:
- **r3:** `wm-no-value?`'s instantiated branch tests only `lf-meta-has-fvar?`. An argument assigned to a term that still holds an unassigned metavariable and no free variable then reads as a value. Add `?d := Nat.succ ?n` in a `Nat.add`, expecting none.
- **r24:** `lf-tac-elab-fail` without `lfa-see!` (the second position). This is unpinned, the same as `edc-tac-fail` was before the branch.

**L8 (low, rebase).** main moved: s2-debt merged, changing whnf.fs (`wm-none?`, `lf-whnf-stuck`), tests/front/whnf.fs, tactic-lib.fs and check_s2.py.
- `git merge-tree 11fa22e9 main b80169d3` merges every source and test file cleanly.
- It conflicts only in PLAN_DRAFT.md and PROJECT_PROGRESS.md.
- After the rebase, re-run whnf.fs, tactic-lib.fs and check_s2.py.
- P's plan text ("waits for s2-debt") is now stale: P is unblocked.

## Lean fidelity (4.35.0 source read; pinned Lean run on probes)
- **J.** `wm-no-value?` is withNatValue (WHNF.lean:976-985): no metavariable but a free variable gives none; otherwise it instantiates, then a metavariable or free variable gives none.
  - A refused instantiation answers "value perhaps", which is unsupported. This is tested with heap refusals.
  - `wm-open?` is the shared form of the old `ws-open?`.
  - `tcr-defeq` is elabTermEnsuringType's `withAssignableSyntheticOpaque <| isDefEq` (ElabTerm.lean:51-63).
- **Removing `tcr-opaque-free` is safe.** `de-assignable-mvar?` (defeq.fs:166-169) is Lean's isReadOnlyOrSyntheticOpaque (Basic.lean:1009-1016). A synthetic opaque goal then takes the same assignment path as a natural one: type check, scope and occurs checks. Unported cases stay unsupported, and the kernel checks the term.
  - Probe j1: `refine ⟨?o, ?h⟩; case h => exact fun (x : p) => x` closes in Lean.
  - Probe j2: `exact p` gives "Type mismatch … of sort `Type` but is expected to have type ?o of sort `Prop`". This is tactic-basic.fs's new 96 text, with `?m.1` for the test's untagged metavariable.
- **M2.** `lf-defeq-elab-at` ORs the elaborator's flags into the flags in force (see L5).
- **rfl.** The order holds:
  - Basic.lean:216-221 tries the newest rule first (getEntries is newest first) and reports the first registered rule's error.
  - So the order is exact Iff.rfl (Init/Core.lean:1042), exact HEq.rfl, eq_refl, then apply_rfl, whose error shows. Both exact alternatives fail on a type whose whnf is Eq.
  - eq_refl is MVarId.refl (Refl.lean:25-40): getType' is whnf, then instantiate (Util.lean:80-81), under withAssignableSyntheticOpaque (BuiltinTactic.lean:320).
  - applyRfl (Rfl.lean:67-97) is whnfR of the instantiated type, at least two arguments, then `approxDefEq isDefEqGuarded` without the opaque bit. Eq gives Eq.refl from the relation's level and type; any other relation is 93.
  - Probes: `0 = ?n + 1` gives 97 with `?n + 1`; `?o = r` closes; `R a a` gives "No [refl] lemma" (LeanForth 93); `MyEq 1` gives the binary-relation error (LeanForth 93).
- **212.** Probe text: "Type mismatch when assigning motive / fun n => Nat / has type / Nat → Type / of sort `Type 1` but is expected to have type / Nat → Prop / of sort `Type`". This is tactic-lib.fs's pin. Induction.lean:271-274 uses isDefEqGuarded, inferred type before the motive's.
- **S.** Probe: "failed to synthesize instance of type class / Append Type". LeanForth prints `@Append Type` (plan 8.6).
- **O and R** are pinned by s2w-case-under.lf and s2w-rw-lt.lf against their twins.
- **AB.** `wc-unfold-run` resumes the smart frame as `wc-loop` does. A "none" from reduceMatcher? gives e and false, as unfoldDefinition? does.
- **Tests changed from 93 to Lean's answers in tactic-basic.fs.** All four are right per the probes:
  - ?o is assigned `p → p`;
  - `p` gives 96 with the sorts;
  - `p = (q → ?m)` gives 97;
  - Ne p q and R p p p stay 93, which is Lean's binary-relation error and its @[refl] search.
- **The twins are real** and in the Lean files' dump lists:
  - rfl_id (`@Eq.refl.{1} Nat #0`) and w_rfl_id, w_rw_lt in s2-proofs.lean and s2-wrong.lean;
  - ap_exact (`@Nat.le_trans a b c h1 h2`) and w_ap_exact in goal-layer(-wrong).lean.
- **Items declared "not a difference":**
  - Agree with Q (cost and re-entrancy, with N), T (`ndrop` copy, receipt evidence) and U (import gate).
  - Agree with V: rewrite's new goals are arguments of heq inside the proof, so `lf-has-open-mvar?` of the instantiated proof alone gives the same 99.
  - Agree with W: `lf-elim-for`'s only caller passes induction? true.
  - P is a difference, a refusal, and is now unblocked (L8).
- **The two noticed gaps:**
  - The `Nat.` guard is acceptable as a planned item once the row exists (L3).
  - The printer differences are acceptable under plan 8.6: `@id Prop`, `@Append Type`, `↦` for `=>`, and addPPExplicitToExposeDiff. They are presentation only, and the comparisons cut those lines.

## Trust boundary
- A goal closes only when one of these holds; each closes the goal in Lean too:
  - eq_refl's isDefEq is true;
  - applyRfl's approxDefEq is true on an Eq;
  - exact's isDefEq is true.
- withNatValue's "none" requires Lean's own condition.
- New Lean errors that `try` catches:
  - 97 for metavariable sides, which needs a definite false from defeq;
  - 125 for a failed synthesis.
- Failures that are not Lean errors keep their class through the catalogue: 138 is exhausted, 139 unsupported, 60 full. M1 pins this.
- The kernel still checks every finished term.

## Reuse
- **Searched:** LIBRARY_WORDS.md, FORTH_LIBRARY.md, meta-spine.fs, app-builder.fs and term-eqv.fs.
- **Grepped all of src/ for these shapes:** `lf-term-first@ lf-term-second@ swap lf-term-second@`, `lf-term-first@ lf-term-app?`, `lf-meta-mvar-free? 0= … lf-meta-has-fvar?`, `lf-meta-defeq-guarded`, `lf-elab-error-term`, `✝`, `lf-with-…` scopes, `dup ok? 0= if … then drop`.
- **check-duplicates.py:** "205 baseline groups, … none new or grown" (head and base).
- **check-lib-callers.py:** clean (bigint.fs is planned, FE1i-4).
- **mutants.py --check** (read-only, in the worktree): 2913 entries, 0 stale, 0 unnamed.
- **Good:**
  - `lf-defeq-approx!` replaces apply's `ap-defeq`;
  - `wm-open?` replaces `ws-open?`;
  - `lf-tac-elab-detail` and `lf-tac-elab-fail` replace `edc-detail` and `edc-tac-fail`;
  - `lf-tac-type-mismatch` serves 96 and 212;
  - `lf-with-names` lives in goal-print.fs;
  - nothing general is in a plug-in (rfl.fs changed comments only).
- **Finding:** B1.

## Re-entrancy
- No new VARIABLE, VALUE or written CREATE in src/. The tests add `variable so` and `variable rr`.
- `lf-with-names` writes the context record `gp`: gp-view, gp-codes and gp-active.
  - It sets gp-active back to false on both paths (`hidthrows` test).
  - gp-view and gp-codes are left changed, but they are read only while gp-active is true.
- rfl's state stays in its `mrf` frame (`lf-with-record`), read through `slab-last`.

## Forth style
`forth-metrics.py --words 10` over the 11 changed source files, base to head:

| Measure | Base | Head |
| --- | --- | --- |
| Words | 779 | 793 |
| 1-2 lines | 70% | 70% |
| 3-5 lines | 29% | 29% |
| Over 5 lines | 0 | 0 |
| Globals | 0 | 0 |
| Locals | 0 | 0 |
| Deep shuffles | 28 | 28 |
| Return-stack operations | 113 | 117 |

- The return-stack growth is elim.fs (9 to 11: `mes-fits`'s `2>r dup 2r>`) and tactic-msg.fs (10 to 12: `lf-tac-type-mismatch`'s `>r … r>`). Both are short and idiomatic.
- No word is longer than five lines.
- Style finding: B1's `lf-meta-app2?` and `lf-meta-args2`. The rest are small, named words with accurate stack comments.

## What I ran
On `git archive` copies of b80169d3 and 11fa22e9, with Gforth 1.0.0, stdin `/dev/null` and `ulimit -u 500`:
- tests/front/whnf.fs, goals.fs, tactic-basic.fs and tactic-lib.fs: all pass on the head.
- coverage.py for goal.fs over tactic-lib.fs and tactic-basic.fs: no never-run block in the rfl words.
- 15 planted faults, plus the probe tests of M1 and L1:
  - caught: r2, r4, r5, r7 (elab.fs and tactic-lib.fs), r9, r17, r23 (through the detail only), and the control `tf-unfold-smart-frame-kept`;
  - survived: r1 (L1), r3 and r24 (L7), r6 (L4), r23b (M1), and r21 and r22 (near-equivalent: the sides are instantiated anyway).
- Pinned Lean 4.35.0 (binary run directly) on two probe files: j1, j2, r1-r4, n1, Append, 212 and the rw on a `≤` goal.
- `bin/leanforth check` on the S2 slice with p-rw-le.lf (head and base) and p-rfl-le.lf.
- forth-metrics, check-duplicates, check-lib-callers, mutants.py --check, and a read-only `git merge-tree` against main.

Not run:
- the implementer's suites, make targets and coverage ratchet;
- check_s2.py and tactic_check.py;
- gforth-fast and Gforth 0.7.3;
- Init and Mathlib.

This AI review does not replace the human review AGENTS.md requires.

## Fixes

Made on branch `tactic-batch-1` (which contains `tactic-fidelity`; the two merge as one stack), commit
`452144a8`, after the review, by the implementer of tactic batch 1. Each fault named below is in
`tests/mutants/faults.d/tactic-fidelity.toml` and was caught (`python3 scripts/mutants.py --only ...`).

| Finding | Resolution |
| --- | --- |
| B1 | `lf-meta-app2? ( e -- flag )` and `lf-meta-args2 ( e -- a b )` in `src/front/meta-spine.fs`, tested in tactic-lib.fs; `mrf-binary?` and `mrf-rel-sides` (goal.fs), `no-sides` (nat-offset.fs) and `et-type-args` (elab-term.fs) deleted, their callers on the shared words; `lf-eq?`'s inner phrase is `lf-term-first@ lf-meta-args2`. Faults `tf-app2-any-application`, `tf-args2-swapped`; `lib-eq-sides-swapped` and `tf-rfl-rel-unchecked` re-targeted. Fixed. |
| M1 | tactic-lib.fs: `pend-starved` (138, exhausted) as given; the unsupported case on `OfNat ?α 1`, stuck until default instances, whose class lookup a stand-in for `lf-elab-class?` answers unsupported (139; the review's Append Type never reaches that lookup, its instance search records 125 first). Fault `tf-synth-failure-is-125` (r23b). Fixed. |
| L1 | tactic-lib.fs: `Nat.succ r` is 93. Fault `tf-app2-any-application` (r1). Fixed. |
| L2 | Plan 9.4.8l item AF (applyRfl for other relations, its errors and the Iff/HEq alternatives). Planned. |
| L3 | Plan 9.4.8l item AG (reduceNat?'s 15 names). Planned. |
| L4 | goal-print.fs's header corrected; goals.fs: no room for the codes gives the plain name. Fault `tf-names-no-room-codes` (r6). Fixed. |
| L5 | meta-must.fs: the note on setElabConfig's constApprox and quasiPatternApprox. Fixed. |
| L6 | tactic-core.fs requires meta-config.fs. Fixed. |
| L7 | whnf.fs: `?sn := Nat.succ ?n` beside a literal is none (fault `tf-nat-value-fvar-only`, r3); elab.fs: a tactic term's error keeps its second position (fault `tf-elab-fail-no-see`, r24). Fixed. |
| L8 | Branch rebased on main earlier (merge 50ca107e); plan item P's text no longer says it waits for s2-debt (P stays open). Fixed. |
