# Design review: tactic blocks (TACTIC_BLOCKS.md, first version), 2026-11-22

Independent reviewer (Opus, not the author), against DESIGN_STAGE_REVIEW.md. Read from Lean's source and LeanForth's runner; nothing was run. Every finding is applied in the second version of the design (its "Review response" lists two refinements).

**Verdict: approve with changes.** The mechanism holds up: frames with modes, one CATCH, saves taken after the frame is pushed, and frame fields kept outside the save all fit lf-tac-save/restore (`lfr-back` cuts frames to `tsv-frames`, tactic-run.fs:648-651). The recover rule (section 1) and the `<;>` reading (section 2) are incomplete in ways that would accept text Lean rejects. Findings 1-6 must change before code.

**Findings**
1. **Must change.** have-by is Lean's `Term.runTactic`, which resets recover. `Tactic.run` starts a fresh context, so recover is true (Basic.lean:42, :111). The nested `by`'s unsolved goals are always logged, never thrown (SyntheticMVars.lean:514-517). Its thrown errors are logged when errToSorry is on, which is the outer recover (:529-537). The design copies `tfr-recover` from the parent, so a have-by leaving goals inside by-try or a non-last by-first alternative would be caught: LeanForth accepts, Lean rejects. Change: the have-by block sets recover true. Its unsolved-goals end is final whatever the parent's recover. An error escaping it is final when the parent's recover is true and thrown otherwise. Add a test: have-by leaving a goal inside by-try is rejected.
2. **Must change.** Term elaboration errors are logged under recover. `runTermElab` keeps errToSorry on when recover is true (ElabTerm.lean:31-39), and `elabTerm` then logs the error and returns sorry (TermElabM.lean:1654). Example: on goals `p ∧ q` and `r`, `any_goals exact ⟨hp, hq⟩` fails in Lean (I read this, did not run it). The design's any-goal mode catches goal 2's failure, keeps the goal, and a later `hr by-exact` is accepted. Change:
   - Sort errors into two classes. Logged under recover: the elaborator funnel `lf-tac-elab-fail` (tactic-core.fs:247), every `throwOrLogError` site, admit points. Thrown: `Tactic.elabTermEnsuringType`'s mismatch (`tcr-ensured`, :265) and ordinary tactic failures.
   - With recover true a logged-class error is final; any-goal catches only thrown-class errors.
   - `tcr-alts` and `lf-tac-try-lean` must clear recover for their non-last alternatives, as Lean's first-macros do (withoutRecover).
   - Add a column "logged under recover" to each row in TACTIC_STATUS.md, each with a pinned-Lean twin.
3. **Must change.** A failure inside all_goals is catchable by an enclosing any_goals. all_goals's recover branch logs, restores, admits the goal, then throws `throwAbortTactic` (BuiltinTactic.lean:241-253). any_goals's catch (:263-268, `tryCatchRestore` at Basic.lean:378-380) restores the state, and that restore includes the message log (Core `SavedState.restore`, CoreM.lean:421-424; the Term restore keeps only traces and info, TermElabM.lean:420-427). So `by-any-goals by-constructor <;> by-assumption by-end` failing on one goal and passing on another is accepted by Lean. The design calls it final and rejects with exit 4. Change: a per-goal failure with recover true is caught by the nearest enclosing any-goal frame, and is final only when none encloses it. Reword decision 6: "same verdict" is false where a later failure in the same any_goals pass or first/try attempt restores away an error Lean logged. Record that remaining case in TACTIC_STATUS.md as a known gap: LeanForth rejects where Lean accepts.
4. **Must change (trust).** Error 92 (`lfa-e-tac-record`) has outcome invalid (author/errors.fs:409-411). `lfr-own-code` maps every refusal of a goal-list or slab operation other than "full" to 92, including exhausted, unsupported and rejected (tactic-run.fs:375-377). `tmg-authored?` (tactic-msg.fs:127) therefore calls a LeanForth fault "Lean's error", and try/first/repeat/any-goal would swallow it and run the next alternative. Today's `lf-tac-try-lean` already has this hole. Change:
   - Give 92 a non-Lean outcome, or exclude it in `lfr-failed`.
   - Map exhausted to 91 and unsupported to 93 in `lfr-own-code`.
   - Add a sweep that refuses `lf-goals!` and `lf-goals-unsolved` inside by-try.
   - Add the meta budgets (whnf.fs:132, defeq.fs:129, synth, `lf-meta-spend?`) to section 5's fuel sweep. They surface as exhausted and are not caught today; pin that.
5. **Must change.** `<;>` reading, so section 2's "one by-end is unambiguous" holds:
   - (a) t1 is the open block's last direct child, which may be a closed block (`by-induction-with ... by-end <;> simp` is common). It is not `lf-tactic-count 1-`, which `at:` uses (tactic-syntax.fs:425-426).
   - (b) The per-goal block cannot close right after t2's word, because `at[ ]` amends the step after it. Close it lazily, at the next token that cannot extend t2: a tactic word, `<;>`, `|`, `by-end` or `end`. Those tokens must first close any pending `<;>` blocks; otherwise `· a <;> b by-end` closes only the per-goal block and the bullet is left open (82).
   - (c) `lft-wrap` must also fix `tac-inner` of the open block and of the new blocks, and `tac-from`/`tac-to` of the focus block. State that `tac-read-open` is below i.
   - Alternative to weigh: no record rewrite. Put a "then" step after t1, and have the runner push the focus frame before a step whose next sibling is a then-step.
6. **Must change.** Name scope. `lft-names-end` cuts hypothesis entries when a block ends (tactic-syntax.fs:385-386, :399). Blocks that leave goals (focus, `<;>`, try, first, all/any_goals, repeat) must not cut; otherwise `by-try by-intro: h by-end h by-exact` and `by-intro: h <;> ...` followed by `h` fail to read, or read a global `h`, where Lean accepts. Rule: done-mode blocks cut, the others keep their names. Decide one rule for names given inside by-first alternatives, and test it.
7. **Should change.** Step log:
   - If the alternative's own frame takes the save, that happens after `lfg-open` (tactic-run.fs:498-512), so a failed alternative's entry survives the restore. Put the first/try/repeat/any-goal save on the holder frame, taken before the loop advances to the alternative or pass; give that frame `mode-fail`.
   - Name the `tactic` strings for the new kinds. The schema pattern `^[a-z][a-z0-9_]*[?!']*$` (schemas/tactic-steps-1.schema.json:131-134) excludes `·` and `<;>`. Use cdot, focus, all_goals, any_goals, first, try, repeat, have, and update the schema's descriptions.
8. **Should change.** The bullet's no-goal check comes before the catch in Lean (Basic.lean:354), so error 90 is thrown, not admitted. Check before pushing the frame; otherwise the error "passes an admits frame" and becomes final inside any_goals.
9. **Should change.** The checklist's consumers table is missing. Contents to add:
   - FE2 nested `by` and simp dischargers run a block from inside a step. Make the loop run down to a base depth (`lfr-loop-from ( base -- )`) and give have-by `runTactic` semantics now, so they share one mode.
   - rcases/obtain patterns use `|` inside a bracket, so `lft-w-bar` must defer to an open pattern bracket.
   - `case a | b =>` re-runs its body per tag; that fits mode-end.
   - have with binders needs the `fun` wrapping, which is FE2 work.
   - conv fits as a mode.
10. **Should change.** Work in flight: the text still says `at:`, now `at[ ... ]`. Name the words both branches touch: `lft-w-at`/`lft-located`, `lft-block-end`, `lft-w-bar`, `lft-names`. Say that slice 1 starts after that branch merges.
11. **Note.**
    - repeat: Lean is bounded by maxHeartbeats through `checkSystem` (Basic.lean:192); it is not unbounded.
    - Missing tests: any_goals with no goals fails (BuiltinTactic.lean:269); `first` with one alternative is just that tactic, without withoutRecover (:637-638).
    - Say how the any_goals error prints the tactic's text (`indentD stx[1]`).
    - Block kinds are hard-coded in more than three places: also `lft-alt-end` :388, `lft-block` :454, `lft-not-pre` :310, `lfr-alt-xt` :424.
    - State that every pass of a repeating mode runs at least one step through `lfr-step`, so fuel bounds it.

**Your four questions**
- **Modes.** done, focus, first (last alternative run bare: yes, :637-638), try (= `first | t | skip`: yes, Init/Tactics.lean:445), repeat (withoutRecover, a restoring catch) and `<;>` (focus plus all_goals; `a <;> b <;> c` nests to the left) match Lean. per-goal and any-goal need findings 2 and 3.
- **all_goals failing on goal 2 of 3.** With recover true, Lean logs goal 2's error, admits goal 2, still runs goal 3, then aborts; the first error shown is goal 2's. With recover false it throws at goal 2 and never runs goal 3.
- **Trust.** The unlisted places are 92 and the meta budgets (finding 4).
- **One `by-end`.** It works with by-induction-with alternatives and by-case: as long as blocks nest strictly; only `<;>` breaks this (finding 5).

**Owner's questions (section 0)**
- **Q1 (bullet).** Right, and requiring `by-end` is the right call: indentation is the only other way to close a bullet, and the owner's rule forbids it. A translator from Lean would write the `by-end`s automatically. `-` is subtraction in terms, so say "taken", not "not verified".
- **Q2 (`<;>`).** Keep it (9,682 lines, and Lean users expect it). Fix the wording: the `by-have: h` analogy is about a fixed number of names. The honest argument is that t2 is one step that ends at its own word or its block's `by-end`, never at the end of a line. `<;>` is the only infix word and needs finding 5's close rule.
- **Q3 (have := by).** Tell the owner that `by-have-by:` will be redundant once FE2 allows block-valued terms (`T by ... by-end by-have: h`). Offer `T by-have-goal: h · ... by-end` as the zero-new-word option; it reaches the same verdict except under try/first (finding 1).
- **Q6 (stop at first error).** Reword it as in finding 3.

**Size and slices.** The body is about 100 lines, so within budget. The code estimate grows by roughly 50 lines with these changes. Slices are fine; give each one a named `.lf` file and add the tests from findings 1-8.

**Not verified**
- Nothing was run on pinned Lean; every Lean behaviour above comes from reading the source, including the ⟨hp, hq⟩ and any_goals examples.
- That Core's try/catch passes runtime exceptions through, and that `logException` ignores aborts.
- Which ported tactics' term errors go through `lf-tac-elab-fail`.
- Where runs (`run-cat`) are allocated.
- The other agent's branch.
- The Mathlib line counts.
- `·` as a word name on Gforth 0.7.3.
- The step-log goldens.
