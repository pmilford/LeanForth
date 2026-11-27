FORTH REVIEW: small-tactics-2

**Range:** `b892c993..7975f210` (9 commits). Reviewed in worktree a worktree of its own.
**Verdict: blocking.**
**Findings by severity:** 3 blocking, 2 medium, 7 low, plus 6 style findings.

## Blocking

**B1. calc puts its new goals after the other goals; Lean puts them in front. LeanForth then accepts proofs that Lean refuses.**
- Where: `src/front/tactics/calc.fs:74-75` (`tcx-goals` calls `lf-goals-append`, which is appendGoals). The wrong order is also stated in the header at calc.fs:21-22 and :32, and in the `by-calc[` row of `docs/user/LANGUAGE_REFERENCE.md:2015` ("new goals after the others").
- Lean's evalCalc calls `pushGoals mvarIds`. Basic.lean:471 defines it as `mvarIds ++ s.goals`, so the new goals go to the front. A `trace_state` confirms the order `[left.calc_1, left.calc_2, right]`.
- Probe `cp_order` (`p/cp_order.lf` in the reviewer's scratch directory):
  - Goal `a = b ∧ c = c`, then `constructor`, `calc a = b := ?_`, `exact rfl`, `exact h1`.
  - Pinned Lean refuses it: Type mismatch `rfl … a = b`.
  - LeanForth accepts it (exit 0). Its step log after calc is `[right ⊢ c = c, left ⊢ a = b]`.
- `cp_tagged.lf` is the same: Lean refuses (expected `c = b`), LeanForth accepts.
- No test has other goals open when calc runs, so nothing catches this.
- Fix: follow Lean's order (pop the main goal, then push the new goals in front). For example:
  - add `: lf-goals-push ( list -- outcome ) lf-goals run-cat gl-set-ok ;` to goals.fs;
  - let calc's xt return `( val goals )`;
  - have `tcr-closing-unchecked` assign and pop the main goal, then `lf-goals-push`.
- Add `cp_order` and `cp_tagged` as accept/refuse twins, and fix the two docs.

**B2. The declared known gap lets LeanForth accept text that Lean refuses.**
- Where: `src/front/tactic-core.fs:293` (`lf-tac-rfl-reducible` uses only `lf-with-reducible`). rfl.fs's `trf-exact` → `lf-tac-ensure-type` reads `lf-tac-transparency`, which is the frame's setting, not the scope's.
- So inside rw's closing `rfl`, the `exact Iff.rfl` rule runs at the block's transparency: default outside a block, `all` inside `with_unfolding_all`.
- `gap_iff`: `(h : a = b) : (Nat.pred (Nat.succ a) = b) ↔ (b = b) := by rw [h]`.
  - Pinned Lean: "unsolved goals".
  - LeanForth: accepted on the branch, and also on main b892c993 (main already forced default in `lf-tac-defeq`).
- `gap_all` (the same inside `with_unfolding_all`): accepted on the branch, refused by Lean. This variant is new with this branch.
- The kernel still checks the term, so no false theorem gets in. But a Lean-refused text is accepted, and the docs (D.12, meta-must.fs:235-244) describe this only as "elaborates at default".
- Not affected:
  - HEq goals (`gap_heq`): 93, not supported (fails closed).
  - Eq goals (`gap_eq`): 89, as Lean.
- Fix, either of:
  - run the rfl row with the top frame's transparency set to reducible and restored with CATCH/THROW (sketch: `: lf-tac-at ( i*x xt mode -- j*x ) lfr-block-transp >r dup lfr-transp! ['] lf-meta-at catch r> lfr-transp! throw ;` with `lfr-transp! ( mode -- ) lfr-top tfr-transp !`). Batch-d's rwa then answers 93 per fault `sm2-block-transp-in-force`; that is acceptable because it fails closed.
  - or answer "not supported" in `trf-exact` when `lf-defeq-mode` differs from `lf-tac-transparency`.
- Add `gap_iff` and `gap_all` as refused twins.

**B3. Reuse rule (owner, 2026-11-13/18): a general combinator sits inside a module.**
- `ecl-each ( x1 x2 x3 xt -- y1 y2 y3 )` at `src/front/elab-calc.fs:107` is a general tri-map (Factor's `tri@`). No library word exists for it, and no other copy exists in `src/`.
- Fix: move it to `src/lib/lib.fs` as `tri@` with a test and a fault, or write `ecl-types!` and `ecl-levels!` without it.
- The fix is trivial, but the rule makes this blocking.

## Medium

**M1. Test gap in the checkedAssign change: an open metavariable plus an out-of-scope local is never tested.**
- On that path only `lf-meta-check-assignment` checks the scope (`goal.fs:436-446`).
- My fault `rv-checked-skip` (ignore the check's verdict) survived `batch-small-2/test.fs`, `check.py`, `tactic-lib.fs`, `tactic-basic.fs` and both rec-depth tests.
- My unit probe catches it: `m/zz-ca-probe.fs` in the reviewer's scratch directory (U1 below; caught in 1.0 s). Add U1 and plant the fault.

**M2. A natural `_` left in a calc proof (Lean's 461) is untested.**
- My fault `rv-new-goals-natural` (`true lf-tac-new-goals`) survived every test I ran.
- Under that fault, `calc a = b := _ … ; exact h1` would be accepted although Lean refuses it.
- My probe `cp_natural` shows the correct 461 today. Add it with a follow-up step.

## Low

1. **No test that a stopped run's frames are dropped.** `rv-run-anew-keeps` (tactic-run.fs:1161) survived. Add a test: a run that stops inside `by-with-unfolding-all`, then a new authoring run with a term proof that needs default transparency.
2. **Only the refusing side of the depth bound is tested.** `rv-weight-default` (weight 4) survived: only 119 nested blocks refused is tested, not 118 accepted.
3. **Three surviving faults on hard-to-reach conditions:**
   - `rv-fits-rhs-type-skipped`: the extension's rhs-type condition; needs a heterogeneous relation.
   - `rv-uv-swapped`: Trans's `u`/`v` levels are 0 in every test; needs a relation in Type. Record it as a gap.
   - `rv-ascribed-always`: probably equivalent.
4. **New public words have no direct stack-effect tests** (coverage class 3); they are only exercised through text: `syn-ascribe!`, `syn-ascribed?`, `lf-tac-new-goals`, `lf-close-main-goal-unchecked`, `lf-tac-diagnostics.`, `lf-elab-configured`, `lf-tac-transparency!`.
5. **Docs:**
   - `lf-tac-elab-must` and `lf-tac-transparency!` are missing from the interface headers of tactic-core.fs and tactic-run.fs.
   - D.12 (LANGUAGE_REFERENCE.md:3159) understates B2.
   - The by-calc row and calc.fs header are wrong about goal order (B1).
6. **First-hole ascription may differ for notation written as an application** (`∧`, `↔`, `∣`). Lean ascribes the type to the first hole of `_ ∧ p`; LeanForth's `ecl-first-leaf` does not descend into application nodes. Not probed end to end; the effect is probably only on error codes.
7. **`lf-calc-lhs`/`lf-calc-rhs` repeat `lf-meta-args2`** (meta-spine.fs:99). Could be `: ecl-parts ( e -- r a b ) dup lf-calc-rel swap lf-meta-args2 ;`.

Places where LeanForth answers "not supported" and Lean refuses (fail closed, mostly documented):
- `wn_calc_proof` and `cp_final_mis`: 131 where Lean reports a type mismatch.
- `wn_inst`: 139 where Lean reports a type mismatch.
- Error positions: LeanForth reports at the calc token, Lean at `step.term`.

## Trust and state (item 3)

- **`lf-close-main-goal-unchecked`** skips only `tcr-fresh-free` (logUnassignedAndAbort). That is Lean's `checkNewUnassigned := false` for calc (Tactic/Calc.lean:24). `checkedAssign` still runs, natural holes still give 461 through `lf-tac-new-goals false`, and the kernel still checks the finished term. Nothing bypasses the kernel.
- **Transparency restore:** `lfr-advance-at` uses `lf-meta-at` (CATCH/THROW). A refused nesting block is popped by `lfr-unopen`.
  - The `try` / `first` / `any_goals` handler paths keep the frame's transparency (wn_first2, wn_first3, wn_any).
- **Dropping frames:** `lfr-run-anew` runs only in `lf-author-begin`, which also resets the term store, so it cannot drop live frames. `lf-tactic-by`'s `lfr-fresh` also clears frames.
- **New globals:** none written after load.
  - `defer lf-tac-transparency`: set at load.
  - The `twr-mode-*` records: built at load.
  - `ecl-trans-frames` and `ecl-step-frames`: context slabs.
  - `tfr-transp` and the syntax node fields: in context records.
- **Addresses:** `ecf`, `ecs` and `lfr-top` are recomputed at every use; no absolute address is cached across a call.
- **`lfr-room` 24→32:** bounded by `lfr-roomy`'s abort at load.

## Probe table (LeanForth branch | main | pinned Lean 4.35.0)

**Calc accepted** (all: branch accepted with type/value equal node for node to Lean, including `Trans.trans.{0,0,0,1,1,1}` and the instances | main error 1, word absent | Lean accepted):
- `cp_eqlt` (= then <), `cp_lteq` (< then =), `cp_lelt` (≤ then <), `cp_ltlt3` (< < <)
- `cp_defeq`: left side `pred (succ b)`, defeq to the previous right side `b`
- `cp_holeplus`: `_ + 0 = c`
- `cp_holes3`: tags `calc_1`..`calc_3`, then `case calc_3` and `case calc_1`
- `cp_hole_ext`: order is the `?_` goal, then `calc.step`
- `cp_step_case`: `case step` finds `calc.step`
- `cp_one_hole`
- `cp_have`: calc inside `have … := by`
- `cp_try`: a failing calc (513) inside `try`
- `cp_later`: `a ≤ _ := ?_`, assigned by the next step
- `cp_mvar_goal`: `apply Nat.le_trans`, then calc closes `a ≤ ?m`
- `cp_wr`: calc inside `with_reducible`

**Calc refused or not supported:**

| Probe | Branch | Main | Lean |
|---|---|---|---|
| `cp_order` | **ACCEPTED** | error 1 | refused |
| `cp_tagged` | **ACCEPTED** | – | refused |
| `cp_ext_le` | 96 | – | Type mismatch |
| `cp_final_mis` | 131 | – | refused |
| `cp_ext_mis` | 131 | – | not run |
| `cp_natural` | 461 | – | 461 text |
| `wn_calc_lhs` | 513 | – | 513 |
| `wn_calc_proof` | 131 | – | Type mismatch |

**with_reducible accepted** (branch accepted, 14 lines equal to Lean's | main error 1 | Lean accepted):
- `wp_after`, `wp_nest`, `wp_first_out`, `wp_then`, `wp_allgoals`, `wp_iter`, `wp_try_in`
- `wp_any` (`any_goals` at default): accepted on both sides

**with_reducible refused:**

| Probe | Branch | Lean |
|---|---|---|
| `wn_back` | 96 | 96 |
| `wn_first_in` | 96 | 96 |
| `wn_then` | 96 | 96 |
| `wn_apply` | 380 | 380 |
| `wn_iff` | 97 | 97 |
| `wn_any` | 469 | 469 |
| `wn_first2` | 96 | 96 |
| `wn_first3` | 96 | 96 |
| `wn_inst` | 139, not supported | Type mismatch |

**Known gap:**

| Probe | Branch | Main | Lean |
|---|---|---|---|
| `gap_iff` | **ACCEPTED** | **ACCEPTED** | unsolved goals |
| `gap_all` | **ACCEPTED** | – | unsolved goals |
| `gap_heq` | 93 | – | refused |
| `gap_eq` | 89 | – | unsolved goals |

**Depth:**
- `rd_calc` (118 nested `with_reducible` around a three-step calc): accepted on both sides.
- `rd_iter` (50 nested around `iterate 134`): accepted on both sides.
- `rd_iter2` (`iterate 2` around 117 nested): LeanForth 99, Lean accepts.
- I found no mix where Lean runs out of recursion depth and LeanForth accepts. LeanForth has no term-level `by`, so calc step proofs cannot hold tactic blocks.

**checkedAssign unit probes** (`ca-probe.fs` in the scratch `p/` folder):

| Probe | Branch | Main | Lean |
|---|---|---|---|
| U1: open metavariable + stray local | 98 | 93 | refused |
| U2: `?g := succ ?g` | 98 | 93 | refused |
| U3: `?g := add ?m ?g` | 98 | 93 | refused |
| U4: metavariable of a wider context | not supported, not assigned | 93 | narrows and assigns |
| U6: open metavariable of the goal's own context | assigned | 93 | assigned |

**Verdict changes on main vs branch from checkedAssign:** "not supported" became refused (U1-U3) or assigned (U6). No case found where LeanForth now accepts and Lean refuses.

## Faults (mine; `scripts/mutants.py --list`, scratch copies, jobs ≤ 3)

The test column names the run where the verdict was decided: "test.fs" is `batch-small-2/test.fs` alone; "broad" is `batch-small-2/check.py`, rec-depth `test.fs` and `check.py`, `tactic-lib.fs` and `tactic-basic.fs` together, run only on the faults that survived test.fs.

| Fault | Result | Test |
|---|---|---|
| `rv-ascribe-dropped` | survived test.fs, caught by check.py | broad |
| `rv-fits-rhs-type-skipped` | survived | broad |
| `rv-extend-type-unchecked` | caught | test.fs |
| `rv-checked-skip` | survived the suite, caught by my probe | broad, then my probe |
| `rv-run-anew-keeps` | survived | broad |
| `rv-transp-not-restored` | caught | test.fs |
| `rv-weight-default` | survived | broad |
| `rv-new-goals-natural` | survived | broad |
| `rv-uv-swapped` | survived | broad |
| `rv-ascribed-always` | survived (probably equivalent) | broad |
| `rv-unchecked-checks` | caught | test.fs |

## Reuse

Searched:
- `FORTH_LIBRARY.md` and `LIBRARY_WORDS.md`, for combinators;
- grep across `src/` for `>r r@ execute rot`, `lf-term-first@ lf-term-second@`, `ok? 0= if lf-tac-elab-fail`, `lf-goals-append`, `lf-name-append-tag`;
- `check-duplicates.py`: "187 baseline groups, none new or grown";
- `check-lib-callers.py`: every lib file has a caller.

Results:
- The calc frames correctly use meta-must.fs's `lf-with-record` (70 users). `lib/frame.fs` is for DAG walks and does not apply.
- `lf-tac-elab-must` is a rename of the private `tcr-synthesized`, not a copy.
- `edc-tac-with` (elab-decl.fs:175) could be `lf-elab-configured dup lf-tac-elab-must`.
- Findings: B3 (`ecl-each`) and Low 7 (`lf-meta-args2`).

## Forth style

**Metrics** (11 changed files): 1000 words; 82% are 1-2 lines, 17% are 3-5 lines, none longer. Every word has a stack comment. 3 globals (registration rows), no locals, 36 deep shuffles, 99 return-stack operations.
- elab-calc.fs: 55 words, 5 deep shuffles, 8 return-stack operations.
- `check-forth-quality.py`: the ratchet holds. The calc.fs baseline row is the approved registration row; tactic-run.fs and goal.fs are within their baselines.

**Findings:**
- S1. `ecl-levels` (elab-calc.fs:121) walks six fields with `i cells +`, and `ecl-applied` reads twelve cells from `ecf-alpha`. Both rely on the layout of `/ecf`. Use `6 cells +field ecf-levels` and `12 cells +field ecf-args` with named index constants, or state the layout invariant at the structure.
- S2. `lf-calc-trans` returns a Lean error code that callers use as a flag (`?dup if` in `ecl-chain`, `if` in `tcx-tried`). Return `( x y true | x code false )`.
- S3. calc.fs: `tcx-calc` drops the target and tag that closeMainGoalUsing passes, and `tcx-target` re-instantiates `tb tb-want` on each of its four reads. Pass the target on the stack: `tcx-fit ( val vtype target -- val' )`.
- S4. `tcx-extend` calls `lf-calc-relation?` only for its flag, then `2drop drop`. Export a flag-only `lf-calc-rel? ( e -- flag )` (today's `ecl-rel?`).
- S5. with-reducible.fs:45-57 repeats the four-word registration three times. Factor it: `: twr-tactic ( mode kind c-addr u -- ) 2 pick lf-tactic-lean! tuck lf-tactic-mode! ['] lf-tac-all swap lf-tactic-action! ;`.
- S6. `ecl-next` (2 lines, `>r`, `tuck swap … swap`) would read better split: `ecl-step ( k -- proof type rhs )`, then `: ecl-next ( k -- ) ecl-step >r ecl-chain r> ecs ecs-prev ! ;`.

## Run and not checked

**Run:** Gforth 1.0.0 (`.tools/gforth/bin/gforth`, through `bin/leanforth` with `GFORTH` set) and pinned Lean 4.35.0 (binary called directly). About 45 probe files and unit probes, on the patterns slice. 19 faults in 3 `mutants.py` runs. `forth-metrics`, `check-duplicates`, `check-lib-callers`, `check-forth-quality`.

**Not checked:**
- `make cover-changed`, gforth-fast, Gforth 0.7.3;
- the implementer's fault list and suites;
- relations valued in Type, and universe levels other than 0/1 (no natural form for them);
- annotation through `∧`/`↔` end to end;
- multi-file runs for stale frames;
- the rows in TACTIC_INVENTORY.md and LEANFORTH_WORDS.md.

AI review does not replace the required human review.

All probe and fault files are in the reviewer's scratch directory (`p/` and `m/`); a copy is kept outside the repository, in the main checkout's untracked `.claude/work/small-tactics-2-probes/`.
## Resolution (fix round, 2026-11-26, branch `small-tactics-2-fix`)

The branch was rebased on main `c8c8a04b` (simp group 4 had landed); the reviewed commits
`b892c993..7975f210` are `778a340a..df773359` there (the registry golden written again with
`check_registry.py --write`), the fixes are `95cf7f93` (code, tests, faults, reference),
`50e79bbc` (plan row 9.4.8z12) and `95ee1d6a` (S5 taken back), and calc's reference section is
D.13 (simp's took D.12).

- **B1 fixed** (`95cf7f93`). Pinned Lean's `trace_state` after `constructor` and a calc with three
  `?_` and a last step gives `left.calc_1`, `left.calc_2`, `left.calc_3`, `left.calc.step`,
  `right`: the `?_` goals in order, `calc.step` last, all in front of the other goals.
  `goals.fs` gains `lf-goals-push` (pushGoals; no word did it before: the other pushers are
  `lf-goals-append`, `lf-replace-main` and the runner's unfocus); `lf-close-main-goal-unchecked`'s
  xt gives `( val goals )`, and the main goal is assigned and popped before the goals are pushed
  (Lean pops it first). `w-calc-order.lf` (the review's `cp_order` with `h2 : c = c`) and
  `w-calc-tagged.lf` are wrong twins refused with Lean's "Type mismatch" (96); `cc_order` is an
  accepted twin with `right` open beside the calc, its term equal to Lean's node for node and its
  step log in Lean's order. calc.fs's header and the `by-calc[` row are fixed. Faults
  `sm2-calc-goals-appended`, `sm2-calc-pushed-before-pop`, `sm2-goals-push-appends`.
- **B2 fixed** (`95cf7f93`), the review's first option: `meta-must.fs`'s `lf-tac-at ( i*x xt mode
  -- j*x )` sets the tactics' transparency (the top frame's, through the hook
  `lf-tac-transparency-to`, which `tactic-run.fs` sets) and the one in force, both put back by
  CATCH and THROW; `lf-tac-rfl-reducible` runs rfl's row in it. `w-rw-iff.lf` (`gap_iff`) and
  `w-rw-all.lf` (`gap_all`, inside `by-with-unfolding-all`) are refused with Lean's "unsolved
  goals" (89), outside a block and inside one. Batch-d's `rwa` on `¬ a ≤ c`, which the review
  expected to answer 93: Lean accepts it because Init's unification hint `Not p =?= p → False`
  fails at once against `Iff ?a ?a` (Iff is an inductive type: `p → False =?= Iff ?a ?a` is false
  with no assignment), so `exact Iff.rfl` is a Lean error that `try` takes back and `assumption`
  closes the goal. `defeq.fs` answered not supported for any Not side; it now ports that case (a
  Not side against a side whose whnfR has an inductive type or a constructor at its head: false,
  as Lean), anything else on a Not side still not supported (plan row 9.4.8z12 (m)). The text stays
  accepted, by Lean's rule, not by a looser check. Fault `sm2-block-transp-in-force` is re-pointed
  to a probe in `test.fs` (a LeanForth scope alone, `lf-with-reducible`, changes the transparency in
  force, not the tactics'): with rw's rfl setting both, batch-d no longer tells them apart. Faults
  `sm2-rw-rfl-scope-only`, `sm2-tac-at-unrestored`, `sm2-tac-at-frame-unset`, `sm2-hint-not-rigid`,
  `sm2-hint-other-side`, `sm2-hint-rigid-pi`. D.13 says what rw's closing rfl does now.
  **Verdicts changed by B2:** no text of the test suite (`make test` on the fix: every target but
  the style ratchet, fixed after, passed). Of the review's probes: `gap_iff` and `gap_all` accepted
  before, 89 now (Lean: "unsolved goals"); `gap_eq` 89 and `gap_heq` 93 unchanged; batch-d's `rwa`
  case accepted before and now (Lean accepts it).
- **B3 fixed** (`95cf7f93`) by the second option: `ecl-each` is gone; `ecl-types` and `ecl-sorts`
  read the three fields each, in Lean's order (inferType a, b, c, then getLevel α, β, γ; the
  tri-map applied its word to the third value first). A library `tri@` was the other way: no
  library file has room for it in the style ratchet (`bounds.fs` is at its baseline of
  return-stack operations, which this round may not raise), and the field reads need no
  combinator.
- **M1 fixed**: U1 is a unit test (an open metavariable beside a local out of the goal's scope:
  98, the goal open); fault `sm2-checked-assign-verdict-ignored` (the review's `rv-checked-skip`).
- **M2 fixed**: `w-calc-natural.lf` (`cp_natural` with a step after it: Lean's 461 and context,
  the step never run) and its unit test; fault `sm2-calc-natural-goal`.
- **Low 1 fixed**: a run that stops inside `by-with-reducible`, then a new authoring run whose
  term proof needs default transparency: accepted; fault `sm2-run-anew-keeps-frames`.
- **Low 2 fixed**: rec-depth's `test.fs` checks 118 nested `by-with-reducible` pass and 119 are 99;
  fault `sm2-wr-weight-default`.
- **Low 3 recorded**: the three surviving faults are known gaps in the comments of
  `tests/mutants/faults.d/batch-small-2.toml` (`rv-fits-rhs-type-skipped`: every relation LeanForth
  can write is homogeneous; `rv-uv-swapped`: no relation in Type has a form yet;
  `rv-ascribed-always`: probably equivalent), and relations in Type and heterogeneous ones are plan
  row 9.4.8z12 (k).
- **Low 4 fixed**: stack-effect tests of `lf-calc-rel?`, `syn-ascribe!`, `syn-ascribed?`,
  `lf-tac-at` (outside a run, inside one, after a THROW), `lf-elab-configured` (mode and flags),
  `lf-tac-transparency!` (a probe tactic), `lf-tac-new-goals` and `lf-close-main-goal-unchecked`
  (probe tactics: the new goal first, a bare natural metavariable refused), `lf-goals-push`
  (goals.fs), and `lf-tac-diagnostics.` (510's detail holds the hint).
- **Low 5 fixed**: `lf-tac-elab-must` is in tactic-core.fs's interface header and
  `lf-tac-transparency!` in tactic-run.fs's; D.13 now says what rw's closing rfl does; the goal
  order (B1).
- **Low 6 planned**: plan row 9.4.8z12 (k) (the first-hole ascription through `∧`, `↔`, `∣`).
- **Low 7 fixed**: `ecl-parts` and `ecl-sides` use `lf-meta-args2`.
- **Style**: S1 fixed by the layout invariant stated at `/ecf`; S2 fixed (`lf-calc-trans ( result
  rtype step stype -- x y true | x code false )`, faults `sm2-calc-result-not-checked` and
  `sm2-calc-goals-dropped` follow the new text); S3 planned (9.4.8z12 (k): calc.fs's baseline
  allows no deep shuffle, so passing the target down waits for a reshaping of the extension's
  words); S4 fixed (`lf-calc-rel?` public, `tcx-extend` uses it); S5 not taken: `scripts/check-tactic-plugins.py` reads each row setter's kind where it is written, so a shared registration word fails it (the reviewed head's `7975f210` had unrolled one for that reason; `95cf7f93` tried `twr-tactic`, `95ee1d6a` took it back); S6
  fixed (`ecl-sided`, then `ecl-next` in one line, no return stack). The reuse note:
  `edc-tac-with` is now `lf-elab-configured dup lf-tac-elab-must`.
- **Unchecked list**: TACTIC_INVENTORY.md's calc row points at D.13.

Checks run on the fix (Gforth 1.0.0, pinned Lean 4.35.0 called directly): the unit tests of
batch-small-2, batch-d, rec-depth, `tests/front/defeq.fs` and `tests/front/goals.fs`;
`batch-small-2/check.py` and `check.py --lean --write-golden` (Lean's golden gains `cc_order`;
Lean refuses the 10 wrong twins with the messages given); the review's probes again (every row of
its tables as before except `cp_order`, `cp_tagged`, `gap_iff`, `gap_all`, now refused as Lean
refuses them); all 24 faults of `faults.d/batch-small-2.toml` caught, with `fe-defeq-hints-off`,
`fe-meta-stuck-hints-run`, `fe-hint-proj-key`, `s2-hint-fuel-unsupported` and
`tf-synth-failure-is-125`; `make cover-changed` (every block on a changed line ran);
`forth-metrics.py`, `check-duplicates.py`, `check-forth-quality.py`, `mutants.py --check`. The
tier's run is recorded in the hand-back.
