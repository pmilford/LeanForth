# Tactic blocks: bullets, `<;>`, try, first, all_goals, repeat, `have := by` (piece F)

Status (2026-11-22): **designed; not reviewed, not approved, no code.** Written by the architect agent for plan
row TB2 (pieces of [TACTIC_STATUS.md](../development/TACTIC_STATUS.md), column "Removed by": F). The owner's page is
section 0; every new spelling there is the owner's decision. The design review
([DESIGN_STAGE_REVIEW.md](../development/DESIGN_STAGE_REVIEW.md)) comes before code. Paths of source files are relative
to the repository; Lean's are under the pinned toolchain's `src/lean/`.

## 0. One page for the owner

**What the user will write.** A block is an opening word, tactics, and `by-end`. Three examples beside Lean:

| Lean | LeanForth (proposed) |
|---|---|
| `constructor` / `· exact hp` / `· exact hq` | `by-constructor  · hp by-exact by-end  · hq by-exact by-end` |
| `constructor <;> assumption` | `by-constructor <;> by-assumption` |
| `first \| rfl \| exact h` ; `try rfl` | `by-first \| by-rfl \| h by-exact by-end` ; `by-try by-rfl by-end` |
| `have h : p := by assumption` | `p by-have-by: h  by-assumption by-end` |

**How it works, in Forth terms.** The reader already records a proof as a flat array of steps with parent links, and the runner already walks it with a stack of frames (one per open block), without recursion. Today a frame knows one behaviour: "run my steps, then no goal may be left". The design gives each frame a *mode* (a small record of execution tokens: what to do at the end of the steps, what to do when a step fails) and puts one CATCH in the flat loop. Every Lean combinator is then a mode of 5 to 15 lines; no combinator has code in the loop.

**Decisions asked (each a new spelling; recommendation first).**
1. Bullet: `·` (Lean's own character) with the ASCII twin `by-dot`, closed by `by-end`. Not `by-focus`: Lean has a different tactic `focus` (goals may be left over), which should keep that name. Not `-`: not verified to be free in terms. Cost to know: every bullet needs a `by-end`; implicit closing at the next bullet is ambiguous for nested bullets.
2. `t1 <;> t2`: Lean's token, written between the two tactics; t2 is exactly one tactic or one block. A fixed count after a word needs no closing word (the `by-have: h` pattern), so it does not break the list rule. Alternative: `t1 by-then t2... by-end`.
3. `have h : T := by tac`: `T by-have-by: h ... by-end` (same order as `T by-have-goal: h`). No block-valued term in the first version.
4. One closing word `by-end` for every block: yes, unambiguous (section 2).
5. `by-any-goals`, `by-repeat`, `by-focus` (Lean's `focus`): same pattern as the approved three.
6. Where Lean logs an error, admits the goal and goes on to report more errors, LeanForth stops at the first (the existing rule, tactic-run.fs:28, ADR 0021 D3). Same verdict, fewer messages.

**Risks.** (a) A failure swallowed by try/first that Lean would report: the one real trust risk; section 5 names three places and their tests. (b) `<;>` must re-order the record at read time (section 2). (c) Size is about 320 lines, not the brief's 190 (section 3). (d) The other agent's work on tactic-syntax.fs: slice 1 rebases on it. Nothing here confers validity: only the kernel accepts the term.

## 1. The mechanism

**What exists (verified by reading).** Record: `/tac` steps with `tac-parent`; a block's steps follow it (tactic-syntax.fs header; `lft-new`, `lft-opened`, `lft-close`). Frames: `trun-frames` slab, fields `tfr-step tfr-next tfr-rest tfr-log` (tactic-run.fs:189-192); `lf-tac-block ( i rest -- )` :451; `lfr-advance`/`lfr-loop` :519-520; `lfr-end-block` :517 always runs `trow-end` then `lf-tac-done`. Saves: `lf-tac-save/restore/commit` :639-662, last in first out, a save holds the frame count (`tsv-frames`) and step-log counts; `lfr-state-lost` :665. `lf-tac-lean-error?`, `lf-tac-forget-lean` (tactic-msg.fs:130-133). Block kinds are hard-coded in three places: `lfr-holder?` (tactic-run.fs:529), `lft-block-end` (a `case` on two kinds) and `lft-in-with` (tactic-syntax.fs).

**Read time.** No new record structure: a block is a step whose children are the following steps with it as parent; nesting is the parent chain. New: a block *shape*, `tac-shape-block ( flags -- shape )`, flags `bars` (holds `|` alternatives), `headed` (TAG NAMES `=>`), `values n`. `by-induction-with` (bars+headed), `by-case:`/`by-next` (headed) and `|` move onto it; `lft-block-end`, `lft-in-with`, `lfr-holder?`, `lfr-alt-right?` ask the shape or row, not the kind. In a `bars` block without `headed` (by-first) `|` opens a plain alternative step; a tactic before the first `|` is error 83. An empty block or alternative stays error 85.

**Run time.** Frame gains `tfr-mode` (address of a mode record, set from the row), `tfr-save` (-1 or a save), `tfr-todo`, `tfr-acc` (runs of goals), `tfr-n` (a count or flag), `tfr-recover`. Mode record: `mode-open ( frame -- )`, `mode-end ( frame -- )` (steps ran out; may reset `tfr-next` to run them again), `mode-fail ( frame -- )` or 0, flags `admits`, `no-recover`. The loop becomes `begin lfr-depth while ['] lfr-advance catch ?dup if lfr-failed then repeat`. `lfr-failed ( code -- )`: not `lf-tac-lean-error?` -> THROW on. Else walk frames from the top: a frame with `admits` and `tfr-recover` true -> THROW on (final, see recover); a frame with `mode-fail` -> `lfr-restore-to` its save (every newer save restored first), `lf-tac-forget`, run its `mode-fail`; none -> THROW on. Frame fields live outside the saved state, as Lean's loop variables do, so the alternative index and `tfr-acc` survive a restore. A mode's save is taken after its frame is pushed, so a restore keeps the frame. No module-level state: all in `trun` slabs of the checker context. `lfr-end-block` runs `mode-end` with the frame still on top, then pops.

**Modes, each a port.**
- **done** (by, `|` of induction, by-case:, bullet): `closeUsingOrAdmit` over `focusAndDone` (Basic.lean:344-361); `evalTacticCDot` BuiltinTactic.lean:176-185; `evalCase` :596-608 (also sets the tag anonymous; the bullet does not). End: unsolved -> 89 at the block's place; goals := rest. `admits`. This is today's behaviour.
- **focus** (`by-focus`, outer part of `<;>`): `evalFocus` :187, `focus` Basic.lean:332-338. End: goals := unsolved ++ rest (`lf-tac-unfocus` exists :441).
- **first** (by-first's alternatives): `evalFirst` :631-639 with `orElse` = `try withoutRecover x catch _ => y ()` (Basic.lean:436) and backtracking `tryCatchRestore` (:377-380). Every alternative but the last: save at open; end -> commit and close the by-first; fail -> restore, next alternative. The last alternative runs with no save and no `no-recover`, so **its error is the one reported** (as `tcr-alts` does today for xts). `no-recover` on the others.
- **try**: macro `first | t | skip` (Init/Tactics.lean:445): first mode with one alternative whose fail closes the block.
- **per-goal** (by-all-goals, inner part of `<;>`): `evalAllGoals` :229-253. Open: `tfr-todo` := goals. Each pass: next unassigned goal alone; end of pass: `tfr-acc` ++= unsolved; more goals -> `tfr-next` back to the first child. Lean's recover branch (:241-247: log, restore, admit, go on, then `throwAbortTactic`) becomes: recover true -> final error at the first failing goal; recover false -> `throw ex`, which the enclosing handler catches. Same verdict; later goals' messages not shown (decision 6).
- **any-goal**: `evalAnyGoals` :256-270. As per-goal with a save per pass; fail -> restore, the goal kept in `tfr-acc`; at the end with no success a new Lean error "Tactic failed on all goals:" (catchable). Does not set `no-recover` (Lean's does not).
- **repeat**: `evalRepeat`, Lean/Elab/Tactic/Repeat.lean:17-26 (`withoutRecover`, `while true` try/catch break; it is an elaborator, not the macro Init/Conv.lean:342 has for conv). Save per pass; end of pass -> commit, new save, again; fail -> restore, close. Lean has no bound; LeanForth's step fuel (`lfr-spend?` :245) ends a repeat that never fails with error 91, never caught. `repeat'` is `Meta.repeat'` = existing `lf-goals-repeat` (meta-tactic/repeat.fs:72), a different tactic, not in F.
- **`<;>`**: macro `focus (x; with_annotate_state; all_goals y)` (Init/Tactics.lean:451-456): a focus block holding t1 and a per-goal block holding t2. No mode of its own.
- **recover.** Lean's context flag `recover` (Basic.lean:42) is true except under `withoutRecover` (first's non-last alternatives, repeat). With it true, an admit point logs the error and the declaration fails whatever happens after. So `any_goals (· exact wrong)` is an error in Lean although any_goals "catches". `tfr-recover` is copied from the parent frame and cleared by `no-recover` modes; an error passing an `admits` frame whose recover is true is final. Without this rule LeanForth would accept text Lean rejects.

**Step log.** Unchanged words: each executed step gets an entry with `tlg-parent` = its block's entry (`lfg-fill` :495), the word as written (`lfr-spelling`). A restore already drops the entries of the failed attempt (`lfr-back-log` :645). A per-goal block logs its steps once per goal under the same parent. Known and unchanged: a block's own entry shows the goals at its opening, not at its end (not verified against the golden file).

## 2. Words and forms

| Lean | Proof text | Mode | Owner |
|---|---|---|---|
| `· tacs`, `{ tacs }` (:168) | `· ... by-end`, twin `by-dot` | done | decision 1 |
| `focus tacs` | `by-focus ... by-end` | focus | 5 |
| `try tacs` | `by-try ... by-end` | try | approved |
| `first \| a \| b` | `by-first \| a \| b by-end` | first | approved |
| `all_goals`, `any_goals` | `by-all-goals ... by-end`, `by-any-goals ... by-end` | per-goal, any-goal | approved / 5 |
| `repeat tacs` | `by-repeat ... by-end` | repeat | 5 |
| `t1 <;> t2` | `t1 <;> t2` | focus + per-goal | 2 |
| `have h : T := by tacs` | `T by-have-by: h ... by-end` | have-goal row, then done | 3 |

- **`<;>` at read time**: `<;>` amends the step just read, as `at:` does: `lft-wrap ( i kind -- )` moves steps i..end up one slot, adds 1 to parents >= i, and puts the focus block at i; then it opens the per-goal block, which the reader closes after exactly one step (or one block's `by-end`). Arguments are in their own store and do not move. `a <;> b <;> c` nests to the left, as Lean's `macro:1 x:tactic <;> y:tactic:2`.
- **`have ... := by`**: in Lean the tactic `have` is `refine_lift have ...; ?_` (Init/Tactics.lean:882, 912); the `by` becomes a synthetic metavariable run by `Term.runTactic` (SyntheticMVars.lean:474-513: `Tactic.run` on that goal alone, unsolved goals reported) when `runTermElab` synthesizes (ElabTerm.lean:31-41). `by-have-by:` runs `by-have-goal:`'s row (via `lf-tac-row`), then a done-mode block on the new goal: the same goal alone, the same "no goal left". Differences to record in TACTIC_STATUS.md: the new goal's tag, and when T's pending problems are synthesized (not verified to be identical). A block-valued term (`exact f (by simp)`) is needed for terms, not for `have`; it needs a re-entrant `lf-tactic-by` (today `lfr-fresh` :679 clears frames and saves, and there is one step record per declaration), so it goes with FE2, not F.
- **Is one `by-end` unambiguous?** Yes. Blocks nest strictly and the reader holds the innermost open one (`tac-read-open`, parent chain); `by-end` closes it, and an alternative first, as today. `|` belongs to the innermost open `bars` block; a `by-induction-with` inside a by-first alternative takes its own bars until its own `by-end`. `end NAME` is another token and needs every block closed (error 82 names the open one). `by-end` with no block open stays error 83. Not verified: that `|` and `·` are never term tokens (only `|`'s natural meaning in tactic-syntax.fs was found).

## 3. Reuse, new words, size

Generalised, not rewritten: `lf-tac-block`, frames and `lfr-loop` (all kinds); `lf-tac-focus`/`lf-tac-unfocus` (focus mode); `lf-tac-save/restore/commit`, `lfr-caught` (:669, to be exported as the one settle word), `lf-tac-lean-error?`, `lf-tac-forget`; `lf-tactic-alt!`/`trow-alt` (by-first's bars run through it, as induction's); `lft-header`, `lft-names-end`, `lft-alt-end` (block closing); `lf-tac-row` (have-by); `lf-goals-unsolved`, `lf-tac-only`, `run-cat`/`run-push`. Kept as they are for tactics that take xts inside one step: `lf-tac-try-lean`, `lf-tac-first-of` (tactic-core.fs:257-265); they share the settle word with the frames. Not used: `lf-commit-when` (meta-must.fs:193, metavariable context only; a block needs the whole saved state), `lf-goals-repeat` (it is `repeat'`).

New words:
- tactic-run.fs (about 70): frame fields; `lf-tactic-mode! ( mode kind -- )`; `lfr-failed ( code -- )`; `lfr-restore-to ( save -- )`; `lf-tac-again ( frame -- )` (steps from the first child); `lf-tac-close ( frame -- )`; `lf-tac-frame-save ( frame -- )`; `lfr-holder?` by row.
- new `src/front/tactic-blocks.fs` (LeanForth-specific library, about 120): `lf-block-mode: ( end-xt fail-xt|0 flags "name" -- )`; modes `blk-done blk-focus blk-first blk-try blk-per-goal blk-any-goal blk-repeat`; `lf-goals-next-open ( run -- goal run' true | false )`.
- tactic-syntax.fs (about 70): `tac-shape-block ( flags -- shape )`, `lft-wrap ( i kind -- )`, `lft-one-step ( -- )`, bars and closing by shape.
- new `src/front/tactics/blocks.fs` (about 45): the rows and spellings; have-by (15) in tactics/have.fs.
Total about 320 lines of Forth. The brief's 190 assumed four modes and no recover rule, no `<;>` re-ordering, no any-goal or repeat.

## 4. Slices (each ends in `bin/leanforth check FILE.lf` plus its pinned-Lean twin run)

1. **Mechanism, bullets, `have := by`, `by-focus`** (66,974 lines). Frame modes with done and focus, the block shape, existing blocks moved onto both (their goldens must not change), the CATCH in the loop with no handler mode yet. Tests: bullets three deep; a bullet leaving a goal (89 at the bullet); a bullet with no goal (90); a block left unclosed at `end NAME` (82); `by-end` with none open (83); empty bullet (85); have-by leaving a goal. Faults: mode-end skipped; rest goals dropped; done check removed; the shape's `bars` flag ignored.
2. **`<;>` and `by-all-goals`** (9,682). Tests: `<;>` after a tactic making 0, 1, 3 goals; chained `a <;> b <;> c`; t2 a block; all_goals where the second goal fails (error at that step, nothing accepted); an assigned goal skipped; `<;>` with no step before it. Faults: `lft-wrap` parent fix-up off by one; a pass's goals not accumulated; the assigned-goal test removed.
3. **`by-try`, `by-first`, `by-repeat`, `by-any-goals`** (545 plus every `<;> try ...`). Tests: an alternative that closes one goal and then fails is fully rolled back (goal open again, step log entries gone); all alternatives fail -> the last one's error and place; try around a failing bullet (caught: recover is off); any_goals around a failing bullet (final: recover is on) with a Lean wrong twin; any_goals failing everywhere; repeat that fails at once (no change), repeat that never fails (91); try three deep with the innermost failing. Faults: restore skipped; restore to the wrong save; last alternative given a save; recover flag not cleared / not inherited; the Lean-error gate removed.
Each slice: Lean twins with wrong twins in `tests/front/tactics/batch-f*/`, rows in TACTIC_STATUS.md and LANGUAGE_REFERENCE.md, `make cover-changed`. Slices 2 and 3 touch tactic-syntax.fs only for `<;>`; slice 3 is nearly confined to tactic-blocks.fs and tactics/blocks.fs.

## 5. Trust

Everything here is untrusted front-end code; a block only builds a term the kernel checks. Places a failure could be swallowed, and the test of each:
- A handler catching what is not Lean's error. Gate: `lf-tac-lean-error?` in `lfr-failed`. Tests: inside by-try, by-first, by-repeat and by-any-goals, a refusal sweep over every store claim (`tests/support/meta-sweeps.fs`), fuel set to each k below the passing count, and a step that answers not supported (80/93/99): each must end with that error's exit code, never accepted, never the next alternative.
- The recover rule above (any_goals over an admit point): a wrong twin Lean rejects.
- A restore or commit refused: `lfr-state-lost`, caught by nothing (exists); a sweep refuses each.
- try leaving the goal open: reaches `end NAME`'s done (89). Test: `by-try` over a wrong `by-exact` as the whole proof is rejected.
- A pass's partial goals kept after its rollback: `tfr-acc` is appended only at a pass's successful end; test with any_goals where the failing pass first created goals.
- A run that stops inside a block: saves forgotten by `lfr-forget-saves` (:677, exists); test two declarations in one file, the first failing inside by-try.

Not verified: that Lean's `SavedState.restore` drops logged messages (inferred from evalAllGoals keeping `msgLog` by hand, :243-245); which already-ported tactics use Lean's `throwOrLogError`; the current lines of tactic-syntax.fs and elab-term.fs in the other agent's worktree; `Init/Tactics.lean` `·` syntax line (only the evaluator was read).

Files read: src/front/tactic-run.fs, src/front/tactic-syntax.fs, src/front/tactic-alts.fs, src/front/tactics/case.fs, src/front/tactic-core.fs (240-270), src/front/meta-must.fs (120-200), src/front/meta-tactic/repeat.fs, src/front/tactic-msg.fs (126-133), src/front/tactic-api.fs (95-125), docs/development/TACTIC_STATUS.md, the TB2 word list (working note), docs/project/OWNER_DECISIONS.md (1869-1907), docs/design/TACTIC_PLUGINS.md (3.6); Lean under the pinned toolchain's `src/lean/` : Init/Tactics.lean, Lean/Elab/Tactic/BuiltinTactic.lean, Lean/Elab/Tactic/Basic.lean, Lean/Elab/Tactic/Repeat.lean, Lean/Elab/Tactic/ElabTerm.lean, Lean/Elab/SyntheticMVars.lean, Lean/CoreM.lean (800-812).
