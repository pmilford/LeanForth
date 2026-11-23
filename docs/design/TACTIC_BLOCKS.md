# Tactic blocks: braces, `<;>`, try, first, all_goals, repeat, `have := by` (piece F)

Status (2026-11-22): **designed and reviewed; the owner approved the spellings (OWNER_DECISIONS "Blocks in proof
text"). Slice 1 written and tested on its branch `tb2-blocks1`** (the hole of error 92 fixed, the modes and the
loop, `{ }`, `by-focus`, `by-have-by:`; `tests/front/tactics/blocks-1/`; Forth-reviewed
([2026-11-22-tb2-blocks1.md](../development/forth-reviews/2026-11-22-tb2-blocks1.md): merge after fixes, fixed on
the branch), not merged or done-checked yet; where it differs from this text: modes are made by `lf-block-mode ( ...
-- mode )` and kept as constants, as shapes are; a final error is a flag of the error record, `lfa-final`, not a
THROW code of its own; `{ }` is read, as Lean's parser reads it, and fails when run; the done, nested and focus
modes are in `tactic-run.fs`, which needs them for its own kinds, so `tactic-blocks.fs` waits for slice 2;
by-induction-with, `|`, by-case: and by-next are still told by kind tests, not on block shapes as "Read time" below
says: slice 2 moves them (plan row 9.4.8s, review finding 3); Lean's errToSorry is not modelled apart from recover:
slice 3 adds it (section 4, review finding 1)). Slice 1 is done (on main). **Slice 2 written and tested on its
branch `tb2-blocks2`** (`<;>`, `by-all-goals`; `tests/front/tactics/blocks-2/`), not reviewed, merged or
done-checked; where it differs from this text: the per-goal modes (`lf-mode-per-goal`, `lf-mode-then`) are in
`tactic-run.fs` beside the others, so `tactic-blocks.fs` still waits; a block's end pops its frame unless its mode
started the steps again (`lf-tac-again`), so `mode-end` keeps its stack effect; t1 is found by walking up from the
step before `<;>` (no field `tac-last`); `<;>` with no step before it is a code of its own, 468, not 86; the
per-goal modes admit (an error inside them is final where the block recovers, as Lean's logged one); plan row 9.4.8s is done there: by-induction-with, `|`, by-case: and by-next are on block shapes (flags `tac-block-bars`, `tac-block-headed`). Slice 3: not
started. Second version, by the architect
agent, after the independent design review
([2026-11-22-tactic-blocks.md](../development/design-reviews/2026-11-22-tactic-blocks.md): approve with changes, all
eleven findings applied, see "Review response"). Plan row TB2, piece F of
[TACTIC_STATUS.md](../development/TACTIC_STATUS.md). Paths of source files are relative to `src/front/` or the
repository; Lean's are under the pinned toolchain's `src/lean/`.

**Coordinator's rule on the open point of section 0** (the owner's "100% Lean by default": never rejected where Lean
accepts): where a logged-class error occurs while a handler frame that could still roll it back encloses it (with
recover true that is a by-any-goals pass), LeanForth answers **unsupported** (exit 2), not rejected, until "log and
carry on, as Lean" is built; outside such a frame the error is Lean's rejection. Slice 3 tests both.

Revision after the owner's decisions ("Blocks in proof text", docs/project/OWNER_DECISIONS.md) and the design review (the review linked above, findings 1-11, all applied; two refined, see "Review response"). Lean paths are under `.tools/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`.

## 0. One page for the owner

**What the user writes.** Braces are a block that must close its goal; a `by-` word opens a block that `by-end` closes.

| Lean | LeanForth |
|---|---|
| `constructor` / `· exact hp` / `· exact hq` | `by-constructor  { hp by-exact }  { hq by-exact }` |
| `constructor <;> assumption` ; `cases h <;> { simp }` | `by-constructor <;> by-assumption` ; `... <;> { ... }` |
| `first \| rfl \| exact h` ; `try rfl` | `by-first \| by-rfl \| h by-exact by-end` ; `by-try by-rfl by-end` |
| `have h : p := by assumption` | `p by-have-by: h  by-assumption by-end` |

**How it works, in Forth terms.** The reader records a proof as a flat array of steps with parent links; the runner walks it with a stack of frames, one per open block, without recursion. Each frame gets a *mode* (a record of execution tokens: what to do when its steps run out, what to do when one fails), and the flat loop gets one CATCH. Each Lean combinator is a mode of 5 to 20 lines.

**Decided (owner, 2026-11-22).** 1. Bullet = `{ tacs }`, no `·`, no `by-dot`. 2. `t1 <;> t2`, t2 one tactic or one block. 3. `T by-have-by: h ... by-end`. 4. `by-` blocks close with `by-end`, braces close themselves. 5. `by-any-goals`, `by-repeat`, `by-focus`. 6. Stop at the first error.

**Still open: one point on decision 6.** The review found that "the verdict is the same" is false in one case. Lean sometimes writes an error to its log and carries on; if a later failure inside the same `any_goals` pass or `first`/`try` attempt rolls the state back, the logged error is rolled back too, and Lean accepts. LeanForth stops at the logged error and rejects. So LeanForth is stricter there, never laxer. Recommendation: build it this way now, record the case in TACTIC_STATUS.md as a known gap with a Lean twin that pins it, and add a plan row "log and carry on, as Lean" (about 60 lines; it needs a goal closed provisionally during a run, which ADR 0021 D3 excluded so far). Reason: the gap can never accept a wrong proof, and closing it touches a trust rule that deserves its own review.

**Risks.** (a) A failure swallowed by try/first that Lean reports: section 5; one such hole exists on `main` today and is fixed first. (b) `{` and `}` become reserved words; no term or statement uses them today (implicit binders are `implicit:`), but Lean's set and structure braces in terms will need another spelling later. (c) Size is about 420 lines of Forth, not 320. (d) Slice 1 starts after branch `tb2-batch3b` (name lists, `at[ ]`) merges: both edit the same reader words. Nothing here confers validity: only the kernel accepts the term.

## 1. The mechanism

**What exists (read on main).** Steps `/tac` with `tac-parent`, a block's steps after it (tactic-syntax.fs). Frames `tfr-step tfr-next tfr-rest tfr-log` (tactic-run.fs:189-192), `lf-tac-block` :451, `lfr-advance`/`lfr-loop` :519-520, `lfr-end-block` :517. Saves `lf-tac-save/restore/commit` :639-662 (last in first out; a restore cuts frames to `tsv-frames` and the step log to its counts), `lfr-state-lost` :665. Block kinds are hard-coded in seven places: `lfr-holder?`, `lfr-alt-right?`, `lfr-alt-xt` (tactic-run.fs:529, 531, 424) and the reader's `lft-block-end`, `lft-in-with`, `lft-alt-end`, `lft-block`, `lft-not-pre`.

**Read time.** No new record structure. New: a block *shape*, `tac-shape-block ( flags -- shape )`, flags `bars`, `headed` (TAG NAMES `=>`), `cuts-names`, `self-closing` (braces), `one-step` (the `<;>` block). The seven places ask the shape or the row. `by-induction-with`, `|`, `by-case:`, `by-next` move onto it unchanged in behaviour.

**Run time.** Frame gains `tfr-mode`, `tfr-save` (-1 or a save), `tfr-todo`, `tfr-acc` (runs of goals), `tfr-n`, `tfr-recover`, `tfr-held` (the goals a `<;>` chain set aside, or -1). Mode record: `mode-open ( frame -- )`, `mode-end ( frame -- )` (steps ran out; it may start them again), `mode-fail ( frame -- )` or 0, flags `admits`, `no-recover`, `fresh-recover`. Loop: `lfr-loop-from ( base -- )`: `begin lfr-depth over > while ['] lfr-advance catch ?dup if lfr-failed then repeat drop`; `lf-tactic-by` runs it from 0. `lfr-end-block` runs `mode-end` with the frame still on top, then pops. Frame fields are outside the saved state (as Lean's loop variables), so counters and `tfr-acc` survive a restore. No module-level state.

**The save is on the holder frame** (review 7): by-first's own frame, and the block's own frame for try, repeat and any-goal, takes the save after its own step-log entry and before the alternative or pass starts; a restore then drops the failed alternative's entries, `|` included. by-first saves at open when it has two or more alternatives, and again after each failure unless the next alternative is the last.

**Two error classes** (review 1-3). Lean's `recover` flag (Elab/Tactic/Basic.lean:42) is true except under `withoutRecover` (:387): first's non-last alternatives (`orElse` :436) and repeat (Elab/Tactic/Repeat.lean:20). `tfr-recover` is copied from the parent frame, cleared by `no-recover` modes, set true by `fresh-recover`.
- **Thrown**: ordinary tactic failures; `tcr-ensured`'s type mismatch (tactic-core.fs:273); no goal (90); unsolved goals at the end of a block that is not an admit point; a failure inside by-all-goals (Lean logs, admits, then `throwAbortTactic`, BuiltinTactic.lean:241-253); "Tactic failed on all goals" (:269). A handler frame may catch these.
- **Logged under recover** (thrown when recover is false; for the term elaborator, when its own flag errToSorry is false, which slice 1 does not model yet, see the nested mode below): the term elaborator's funnel `lf-tac-elab-fail` (tactic-core.fs:247; Lean: `runTermElab` keeps errToSorry, Elab/Tactic/ElabTerm.lean:31-39, `exceptionToSorry` Elab/Term/TermElabM.lean:1654); every `throwOrLogError` site (Basic.lean:422-431); any error reaching an `admits` frame (`closeUsingOrAdmit`, Basic.lean:351-361: braces, `by-case:`, induction's `|`). **Always logged**: unsolved goals at a have-by block's end (Elab/SyntheticMVars.lean:514-517).
- Words: `lf-tac-recover? ( -- flag )`; `lf-tac-log-fail ( code -- )` (recover true: THROW `lfr-logged`, a code no handler catches, reported as that error; false: an ordinary failure); `lf-tac-no-recover ( i*x xt -- j*x )` clears the top frame's flag around xt. `lf-tac-elab-fail` and each ported `throwOrLogError` site call `lf-tac-log-fail`; `lf-tac-try-lean` and `tcr-alts` (tactic-core.fs:257-265) run their non-last alternatives under `lf-tac-no-recover`, as Lean's `first` macros do.
- `lfr-failed ( code -- )`: not a Lean error (section 5) or `lfr-logged` -> THROW on. Else walk frames from the top: an `admits` frame whose recover is true -> final; a frame with `mode-fail` -> `lfr-restore-to` its save, `lf-tac-forget`, run `mode-fail`; none -> THROW on.
- TACTIC_STATUS.md gets a column **"Logged under recover"** per word: which of its errors are in the logged class (for most: its term's elaboration errors), each with a pinned-Lean twin inside `any_goals`.

**Modes, each a port.**
- **done** (`{ }`, `by-case:`, induction's `|`, `by`): `evalTacticSeqBracketed` BuiltinTactic.lean:167-173 (`evalTacticCDot` :176-185 is its copy), `evalCase` :596-608. The opener checks for a goal *before* pushing the frame (`lf-tac-focus`, error 90 thrown: Basic.lean:354 is outside the catch; review 8). End: unsolved -> 89; goals := rest. `admits`.
- **nested** (have-by): `Term.runTactic` (SyntheticMVars.lean:474-537) over `Tactic.run` (Basic.lean:95-111, a fresh context: `fresh-recover`). End: unsolved -> always final. An error leaving it: final when the *parent's* errToSorry is true (:530-534), thrown otherwise (:536). Lean's errToSorry is a term-level flag apart from recover: `runTermElab` clears it when recover is false (ElabTerm.lean:31-39), and `Tactic.run`'s fresh context resets recover but not errToSorry, so inside a have-by inside a no-recover frame a term error is thrown. Slice 1 reads the parent's recover in place of its errToSorry and the have-by's fresh recover for its term errors, so today such an error is final where Lean throws it: stricter than Lean, never laxer, and no text can reach it until by-try and by-first exist (slice 3 adds the frame field `tfr-sorry`, section 4). The same mode serves nested `by` in terms later.
- **focus** (`by-focus`): `evalFocus` :187, `focus` Basic.lean:332-338. End: goals := unsolved ++ rest (`lf-tac-unfocus`).
- **first**: `evalFirst` :631-639; restoring catch `tryCatchRestore` Basic.lean:377-380. Non-last alternatives: `no-recover`; end -> commit, close by-first; fail -> restore, next. The last alternative runs bare with the inherited recover, so its error is the one reported; one alternative alone is just that tactic (:637-638).
- **try**: macro `first | t | skip` (Init/Tactics.lean:445): one saved alternative; fail closes the block.
- **per-goal** (`by-all-goals`, the `<;>` block): `evalAllGoals` :229-253. `tfr-todo` := goals; each pass the next unassigned goal alone; pass end: `tfr-acc` ++= unsolved; then `lf-tac-again` or goals := `tfr-acc`. No `mode-fail`: its failure is a thrown error, caught by an enclosing handler (with recover true only an any-goal frame can be one) unless an `admits` frame lies between.
- **any-goal**: `evalAnyGoals` :256-270: save per pass; fail -> restore, goal kept; no success, or no goals at all -> thrown error with the block's own source text (Lean prints `indentD stx[1]`; LeanForth prints its text from `tac-from`..`tac-to`, so the message's second part differs by design). Does not clear recover.
- **repeat**: `evalRepeat` Repeat.lean:17-26: `no-recover`; save per pass; pass end -> commit, save, again; fail -> restore, close. Lean is bounded by `checkSystem` in `evalTactic` (Basic.lean:192, maxHeartbeats); LeanForth by step fuel: a block holds at least one step (error 85) and every step passes `lfr-step`, so each pass spends fuel and ends in 91, never caught.
- **`<;>`**: macro `focus (x; all_goals y)` (Init/Tactics.lean:451-456), section 2.

**Step log.** Entries as today (`lfg-fill` :495, parent = the block's entry). `tactic` strings for the new kinds, valid for the schema pattern (schemas/tactic-steps-1.schema.json): `braces`, `focus`, `all_goals`, `any_goals`, `first`, `try`, `repeat`, `have`, `and_then`; the schema's descriptions updated. A per-goal block logs its steps once per goal. Unchanged: a block's own entry shows the goals at its opening.

## 2. Words and forms

| Lean | Proof text | Mode | Names given inside |
|---|---|---|---|
| `· tacs`, `{ tacs }` | `{ ... }` | done | cut at `}` |
| `focus` | `by-focus ... by-end` | focus | kept |
| `try` | `by-try ... by-end` | try | kept |
| `first \| a \| b` | `by-first \| a \| b by-end` | first | kept, of every alternative |
| `all_goals`, `any_goals` | `by-all-goals ... by-end`, `by-any-goals ... by-end` | per-goal, any-goal | kept |
| `repeat` | `by-repeat ... by-end` | repeat | kept |
| `t1 <;> t2` | `t1 <;> t2` | per-goal, with `tfr-held` | kept |
| `have h : T := by tacs` | `T by-have-by: h ... by-end` | have-goal's row, then nested | cut at `by-end`; `h` stays |

**Name scope** (review 6). Only done and nested blocks cut hypothesis names when they close (`lft-names-end`); the others leave goals behind and keep them, to the end of the enclosing done block. So `by-try by-intro: h by-end h by-exact` reads. A hypothesis node holds a name, resolved in the goal's context when its step runs (`lft-hyp-node`), so a name from a by-first alternative that did not run fails at run time as Lean's unknown identifier does (message per TACTIC_STATUS row NR); the same name in two alternatives is one name.

**Braces.** `{` opens; `}` closes the innermost open block, which must be a brace. Cases:
- by-first: `by-first | { a } | b by-end` reads; a `|` belongs to the innermost open block after its current alternative is closed, so `|` inside a brace inside by-first is error 83.
- `by-induction-with` alternatives and `by-case:`: `| zero => { ... } ...` and `by-case: t => { ... } by-end` read; the brace is one step of the alternative.
- `}` while a `by-` block or an alternative is innermost: 83, with that block's place as the second place. `}` with only `by` open: 83.
- `by-end` while a brace is innermost: 83, with the `{`'s place. `end NAME` with a brace open: 82 naming the `{` (existing `lft-closed`).
- `{ }` empty: 85, as other blocks (not verified that Lean's parser refuses an empty `{ }`).
- `{` and `}` join the printer's reserved list (`lf-pf-reserve-more`, present/print-forth.fs), so `lft-no-word` refuses them as hypothesis names (84) and a binder so named is 78.
- Verified by grep: no LeanForth word `{` or `}` in author/words.fs, front/reader.fs, syntax.fs; implicit binders are `implicit:` (reader.fs:274, words.fs:153); `{` is only printed (present/print-tokens.fs:39).

**`<;>`: a "then" step, no record rewrite** (review 5; the reviewer's alternative chosen). `<;>` first settles (below), takes t1 = the open block's last *direct child* (kept per block in a new field `tac-last`; it may be a closed block such as `by-induction-with ... by-end`; none: 86), sets the flag `tac-then` on t1 and opens a `one-step` per-goal block after it. Run: before a step with `tac-then`, the parent frame sets `tfr-held := lf-tac-focus` if it holds none; when a then-block ends and does not itself carry `tac-then`, the parent unfocuses with `tfr-held`. `a <;> b <;> c` is one focus, two per-goal passes, one unfocus: the same goals as Lean's left-nested `focus(focus(a; all b); all c)`. `lf-tac-again` and `mode-fail` clear `tfr-held`. Why not move the records (the first design's `lft-wrap`): moving steps i..end means fixing parents, `tac-inner`, `tac-from`/`tac-to` and every index other words hold, in files a second branch edits; the flag keeps "a step never moves" and `lfr-record-ok?` as it is, for one flag test per step.
**Lazy close** (`lft-settle ( -- )`): a `one-step` block that has its one child, closed, is closed at the next token that cannot extend that child: any tactic word, `{`, `}`, `<;>`, `|`, `by-end`, `end`. `at[ ... ]` does not settle: it amends t2. A `one-step` block still empty at `}`, `by-end` or `end` is 85.

**One `by-end`.** Blocks nest strictly and the reader holds the innermost (`tac-read-open`); with settle before every closer, `{ a <;> b }` closes the then-block and then the brace. `end NAME` needs every block closed (82).

## 3. Reuse, new words, consumers, size

Reused: `lf-tac-block`, frames, `lf-tac-focus`/`lf-tac-unfocus`, `lf-tac-save/restore/commit`, `lfr-caught` (:669, exported as the one settle word), `lf-tac-forget`, `lf-tactic-alt!` (by-first's bars), `lft-header`, `lft-names-end`, `lft-alt-end`, `lf-tac-row` (have-by), `lf-goals-unsolved`, lib/runs.fs. Kept for tactics that take xts in one step: `lf-tac-try-lean`, `lf-tac-first-of`, now with `lf-tac-no-recover`. Not used: `lf-commit-when` (metavariable context only), `lf-goals-repeat` (it is `repeat'`).

New, by file:
- author/errors.fs, front/tactic-msg.fs (30): a "Lean's error" bit per code, set where a code is registered (`lfa-lean,`); `lf-tac-lean-error?` reads the bit.
- front/tactic-run.fs (95): frame fields; `lf-tactic-mode! ( mode kind -- )`; `lfr-loop-from ( base -- )`; `lfr-failed`; `lfr-restore-to ( save -- )`; `lf-tac-again ( frame -- )`; `lf-tac-close ( frame -- )`; `lf-tac-frame-save ( frame -- )`; `lf-tac-recover?`, `lf-tac-log-fail`, `lf-tac-no-recover`; the `tac-then` test in `lfr-go`; `lfr-own-code` corrected.
- new front/tactic-blocks.fs (150): `lf-block-mode: ( open-xt end-xt fail-xt|0 flags "name" -- )`; modes `blk-done blk-nested blk-focus blk-first blk-try blk-per-goal blk-any-goal blk-repeat`; `lf-goals-next-open ( run -- goal run' true | false )`.
- front/tactic-syntax.fs (75): `tac-shape-block`, `lft-settle`, `lft-w-brace`, `lft-w-brace-end`, `lft-w-then`, `tac-last`, `tac-then`, closing and bars by shape, the name-scope flag.
- new front/tactics/blocks.fs (55): rows, spellings, Lean names; tactics/have.fs (+20): have-by; tactic-core.fs (+15).
About 440 lines with comments counted as today's files do, 420 without the status-table work. The first estimate (320) lacked the error classes, the Lean-error bit, the nested mode and the lazy close.

**Consumers** (review 9):
| Later work | What it uses from F | What F leaves ready |
|---|---|---|
| nested `by` in terms (FE2), simp dischargers | `blk-nested`, `lfr-loop-from` called from inside a step with the current depth | Forth recursion only as deep as the text nests `by`; `lf-tactic-by` must stop clearing frames (`lfr-fresh` :679) when FE2 lands |
| rcases/obtain patterns (E) | `|` inside a pattern bracket | inside an open bracket list a bar is that list's item (a pattern bar), also at a line's start, and the list's own reader takes it; outside brackets a bar at a line's start begins an alternative ([TACTIC_PATTERNS.md](TACTIC_PATTERNS.md), section 2) |
| `case a \| b =>` | the body run once per tag | `lf-tac-again` in a mode-end |
| have with binders | `fun` wrapping | FE2; have-by's row unchanged |
| conv | its own mode and goal kind | `lf-block-mode:` |
| `repeat'`, `iterate`, `fail_if_success`, `case'` | modes of a few lines | the same |

**Work in flight** (review 10): `tb2-batch3b` edits `lft-w-at`/`lft-located` (now `at[ ... ]`), `lft-block-end`, `lft-w-bar`, `lft-names`. Slice 1 starts on main after it merges.

## 4. Slices (each ends in `bin/leanforth check FILE.lf` and its pinned-Lean twin run)

Each folder holds `test.fs`, `check.py`, `steps.golden`, a Lean twin and a wrong twin (`NAME.lean`, `NAME-wrong.lean`), and a `faults.d/NAME.toml`.

**Slice 1, `tests/front/tactics/blocks-1/`: the fix, the mechanism, braces, have-by, by-focus (about 67,000 Mathlib lines).**
First commit: the hole on `main`. Confirmed by reading: `lfr-own-code` (tactic-run.fs:375-377) turns every refusal other than "full" into 92; 92 has outcome invalid (author/errors.fs:409-411); `tmg-authored?` (tactic-msg.fs:127) calls any invalid authoring error Lean's; so `lf-tac-try-lean` and `lf-tac-first-of` (used today by by-trivial, by-rfl, by-rwa and others) take a refused goal-list operation for a failed alternative. Fix: the Lean-error bit (default: not Lean's), `lfr-own-code` mapping exhausted to 91 and unsupported to 93, and a sweep in `test.fs` that refuses `lf-goals!`, `lf-goals-unsolved` and each slab claim in turn inside `lf-tac-try-lean`. Not verified: that `lf-goals!` can answer anything but full or invalid today.
Files: `braces.lf` (two and three deep, inside induction alternatives and `by-case:`), `have-by.lf`, `focus.lf`, `brace-errors.lf` (goal left 89; no goal 90; `}` stray; `{` open at `by-end` and at `end`; empty; `{`/`}` as a name 84/78; `|` inside a brace), `blocks-1-wrong.lf`. Existing goldens of induction and case must not change. Faults: mode-end skipped; rest goals dropped; the no-goal check moved after the push; names not cut at `}`; own-code mapping reverted.

**Slice 2, `tests/front/tactics/blocks-2/`: `<;>` and by-all-goals (about 9,700).**
Files: `and-then.lf` (t1 leaving 0, 1, 3 goals; `a <;> b <;> c`; t1 a closed `by-induction-with`; `<;> { ... }`; t2 followed by `at[ ]`; `{ a <;> b }`), `all-goals.lf` (second of three goals fails: error at that step; an assigned goal skipped), `then-errors.lf` (`<;>` with no step before it; nothing after it; a name given by t1 used after the chain). Faults: `tfr-held` not cleared on a re-run; unfocus after the first of two thens; settle skipped before `}`; pass goals not accumulated.
Also in slice 2 (plan row 9.4.8s, review tb2-blocks1 finding 3; slice 1 did not do it): by-induction-with, `|`, by-case: and by-next move onto `tac-shape-block` with the `bars` and `headed` flags, as "Read time" (section 1) says, so `lft-settle` treats every closer alike; the kind tests that go are tactic-run.fs's `lfr-fixed-block?` and `lfr-block-word`'s by/`=>` choice, and tactic-syntax.fs's `lft-block-end` (its `case`), `lft-alt-end`, `lft-in-with` and `lft-not-pre`; `lfr-holder?` then asks the shape alone. The goldens of induction and case must not change.

**Slice 3, `tests/front/tactics/blocks-3/`: by-try, by-first, by-repeat, by-any-goals (545, plus every `<;> try`).**
Files: `try.lf`, `first.lf` (an alternative that closes a goal and then fails is rolled back, its log entries gone; all fail: the last one's error; one alternative alone), `repeat.lf` (fails at once; never fails: 91), `any-goals.lf` (no goals; all fail; a failing by-all-goals inside it is caught), `recover.lf` (have-by leaving a goal inside by-try: rejected; a brace failing inside by-any-goals: rejected; inside by-try: caught; a term that does not elaborate inside by-any-goals: rejected, the review's `⟨hp, hq⟩` example once `<< >>` exists, an ill-typed application until then; the known gap pinned), `names.lf` (names out of by-try and by-first), `refusals.lf` and the sweeps of section 5; blocks three deep. `mvars.fs`'s `lf-mvar-named` (findUserName?) must not see the metavariables of a rolled-back alternative, which it does today because it searches every metavariable the declaration made and records are never reused: a `?: x` made in a failed by-first alternative would make the next alternative's `?: x` answer 139 where Lean goes on (review tb2-batch3b 11; a test in `names.lf`). Faults: restore skipped; restore to the wrong save; the last alternative given a save; recover not cleared, not inherited, not reset by have-by; `lf-tac-log-fail` made an ordinary throw; the Lean-error bit set by default.
**Task of slice 3: Lean's errToSorry** (review tb2-blocks1 finding 1; section 1, the nested mode). A frame field `tfr-sorry`: at push, a `fresh-recover` mode sets it to the parent's sorry AND the parent's recover, any other mode copies the parent's sorry, the first frame takes true. `lf-tac-logged` makes an error final only when the top frame's recover and sorry are both true; `lfr-final-at?` reads the frame's own `tfr-sorry` for nested modes and keeps the recover below it for done modes (closeUsingOrAdmit reads only recover). Pinned by twins: the review's Q8, `by-probe-try b a = by-have-by: j << ' h >> by-exact by-end by-end ' h by-exact` (blocks-1 `test.fs` pins today's answer, 467 final; slice 3 changes it to Lean's, accepted), and its Lean twin q8, `try (have j : b = a := by exact ⟨h⟩)` then `exact h`, accepted; and a have-by inside a have-by inside such a frame, whose inner error Lean throws. In `recover.lf` with `by-try` once it exists.
Every slice: TACTIC_STATUS.md (rows and the new column), LANGUAGE_REFERENCE.md, `make cover-changed`.

## 5. Trust

All of this is untrusted front-end code; a block only builds a term the kernel checks. Where a failure could be swallowed, and its test:
- **A handler catching what is not Lean's error.** Gate: the Lean-error bit, closed by default. Tests, inside each of by-try, by-first, by-repeat, by-any-goals and `lf-tac-try-lean`: a refusal sweep over every store and goal-list request (`tests/support/meta-sweeps.fs`); step fuel at each k below the passing count; the meta budgets (whnf, defeq, instance synthesis, `lf-meta-spend?`), which surface as exhausted and are not caught today, pinned so; a step answering not supported (80/93/99). Each must end in that error's exit code.
- **The error classes**: a logged-class error caught as if thrown. Tests in `recover.lf`, each with a wrong twin Lean rejects.
- **A restore or commit refused**: `lfr-state-lost`, caught by nothing; swept.
- **try leaving the goal open**: `end NAME`'s 89; test: by-try over a wrong by-exact as the whole proof.
- **A pass's goals kept after its rollback**: `tfr-acc` grows only at a pass's good end; test: an any-goal pass that makes goals and then fails.
- **A run stopped inside a block**: `lfr-forget-saves` (:677); test: two declarations, the first failing inside by-try.
- **Stricter than Lean, never laxer**: the open point of section 0.

## Review response

1-11 are applied as written, except:
- **3, refined.** A per-goal failure is caught by the nearest enclosing any-goal frame *unless an admit point with recover true lies between*: `closeUsingOrAdmit` catches the abort with `tryCatchRuntimeEx` and admits without restoring (Basic.lean:355-361), so the logged error stays. The general frame walk already gives this; no special case is needed.
- **5, alternative taken**: the then-step, for the reasons in section 2.
- **7, one string changed**: `braces`, not `cdot`: the owner's form is Lean's `tacticSeqBracketed` (BuiltinTactic.lean:167-173).
- **Q3's zero-new-word option** is dropped: the owner chose `by-have-by:`.
- **1, one addition**: "final" for have-by's unsolved goals carries the same known gap as every logged error (a later rollback in Lean removes the message, CoreM.lean:420-424).

Not verified: anything by running pinned Lean (all Lean behaviour is from reading); that `logException` ignores aborts; which ported tactics have `throwOrLogError` sites; Lean's parser on an empty `{ }`; the step-log goldens; the Makefile's discovery of new test folders (taken from the TB2 brief); branch `tb2-batch3b` itself; the Mathlib counts.
