# Forth review: tactic-move C4, induction and case on the tactic library (2026-11-19)

Branch tactic-move-c4, range 1bf0d162..54e20bcc (6 commits; main 5ccafff0 adds only a CI record on top of 1bf0d162); reviewer forth-reviewer (Opus), independent.

Findings: 0 high, 3 medium (1 blocking), 10 low (3 blocking: reuse). **Verdict: merge after fixes.**
- B1, B2 and B3 must be fixed before the merge. Each is a few lines.
- B4 is fixed, or the coordinator cites a plan row for it.
- M1 should land before the done check.
- Apart from B1, "no behaviour change" holds. B1 is a path no caller reaches yet.

## Findings

**B1 (medium, blocking: a difference from Lean).** `lf-elim-for`'s cases path (`induction?` false) behaves like induction's.
- The library documents the flag ("its cases eliminator", "C.casesOn for induction? false"), and the word list names cases as the next caller.
- elim.fs:162: `mel-recursor` runs `mel-simple` whatever the flag says. A mutual or nested type is refused with 209 ("The `induction` tactic does not support…").
  - Lean refuses only under induction: Induction.lean:833-836, `if induction && indVal.all.length != 1`, `if induction && indVal.isNested`.
  - For cases, Lean takes `C.casesOn`.
- elim.fs:126-129 and author/errors.fs:490: 205's text is induction's. The header says "Tactic `induction` failed", and the explanation says "the `induction` tactic … custom induction principles … '@[induction_eliminator]'".
  - Lean builds both from `tacticName` (Induction.lean:775-778): `cases` and `@[cases_eliminator]`.
- Reproduced on a scratch copy (Gforth 1.0.0, tactic-lib.fs's own setup):
  - `fe10 false lf-elim-for` on FE6.Even (several.ndjson) gives 209. `FE6.Even.casesOn` exists there: `mel-rec` with false finds it.
  - `p false lf-elim-for` on `p : Prop` gives 205 with induction's text, word for word.
- Fix:
  - Run the mutual and nested refusal only under induction, as Lean does:
    ```forth
    : mel-checked ( t d induction? -- t d ) if mel-simple then ;
    : mel-recursor ( target induction? -- d )
      >r lf-infer! lf-whnf! dup mel-inductive 0= if mel-not-inductive then
      r@ mel-checked nip r> mel-rec ;
    ```
  - For 205, either pass the tactic's name to `mel-explanation.` and add cases' code text, or state in elim.fs's header and in the cases plan row that 205's text is induction's until cases lands.
  - Add a test: `fe10 false lf-elim-for lf-menv-name` is `FE6.Even.casesOn`.

**B2 (low, blocking: reuse).** `tal-n.` (tactic-alts.fs:169) is a copy of `lf-pp-number` (present/print-job.fs:127).
- Both are `u>decimal lf-pp-emit`.
- Use `lf-pp-number` in `tal-too-many.` and delete `tal-n.`. The old `lfi-n.` was the same copy; the move kept it.

**B3 (low, blocking: reuse).** `mel-past ( t -- body n )` (elim.fs:168) counts a pi telescope, a term walk with three copies:
- meta-spine.fs:126 `lf-meta-forall-body` is the same loop without the count;
- elab-app.fs:281 `ea-result?` is the same loop with the count, then `lf-term-bvar-is?`.

Add the counting word to meta-spine.fs, beside its application analogue `lf-meta-head-args`:
```forth
: lf-meta-forall-body# ( term -- body n )   \ past every pi, and how many
  0 swap begin dup lf-term-pi? while lf-term-second@ swap 1+ swap repeat swap ;
: lf-meta-forall-body ( term -- body ) lf-meta-forall-body# drop ;
```
Then `mel-past` becomes `lf-meta-forall-body#`, and `ea-result?` becomes `lf-meta-forall-body# lf-term-bvar-is?`. If elab-app.fs is claimed by a branch in flight, the coordinator schedules that one copy.

**B4 (low, reuse: fix or cite a plan row).** The counting loop `0 n 0 ?do i pred? - loop` has four copies:
- `tal-unhandled#` (tactic-alts.fs:104) and `tal-explicit#` (:134), both new;
- `tcs-named#` (tactics/case.fs:56, moved);
- `cli-again#` (cli/leanforth.fs:808).

lib/find.fs has `find-index` and outcome.fs has `any?`, but neither counts. Add this to lib/find.fs, with its test and a fault:
```forth
\ How many k < n for which xt ( k -- flag ) answers true (n <= 0: none).
: count-index ( n xt -- m ) 0 -rot dup 1+ swap ?do 0 max 0 ?do i j execute 0<> - loop loop ;
```
Then:
```forth
: tal-unhandled# ( -- n ) tal-info@ lf-elim-alts# ['] tal-unhandled? count-index ;
: tal-explicit# ( -- n ) tal-fields ['] tal-explicit? count-index ;
: tcs-named-at? ( k -- flag ) tcs-tag-at 0<> ;
: tcs-named# ( -- n ) tcs-goals# ['] tcs-named-at? count-index ;
```

**M1 (medium, tests).** The tactic-alts.fs words have no library-level tests, and the block-stack discipline is not pinned.
- The word list asks for "205-213 and 210-211 at the library". Errors 206, 207, 208 and 213, and `lf-eval-alts`' two modes, are reached only end to end (check_s2.py, with Lean twins).
  - Only `tal-expected.`'s text, `tal-kind`'s 99, `tal-name-for`, `tal-cleared` and `tal-k!`'s 92 are unit-tested.
- Two of my planted faults survive both the unit files and `check_s2.py --tactics`:
  - **R7**: `lf-alts-missing` without `dup tal-alts-of`, so a stale tal-js from a nested block is used.
  - **R8**: `lf-alts-missing` without `tal-blocks slab-drop`.
- Every .lf with nested blocks (04-nested-ih, s2-case, ps-*) puts the inner block in the last alternative, and inner and outer have the same alternative names. So neither fault can show.
- Add:
  - a proof whose inner `by-induction-with` sits in `| zero =>`, followed by `| succ`;
  - a wrong twin whose outer block omits `succ` after a complete inner block: 207, which stale tal-js hides.
  - Both can be unit tests in tactic-run.fs or an .lf pair with pinned-Lean twins. Add R7 and R8 to faults.d/tactic-lib.toml.
- Also add one `T{ }T` per public word that checks the stack effect:
  - `lf-alt-names-check` (213 before 206);
  - `lf-alts-missing` (207 at i, the block dropped);
  - `lf-eval-alts`' plain mode (goals in order, fields inaccessible).

**M2 (medium, style: raw offsets).** The information run is read by position:
- elim.fs:88-91: `0 run@`, `1 run@`, `run-count 4 - 3 /`, `swap 3 * + 4 + run@`;
- :177 and :224-225: `2 run@` and `3 run@` in `mel-special?` and `mea-arg`.
- The tests also build infos by position (`one-more`, `first-cells`, `header-info`, `alt+`).

Name the layout:
```forth
4 constant mel-head#        \ d, binders, the motive's and the target's positions
3 constant mel-alt-cells    \ name, position, fields
: mel-motive-at ( info -- k ) 2 run@ ;
: mel-target-at ( info -- k ) 3 run@ ;
: lf-elim-alts# ( info -- n ) run-count mel-head# - mel-alt-cells / ;
: mel-alt@ ( info k field -- x ) swap mel-alt-cells * + mel-head# + run@ ;
: mel-special? ( info k -- flag ) 2dup swap mel-motive-at = >r swap mel-target-at = r> or ;
: mea-arg ( pi k -- arg )
  dup mea-info@ mel-motive-at = if drop mea-motive-arg exit then
  dup mea-info@ mel-target-at = if drop mea-target-arg exit then
  dup mea-alt? if drop mea-alt else mea-implicit then ;
```

**M3 (low, style: PICK and a four-cell interface).**
- `lf-eval-alts` needs `3 pick` (tactic-alts.fs:164); `tal-checked` needs `2over` (:155).
- The step record already holds step, info and target (`tal-start`). Add `tal-alts` and hand the words nothing:
  ```forth
  : tal-begin ( i info alts target -- )
    tal tal-target ! tal tal-alts ! tal tal-info ! tal tal-step ! 0 tal tal-given ! ;
  : tal-i ( -- i ) tal tal-step @ ;
  : lf-eval-alts ( i info alts target -- ) tal-begin tal-i tal-holder? if tal-with else tal-plain then ;
  ```
  Here `tal-with ( -- )` and `tal-plain ( -- )` read the record.
- `tind-app` (tactics/induction.fs:49-50) juggles `-rot 2>r … 2r> swap` around three results. Keeping info and target in the step record would also remove that.

**L1 (low, robustness).** `lfr-alt` (tactic-run.fs:305) executes the parent kind's `trow-alt` without checking it.
- `0 execute` crashes the host.
- It is unreachable today: the record check admits `|` only right inside by-induction-with, and induction.fs sets both rows.
- A later `lf-tactic-alt!` for another kind, with induction.fs not loaded, would reach it.
- Fail closed (92, the record not as made). `lfr-alt` and `lf-tactic-alt!` move below `lfr-misplaced` (:390):
  ```forth
  : lfr-alt-xt ( j -- xt )
    lfr-parent lfr-kind lfr-row trow-alt @ dup 0= if drop ['] lfr-misplaced then ;
  : lfr-alt ( j -- ) dup lfr-alt-xt execute ;
  ```

**L2 (low, re-entrancy, written at load only).** `trow-alt` is a new field of the load-time row table `lfr-rows`.
- `lf-tactic-alt!` writes it, and the `|` row, with no `context-sealed?` guard. So does every row setter: `lfr-set`, `lf-tactic-end!`, `lf-tactic-shape!`, `-plan!`, `-lean!`.
- Its only writer is tactics/induction.fs, while it loads. Runs, and workers, read it in place.
- Give all setters one guard: `: lfr-open ( -- ) context-sealed? abort" tactic-run: a row set after context-new" ;`.

**L3 (low, state; already on main).** `tal-blocks` is never cleared when a run starts.
- A run stopped inside a with block leaves the block on the slab, for example at 207, which throws before `slab-drop`.
- Answers stay right, because later blocks sit above it. But every later save copies it, since `slab-keep` copies the whole slab.
- Old `tind-withs` had the same gap. Clear it at the run's start, for example with a reset xt beside `tac-state:`.

**L4 (low, tests).** The known gap `s2-alt-field-kinds-ignored` is closeable now. Its reason held end to end: an eliminator with an implicit field needs an index target, which answers 99.
- After C4, `tal-explicit?` and `tal-kind` are unit-tested with hand-made informations (`kind-in`, tactic-lib.fs:770).
- An information whose alternative's binder domain has an implicit field would catch it, for example Nat.le.rec's `step` if the slice holds it.
- Note also that Lean 4.35.0's `getNumExplicitFields` (Induction.lean:317) counts explicit binders after `introN`, and let-bound ones count as explicit. LeanForth counts the eliminator type's declared kinds. Say this in tactic-alts.fs's header, as a Lean difference kept from S2.

**L5 (low, requires and docs).** All five new files load on their own, transitively (checked), but some words come in without a direct require:
- elim.fs uses `lf-mk-app` but no longer requires app-builder.fs (the old file did).
- tactic-alts.fs uses `lf-binder-default` (present/binder-table.fs) and `lf-pp-emit` (present/print-job.fs) without requiring them.

The docs have two small gaps:
- `lf-alt-names-check`'s comment does not say it writes the running step record's `tal-info`.
- FRONT_LAYERS.md's Meta/Tactic row lists elim.fs and rename.fs but not their words.

**L6 (low, test comment).** tactic-lib.fs:636/653 pins `Nat.casesOn` for `fn9 false`.
- This is right for the S2 slice: its elaboration data has no cases eliminator.
- Lean 4.35.0 with full Init takes `Nat.casesAuxOn` (`@[cases_eliminator]`, Init/Data/Nat/Basic.lean:48).
- Say "the slice has none" in the comment. The custom cases-eliminator branch (`mel-custom` finding an `elab-cases` record) is never run.

## Word list (C4)
- Every C4 row exists with tests and faults, and both old files are deleted.
  - Library words: `lf-elim-info`, `lf-elim-for`, `lf-elim-app`, `lf-elim-set-motive`, `lf-eval-alts`, `lf-alt-names-check`, `lf-alt-run`, `lf-alts-missing`, `lf-goal-rename-inaccessibles`, `lf-tactic-alt!`, plus `lf-tactic-alt@`.
  - The plug-ins hold only their tactic's words. `findTag?` stays in tactics/case.fs, as the list says: it is private in Lean.
- Declared departures:
  - **(a)** `lf-eval-alts ( i info alts target -- )`: **acceptable** as an interface. It mirrors evalAlts' elimInfo, alts, syntax and toClear. Remove the PICK (M3).
  - **(b)** No case slab; missing alternatives read from the alternatives written: **acceptable**.
    - Under stop-at-first-error, "a `|` written" means "an alternative taken". Names are checked first, every `|` right inside the block runs unless the run stops, and a try restores tal-blocks.
    - The recompute at the block's end is load-bearing for nested blocks and untested (M1, R7).
  - **(c)** `lf-goal-rename-inaccessibles ( goal names -- goal' )`, names a run: **acceptable**. "None, or all `_`, gives goal" is Lean 4.35.0's `hs.findSome? … | return mvarId` (RenameInaccessibles.lean:24-27).
  - **(d)** One `lf-tac-intro1` per field: **acceptable**. It is recorded in PLAN_DRAFT's 9.4.8l row, the goldens are unchanged, and the term is the same once instantiated.
  - **(e)** `tac-k-alt` owned by the runner: **acceptable**. test_check_tactic_plugins.py pins it: induction.fs sets the row through `tac-k-with`, and naming `tac-k-alt` is refused. L1 makes the dispatch fail closed.

## Reuse
Searched:
- the index LIBRARY_WORDS.md, FORTH_LIBRARY.md and lib/find.fs and outcome.fs;
- `git grep` over src/ for the shapes `lf-term-pi? while`, `u>decimal lf-pp-emit`, `0 … ?do i … - loop`, `, or ` / orList, `lf-tac-args#` run builders, and `?do … unloop exit` searches.

Tool results:
- `check-duplicates.py`: "205 baseline groups, each with a reason, none new or grown". Its six-token threshold misses B2-B4.
- `check-lib-callers.py`: clean (bigint.fs is planned, FE1i-4).

New findings: B2, B3 and B4.

Considered and not raised:
- `lf-elim-alt-find`'s hand loop: `find-index` passes one value, and the search needs info and name.
- `tal-sep`/`tal-expected.` (Lean's orList): there is one copy in src/. It may later join tactic-msg.fs.
- `tcs-names`: the only run built from step arguments.

The baseline edits are honest:
- `tal-intros` is the generic `n 0 ?do i word loop`, the same false positive as `lf-sch-fill`.
- `lfi-setup`'s removal follows the deleted file.

## Re-entrancy
New state, all context members (ADR 0009):
- `mea-frames` and `mes-frames` (elim.fs), and `mrn-frames` (rename.fs): one `lf-with-record` frame per call.
- `tal-blocks`, `tal-blocks-kept` (saved by `tac-state:`) and `tal-js` (tactic-alts.fs).
- One load-time row field, `trow-alt` (L2).

These replace `tind-alts`, `tind-withs`, `tind-js` and their two kept slabs.

Frame access:
- Every read of a frame goes through `mea`, `mes` or `mrn` (`slab-last`) after any call that may claim. No frame address is held across a nested claim.
- The one held address is `mes mes-target`, the one-cell xs that `mes-lam` passes to `lf-mk-lambda-fvars`. That word claims nothing on mes-frames, so the address stays valid.
- Faults: frames left behind are caught (`lib-elim-frame-kept`, `lib-rename-frame-kept`, and my R1 for mes).

## Lean fidelity (4.35.0 source compared)
These match the old files and Lean, apart from the gaps the moved code already documents (generalizeVars, index targets, instance binders and coercions: 99; 207/211 stop instead of logging):
- getElimExprInfo. `altArity` counts forall and let; `mel-past` counts pis, and recursors have no lets.
- getCustomEliminator?.
- mkElimApp: motive synthetic opaque, alternatives tagged by appendTag, implicit binders natural.
- setMotiveArg, with the same defeq order.
- checkAltNames: duplicates first, then invalid names with orList.
- evalAlts and evalAlt: names fit before introN, then tryClear.
- renameInaccessibles. Shadowing counts only user-nameable newer locals; in Lean an inaccessible name carries macro scopes, so the result is the same.
- evalCase: rename, then setGoals and setTag.

Differences:
- B1, new in the library contract.
- L4's explicit-field count, kept from S2.

The mutual and nested check under induction, and its texts, are unchanged.

## Coverage and faults
- tests/coverage-baseline.json drops tactic-induction.fs (83 never run). It adds elim.fs (220 blocks), tactic-alts.fs (155), rename.fs (57), tactics/induction.fs (28) and case.fs (50), all at 0. No behaviour branch is hidden as debt.
- The rest of the diff is entries re-sorted, not changed.
- The new unit tests check outcomes, texts, terms and frame counts, not only line reach. A few drive private words with deliberately malformed informations (`one-more`, `first-cells`, `-1 mel-major.`) to reach refusals. That is acceptable, but it ties the tests to the run's layout (M2).
- My 21 planted faults:
  - 16 caught by tactic-lib.fs and tactic-run.fs: R1-R6, R10-R15, R17, R18, R20 and R21. They include the motive's frame, mutual taken, implicit taken as an alternative, motive and target swapped, the custom kind ignored, the holder test inverted, a kinds bound off by one, the let and dependency refusals, the scan skipping the newest local, `|` dispatched on its own kind, and the saved state unregistered.
  - 3 caught only end to end: R9, the plain mode giving names (check_s2 `--tactics`); R16 and R19, rename (check_s2 `--case`).
  - 2 survive: R7 and R8 (M1).
- The declared gap `s2-alt-field-kinds-ignored` is acceptable as it stands; L4 says how to close it.

## Forth style
`python3 scripts/forth-metrics.py --words 10` over elim.fs, rename.fs, tactic-alts.fs, tactics/induction.fs, tactics/case.fs, tactic-run.fs and tactic-core.fs:

| File | Words | 1-2 lines | 3-5 lines | Over 5 | Deep shuffles | Return-stack ops | Globals |
| --- | --- | --- | --- | --- | --- | --- | --- |
| elim.fs | 64 | 60% | 39% | 0 | 4 | 9 | 0 |
| tactic-alts.fs | 58 | 72% | 27% | 0 | 4 | 6 | 0 |
| rename.fs | 26 | 96% | 3% | 0 | 1 | 0 | 0 |
| tactics/case.fs | 31 | 100% | 0 | 0 | 2 | 0 | 0 |
| tactics/induction.fs | 14 | 92% | 7% | 0 | 1 | 4 | 0 |
| **Total (7 files)** | 426 | 80% | 19% | 0 | 15 | 36 | 2 (tactic-run.fs's existing ones) |

- The longest word is 5 lines (`mel-type-hint.`, four string emits). There are no locals, and the ratchet holds.
- Style findings: M2 (raw run offsets), M3 (`3 pick`, `2over`, four-cell words, `tind-app`'s shuffle), L1.
- Smaller points:
  - `mel-alt+` (elim.fs:183) reads better as `>r tuck lf-binder-name mel+ r> mel+ swap lf-term-first@ mel-past nip mel+`.
  - `lf-elim-info` (:190) chains `rot swap … swap`. A helper `mel-head ( d -- info concl )` would name the first half.
- Otherwise the files are small, named words with accurate stack comments and headers.

## Trust boundary
- Nothing here confers validity. The goal is assigned the eliminator's application, and the kernel checks the finished term at hand-over.
- Every failure throws, and the runner turns it into an authoring error. A `lf-must` code becomes the same code `lf-tac-must` gave, through `lfr-authored`.

## What I ran
On scratch archive copies of 54e20bcc and main (`git archive`), with Gforth 1.0.0, stdin `/dev/null`, `ulimit -u 500`:
- tests/front/tactic-lib.fs and tactic-run.fs (pass), then s2-sweeps.fs, elab.fs and tactic-syntax.fs, as fault judges;
- probes P1 and P2 (B1);
- each new file loaded alone (all load);
- `test_check_tactic_plugins.py` (11 OK);
- `check-tactic-plugins.py` on the branch (not confined, so the full tier applies);
- `check_s2.py --tactics` and `--case`, only with my faults R7, R8, R9, R16 and R19 planted;
- forth-metrics, check-duplicates and check-lib-callers.

Not run:
- the implementer's recorded suites, make targets and coverage;
- pinned Lean (Lean source read instead);
- Gforth 0.7.3 and gforth-fast;
- Init and Mathlib.

Note for the coordinator: the branch changes scripts/check-tactic-plugins.py. The word list (section 3) says that puts it in the full tier: `make check`, `make test-unit` on gforth-fast and `make check-rest`. The implementer's report lists only front-end targets plus coverage-focus. `make tier` must record the full tier once on the final head.

This AI review does not replace the human review AGENTS.md requires.

## Fixes (2026-11-19, 54e20bcc..HEAD of `tactic-move-c4`)

Fixed on the branch by the implementer, each finding with its commit; three items left to plan row 9.4.8l as (W), (X) and (Y). No golden line changed: two lines appended to `tests/front/s2-proofs.golden` and ten to `tests/front/s2-steps.golden` for the new `.lf` file of M1. Duplicates stay at 205 groups.

- **B1: fixed** (`72f748e7`). `mel-checked` runs the mutual and nested refusal only under induction, so cases takes `C.casesOn` (`fe10 false` gives `FE6.Even.casesOn`; a nested type is never 209 under cases). 205's explanation names the tactic as Lean's `tacticName` does (`cases`, `@[cases_eliminator]`), through `mel-major.`'s second cell. 205's header is the catalogue's fixed text, which `tests/front/tactic-registry.golden` lists, so it stays induction's on the cases path: elim.fs's header says so, and plan 9.4.8l (W) changes it when cases is ported. Tests in tactic-lib.fs; faults `lib-elim-cases-mutual-refused` and `lib-elim-explanation-induction-only`.
- **B2: fixed** (`4f579af9`). `tal-n.` deleted; `tal-too-many.` uses `lf-pp-number`.
- **B3: fixed** (`085bfd33`). `lf-meta-forall-body# ( term -- body n )` in meta-spine.fs, `lf-meta-forall-body` its first result; `mel-past` deleted, `ea-result?` is `lf-meta-forall-body# lf-term-bvar-is?`. Tests in tests/front/elab.fs; new fault `fe-meta-forall-count-none`; `fe-meta-forall-body-one` re-targeted at the counting loop. The style notes on `mel-alt+` (no `rot`) and `lf-elim-info` (`mel-head`) are taken too.
- **B4: fixed** (`05de065a`; the header example's output on one line, `7b0672b6`). `count-index ( n xt -- m )` in lib/find.fs, without `-rot` (`0 swap` inside the loop), with its header, example, tests in tests/lib/lib.fs, fault `lib-count-index-raw-flag`, FORTH_LIBRARY.md profile (measured: 3-4 ns an index on `gforth`, 2 ns on `gforth-fast`) and LIBRARY_WORDS.md. Used by `tal-unhandled#`, `tal-explicit#`, `tcs-named#` (one word `tcs-named?` serves `find-index` and `count-index`) and `cli-again#`. `check-run.fs`'s `ck-again#` counts with a value (`why`) below k, which `count-index`'s test cannot read; it stays.
- **M1: fixed** (`1dac6e13`). tactic-lib.fs part 9b calls the public words on the step records a run leaves: `lf-alt-names-check` (213 at the second `| zero` before 206; 206 with "Expected `succ`"; nothing when the names fit), `lf-alts-missing` (207 at the block's word; the outer block's own steps read after the inner block's were checked; the block dropped when complete), `lf-alt-run` (208 at its `|`), `lf-eval-alts` without alternatives (the goals in order, tags `t.zero` and `t.succ`, succ's fields inaccessible, the target cleared). `tests/front/04-nested-first.lf` puts the inner block in `| zero`, then `| succ`: accepted, its term node for node pinned Lean's (`zero_add_inner`, last in s2-proofs.lean); its wrong twin `s2w-alt-inner.lf` leaves out the outer succ: 207 with Lean's message (`w_alt_inner`, Lean's error at 84:2). Faults R7 `lib-alts-missing-stale-js` and R8 `lib-alts-block-kept` are caught by tactic-lib.fs, and also by `check_s2.py --tactics` (checked with a scratch list).
- **M2: fixed** (`02caee87`). `mel-head#`, `mel-alt-cells`, `mel-motive-at`, `mel-target-at`; `mel-special?` and `mea-arg` read through them, and the tests' hand-made informations use the names.
- **M3: fixed for tactic-alts.fs** (`20266f76`). `tal-begin` stores i, info, alts (new field `tal-alts`) and target in the step record; `tal-with` and `tal-plain` take nothing, `tal-plain-case` lost its `rot`. No `pick` or `2over` is left (tactic-alts.fs: deep shuffles 4 to 1, return-stack operations 6 to 4). `tind-app`'s shuffle in tactics/induction.fs: plan 9.4.8l (Y).
- **L1: fixed** (`3cd52d2b`). `lfr-alt-xt` gives `lfr-misplaced` (92) for a kind with no alternatives' row; `lfr-alt` and `lf-tactic-alt!` sit below `lfr-misplaced`. Test in tactic-run.fs; fault `tac-alt-row-unchecked`.
- **L2: fixed** (`3cd52d2b`). `lfr-open` (`context-sealed?` abort) guards every row writer through `lfr-row!` and `lfr-row-new`. tactic-run.fs's one `context-new` (the binder-kind table test) moved to the end of the file, after the row stand-ins it would now refuse; fault `tac-row-set-after-context`. Fault `tac-alt-row-unset` re-targeted.
- **L3: planned** as plan 9.4.8l (X).
- **L4: fixed** (`510932ad`). tactic-lib.fs counts the fields of Nat.le.rec's step (an information made by hand, since `lf-elim-info` refuses Nat.le.rec's two targets with 99): one implicit, two explicit. The gap line of `s2-alt-field-kinds-ignored` is removed and its test is tactic-lib.fs (caught). tactic-alts.fs's header states the Lean difference (getNumExplicitFields counts after introN, let-bound fields as explicit).
- **L5: fixed** (`4f579af9`, `20266f76`, this commit). tactic-alts.fs requires present/binder-table.fs and present/print-job.fs, elim.fs requires app-builder.fs; the header says `lf-alt-names-check` writes the running record's `tal-info`; FRONT_LAYERS.md's Meta/Tactic row lists the information's readers and each word's file.
- **L6: fixed** (`510932ad`). The comment says the slice's data has no cases eliminator, Lean with all of Init takes `Nat.casesAuxOn` (Init/Data/Nat/Basic.lean:47-48), and `mel-custom`'s cases branch is not run.
