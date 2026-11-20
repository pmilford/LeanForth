# Forth review: cleanup-families-1, clean-up by family (2026-11-19)

Branch `cleanup-families-1`, range `15f52a79..ca867d82` (7 commits); reviewer forth-reviewer (Opus), independent of the implementer.

Findings: 0 high, 1 medium, 7 low (2 blocking: reuse; 1 reuse to fix or plan). **Verdict: merge after fixes.**
- B1 and B2 must be fixed before the merge. Each is a few one-word edits in src/front. B1's kernel copies go on the owner's list (plan row).
- B3 is fixed, or the coordinator cites a plan row for it.
- M1 should land on the branch: one test line and a few fault entries.
- "Behaviour identical" holds:
  - Every counting conversion and pair field was traced, and 31 of my own planted faults were run.
  - Base and head give the same counts in three run states.
  - The kernel members match a re-run of the tool byte for byte.

## Findings

**B1 (low, blocking: reuse).** `lf-made-term`'s exact phrase `if drop outcome-ok else -1 outcome-full then` still ends six other words. The tool missed them because it groups whole bodies only.
- src/front, fix now:
  - level-map.fs:43 `lmap-sort-new`;
  - lib-decode.fs:277 `lbd-nat`;
  - infer.fs:127 `if-sort-new`.
- src/kernel, for the owner's list (plan row, as AF's pairs):
  - mixed-infer.fs:354;
  - iota.fs:181;
  - string-literals.fs:81.
- Fix:
  ```forth
  : lmap-sort-new ( level -- image outcome ) dup lmap-identity lf-hterm-sort lf-made-term ;
  : lbd-nat ( e src -- term outcome ) src-text lf-hterm-decimal lf-made-term ;   \ + require ../core/generation-handles.fs
  ```
  `if-sort-new`'s last line becomes `lf-hterm-sort lf-made-term ;`.

**B2 (low, blocking: reuse).** `ok-or-none` is the word the branch adopted for group dfdf. Its exact phrase `dup ok? 0= if nip no-result then` remains in three words:
- meta-env.fs:210 `me-decoded`;
- elab-term.fs:445 `et-rel-done` (mid-word, before `et-eo-end`);
- infer.fs:390 `idl-assign`.

Replace each phrase with `ok-or-none`.
- Probe: B1, B2 and B3 applied together on a scratch copy pass tests/front/meta.fs, defeq.fs, front.fs, elab.fs, menv-run.fs, goals.fs and whnf.fs.
- check-duplicates.py then re-keys the accepted group c0d6 (meta-env.fs `lf-menv-sunfold`/`lf-menv-matcher`) as cd86. Its baseline key needs updating.

**B3 (low, reuse: fix or cite a plan row; pre-existing, found by step 3a).** Five words hand-write lib/outcome.fs's `room-result ( x true | false -- x outcome )` as `if outcome-ok else -1 outcome-full then`:
- meta-spine.fs:133 `lf-meta-app`;
- nat-offset.fs:75 `no-seek`;
- nat-offset.fs:95 `no-app`;
- level-map.fs:64;
- assign-check.fs:218.

The effect is identical, since `no-result` is `-1 swap`. level-map.fs:62 already calls `room-result` one line above its copy. Replace each with `room-result` (probed with B1 and B2).

Process note: after each `--extract`, grep for the extracted phrase itself. A `--phrase TEXT` mode in check-duplicates.py would find tails like these.

**M1 (medium, tests and faults).** The converted callers have no planted faults, and two are pinned only end to end.
- Faults are recorded only for `lfc-zero-at?` and the library words. Nothing is recorded for:
  - `ck-slot?` and `ck-stage-slots`, `ck-fresh?` (`ck-checked#`), `ck-saved?`, `ck-again-for?` and `ck-verdicts#`;
  - `kept-at?` and `kept-before`;
  - `lf-pf-inner#`, `lf-pp-shown#` and `lf-pp-last` (now a backward search).
- My faults on them are caught, but:
  - **r6**: `ck-fresh?` counting taken declarations. Only `test_leanforth.py Imports` catches it (13 s).
  - **r9**: `ck-again-for?` counting any why. Only `OlderSnapshots.test_carried` catches it (about 90 s).
  - Neither is caught by tests/core/env-import.fs or tests/cli/leanforth.fs.
- Fix:
  - Add after env-import.fs:506. It is probed: it passes unfaulted and catches r6 and r9.
    ```forth
    T{ why-answers ck-again# ck-checked# ck-saved# -> 16 56 107 }T
    ```
  - Record these faults with the judges that caught them:
    - r4 `ck-slot?` inverted and r7 `ck-saved?` inverted (env-import.fs);
    - r6 and r9 (env-import.fs once the line above is in);
    - r10 `kept-at?` inverted (constructions.fs);
    - r12 `lf-pf-inner#` one short (check_author.py);
    - r14 `lf-pp-last` on `find-index` (check_golden.py, print-cases.golden:106);
    - r16 `lf-pp-shown#` one short (term-printer.fs).

**L1 (low, docs).** The orientation of x and the count is stated backwards.
- find.fs:58 says "The count sits below x". FORTH_LIBRARY.md:1205 says "the count below x".
- In fact the stack is `x count`, and `over` gives the test a copy of x above the count.
- Say: "x stays below the count; each test is given a copy of x above it."

**L2 (low, requires).** nat-offset.fs:86 now uses `lf-made-term` from core/generation-handles.fs without requiring it. It loads only transitively, through constant-references.fs.
- Add `require ../core/generation-handles.fs`, or use the tool's `--add-require`.

**L3 (low, report accuracy).** I re-ran the tool on d70ecad5 with the commit's arguments:
- `level-make.fs`, `mixed-level-substitute.fs`, `reduce-nat.fs` and `generation-handles.fs` come out byte-identical to 31056f84.
- `core/terms.fs` differs only by the hand re-wrap of the tool's line, which is over 90 characters. The tokens are identical.
- The commit message says this; the OWNER_DECISIONS.md report line does not. Add "(core/terms.fs's new line wrapped by hand to stay under 90 characters; tokens unchanged)".
- In my reading this is not a change beyond the extraction, so it does not block.

**L4 (low, names and comments).**
- `ck-verdicts# ( xt -- n )` reads as a count of verdicts, but it counts input declarations passing xt.
  - Better: `ck-inputs-passing# ( xt -- n )`.
  - `0 swap lf-input-count swap count-index` reads better as `>r 0 lf-input-count r> count-index`.
- source.fs:73's comment describes both `lfa-token-at` and `lfa-token!`. Put it in two parts: `lfa-token-at` makes c-addr u the current token; `lfa-token!` also marks the line as read to its end.

## The four parts
1. **count-index.**
   - `( x n xt -- m )` is find-index's convention; x is dropped. Each test gets a copy of x, and the test's own x is discarded.
   - Edge cases on Gforth 1.0.0: n = 0 and n = -3 give 0, and the depth stays balanced.
   - The header example prints `-1 1 0 -1 2 2`.
   - All eight conversions count what the old loops counted.
     - The `1 and +` copies need well-formed flags, and both tests give them:
       - `slot-record?` is `block? if block-empty?(0=) else 2drop true`;
       - `lf-env-final?` is `?keep`'s copy of `lf-slot-final?`, which is `=` or 0, ANDed with `ck-taken? 0=`.
     - The `if 1+ then` copies (`lf-pf-inner#`, `lf-pp-shown#`) count any nonzero value, as `0<>` does.
     - The `-` copies (`ck-again#`, `ck-saved#`, `lfc-zeros`, `kept-before`) use `=` or `0=`.
     - Calls happen in the same order, so `lf-slot-early`'s side effect is unchanged.
   - Differential: `ck-checked#`, `ck-saved#`, `ck-stale#`, `ck-again#` and `ck-stage-slots` are identical on base and head in three env-import.fs states: 56 107 107 51 56 16 107 / 0 0 107 51 0 16 107 / 107 107 107 0 107 0 107.
   - `lf-pp-last`:
     - It is the last shown index, else -1, the same as the loop.
     - The -1 path is never run, by design (0b1ab2ec). My r15 survives for that reason.
     - `lf-pp-visible?` only reads, so the early exit changes nothing.
2. **Pairs.**
   - All 10 fields are read only with `2@` and written only with `2!`, through their accessors. No half is read alone: `lfa-offset` is `2@ drop`, `lf-print-sink` is `2@ drop`, `lf-pp-options` is `2@ nip`. No old name or raw offset is left in src/ or tests/.
   - Layout dependents:
     - The records are erased by range (`pv-the-run`, `ir-the-read`, `lfa-source-reset`) and never hashed or written out.
     - The clamp receipts hash `ir-run.fs`, which the branch leaves alone, and not ir-reader.fs or the verify files.
     - `lf-pjob-setup` sits at offset 64, so it is cell-aligned (`/frames` is 8 cells).
   - The swapped-pair faults p1 and p3-p11 are all caught.
3. **b441: honest.** Its 21 members have a different test and different arms each; even pv-lit, pv-call and pv-prim, which share `pv-in-def?`, have different arms. The old reason pointed at plan 9.4.8k, which no longer holds it.
4. **Exact groups.**
   - Each new word's body is token for token the phrase it replaced: `first-or-second`, `lf-term-no-params?`, `lf-made-term`, `lf-mvar-delayed?`. `ok-or-none`'s body equals `gl-result`'s.
   - Kernel requires:
     - mixed-level-substitute.fs requires core/terms.fs (:43);
     - reduce-nat.fs requires core/generation-handles.fs (:29);
     - level-make.fs requires lib/lib.fs (:39), which loads bounds.fs, as for its other library words.
   - Only commit 31056f84 touches src/kernel, src/core or src/import (`git log` and `git diff --stat` checked). src/import is untouched. **No other change there.**
   - Leftover copies: B1 and B2.
   - Reasons for what was left:
     - AF: spot-checked lib-decode.fs, assign-check.fs (15 half reads), synth.fs and tactic-run.fs. The reasons are sound.
     - Z: `gp-like` counts over a range with an offset, and the kernel's `lay-count` needs approval. Both reasons are sound.
     - AH: d106, 3654 and 6cc6 keep their recorded reasons. Sound.

## Reuse
Searched:
- LIBRARY_WORDS.md (regenerated: current), FORTH_LIBRARY.md, lib/find.fs, outcome.fs and bounds.fs.
- `grep` over src/ for:
  - the counting spellings: `- loop`, `1 and +`, `if 1+ then`, `0<> -`, `if swap 1+ swap then`;
  - pair reads (`dup X @ swap Y @ ;`) and writes;
  - each extracted phrase, as a whole body and as a tail;
  - `if drop else nip then`, `room-result` and `lf-data-params?`.

Tool results:
- `check-duplicates.py`: 205 groups on base, 200 on head, "none new or grown".
- `check-lib-callers.py`: clean (bigint.fs is planned, FE1i-4).

Every new word has callers: count-index has 12, and first-or-second, lf-term-no-params?, lf-made-term and lf-mvar-delayed? have 2 each.

New findings: B1, B2 and B3.

Considered and not raised:
- Other pair reads (telescope.fs `tl-run`, tactic-syntax.fs `lf-tactic-arg`, log-view.fs `lf-lv-visited`, lib's `sec-data`, `store-bounds`): each pair has a half written or read alone (for example tactic-syntax.fs:349, telescope.fs:126-130).
- `first-or-second`'s convention (n = 1) is narrow. Both callers number parts 1 and 2, and it sits well beside `first-nonzero`. A flag-taking select could later also serve elab-term.fs:336's `et-side`.

## Re-entrancy
- No new VARIABLE, VALUE or written CREATE. The new words are pure.
- The ten pair fields stay in their context records (ADR 0009).
- `count-index` keeps no state.

## Coverage and faults
- Implementer's 11 faults, all caught: the 3 `cf-*`, `lib-count-index-raw-flag` and `-count-as-x`, `fe-bk-arity-zeros` and `-nonzero`, `s4-mls-closed-always`, `cov2-mls-no-data-closed`, `fe-goal-except-ignored` and `pr-print-sink-type`.
- Mine, 31 planted:
  - library: r1 and r3 (lib.fs);
  - check-run.fs: r4, r5 and r7 (env-import.fs); r6 and r9 (end to end only, M1); r8 (`ck-verdicts#`' guard dropped) survives cli/leanforth.fs, not judged further (old behaviour);
  - cases-several.fs: r10 and r11 (constructions.fs);
  - print-forth.fs: r12 (check_author.py only);
  - print-analysis.fs: r13 survives term-printer.fs and check_golden.py (a gap that predates the branch); r14 (check_golden.py only); r15 (unreachable); r16 (term-printer.fs);
  - pairs: p1 and p3-p11, all caught;
  - extracted words through their callers:
    - `first-or-second` swapped is caught by level-compare.fs (kernel `lf-lmk-pick`) and derivation-log.fs;
    - `lf-made-term` full→ok is caught by reduce-nat.fs and survives defeq.fs; a variant giving 0 for -1 is caught by generation-handles.fs;
    - `lf-term-no-params?` no-data→true is caught by terms.fs and mixed-level-substitute.fs; params ignored is caught by meta.fs and mixed-level-substitute.fs (terms.fs cannot build a node with parameters);
    - `lf-mvar-delayed?` never is caught by whnf.fs.

## Forth style
`forth-metrics.py --words 10` over the 31 changed src files, base → head:
- words 3465 → 3477;
- 1-2 lines 2449 → 2465; 3-5 lines 978 → 974; 6-10 lines 35 → 35; >10 lines 3 → 3;
- deep shuffles 189 → 188; return-stack operations 785 → 784;
- globals 57 → 57; lines over 90 characters 20 → 20; no locals.

No new long words. `check-forth-quality.py --warn`: the ratchet holds. It also warns about the four unlogged commits, which is expected before this log row.

Style findings are L1 and L4 only. Otherwise the conversions are idiomatic: named per-index tests with stack comments, and the pair accessors are one line each.

## What I ran
On `git archive` copies of 15f52a79, ca867d82, d70ecad5 and 31056f84, with Gforth 1.0.0 through scripts/gforth-strict.sh, stdin `/dev/null` and `ulimit -u 500`:
- 21 test files as fault judges, all passing unfaulted on head: tests/lib/lib.fs; core/terms.fs, generation-handles.fs, env-import.fs, level-compare.fs, derivation-log.fs, reduce-nat.fs and mixed-level-substitute.fs; front/front.fs, constructions.fs, menv-run.fs, goals.fs, defeq.fs, meta.fs and whnf.fs; author/author.fs; present/term-printer.fs and print-deep.fs; program/ir-reader.fs and verify.fs; cli/leanforth.fs.
- Each of the 31 changed files loaded alone: all load.
- Probes:
  - the find.fs example;
  - the differential of the counts;
  - the M1 test line;
  - the B1-B3 replacements;
  - the tool re-run (L3).
- Python only as fault judges: test_leanforth.py Imports, OlderSnapshots.test_carried and Names; check_author.py; check_golden.py.
- forth-metrics, check-duplicates, check-lib-callers and lib-index.

Not run: the implementer's suites, make targets and coverage; gforth-fast and Gforth 0.7.3; pinned Lean (no kernel semantics changed: the members are token-identical); Init and Mathlib.

Note for the coordinator: the branch touches src/kernel and src/core, so the tier is the full one: coverage-focus, `make test`, `make test-unit` on gforth-fast and `make check-rest`.

Uncertainty, not caused by this branch (base and head agree): in env-import.fs's stale-ok run where "every result is stale, none carried", `ck-checked#` and `ck-saved#` are both 107 of 107. Someone who knows the report should check whether "checked in this run" should exclude those results.

This AI review does not replace the human review AGENTS.md requires.

## Fixes (2026-11-19, branch `cleanup-families-2`, on top of `ca867d82`)

Made by the implementer of round 2 before its own families, as their own commits, so that the two rounds merge as
one stack. Focused runs after the fixes (Gforth 1.0.0 through scripts/gforth-strict.sh, `ulimit -u 500`, stdin
`/dev/null`), each exit 0 with no failure line: tests/lib/lib.fs; tests/core/iota.fs, mixed-infer.fs,
mixed-infer-coverage.fs, string-literals.fs, env-import.fs; tests/front/front.fs, meta.fs, menv-run.fs, whnf.fs,
defeq.fs, elab.fs, goals.fs, constructions.fs; tests/author/author.fs; tests/cli/leanforth.fs;
tests/present/term-printer.fs and check_golden.py.

- **B1, fixed in `3a482385`.** `lf-made-term` is called by level-map.fs `lmap-sort-new`, lib-decode.fs `lbd-nat`,
  infer.fs `if-sort-new`, and in the kernel by mixed-infer.fs `lf-minfer-sort`, iota.fs `lf-iota-ctor-const` and
  string-literals.fs `lf-sx-const` (under the owner's rule of 2026-11-19, recorded in OWNER_DECISIONS.md). A grep
  for the phrase's other spelling, `if drop outcome-ok else outcome-full no-result then`, found one more:
  elab-term.fs `et-lit`, converted too. nat-offset.fs's alias `no-made` (a word whose body was only
  `lf-made-term`) is gone; its two callers call `lf-made-term`.
- **B2, fixed in `3a482385`.** `ok-or-none` in meta-env.fs `me-decoded`, elab-term.fs `et-rel-done` and infer.fs
  `idl-assign`. The accepted group c0d6 (`lf-menv-sunfold`, `lf-menv-matcher`) is re-keyed cd86 in the baseline,
  same members and reason.
- **B3, fixed in `3a482385`.** `room-result` in meta-spine.fs `lf-meta-app`, nat-offset.fs `no-seek` and `no-app`,
  level-map.fs `lmap-const-new` and assign-check.fs `ac-lam`; the grep for the `outcome-full no-result` spelling
  found elab-term.fs `et-sort-mvar`, converted too.
- **M1, fixed in `1e0903d7`.** env-import.fs pins `why-answers ck-again# ck-checked# ck-saved# -> 16 56 107` after
  its stale-ok run. Planted faults, each caught: `cf-ck-slot-inverted` (r4), `cf-ck-fresh-counts-taken` (r6),
  `cf-ck-saved-inverted` (r7), `cf-ck-again-any-why` (r9), all by tests/core/env-import.fs;
  `cf-kept-at-inverted` (r10, tests/front/constructions.fs); `cf-pf-inner-one-short` (r12, check_author.py);
  `cf-pp-last-first` (r14, check_golden.py); `cf-pp-shown-one-short` (r16, tests/present/term-printer.fs).
- **L1, fixed in `630b5c39`.** find.fs and FORTH_LIBRARY.md: x stays below the count; each test is given a copy of
  x above it.
- **L2, fixed in `3a482385`.** nat-offset.fs requires core/generation-handles.fs (so do lib-decode.fs,
  elab-term.fs and iota.fs, which now call `lf-made-term`).
- **L3, fixed in `3a482385`.** OWNER_DECISIONS.md's report line says core/terms.fs's new line was wrapped by hand
  to stay under 90 characters, tokens unchanged.
- **L4, fixed in `630b5c39`.** `ck-verdicts#` is `ck-inputs-passing# ( xt -- n )`, body
  `>r 0 lf-input-count r> count-index`; source.fs's comment is split between `lfa-token-at` and `lfa-token!`.
- **Faults re-targeted** by the fixes (named in `3a482385`): `cov2-str-const-refusal-rejected`,
  `fe-env-refused-handle`, `fe-declevel-assign-kept`; each still caught.
- **The reviewer's question on `ck-checked#` (answered, behaviour not changed).** In the stale-ok run of a
  snapshot alone (env-import.fs, `true snap-stale-allowed !` then `nested-snap carry-alone`), nothing is imported
  or carried, so `ck-passing?` is false and `ck-taken?` answers false for every declaration: `ck-fresh?` ("final,
  not taken") then holds for all 107 slots, which were in fact read from the snapshot (`ck-saved#` is 107 too).
  So outside an import run `ck-checked#` does not count what its name says. Nothing shows the wrong number:
  both readers, the text report's `cli-import.` (leanforth.fs) and the JSON's `cj-import` (check-json.fs), print
  it only when `ck-importing?`, where "taken" is exactly "read from the snapshot"; the summary line computes
  "checked in this run" as `lf-input-count ck-saved# -` (0 here). Recommendation, for a plan row rather than this
  clean-up: make `ck-fresh?` also refuse a slot whose origin is saved (`ck-saved? 0=`), or say in its comment that
  the count is meaningful only while importing.
