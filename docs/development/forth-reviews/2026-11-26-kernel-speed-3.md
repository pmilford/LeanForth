FORTH REVIEW: kernel-speed-3

Range: ea791fac..c9ff49e6 (net diff of `src` and `tests`). Worktree: /home/peter/code/LeanForth/.claude/worktrees/agent-a220eb5ef124473e3.
Findings: High 0, Medium 2, Low 6.
Verdict: **merge after fixes.** Before merging, finding 1 needs a test and a fault entry, finding 2 must be fixed or cite a plan row (the reuse rule makes it blocking), and finding 3 needs the design text widened. This AI review does not replace the owner's review of the kernel change.

Main result: I found no difference in verdict, fuel, result node or diagnostic when the heap grants every request. I compared every fuel limit from 1 up, on generated terms, on both engines (tables below). Every difference I found is under a heap refusal, and those differences go beyond what the declared exception says (finding 3).

## Findings

**1. Medium: a fail-closed check of the quick path has no test (`src/core/scratch-marks.fs:91-92`, used at `src/kernel/mixed-open.fs:341`).**
- `lf-scratch-counts?` stands in for the store-count refusal of `lf-open-marked` and `lf-scratch-push` on the closed-root path.
- My planted fault M4 (`: lf-scratch-counts? ( -- flag ) true ;`) survives `mixed-instantiate.fs`, `mixed-shift.fs`, `mixed-beta.fs` and `check-declaration-ndjson.fs`.
- No entry in `faults.d/kernel-speed-3.toml` covers it.
- Failing input: make `lf-levels` (or `lf-crefs`) have an invalid count, then run `closed-11 subst 1 lf-instantiate-rev`. Main gives `-1 outcome-invalid` (the scratch push is refused). With M4 the branch gives `closed-11 outcome-ok`.
- The term store's own count does not show it: a store node then fails `lf-term-data@` and takes the walked path.
- Fix:
  - In `tests/core/mixed-instantiate.fs`, corrupt each family's count in turn and expect `-1 outcome-invalid` with the fuel unchanged.
  - Add a unit test of `lf-scratch-counts?` for each family.
  - Add a fault entry.

**2. Medium (reuse; blocks until fixed or given a plan row): the per-node decision is written twice in `mixed-open.fs`.**
- `lf-open-look` / `lf-open-pair?` (258-266) repeat `lf-open-visit` / `lf-open-pair` / `lf-open-again` / `lf-open-binary` (162-165, 246-253): the same tests in the same order (readable, tag, skip, known, children, stuck).
- The old copies stay only because abstract "keeps the frame machine". No comment says why.
- The two copies are kept in step by hand, and each has its own faults. A fault in the abstract copy is caught only by abstract's tests.
- Factoring: send abstract through the walk too, so there is one path.
  ```forth
  : lf-open-enter ( node frames -- ... frames next ) lf-walk-node 0 ;
  ```
  Then delete `lf-open-visit`, `lf-open-pair`, `lf-open-again`, `lf-open-binary`, `lf-open-second` and `lf-open-updated`. Abstract's leaf, skip and join are already in `lf-open-leaf`, `lf-open-skip?` and `lf-open-update`.
- If abstract has to keep the frame machine, write the reason in a comment and cite a plan row.
- I did not test the merged path.

**3. Low: the declared exception is narrower than what heap refusals actually change (`docs/design/TERM_STORE.md:403-411`).**
- P1 makes two memos per record, so `lf-rmemo-make` allocates twice as many blocks. That shifts where a refusal lands for all four `replace-memo` users, including abstract, shift, `lf-minst` and inductive-nested.
- The quick path also skips the scratch-mark push and its refusals (slab growth; numbers at max-n).
- My refusal sweep: four terms × five modes × refusal k=1..11, gforth, store rolled back before each probe. 25 of 55 points per term differ, for example:
  - 40-lambda chain over `app(#0,#25)`, instantiate with two terms, k=2: main gives `full` with 1000 fuel left; the branch gives `ok` with 919 left.
  - Abstract (mode 4) differs at k=2..7.
  - DAG of depth 11, k=1/2: main gives `exhausted` (memo refused, so the walk is exponential); the branch gives `ok` with 977 left.
- Also: if one of the two memos is refused, `lf-rmemo-live?` is false. Every later begin then frees and remakes both, dropping the stamped scope entries that main kept.
- Fix: widen the text to "any heap refusal (frame stack, either replace memo, scratch-mark stack) may land at another step; the outcome and fuel at a refused allocation may differ, including full against ok". Test one memo refusal. Optionally, make `lf-rmemo-ready` remake only the memo that is not live.

**4. Low: the quick path's memo call for the scope mode has no test (`mixed-open.fs:347`).**
- My fault M5 (the `lf-open-stamp ?dup if … lf-open-end then` clause deleted) survives all four tests.
- Without it, a crowded table (more than 2^20 entries) would not be emptied at the same call as on main, so later scope closings keep different entries and spend different fuel.
- Fix: after a closed-root `lf-instantiate-scope`, assert that `lf-open-memo lf-rmemo-stamp @` is x's identity + 1 and that `lf-rmemo-base` equals the table count.

**5. Low: negative stamps now collide with the scratch memo's call numbers (`replace-memo.fs`, `lf-rmemo-begin` / `lf-rmemo-scratch?` / `lf-rmemo-in`).**
- `lf-rmemo-begin` treats any non-zero stamp as stamped. `lf-rmemo-scratch?` (`stamp 0<`) then sends a negative-stamped call to the scratch memo.
- Its entries are never cut on failure, and an unstamped call with the same number would find them (another substitution's results).
- Not reachable today: the only stamp is a live store free variable's identity + 1, which is at least 1. But the header still says "a stamp other than 0".
- Fix: document "stamp ≥ 0" and fail closed:
  ```forth
  : lf-rmemo-begin ( stamp memo -- )
    over 0< if nip 0 swap then
    2dup lf-rmemo-ready over if lf-rmemo-stamped else nip lf-rmemo-unstamped then ;
  ```
  Add a test.

**6. Low (doc): the `replace-memo.fs` header says a call that THROWs leaves entries that "the count shows … until the memo is emptied".**
- In fact `lf-rmemo-held!` at the next unstamped call's begin sets held to the scratch count. From then on `lf-rmemo-count` no longer shows them.
- It is harmless: after a THROW the frames stay busy until `lf-open-reset` / `lf-mixed-rebuild-reset`, which empty both memos, and `lf-nest-memo-begin` still empties when the count is not 0. Correct the sentence.

**7. Low (re-entrancy and generality): globals and the `frame-job` cell.**
- New globals: DEFERs `lf-walk-look` and `lf-walk-join` (`open-walk.fs:38-39`) and the constant `lf-walk-first`.
- The DEFERs are written only at load (`mixed-open.fs:267-268`) and, temporarily, by the test's `stubbed`. They are constant after load, so they are safe with several contexts and workers. They have no seal guard, the same as the existing `lf-open-unchanged?` hook.
- Because the pair is global, the walk has a single client: a second pass setting them would overwrite instantiation's steps.
- The walk also keeps its base in `frame-job`, a field `lib/frame.fs` reserves "for the pass".
- To make it the shared replace walker (item 7, not designed here):
  - take look and join from a two-xt walker record given to `lf-walk-node`, or kept in the frames' job;
  - keep the base on the frames stack, not in `frame-job`;
  - move `lf-open-pair?`'s skip/known/children/stuck order into a shared word.
- No new VARIABLE, VALUE or CREATEd table. `replace-memo.fs` adds record fields only. `lf-rmemo-scratch-most` is a constant.

**8. Low (style): `lf-open-quick?` (`mixed-open.fs:343-344`).**
```forth
: lf-open-quick? ( node -- flag ) dup lf-open-closed? if lf-open-root? else drop false then ;
```

## Checked and holding (by reading, and by the runs below where named)

- **Walk against the frame machine, for every node kind** (app, lam, pi, let, let-nondep, projection, bvar, fvar, constant, symbolic sort, plain Sort, unknown tag 17, malformed bvar):
  - fuel is charged at the same moment (`lf-walk-fuel?` = `frame-admit`'s fuel test);
  - the binder check comes before any child is charged;
  - the second child is visited only after the first child's subtree returns, one binder deeper;
  - the leaf tests are shared code (`lf-open-leaf`);
  - memo keeps happen only in `lf-open-update`, as before; kept children were not kept in the memo before either.
- **Closed root:** a data word of "unknown" has loose range all ones, so it is never taken as closed. An input record with code 0 has tag 0, so it is not binary and not quick. A store node goes through the checked `lf-term-data@`.
- **Restoring state on failure:** context, `frame-used` and the scratch marks are restored on failure (my faults M2, M6 and M8 are caught).
- **Nested passes:** a nested pass is refused as before, because the root's frame depth stays 1 during the walk.
- **Depth:** the walk is iterative. A chain of 200,000 lambdas on the default return stack is ok on both trees, with identical fuel (9,599,999 left), 1.26 s and 72 MB on the branch; frame capacity is 524,288 cells on the branch against 1,048,576 on main.
- **P1:**
  - keys hold the node identity, which never rolls back;
  - call numbers are reused only after the memo is emptied (a refused remake leaves it not live, so the entries are gone);
  - nesting is impossible because every `lf-rmemo-begin` caller sits behind a busy or `frame-budget` refusal;
  - stamped-call count and crowding are unchanged on non-refusal paths.

## Runs (`ulimit -u 500`; scratch copies under /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-ks3/{br,mn})

| Run | Result |
|---|---|
| Differential harness `h/diff-walk.fs`: random trees of 6 binary tags with good and bad leaves, DAGs; 5 modes (inst 1, inst 2, rev, scope, abstract); fuel 1..69. 10 seeds × sharing on/off × gforth and gforth-fast = 40 runs, 14,040 lines each | branch = main, byte for byte |
| Large batches (6 seeds) plus right/left chains of 30 and a shared DAG of depth 10, fuel 1..79; both sharing settings, both engines = 16 runs | identical |
| Heap-refusal sweeps (gforth only) | 25 of 55 points per term differ; see finding 3 |
| 12 planted faults (M1-M12) | 10 caught; M4 and M5 survive (findings 1 and 4) |
| decide slice `check --json --resources`, gforth-fast: main j1 against branch j1 and j4; `--fuel 2000` (740 accepted / 478 unknown / 72 exhausted); `--fuel 20000` | identical outside measured/settings/run; exit codes 0/0 and 3/3 |
| `scripts/mutants.py --check --history --base main` | 3860 entries, exit 0. The revert's message (a96646ff) names the 13 faults removed and the 7 whose old text is main's again |
| `forth-metrics.py --words 10` on the 4 changed files | see below |
| `check-duplicates.py` | 187 baseline groups, none new |
| `check-lib-callers.py` | ok |
| KERNEL_SPEED arithmetic | 656.5−637.0=19.5; 182.1−174.4=7.7; 651.0/31.0=21.0; 191.3/9.7=19.7. Loads stated; one run each |

## Forth style

Metrics (4 files, 167 words):
- 74% of words are 1-2 lines, 25% are 3-5, and one is 6-10 lines: `lf-open-leaf`, 7 lines, unchanged, a CASE.
- No missing stack comments, no locals, no new globals.
- `open-walk.fs`: 19 words, 2 deep shuffles, 2 return-stack ops.
- `replace-memo.fs`: 4 deep shuffles, 20 return-stack ops.
- `mixed-open.fs`: 1 line over 90 characters.

Style findings are 2, 7 and 8. Stack comments match the code where I checked: `lf-walk-node`, `lf-walk-into`, `lf-walk-up`, `lf-open-pair?`, `lf-rmemo-both`, `lf-rmemo-in`.

## Reuse

- **Searched:** FORTH_LIBRARY.md entries frame/walk/memo; `src/` for `lf-walk-*`, `lf-rmemo*`, `frame-job`, `lf-scratch-*`; the other replace passes (`mixed-shift.fs`, `mixed-instantiate.fs`, `inductive-nested.fs`); `check-duplicates.py`; `check-lib-callers.py`.
- **Result:** no copy of a library word. One in-module duplicate (finding 2). `open-walk.fs` is a candidate for the shared replace walker; what that would take is in finding 7.

## Not done

- The 10 malformed or rejected exports (exit code, stdout and stderr compared).
- The planted faulty check on the constant fixture at `--jobs` 1, 2 and the default (I relied on the implementer's record).
- Input-tier nodes in the harness (by reading only).
- Planted faults on gforth-fast; refusal sweeps on gforth-fast.
- Gforth 0.7.3.
- A planted fault in the nested-hook path.
- Init (the implementer's Init reports were not compared; I checked only that their saved decide reports match).

Harness and scripts are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-ks3/h/ (`diff-walk.fs`, `mut.py`, `run.sh`, `run2.sh`, `e2e.sh`).

## Resolution (fix round, 2026-11-26)

The reviewed net diff (`ea791fac..c9ff49e6`) leaves out the stored-hash commits `86d9d31a` and `7f6a3ac9`, which
`a96646ff` reverted. The code fixes are one commit, `b7711ad5`; the documentation fixes and this record are the
commit that adds this section.

| Finding | Resolution |
|---|---|
| 1 (medium) | Fixed in `b7711ad5`: `tests/core/mixed-instantiate.fs` tests `lf-scratch-counts?` with each family's seal broken (terms, levels, constant references) and a closed root `closed-11 subst 1 lf-instantiate-rev` over each, `-1 outcome-invalid` with the fuel unchanged; fault `ks3-scratch-counts-always-true` (M4), caught. |
| 2 (medium, reuse) | Planned: plan row 9.4.8z9 (abstract through the walk, the six frame-machine words deleted). `mixed-open.fs` now says why abstract keeps the frame machine and cites the row (`b7711ad5`). |
| 3 (low) | (a) Fixed in the documentation commit: TERM_STORE.md "As landed" and KERNEL_SPEED.md section 0 declare every heap refusal (the frames' stack, either replace memo, the scratch-mark stack) may land at another step and change the outcome and fuel at a refused allocation, including full against ok; nothing differs when the heap grants every request. (b) Fixed in `b7711ad5`: a refusal of the scratch memo (made second) keeps a stamped call's keep, find and cut, and gives an unstamped call a miss. (c) Done in `b7711ad5`: `lf-rmemo-make` remakes only the memo that is not live (the scratch memo's numbering restarts only when it is made), and `lf-rmemo-end` acts when the memo its call keeps in is live, so a failed stamped call is cut with the scratch memo refused, as on main; faults `ks3-rmemo-remake-both` and `ks3-rmemo-end-needs-both-live`, caught. |
| 4 (low) | Fixed in `b7711ad5`: after a closed-root `lf-instantiate-scope` the memo's stamp is x's identity + 1 and its base the table's count (the base set to max-n first); fault `ks3-closed-root-scope-memo-skipped` (M5), caught. |
| 5 (low) | Fixed in `b7711ad5`: `lf-rmemo-begin` takes a negative stamp as 0 (every caller passes 0 or an identity + 1, so none changes); the header says stamps are >= 0; a test that a negative stamp naming a scratch call's number finds none of its entries; fault `ks3-rmemo-negative-stamp-kept`, caught. |
| 6 (low, doc) | Fixed in `b7711ad5`: the header says the count stops showing a thrown unstamped call's entries when the next unstamped call begins, and that the passes' recovery empties both memos. |
| 7 (low) | Planned: plan row 9.4.8z9 (look and join from a walker record, the base on the frames' stack instead of `frame-job`). |
| 8 (low, style) | Fixed in `b7711ad5`: `lf-open-quick?` as the review writes it (two lines, to stay under 90 characters); the form is a member of the false-positive duplicate group `8c62bb325216` (`dup a? if b else drop false then`), whose record lists it in `452e7d52`. |

Checks of the fix round (`ulimit -u 500`): the five new faults caught (`scripts/mutants.py --only ...`, gforth);
`tests/core/mixed-instantiate.fs`, `mixed-shift.fs`, `mixed-beta.fs`, `check-declaration-ndjson.fs` and
`heap-refusals.fs` pass on gforth and gforth-fast; `bin/leanforth check --json --resources
tests/front/decide-slice.ndjson` on gforth-fast at `--jobs 1` and `--jobs 4` is identical to a `git archive` copy
of main `ea791fac` outside `measured`, `settings` and `run` (1,290 accepted, fuel 2,649,895);
`scripts/mutants.py --check --history --base main` passes (3,865 entries).
