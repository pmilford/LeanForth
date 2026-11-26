FORTH REVIEW: kernel-reads-1

Range: `0e73e92c..4103a9fd` (commits 2ca4449b code, tests and faults; 19f2d86d docs; 4103a9fd profile note). Worktree: /home/peter/code/LeanForth/.claude/worktrees/agent-a1c4bdb62fc1f019b

**Findings by severity:** Critical 0, High 0, Medium 1 (blocking under the reuse rule), Low 10, Info 2.

**Verdict: merge after fixes.** Finding 1 blocks the merge under the reuse rule (FORTH_REVIEWER.md step 3a, AGENTS.md "Reuse first"). The fix is a one-line, behaviour-preserving change. The Low findings can be fixed in the branch, or the style item recorded as a plan row.

**The claim "no check moved or weakened, verdicts identical" held up.** None of my probes broke it:
- My own edge values, on gforth and gforth-fast.
- 10 planted faults of my own in terms.fs: all caught.
- The planted wrong check: exit 5 at every job count.
- The decide slice: identical to main at jobs 1 and 4.
- 23 malformed or rejected exports: identical exit codes, stdout and stderr.
- The implementer's two Init reports: identical outside `measured`, `settings` and `run`.

## Findings (actionable first)

**1. Medium, blocking (reuse). `src/core/terms.fs:721` re-implements the new library word `context-offset` and leaves a general context operation inside a module.**
- `: lf-member-in ( addr context -- addr' ) swap lf-context @ - + ;` is `swap context-offset +` written out by hand.
- `context-offset` is the word this branch adds as public in `src/lib/context.fs:285`.
- `lf-member-in` ("a member's address in another context: every context has the same layout") is pure context-layout knowledge with 16 callers in four files:
  - `src/core/input.fs:511-524`
  - `src/core/terms.fs:729,743`
  - `src/import/feed.fs:675`
  - `src/core/constant-references.fs:399-407`
- AGENTS.md says every existing copy is replaced in the branch that adds the library word.
- `check-duplicates.py` misses it because the phrase is only 3 tokens.
- Fix, as the minimum before merge, in terms.fs:
  `: lf-member-in ( addr context -- addr' ) swap context-offset + ;`
- Better: move it to `lib/context.fs` as a public word (all four files already load it), with a test in `tests/lib/context.fs` (an address in a second context's record and in a store header), and rename the 16 callers:
  `\ addr's place in another context (every context has the same layout).`
  `: context-in ( addr context -- addr' ) swap context-offset + ;`

**2. Low ×7: risky paths without a planted fault in `tests/mutants/faults.d/kernel-reads.toml`.** I planted each of these myself (scratch runner `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-kr1/mut.py`). `tests/core/check-declaration-ndjson.fs` catches every one, but none is pinned. Add each as a fault with `test = "$GFORTH tests/core/check-declaration-ndjson.fs"`:
- a. Tier boundary (index = base read as input), `lf-term-valid?`:
  `lf-term-base 2dup u< if drop lf-tin-valid? exit then - lf-terms store-at? ;` → `lf-term-base 2dup 1+ u< if ...` (the test segfaults, rc 139).
- b. `lf-term-at` record offset from the count, not the capacity:
  `dup store-block @ swap store-capacity @ cells + + ;` → `... store-count @ ...`
- c. Block read once at load: `lf-terms store-block @ constant blk0`, used in `lf-term-at` in place of `dup store-block @`.
- d. Identity bounded by the capacity, not the count, `lf-term-store-identity`:
  `dup lf-terms store-at? 0= if` → `dup lf-terms store-capacity @ u< 0= if`
- e. Entry bit dropped in `lf-tin-record`:
  `head-tag swap 1 and lf-tin-entry @ ;` → `head-tag swap drop 0 lf-tin-entry @ ;`
- f. `lf-tin-second@`'s other branch takes the wrong half:
  `else nip lf-tin-other@ nip then ;` → `... drop then ;` (`kr1-tin-record-other` covers only `lf-tin-first@`).
- g. `lf-term-data-word` reads the wrong field:
  `- lf-term-at lf-term-data-at + u32@ ;` → `... lf-term-second-at ...`

**3. Low (style, FORTH_STYLE.md:22 "factor repeated phrases"). `lf-term-base 2dup u< if drop` is written out 7 times**, at terms.fs:461, 470, 481, 489, 494, 497 and 566.
- It replaced a named predicate (`lf-term-input?`).
- The comment at about :457 justifies the single base fetch but does not name the phrase.
- A portable factoring that keeps both the single fetch and the no-call cost is an immediate POSTPONE word, the same pattern as context.fs's `member-body`:
  ```
  \ Compiles the reads' split: ( index -- index base flag ), flag true for
  \ an input node; the true branch drops base, the other subtracts it.
  : lf-term-split, ( -- ) postpone lf-term-base postpone 2dup postpone u< ; immediate
  : lf-term-tag@ ( index -- tag ) lf-term-split, if drop lf-tin-tag@ exit then - lf-term-at u32@ ;
  ```
- The design said "no macros". If that stands, record the phrase in the baseline or as a plan row with the next speed group (item 9 touches the same words).
- The re-keyed accepted pair `lf-term-first@`/`lf-term-second@` (finding 7b1d368100da) is the same two members with the same reason, plus "the base fetched once". I agree with accepting it: a defining word for two instances is not worth it, and a shared field word costs a call per read.

**4. Low. `context-offset` (`src/lib/context.fs:285`) does not refuse an address outside the context, and its comment does not say "Unchecked".**
- Reproduction: `create outside 16 allot outside context-offset .` prints 26782895555272, with `context-bytes` 16.
- A constant built from that reaches wild memory in every context.
- The word runs only while files load, so a guard costs nothing per read:
  `: context-offset ( addr -- u ) lf-context @ - dup context-bytes u< 0= abort" context-offset: not in the context" ;`
- Add a test that it refuses a CREATEd address.

**5. Low. The fused `hash-fmix` is not tested on a million inputs, as the design said.**
- Binding change 4 of KERNEL_TERM_READS.md says "compared with the old word on a million inputs in its test".
- `tests/lib/hash32.fs` `randoms-same?` runs 100,000 + 100,000 random values plus edges, about 200k. The commit message states that honestly.
- Fix: raise the loop to 500,000, or amend the design line.
- My own run: about 2,000,000 comparisons on both engines, 0 differences (details below).

**6. Info. The 7.5-point gain is measured on wall time, and the branch's run was the more loaded one.**
- The branch's check phase: 712.4 s wall against 701.4 s CPU, load 1.9-3.8. Main's: 770.3 wall against 770.2 CPU, load 0.6-1.2.
- On CPU time the gain is 68.8 s, 8.9 points, which is the low edge of the 9-12 estimate. KERNEL_SPEED.md gives both CPU numbers but computes the gain only on wall time; add the CPU figure.
- The arithmetic checks: 770.3 − 712.4 = 57.9 s, 7.52 %; 712.4 / 38.4 = 18.55, written 18.6; 770.3 / 38.4 = 20.06, written 20.1.
- Loads and "one run each" are stated.

**7. Info (test classes).**
- Class 5, 32-bit cells: not runnable here (no 32-bit Gforth). By reading it is identical: `u32-mask` is `$10000 dup * 1-`, all ones on 32-bit; `4 lshift` and `16 *` wrap the same; `store-at?` compares unsigned.
- The module's own `tests/core/terms.fs` misses 2e, 2f and an input-validity weakening (`drop lf-tin-valid?` → `drop lf-tin-code 0<>`). The input tier is reached only through check-declaration-ndjson.fs, which catches all three.

## The questions, briefly

1. **Old against new.** In every changed word the conditions, their order and their stack effects match: `lf-term-valid?`, `-identity` (validity first, then the identity), `-fields`, `-tag@`, `-first@`, `-second@`, `-data-word`, and `lf-tin-record` against `lf-tin-code`'s order (tag, then entry bit). My harness was the implementer's old chains plus my own values:
   - 0, 1, −1, −2, max-n, min-n, max-n−1
   - 2^31±1 and 2^32±1
   - base−1, base, base+1
   - base+count±1, base+capacity±1, base+limit±1
   - 2^(cellbits−4)+base and +1 (the shift wraps to 0), 2^(cellbits−5)+base
   - slot addresses at −1+base and at max-n
   - after growth; in a fresh context with base 0 (grown twice, to capacity 128 and then 256)
   - with marks.ndjson; with kinds.ndjson, which has 1087 input numbers of code 0

   Result: 0 differences on gforth and gforth-fast.
2. **`lf-term-at` and `lf-term-id-at`.**
   - The block and the capacity are re-read from the header on every call; my fault 2c (block cached at load) is caught.
   - The layout: identity cells come first, at block + r cells, and the records after them, at block + capacity cells + 16r (store.fs:82-87). The brief had this the other way round. The code is right: capacity, not count (fault 2b caught).
   - The constants are offsets read at the same moment from the same `lf-context @`, so they are right in any context and after the main context is resized.
   - The layout only grows, and offsets are fixed once given (context.fs:227); a member added earlier in the source is simply compiled into the new constants. There is no load-order assumption beyond "after the member exists".
   - A non-heap `lf-terms` cannot exist: `lf-terms-make` aborts, and `context-new` catches that.
   - The load-time `/lf-term 16 <>` guard is portable (`[if]`, `.(`, `abort`).
3. **`context-offset`.** It is public, listed in the header interface, FORTH_LIBRARY.md and LIBRARY_WORDS.md, and has an example and tests; its fault and a `context-main` variant are both caught. For an address outside the context, see finding 4.
4. **`hash-fmix`.** Bit-identical by inlining; my run is under "What I ran". On 32-bit cells the mask is all ones, so it is identical there too. On 0.7.3 it was checked by reading only: only standard words are used. `hash-mul` stays, used by FNV.
5. **Faults.** My 10 planted faults were all caught by check-declaration-ndjson.fs; tests/core/terms.fs catches 7 of them. The 14 kr1 faults' `old` texts and the requoted `base-zero-crash` each occur exactly once.
6. **End to end.** All as expected; see the table below.
7. **Baselines.** `tests/forth-quality-baseline.json` is untouched. Metrics show no new long words, globals or shuffles (summary below). check-duplicates: 187 baseline groups, none new or grown. check-lib-callers: every lib file is used or has a plan row.
8. **History and docs.** The commit names all 14 faults and the `base-zero-crash` requote. KERNEL_SPEED.md's numbers recompute (finding 6).
9. **Why 7.5 points against 9-12, and why `lf-term-base` stays at 3.0 %.**
   - Partly measurement: on CPU time the gain is 8.9 points (finding 6).
   - `lf-term-base` is still a called colon word, once per read. Most reads already called it once before, through `lf-term-input?`, so its call count barely fell. What went away was its nested `lf-term-view` call (3.63 → 0.36) and `lf-term-input?` (1.42 → 0.11). A four-cell body's cost is mostly the call and return, so its own share stayed.
   - A further safe step exists in this file: compile the base fetch into the read words, and in their store branches use one `lf-context @` for both the view's base and the store header (`lf-terms` is still 0.57 through `store-at?`). Neither moves a check.

## Reuse (step 3a)
- **Searched:** FORTH_LIBRARY.md (context.fs and hash32 rows), LIBRARY_WORDS.md, and src/ by name and by shape, with the patterns `lf-context @ -`, `store-block @` outside store.fs, `rshift xor`, `fmix` and `murmur`.
- **Ran:** `scripts/check-duplicates.py` and `scripts/check-lib-callers.py` on the head copy.
- **Found:** `lf-member-in` (finding 1). There is no other copy of `context-offset`, of the fused slot or of fmix; sha256's `rshift xor` lines are its own sigma functions.

## Re-entrancy (step 4a)
- The only new globals are three CONSTANTs, `lf-terms-at`, `lf-tview-base-at` and `lf-tview-records-at`, set once while terms.fs loads and never written after.
- There is no new VARIABLE, VALUE or written CREATE.
- The reads use the per-task `lf-context`, and the second-context test and my base-0 context agree with the old chains.

## Forth style: metrics
`forth-metrics.py --words 10`, base → head:

| File | Words | 1-2 lines | 3-5 lines | 6-10 lines | Globals | Constants | Deep shuffles | R-stack ops |
|---|---|---|---|---|---|---|---|---|
| terms.fs | 211 → 216 | 159 → 162 | 49 → 51 | 3 → 3 | 8 → 8 | 29 → 32 | 25 → 25 | 53 → 53 |
| context.fs | 75 → 76 | 61 → 62 | 14 → 14 | — | 6 → 6 | — | — | — |
| hash32.fs | 6 → 5 | — | 0 → 1 | — | — | — | — | — |

- hash32.fs's 3-line word is `hash-fmix`; its comment says why it is written out.
- No word is longer than 6 lines, and the longest ten are unchanged.
- No PICK or ROLL in source. The `3 pick` is in the test's `3=` only.
- Style findings are 3 and 4 above.

## What I ran

All runs used Gforth 1.0 from `.tools`, under `ulimit -u 500`, one process at a time, on `git archive` copies under `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-kr1/` (`base` = 0e73e92c, `head` = 4103a9fd, `planted`).

| Probe | Result |
|---|---|
| Edge harness `.../review-kr1/head/tests/core/mine.fs`, gforth and gforth-fast | 0 differences; the branch's 6845-number check also passes |
| 10 planted faults in terms.fs, via `scripts/gforth-strict.sh`, on check-declaration-ndjson.fs and core/terms.fs | 10 of 10 caught by the first; 7 of 10 by the second |
| hash32 mask faults (2), `context-offset`→`context-main` fault, tests/lib | all caught |
| fmix `.../review-kr1/fmix.fs`: 64 single bits ×3, 1M LCG cells and their 32-bit masks, 0..999,999 | 0 differences on both engines; Murmur3 vectors 514E28B7 and 81F16F39 match |
| Planted check fault on constant-fixture: jobs 1, 2, default | 5 / 5 / 5 (head unmutated: 0 / 0 / 0) |
| decide slice, gforth-fast, `--json --resources`, jobs 1 and 4, base vs head | identical outside measured/settings/run, stderr identical; check phase 3.38→2.88 s (j1), 1.50→1.26 s (j4) |
| 23 exports with `--no-manifest --jobs 1`: 15 check-declaration-cases, 5 check-block-cases, 3 tests/cli | exit codes (0, 1, 2, 3, 4), stdout and stderr identical base vs head |
| Implementer's Init before/after JSON, diffed by me | identical outside measured/settings/run |
| `context-offset` probe `.../review-kr1/off.fs` | no refusal outside the context (finding 4) |
| forth-metrics, check-duplicates, check-lib-callers | as above |

## Not run or not looked at
- Init, `make tier`, the suites and `make cover-changed`: not run, as you asked; the tier passed on this head.
- The implementer's 14 kr1 faults: not re-run (their recorded runs).
- Gforth 0.7.3 and 32-bit cells: by reading only.
- The profile and `make profile-check`: not re-run.
- LIBRARY_WORDS.md: not regenerated.
- The design review document: only its binding section read.

This AI review does not replace the owner's required human review of trusted semantics and interfaces.

## Resolution

The fix round (2026-11-25) ran on the branch after its rebase on main `86e2448b`, which renumbered the
reviewed commits: `2ca4449b` is `a7da6ac4`, `19f2d86d` is `0fb1dcd8`, `4103a9fd` is `e893f8be`. Main's simp
slice SL1a-1 had taken plan row 9.4.8z2, so this branch's row and its citations became 9.4.8z3 (`b3c21372`).

- **1, fixed in `1b6818ad`.** `lf-member-in` is gone from `src/core/terms.fs`; `src/lib/context.fs` has the public
  word `context-in ( addr context -- addr' )`, `swap context-offset +`, in the header's interface,
  FORTH_LIBRARY.md and LIBRARY_WORDS.md (regenerated). Its callers, 14 calls (the review's 16 lines counted
  the definition and its comment), are renamed in `core/input.fs`, `core/terms.fs`,
  `core/constant-references.fs` and `import/feed.fs`. `tests/lib/context.fs` reads a second context's record
  cells and store count through it, writes a cell there, and checks it in the current context; faults
  `kr1-context-in-current` and (finding 4) `kr1-context-offset-unguarded` are caught by that file.
- **2a-2g, fixed in `1b6818ad`.** The seven faults are listed in `tests/mutants/faults.d/kernel-reads.toml`, each
  with `test = "$GFORTH tests/core/check-declaration-ndjson.fs"`: a `kr1-valid-boundary` (caught, exit 139),
  b `kr1-at-count`, c `kr1-at-block-once`, d `kr1-identity-capacity`, e `kr1-tin-entry-dropped`, f
  `kr1-tin-second-other`, g `kr1-data-word-field` (each caught, exit 1); `python3 scripts/mutants.py --only`
  of the nine new faults and the changed `kr1-context-offset-cell`: 10 run, 10 caught.
- **3, planned in plan row 9.4.8z4** with the further safe step of question 9 (the base fetch compiled into
  the read words; one context fetch for the view's base and the store header), as the start of the next
  kernel speed group.
- **4, fixed in `1b6818ad`.** `context-offset` aborts with "context-offset: not in the context" for an address
  outside the current context (it runs while files load and in `context-in`, never in a read); its comment
  says so. Tests: the context's first and last byte accepted, the byte below it, the byte just past it and a
  CREATEd address refused (THROW -2), and `context-in` on the CREATEd one refused. The fault
  `kr1-context-offset-cell` now quotes the guarded body.
- **5, fixed in `1b6818ad`.** `tests/lib/hash32.fs` compares the fused `hash-fmix` with the old chain on 500,000
  random 32-bit values and 500,000 random cells, plus the edges (48 ms of the file's run on Gforth 1.0).
- **6, fixed in `1b6818ad`.** KERNEL_SPEED.md's "Measured after the fused reads" and section 10's table row give
  the CPU figures (770.2 s -> 701.4 s, 68.8 s, 8.9 points) beside the wall figures.
- **7 (info)**: nothing to change; the missed faults of `tests/core/terms.fs` are now pinned on
  `check-declaration-ndjson.fs` (2e, 2f). The input-validity weakening (`drop lf-tin-code 0<>`) is not
  listed as its own fault; the listed `kr1-valid-input-unchecked` (every input number valid) covers the
  same branch on the same file.
