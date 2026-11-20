# Forth review: cleanup-families-3, clean-up by family, round 3 (2026-11-19)

Branch `cleanup-families-3`.
- **Range:** `93cf381c..b19cd408`: 15 first-parent commits, 14 of them round 3's own. The merge of main (a4bf484b) brought no `src/` change, so it was not reviewed.
- **Round 2's fixes:** their source changes (a14486e7..93cf381c, after 968ff251) were also checked line by line (part "Round 2 closed"). A log row can therefore cover `3a5efff3..b19cd408`.
- **Reviewer:** forth-reviewer (Opus), independent of the implementer.

Findings: 1 high, 2 medium, 5 low (one of the low blocking: reuse).

**Verdict: merge after fixes.**
- **Must be fixed on the branch:** H1, R1 and M2.
- **Fix or plan with a row:** M1. It did not cause a wrong rewrite here.
- **Owner decision needed:** item 3. Its recommendation is below.

Recommendation on item 3 (one line): **keep `one-of2?` and `one-of3?` in `lib/bounds.fs` as written (do not revert 312ab2ce or a80d58c9), and ask the owner to raise bounds.fs's `rstack` baseline from 3 to 6 (shuffles stay at 4), citing this review.**

## Findings

**H1 (high, blocking: a "behaviour-preserving" chain eats a caller's cell on a failure). `src/front/assign-check.fs:215-220`, `ac-lam` (81799585, written by hand).**
- What is wrong: `ac-abstract ( e i type -- type body outcome )` is passed to `ok-apply3`. `ok-apply3` expects a step that gives `result outcome`, but this step gives two values and an outcome.
- What happens:
  - When `lf-meta-head-beta` fails, `ok-apply3` leaves `-1 outcome`: two cells, where a success leaves three.
  - The next `['] ac-lam-of ok-apply2` then drops `-1` and **the caller's top cell**.
  - The base's `ac-lam` gave `-1 outcome` and kept the stack below it.
- Who sees it:
  - `ac-binders` then `nip`s another cell, so `lf-meta-mk-lambda`'s caller loses one.
  - A store-full or fuel refusal in mkLambdaFVars's assignment check becomes a corrupt stack instead of a clean `-1 full`.
  - It is in the front end (untrusted), so the kernel's verdicts are not affected.
- Reproduction: a model of the chain using the real `lib/outcome.fs`, with stubs that have the real words' stack effects (scratchpad `cf3-review/probe/aclam.fs`):
  ```
  old ok:   111 222 85 0        new ok:   111 222 85 0
  old fail: 111 222 -1 6        new fail: 111 -1 6        \ 222 eaten
  ```
- It is the only such site: a script checked the declared stack effect of every step passed to `ok-apply`, `ok-apply2` or `ok-apply3` in src/ (N inputs, `-- result outcome`). Of the 26 steps round 3 added, only `ac-abstract` breaks the rule.
- **Fix:**
  ```forth
  : ac-lam-from ( e i type -- lam outcome )
    -rot cells ac ac-xs @ + 1 lf-meta-abstract ['] ac-lam-of ok-apply2 ;
  : ac-lam ( e i -- lam outcome )
    dup ac-x lf-fvar-type lf-meta-head-beta ['] ac-lam-from ok-apply3 ;
  ```
- **Test:** a sentinel under `lf-meta-mk-lambda`, with the type's head-beta refused. Either use a room sweep of `tests/support/meta-sweeps.fs` over an fvar whose type is a beta-redex, or use defeq.fs:196's setting with the term store full. The test pins `S -1 outcome-full`.
- **Fault:** record the current text as `cf3r-ac-lam-eats-cell`.
- **Prevention:** add the 20-line shape check (scratchpad `cf3-review/tools/apply_shapes.py`) to the duplicate or quality checks.
- **Why nothing caught it:** `make cover-changed` cannot see this kind of bug. The failure branch is inside `ok-apply3`/`ok-apply2` in `outcome.fs`, which other tests run. Round 2 noted the same masking.

**M1 (medium, the `--rewrite` tool; fix or plan). `scripts/check-duplicates.py:1050` (`NOT_A_NAME`), `:1075` (`Pattern.match`), `:384` (`spans`).**

The tool rewrites purely by syntax, and it can produce wrong rewrites that its tests do not cover. Probed with `Pattern("dup $A = swap $B = or", "$A $B one-of2?")`:
- **A wildcard can bind a word that is not a value.** `dup over = swap k = or` becomes `over k one-of2?`, which is a different stack effect. Nothing reports the bindings.
- **A match can start on a parsed name.** `['] dup k1 = swap k2 = or` becomes `['] k1 k2 one-of2?`, and `postpone dup …` is rewritten the same way. The tool never looks at the token before a match (`'`, `[']`, `postpone`, `char`, `[char]`, `to`, `is`, `action-of`, defining words).
- **Defining and parsing words are accepted as wildcard names.** `dup constant = swap create = or` and `dup to = swap value = or` are rewritten. The docstring says a wildcard is "never … a defining word"; `DEFINERS` is not in `NOT_A_NAME`.
- **The tokenizer has gaps.**
  - `spans()` ends an `s\"` string at its first escaped `\"`, and src has such strings (`cli/leanforth.fs:778`, `program/ir-run.fs:518`, `author/errors.fs:305`). The rest of the string is read as code.
  - `[char] (` and `[char] \` open a comment. None occurs in src today.
  - The module docstring says `[char]`/`char` and the word after them are one token. `spans()` does not do that.
- **The recursion guard is direct only.** A site inside a word that the new word calls indirectly is not caught.

None of this affected the 42 sites:
- **All 36 comparison sites:** a script checked every A, B and C. Each is a `constant` (or `true`/`false`/`bl`), so the order of evaluation does not matter.
- **The six refusal-tail sites:** each `$X` is a step word of the right shape (H1's script).
- **No site follows a parsing word.**

Fix:
- refuse a match that follows a parsing or defining word;
- add `DEFINERS` and the parsing words to `NOT_A_NAME`;
- print each wildcard's bindings with their kind (constant, value, `:`), and refuse non-constant bindings unless the caller asks for them;
- handle `\"` inside `s\"`, and join `[char]`/`char` with the next token;
- add a test for each.

**M2 (medium, blocking under "Coverage debt ended": tests and faults of the kernel and import splits).** On my faults (below):
- **F1 survives all 18 core unit files.** It is `ok-apply2` → `ok-apply` in `lf-axd-made` (`kernel/environment.fs:1404`), the typical wrong-arity fault of this refactor. No test reaches the `slab-room` refusal.
- **F3 survives.** It is `lf-nest-grow-ctor` (`inductive-nested.fs:337`) holding the decls room after `lf-nest-ctor-new` writes slot j. That write lands past the block when the decls slab is at capacity.
- **F2 survives.** It is `lf-axd-row-for` (`:1399`) never sharing a row. The implementer saw this ("only loses sharing").
- **No fault is recorded for the 14 new kernel and import step words.** aee52c45 says its probes were caught but records none.

Fix:
- `lf-axd-made` with the rows refusing room (inject the refusal as heap-refusals.fs does), pinning `S -1 outcome-full`;
- `T{ 5 lf-axd-row-for -> 5 outcome-ok }T` and the row count after `1 axiom-trial` (catches F2);
- `lf-nest-grow-ctor` across the decls slab's capacity, then every constructor's kind (catches F3);
- record F1-F3 with those tests, and my caught F4, F5, F6 and F6b, in `faults.d/cleanup-3.toml`.

**R1 (low, blocking: reuse; copies of the new words left in src).** a80d58c9 says the budget family was converted by hand, but these copies remain. Exact copies:
```forth
: lf-pp-spend ( -- flag ) lf-print-fuel cell-spend? ;                 \ present/print-job.fs:183, token for token
: lf-meta-spend? ( -- flag ) mcfg mcfg-budget cell-spend? ;           \ front/meta-config.fs:106 (getter/setter of one cell)
: lfr-spend? ( -- flag ) trun trun-fuel cell-spend? if lf-meta-spend? else false then ;  \ front/tactic-run.fs:240
: lf-tex-angle? ( code -- flag ) $ab $bb one-of2? ;                    \ present/latex-text.fs:72 (numbers: the wildcard skipped them)
: pv-settled? ( code -- flag ) 0 pv-throw one-of2? ;                   \ program/verify-runner.fs:153 (dup 0= swap pv-throw = or)
```
Same shape: convert, or name them in a 9.4.8l row:
- **x kept (`dup` first):**
  - `present/proof-outline.fs:270` `dup lf-class-prop lf-class-type one-of2? if`;
  - `front/whnf.fs:382` `dup lf-tr-all lf-tr-default lf-tr-implicit one-of3? if`;
  - kernel `caches.fs:480` `lf-ci-short` is `lf-check-short?` with x kept. check-declaration.fs requires caches.fs, so move the word there as `lf-short? ( outcome -- flag )` and call it at both sites.
- **Negated (`A B one-of2? 0=`):** cli/check-run.fs:280, front/whnf.fs:620, front/assign-check.fs:164, import/stage-records.fs:436 `more?`, import/snapshot-layer.fs:107 `ly-field?`.

**L1 (low, tests of changed words).** Four comparison-family faults survive the 18 core unit files:
- F8 `lf-check-short?` without full;
- F9 `lf-env-quot-open?` without full;
- F12 `lf-log-level-leaf` without param;
- F14 `unrepeatable?` without invalid.

These are old gaps; the rewrite is identical by construction. Probed one-liners pass on head and catch F8 and F14:
```forth
T{ outcome-full lf-check-short? outcome-exhausted lf-check-short? outcome-invalid lf-check-short? outcome-ok lf-check-short? -> true true false false }T   \ tests/core/check-declaration.fs
T{ outcome-invalid unrepeatable? outcome-full unrepeatable? outcome-exhausted unrepeatable? outcome-ok unrepeatable? outcome-unsupported unrepeatable? -> true true true false false }T   \ tests/core/env-import.fs
```

**L2 (low, style and coverage). `front/defeq.fs:752`: `de-nonrec? ( data -- flag ) lf-structure-like? ;` is an alias added in b19cd408.** Its only purpose is to keep `de-induct-nonrec?`'s text unchanged, so that `cover-changed` does not flag that word's never-run else arm (a constructor whose inductive is not found). The arm is still not tested.

Fix: call `lf-structure-like?` in `de-unit-data?` and `de-induct-nonrec?`, drop the alias, and add a defeq.fs line with a constructor whose inductive has no decoded data (→ false).

**L3 (low, style). `import/snapshot-layer.fs:297`: `ly-fam-tagged` adds a `2 pick`.** The base's shape had none:
```forth
: ly-fam-tagged ( j fam head -- e outcome )
  dup head-tag let-tag? if -rot ly-fam-let else -rot ly-fam-other then ;
```

**L4 (low, the duplicate baseline; 73f22cc1).** All 26 "accepted" groups get one blanket reason. Having read the larger ones, it is honest for most:
- `aux-same?`/`aux-alike?` need two different steps;
- `pq-*-leaf` and `mv-own?`/`mvl-own?` cover parallel stores;
- `if-telescope`/`if-pi-telescope` could share `if-binders ( term xt -- body outcome )`, but only at the cost of an EXECUTE per binder and return-stack use.

Two problems remain:
- **Two plans dropped.** `26354411` (`wc-matcher`/`wc-smatch-sizes`) and `719a2248` (`wc-app`/`wc-smatch`) had concrete "S2 merge B" plans. They now carry the blanket reason without saying why the plan was dropped.
- **Method not recorded.** The commit cites "the owner's method of 2026-11-19". I could not find it in OWNER_DECISIONS.md.

Fix: give the two whnf groups their own reason, or keep them planned, and record the owner's method.

## The six parts asked
1. **`--rewrite`.**
   - **Sites reproduced:** a dry run of the head's tool on a copy of 312ab2ce, with `--from 'dup $A = swap $B = or' --to '$A $B one-of2?'` and the three-value form. It gives 30 + 9 sites. These are exactly a80d58c9's 36 lines plus the three left on purpose (kernel `whnf.fs` `lf-whnf-valued?`, `mixed-open.fs` `lf-open-rev?`, `ir-run.fs` `irx-ended?`). `diff` of the +/- lines finds no other difference, apart from the three hand-made `cell-spend?` edits.
   - **Faults carried:** they match the commit's list. Spot-checked `snapc-exhausted-carried`, `fri-l2-layer-opaque-kind` and `fe-defeq-fuel-unspent`: all caught.
   - **Tests:** they cover strings, comments, line breaks, a comment inside the phrase, repeated wildcards, frame and control words, numbers, strings, the new word's own definition, requires, duplicate refusal, the baseline and fault carrying. They do not cover M1's cases.
2. **Kernel, core and import.**
   - **The five hand splits are identical on every path, traced against the old text.** The `ok-applyN` failure arm equals the old `ok-then? 0= if nip… no-result exit then`, and each step has the right shape.
     - `lf-axd-made`: `tuck swap` gives `lf-axd-join` `slot j` as `dup >r swap` did.
     - `lf-nest-grow-ctor` and `lf-nest-occurrence`: the `0= if … exit` became `if … else … then`, so the flags are read the same way.
     - `lf-str-expand`; `ly-fam-expr-of` (`-rot 2 pick` = `dup … -rot`).
     - `lf-nest-instance`, by the tool.
   - **The comparisons are identical:** constants only (part 1). `cell-spend?` is token for token `lf-copier-spend`'s old body. `wc-spend` and `de-fuel?` agree at a count of 1 (→ 0, true), 0 (false, unchanged) and below 0 (false, unchanged).
   - **No field, record, saved or hashed layout is touched.**
3. **`one-of2?`/`one-of3?`:**
   - **Worth having.** 36 sites go from 6-10 tokens with shuffles to 3-4 tokens that read as the test they are. Four duplicate groups go. The kernel's two hot loops rightly keep the phrase (the measured cost is 2x a call).
   - **No form without both the return stack and a deep shuffle.** A three-operand test needs one or the other, since x sits under two cells that are both still needed. `rot tuck = -rot = or` trades two return-stack operations for two deep shuffles and would need a shuffles raise instead. `>r over = swap r> = or` is the clearer bracket, and `one-of3?` built on `one-of2?` is right.
   - **Placement.** `bounds.fs` already holds the range and set tests (`between?`, `in-ranges?`, `cells-has?`). A new file would fail the new-file limit (0.5 per word), and `outcome.fs` cannot use them (bounds.fs requires it).
   - **Raise:** `rstack` from 3 to 6 for `src/lib/bounds.fs` only; `shuffles` stay at 4. It needs the owner's approval in the review row.
4. **`lf-structure-like?`.** It is token for token both old copies, and defeq.fs requires whnf.fs. The detector's claim holds: 187 groups, "none new or grown" (base 192). See L2 and L4.
5. **`check_log_isolation.py`: stronger.** Rule 4 now counts `cell-spend?` after a field. I planted `logrec-a cell-spend?` in present/log-view.fs and the check exits 1. Rule 5's allow-list gains two pure lib words (one compare, and one store through an address the module owns).
6. **Style:** see below. Only bounds.fs got worse.

## Round 2 closed
- **B1:** `slab-since` in all nine places (checked line by line: the same arithmetic).
- **B2:** `lf-meta-instantiate-forall` ends with `ok-or-none`.
- **M1:** the six tests (697a344e) assert `-1` and the failing outcome. `T{ }T` checks the depth, so an arity fault is caught (r12 is recorded and caught). The 8 `cf2r-*` faults are recorded.
- **M2:** the `site-of` test and its fault are in place.
- **L2:** `lf-sx-const0` is used at 3 sites.
- **L3:** the export-marks and tombstone tests are in place.
- **L4:** `if-delta-by`.
- **L5:** FORTH_LIBRARY.md has the speeds.

## Reuse
Searched:
- **Library index:** LIBRARY_WORDS.md and FORTH_LIBRARY.md (bounds, outcome, slab). core/terms.fs's `lf-tags`/`lf-tag-in?` is a bit mask of term tags. It does not serve outcomes, `true`/`false`, characters ≥ cell bits or kinds, so `one-of2?` is not a copy of it.
- **`grep` over all of src/** for:
  - `dup X = swap Y = or`, `dup X = over Y = or`, the `<> … <> and` forms and the forms that keep x;
  - `@ dup 0> if 1-`, `-1 swap +! true`, and words named `*spend*`;
  - `['] X ok-applyN` with the step's stack comment.
- **Tool results:** `check-duplicates.py`: 187 groups, none new or grown. `check-lib-callers.py`: clean (bigint.fs is planned, FE1i-4).

New words and callers:

| Word | Callers |
|---|---|
| `ok-apply3` | 10 |
| `one-of2?` | 27 |
| `one-of3?` | 9 |
| `cell-spend?` | 3 |
| `lf-structure-like?` | 2 files |

Findings: R1.

Considered, not raised:
- lib/walk.fs:195 `walk-spend?` spends below zero, so it is not the same operation (a note for 9.4.8l);
- `lf-lv-made?` does not store;
- the four-way tests (`json-space?`, `ir-run.fs:779`, `tactic-run.fs:507`) have no `one-of4?`, and `in-ranges?` or a table would fit them later.

## Re-entrancy
- **New state:** no new VARIABLE, VALUE or written CREATE.
- **The new words:** `cell-spend?` writes only through the address its caller passes: the `wc`, `df` and copier context records. The other new words are pure.

## Planted faults (mine, on head copies; judges: 18 core unit files)
The judges were environment, env-import, env-snapshot, env-signature, check-declaration, check-declaration-ndjson, check-block, failure-paths, heap-refusals, inductive-nested, inductive-table, string-literals, tagged-sort-boundary, derivation-log, stage, whnf, iota and definite-rejection.

| Fault | Where | Caught by |
|---|---|---|
| F1 `ok-apply2`→`ok-apply` | environment.fs `lf-axd-made` | **survived** (M2) |
| F2 never share a row | environment.fs `lf-axd-row-for` | **survived** (M2) |
| F3 decls room after the write | inductive-nested.fs `lf-nest-grow-ctor` | **survived** (M2) |
| F4 `ok-apply`→`ok-apply2` | inductive-nested.fs `lf-nest-if-candidate` | inductive-nested.fs |
| F5 `ok-apply2`→`ok-apply` | string-literals.fs `lf-sx-of-chars` | string-literals.fs |
| F6 `ok-apply3`→`ok-apply2` | snapshot-layer.fs `ly-fam-expr-of` | env-import.fs |
| F6b let and other exchanged | snapshot-layer.fs `ly-fam-tagged` | env-import.fs |
| F7 opaque dropped | core input.fs `lf-kind-valued?` | check-declaration, check-block, whnf |
| F8 full dropped | check-declaration.fs `lf-check-short?` | **survived** (L1) |
| F9 full dropped | environment.fs `lf-env-quot-open?` | **survived** (L1) |
| F10 recursor dropped | import feed.fs `feed-member?` | env-import and 9 others |
| F11 symbolic dropped | core tagged-sort-boundary.fs `lf-repr-mode?` | tagged-sort-boundary.fs |
| F12 param dropped | core derivation-log.fs `lf-log-level-leaf` | **survived** (L1) |
| F13 quotient dropped | environment.fs `lf-kind-bare?` | env-signature, check-block, heap-refusals |
| F14 invalid dropped | env-import.fs `unrepeatable?` | **survived** (L1) |
| F15 opaque dropped | import stage-records.fs `valued?` | env-import, check-declaration-ndjson, check-block, stage |

The implementer's six `cf3-*` faults were read; their tests in lib.fs cover:
- each position, none, both, a negative budget;
- the stack effects, through `rs-checked`;
- `ok-apply3` against the hand-written guard for every outcome.

## Forth style
`forth-metrics.py --words 10`, base → head:

| Measure | 38 changed src files | 12 kernel, core and import files |
|---|---|---|
| Words | 5426 → 5454 | 1723 → 1737 |
| 1-2 lines | 3765 → 3804 | 1164 → 1179 |
| 3-5 lines | 1618 → 1611 | 529 → 532 |
| 6-10 lines | 43 → 39 | 30 → 26 |
| >10 lines | 0 → 0 | 0 → 0 |
| Deep shuffles | 479 → 479 | 280 → 280 |
| Return-stack operations | 1367 → 1366 | 723 → 721 |
| Globals | 161 → 161 | 42 → 42 |
| Lines over 90 characters | 10 → 10 | 3 → 3 |

- **Per file, only bounds.fs got worse:** return-stack operations 2 → 6, against a baseline of 3 (item 3).
- **Better:**
  - synth.fs: return-stack operations 35 → 32;
  - environment.fs: return-stack operations 85 → 83, and words of 6-10 lines 3 → 2.
- **Style findings:** H1 (its fix), L2 and L3. The kernel splits are one-line words with honest stack comments.

## What I ran
Setup: `git archive` copies of 93cf381c, 2cf1ddf1, 81799585, aee52c45, 312ab2ce, a80d58c9 and b19cd408, in the scratchpad `cf3-review/`. Gforth 1.0.0 ran through scripts/gforth-strict.sh, with `LEANFORTH_GFORTH` absolute, `ulimit -u 500` and stdin `/dev/null`.
- **The rewrite tool:**
  - `--rewrite --dry-run` (both patterns) on 312ab2ce, compared with a80d58c9;
  - `Pattern` probes for M1.
- **Detector and checks, on base and head:** check-duplicates.py, check-lib-callers.py, check_log_isolation.py (plus one planted write), and forth-metrics.py.
- **Unit files, unfaulted on head:** the 18 core files listed above, and tests/lib/lib.fs.
- **Faults:** my 16, and 3 of the carried ones.
- **Probes:**
  - the L1 one-liners (they pass on head and catch F8 and F14);
  - the H1 model;
  - a test of lf-axd-made with no room failed to set up. Re-initialising `lf-axd-rows` left `lf-axd-row-of@` reading freed memory, so M2's test needs a refusal injected as heap-refusals.fs does.
- **Scripts:** the constant check over every `one-of` site, and the step-shape check over every `ok-applyN` site.

Not run:
- the implementer's suites and make targets;
- `pre-tier.sh`;
- Gforth 0.7.3 and gforth-fast;
- pinned Lean, Init and Mathlib;
- the Python end-to-end judges (for example check_s2.py).

Uncertainty: H1 was shown on a model of the chain (the real `outcome.fs` with stubs), not on the real `ac-lam`, because no test drives `lf-meta-head-beta` to fail. Whether an end-to-end target catches the M2 and L1 survivors was not measured.

The branch touches src/kernel, src/core and src/import, so the full tier applies. This AI review does not replace the human review AGENTS.md requires for checker changes.

## Fixes

Made by the implementer on branch `cleanup-families-3` after main was merged into it (`0f78c8e3`: rounds 1 and 2
and the tactic batch), each its own commit:

- **H1** (`f53dae2e`): `ac-lam-from ( e i type -- lam outcome )` abstracts and makes the lambda as one step, and
  `ac-lam` chains it on `ok-apply3`, as the review wrote it. tests/front/defeq.fs runs a room sweep
  (tests/support/meta-sweeps.fs) of `lf-meta-mk-lambda` over a binder whose type is the beta-redex
  `(fun a : Type => a -> a) Nat`, with 55 under the call: every refusal ends full and the 55 stays. Fault
  `cf3r-ac-lam-eats-cell` (round 3's chain), caught (`WRONG NUMBER OF RESULTS`).
- **Prevention** (`3c39140a`): `scripts/check-outcome-steps.py`, in `check-forth-quality` (make test) with its 15
  tests (tests/scripts/test_check_outcome_steps.py) and in `scripts/pre-tier.sh`. For every `['] X ok-apply`,
  `ok-apply2` or `ok-apply3` in src/ outside comments and strings, X's stack comment (its `:` definition or
  `defer`) must take exactly the 1, 2 or 3 cells the chain passes and leave two cells per alternative, the second
  `outcome` or `status`. What it cannot count (no definition in src/, `...`, `|` before `--`, disagreeing
  definitions) it prints as "not checked" and does not fail on; a step whose xt is not named at the call is not
  seen. On src/ now: 121 sites, 121 right, 0 not checked; on the text before H1's fix it names `ac-abstract`.
- **R1** (`fcccf762`): the five exact copies are on the shared words (`lf-pp-spend`, `lf-meta-spend?`,
  `lfr-spend?` on `cell-spend?`; `lf-tex-angle?`, `pv-settled?` on `one-of2?`); proof-outline.fs's
  `lf-ol-binders` (`one-of2?`) and whnf.fs's `wc-at-most-i` (`one-of3?`) converted; kernel `caches.fs` defines
  `lf-short? ( outcome -- flag )`, which `lf-ci-short` calls and which replaces check-declaration.fs's
  `lf-check-short?`. Faults re-targeted: `tex-guillemet-raw`, `fe-run-fuel-free`, `fe-whnf-at-most-i-implicit`.
  The five negated forms are plan 9.4.8l item AT.
- **L3** (`257e6f64`): `ly-fam-tagged` reads the tag from head on top, `-rot` in each arm.
- **M2** (`46b237d3`, `ea70af70`): tests/core/environment.fs pins the axiom table's one shared row after
  `lf-env-axiom-deps` (the main input has no axiom; F2 makes it 28), `lf-axd-row-for` of a shared row, and
  `lf-axd-made` with the rows slab filled to its capacity and its growth refused (heap-watch.fs): `55 -1 full`.
  tests/core/inductive-nested.fs (now with heap-watch.fs) grows nested.tree's translated constructors past the
  declarations' capacity (each numbered in turn, ok, of kind constructor), then, both arrays full, refuses the
  cells' growth and then the declarations': `-1 full`, the count unchanged, the cell under the call kept. The
  review's F1-F6b are recorded (`cf3r-axd-made-keeps-j`, `cf3r-axd-row-never-shared`,
  `cf3r-nest-ctor-written-first` (caught as an abort: the write past the block corrupts the heap),
  `cf3r-nest-candidate-two-values`, `cf3r-sx-of-chars-keeps-list`, `cf3r-fam-expr-two-values`,
  `cf3r-fam-let-other-swapped`), and one more fault on each other split step (`cf3r-str-expand-nil-two`,
  `cf3r-str-expand-chars-two`, `cf3r-sx-applied-unswapped`, `cf3r-nest-occurrence-two`,
  `cf3r-nest-new-key-no-result`, `cf3r-nest-instance-two`, `cf3r-fam-other-unswapped`): all caught.
- **L1** (`735150e8`): the two probed lines (on `lf-short?`, which replaced `lf-check-short?`, in
  tests/core/check-declaration.fs; `unrepeatable?` in tests/core/env-import.fs), `lf-ci-short` on every kind of
  failure (the arm `make cover-changed` found never run), `lf-env-quot-open?` with the name store at its limit
  (tests/core/environment.fs) and `lf-log-level-leaf`'s two leaves and a cut (tests/core/derivation-log.fs).
  Faults `cf3r-short-without-full` (F8), `cf3r-quot-open-without-full` (F9), `cf3r-level-leaf-without-param`
  (F12), `cf3r-unrepeatable-without-invalid` (F14) and `cf3r-ci-short-keeps-all`: all caught.
- **L2** (`f1cc0c0a`): `de-nonrec?` is gone; `de-unit-data?` and `de-induct-nonrec?` call `lf-structure-like?`.
  tests/front/defeq.fs runs the else arm: Prod.mk with its inductive's name made one no declaration has (put
  back after) is false. Fault `cf3r-induct-unknown-structure`, caught.
- **L4** (`9b47c679`): the accepted families' reason states the rule (plan 9.4.8l: a family stays as copies
  when a shared word would be as long as each copy or would cost an EXECUTE on a hot path); groups 26354411 and
  719a2248 have their own reasons, saying why their S2 merge B plan is dropped; the plan row says the same.
- **M1** (`6207e804`): a wildcard refuses stack words, every defining word and the words that read the next
  word as a name; a match right after such a word (`'`, `[']`, `postpone`, `to`, `is`, `:`, a defining word) is
  left and listed; `s\"` and `.\"` strings end at their first unescaped quote; `[char]`/`char` join the next
  word. Tests for each (test_duplicates_extract.py), failing on the old tool. The detector now reads
  print-forth.fs's `s\"` strings right, so group 8c62bb32 gains `lf-pf-declarable?`. Left (plan 9.4.8l AU):
  printing each wildcard's bindings with their kind and refusing a value or a variable unless asked; indirect
  recursion.
- **Item 3**: not changed. `scripts/pre-tier.sh` fails only on src/lib/bounds.fs's return-stack count (6
  against a baseline of 3), which is the owner's decision (plan 9.4.8l AV).

Checks on the final head (`GFORTH`, `LEAN` absolute, `ulimit -u 500`): `scripts/pre-tier.sh` exit 1, every line ok but "forth quality + review log" (bounds.fs, item 3); `make cover-changed BASE=main JOBS=4` exit 0 (every block on a changed line ran, 146 unit test files, 89.6 s); `make -k test-unit JOBS=4` on `gforth` and on `gforth-fast` exit 2 each, the one failing target `check-forth-quality` (its test of today's tree: bounds.fs's return-stack count), every other target passed. Each recorded fault was run with `scripts/mutants.py --only` and caught. Not run: `make tier`, the end-to-end targets, pinned Lean, Gforth 0.7.3.

The fix commits that change Forth source (`f53dae2e`, `fcccf762`, `257e6f64`, `f1cc0c0a`) are covered by this report's log row, `3a5efff3..f1cc0c0a`, as the implementer's fixes of the findings above; no reviewer has read them yet.
