# Forth review: cleanup-families-2, clean-up by family, round 2 (2026-11-19)

Branch `cleanup-families-2`, range `ca867d82..3a5efff3` (18 commits, head 3a5efff3); reviewer forth-reviewer (Opus), independent of the implementer.

Findings: 0 high, 2 medium, 7 low (2 of the low blocking: reuse). **Verdict: merge after fixes.**
- B1 and B2 are fixed on the branch: a few one-line edits, all probed.
- M1 is fixed or planned before the merge: faults recorded, or a coverage-debt plan row naming the sites.
- M2 should land on the branch: one test line, already probed, and one fault.
- "Behaviour identical" holds for every kernel, core and import member.
  - Each pair and triple was traced against its layout and against every reader and writer.
  - A script checked all 65 hand-written refusal tails: each maps to `ok-apply` or `ok-apply2` as its `nip` requires, 0 mismatches.
  - 26 of my own faults were planted; 9 kernel survivors (M1, M2).
  - No field of a saved, hashed or written record moved.
- Round 1's findings B1-B3, M1 and L1-L4 are all closed.

## Findings

**M1 (medium, tests and faults: kernel refusal tails).** No test pins the failing outcome of six of the eight converted kernel tails. My faults survive 19 kernel unit test files (whnf, defeq, defeq-sweeps, reduce-nat, iota, quot, failure-paths, heap-refusals, mixed-infer, mixed-infer-coverage, string-literals, check-declaration, infer-proj, infer-deep, mixed-convert, inductive-recursor, environment, definite-rejection, check-forged):
- whnf.fs:356 `lf-whnf-delta-of`: failure becomes `-1 ok` (r10), or `-1 unknown` (r20);
- whnf.fs:387 `lf-whnf-reapply`: failure becomes ok (r11), or `ok-apply` stands where `ok-apply2` belongs, leaving a cell behind (r12);
- mixed-infer.fs:345 `lf-minfer-put-closed`: failure becomes ok (r14);
- mixed-infer.fs:1009 `lf-minfer-typed`: failure becomes ok (r15);
- iota.fs:167 `lf-iota-typed` (r16);
- reduce-nat.fs:70 `lf-rn-truth` (r17).

Only two are pinned: whnf.fs:616 `lf-nat-literal` (r13, by heap-refusals.fs) and reduce-nat.fs:157 (r18 and r19, by reduce-nat.fs).

Why they survive:
- On base, the old `else` arms at whnf.fs:356, :387, iota.fs:166 and reduce-nat.fs:70 were never-run blocks over those tests (`coverage.py --file`, base). This debt predates the branch.
- mixed-infer.fs:345 is reached only with outcome 2 (exhausted), in iota.fs and failure-paths.fs. Fuel stays spent, so the next step fails the same way and masks the fault.
- mixed-infer.fs:1009's arm is never reached.

The conversions are identical by construction: `ok-apply2`'s failure arm is the old `ok-then?` followed by `nip no-result`, and lib.fs tests both words against the hand-written tail for every outcome. But the wrong-arity choice (r12) is the typical fault of this refactor, and it is visible only on these failure paths.

Note also that the block counts fell (whnf.fs 580 → 568; mixed-infer.fs 792 → 779; iota.fs 496 → 490; reduce-nat.fs 153 → 141). Never-run `else` arms became one shared arm in `ok-apply`, which hides them from the ratchet without adding tests.

Fix, either:
- record faults r10-r12, r14-r17 and r20 in faults.toml with a judge that catches them, for example a refusal injected as heap-refusals.fs does, pinning `-1 outcome-full` from `lf-whnf-reapply` and `lf-minfer-put-closed`; or
- record them as coverage debt in a plan row naming the six words (the owner's exception of 2026-11-17).

**M2 (medium, test gap in the snapshot writer).** env-snapshot.fs:315 `site-paired` with its pair swapped (r3: `seen-at 2!`) survives tests/core/env-snapshot.fs and env-import.fs. `site-seen` then never finds a site, so every snapshot written stores each site text again: the bytes on disk change and nothing notices. The implementer's 27 crosswise faults skip this word.

Fix: add to tests/core/env-snapshot.fs and record the fault `cf2-site-paired-swapped` with that judge. This was probed: it passes on head and catches r3.
```forth
create st1 3 c, char a c, char b c, char c c,
create st2 2 c, char x c, char y c,
T{ sites-init -> outcome-ok }T
T{ st1 site-of st2 site-of st1 site-of site-bytes slab-count -> 1 outcome-ok 5 outcome-ok 1 outcome-ok 7 }T
sites-free
```

**B1 (low, blocking: reuse).** Copies of the operation `slab-since` was extracted for remain. They are the units added since a mark, written `X slab-count M -`. The commit message (86a88e2f) does not name them, and they are not index computations:
- front/defeq.fs:470 `de-post#`, :358 `de-bind-n`;
- front/elab-pending.fs:484 `ep-c#`;
- author/errors.fs:617 (in `lfa-.detail`);
- core/string-literals.fs:72 `lf-str-fields?`.

```forth
: ep-c# ( -- n ) ep-c-first ep-goals slab-since ;
: de-post# ( -- k ) de-post0 de-cells slab-since ;
: de-bind-n ( -- n ) de-x de-cells slab-since 2 - 2/ ;
\ errors.fs:617:  lfa-inline# lfa-detail slab-since ?dup if ...
\ string-literals.fs:72:  swap lf-str-bytes slab-since swap - 0< 0= ;
```

Also recommended: the "index" sites. An index into a slab is a count the slab once held, so they are slab-since's definition exactly:
```forth
: ep-kept ( first n -- from m ) + dup ep-scratch slab-since ;
: ep-tail ( w -- from w ) dup ep-scratch slab-since swap ;
\ whnf.fs:295 wc-rest:  wc-major-at 1+ dup wc-args slab-since swap wc-args lf-meta-apply-from ;
\ whnf.fs:472 (wc-alt-apply):  ... wc wc-malts @ + dup wc-args slab-since swap wc-args ...
```
- Probe: all nine together pass tests/front/defeq.fs, elab.fs, whnf.fs, goals.fs, tests/core/string-literals.fs and tests/author/author.fs.
- Rightly left:
  - meta-env.fs `me-newest`: n is a length, not a mark;
  - whnf.fs:465 `wc-h@`: an index from the end;
  - lib/cons.fs:304 and import/snapshot-tier.fs:204: no shorter.

**B2 (low, blocking: reuse).** front/whnf.fs:873 `lf-meta-instantiate-forall` ends `['] outcome-ok ok-apply`, which is `ok-or-none` (same stack for every outcome, and one `execute` less). Write `swap ['] wm-inst-at ok-fold ok-or-none ;`.

**L1 (low, process).** Seven intermediate commits fail a check:
- `check_log_isolation.py` fails at e8e5062a, 821ec647 and 21fee9ea (rule 5: `cell-pair!` and `cell-pair@` outside the allow-list) and passes again at fa427115. The implementer named only e8e5062a.
- check-docs fails from 23c4f8b6 to e6dc70a1 (the implementer's statement; not re-run).

This is acceptable for a merge of the whole stack:
- main's checks (the logged ranges of check-forth-quality.py, and mutants.py --history, which reads commit messages) do not require each commit to pass;
- the merged head passes;
- the cost is a `git bisect` that stops on unrelated failures.

Say so in the merge message, or, since the branch is unpushed, move fa427115's check_log_isolation.py hunk before e8e5062a.

**L2 (low, plan accuracy).** Plan 9.4.8l (AK) says "every `ok-then? if X else no-result then` … in src". 34 multi-word tails remain, 11 of them in the kernel:
- whnf.fs:284, 309, 338, 389;
- mixed-infer.fs:718, 857;
- iota.fs:448;
- string-literals.fs:85, 93, 95, 103.

"Left for the next round" lists only the mid-word guards. Say "every single-word step" and list these.

string-literals.fs's three `ok-then? if 0 lf-sx-const else no-result then` are a repeated phrase. Fix: `: lf-sx-const0 ( id -- node outcome ) 0 lf-sx-const ;`, then `['] lf-sx-const0 ok-apply`.

**L3 (low, tests outside the kernel).**
- r23, `export-marks` fetch swapped (ndjson.fs:874), survives tests/core/ndjson.fs and manifest.fs. Its only reader (ndjson.fs:1248) passes the pair through `2>r` to `export-marks!`, so key and why come back exchanged after a shape failure.
- r26, `gp-like` one short, survives goals.fs, goals-print.fs and goal-states.fs. It is caught only end to end, by check_goals.py (Lean `x✝² x✝¹ x✝`, LeanForth `x✝¹ x✝ x✝`). A unit line in goals-print.fs pinning a tombstone with two later like-named locals would judge it, and the implementer's `gp-later-like?` fault too.

**L4 (low, name).** infer.fs `if-delta-if ( type flag -- type' outcome )` reads like a typo. Call it `if-delta-by`, as the same file's `idl-by`.

**L5 (low, library profile).** FORTH_LIBRARY.md measures `cell-pair@`, but gives no speed for `ok-apply2` or `slab-since`. Add the measurement below (part 5).

## The eight parts
1. **Pairs.**
   - Every kernel, core and import conversion is adjacent `field:`s in the old order:
     - `lf-crec-name/generation`; `lf-logs-cut/bound`, `-slot/outcome` and `-at-node/at-context`; `logrec-a/b`;
     - `lf-mdreq-*-root/id`; `lf-cache-hits/misses`; `lf-dqs-dt/ds`; `rp-code/rp-path-size`; `export-key/why`;
     - the `2@ swap` and `tuck cell+ ! !` copies, which are `cell-pair@`/`!` token for token.
   - `rp-saved`/`rp-restore` are now `( code size )`. All three call sites (run-replay.fs:189, 228, 238) pass the pair through `2>r`/`2r>`.
   - Moved and merged fields are reached only by name, so none is written, hashed or saved:
     - `buffer-used` sits in a heap-buffer descriptor (`/buffer erase`; tests/core/ndjson-emit.fs by name);
     - `trow-plan` is in dictionary rows;
     - `lf-stmt-left` is a context record. `2!` reverses its memory order, which nothing else reads.
   - env-snapshot.fs:
     - no `field:` changed;
     - `site-paired`'s pairs are memory-only (the site texts are what is written);
     - `snap-layer-slots!` fills the in-memory record (`snap-wn which renum`, the order `imp-layer-slots` gives);
     - `start@` reads the same cells.
     - **No on-disk order or size changed.**
2. **Counting.**
   - `lay-count` equals the old loop. `slot-record?` gives well-formed flags (`0=` or `true`).
   - `gp-like` counts j = i+1+k for k < count-i-1, the old `gp-after` range; `gp-after` is still used at :98. They differ only for i ≥ count, where the old `?do` would wrap, which is unreachable.
3. **Triples.**
   - env-import.fs:584 `imp-ldecls/ldn/llines`;
   - env-snapshot.fs:540 `snap-wn/which/renum`, matching `imp-layer-slots`' order;
   - env-signature.fs:97 `lf-esreq-pairs/count/fuel`;
   - terms.fs:313/315 `lf-sought-tag/first/second`;
   - derivation-log.fs:789 `logcref-name/generation/count`.

   All are in order. defeq.fs:472 and derivation-log.fs:935 are pairs after one single store, also correct.
4. **slab-since.**
   - `pool-left`, `rn-from`, `slab-rest`, `lfg-entries` and the ea-, ed- and ep- words are equal to the old arithmetic.
   - Its edge tests (0, count, negative) and fault are in place. Leftovers: B1.
5. **Refusal tails.**
   - Script over the diff: 65 old tails, `else no-result` → `ok-apply`, `else nip no-result` → `ok-apply2`, 0 mismatches.
   - The eight kernel sites were traced by hand, with the stack effects of `lf-whnf-lookup ( const -- d outcome )`, `lf-whnf-spine-args ( node -- n outcome )`, `lf-minfer-close ( node -- node' status )`, `lf-reduce-nat-pred ( a -- node outcome )` and the others.
   - The propagated outcome is the step's own, and the result cell is -1 (`no-result` unchanged).
   - Any X is carried: `ok-apply` only `execute`s it on ok. No X is a return-stack, loop-index or parsing word.
   - infer.fs: `if-fail` is `nip no-result` and `if-bad` is `outcome-invalid if-fail`, so the chains give the same `-1 outcome` as the old early exits. Each new helper (`if-delta-if`, `if-flush-rest`, `if-ctor-kind`, `if-induct-data`, `if-pi-or-bad`, `if-skip-body`, `if-imax-of`, `idl-by`) was traced.
   - **Cost** (10^7 calls, Gforth 1.0.0):
     - on gforth, old against new is within noise (77-90 ms both);
     - on gforth-fast, `ok-apply` costs about 1.7 ns more a call (33-36 against 50-53 ms) and `ok-apply2` about 0-1 ns.
     - The kernel sites run once per delta unfold, instantiation with a close, or Nat step, each doing lookups and allocations. 10^7 such calls cost about 20 ms.
     - **An Init timing check before the merge is not warranted.** The nightly run's timings will show any change.
6. **Baseline.**
   - `check-duplicates.py` on my copies: base 200 groups, head 192, "none new or grown".
   - The idioms are honest; I read every member:
     - 3a7e, 6876 and 6a44 are `ok-with` chains of different steps (3, 6 and 5 of them);
     - 8c62 is the guarded `dup a? if b else drop false then` with six different word pairs;
     - aca7 is `a if b else false then` nine times in nine files.
7. **Isolation check: stronger, not weaker.**
   - Rule 4 now also counts `2!`, `cell-pair!` and `cell-triple!` after a log field.
   - I planted `logrec-a <word>` in present/log-view.fs for each of `cell-pair!`, `2!`, `cell-triple!` and `!`: exit 1 every time.
   - The allow-list gains three memory words with the power of `@` and `!`.
   - Head passes.
8. **Intermediate red commits:** L1.

## Round 1 closed
- B1: no `if drop outcome-ok else …outcome-full… then` is left in src; `lf-made-term` is called in the three kernel sites.
- B2: the phrase is left only in `ok-or-none`'s own body.
- B3: no `if outcome-ok else … outcome-full … then` is left outside outcome.fs.
- M1:
  - env-import.fs:507 pins `16 56 107`;
  - all 8 `cf-` faults are recorded; `cf-ck-again-any-why` spot-checked, caught.
- L1: find.fs and FORTH_LIBRARY.md are fixed.
- L2: nat-offset.fs:56 requires generation-handles.fs.
- L3: OWNER_DECISIONS.md:1622 has the wrap note.
- L4: `ck-inputs-passing#` is in use, and source.fs's comment is split.

## Reuse
Searched:
- LIBRARY_WORDS.md and FORTH_LIBRARY.md (bounds.fs, outcome.fs, slab.fs);
- `grep` over all of src/ for:
  - `2@ swap` and `tuck cell+ ! !` (`dup @ swap cell+ @`);
  - `slab-count swap -`, `slab-count over -`, `slab-count X -`, `slab-count X @ -` and `slab-count r@ -`;
  - `ok-then? if X else (nip )?no-result then`, single- and multi-word;
  - `['] outcome-ok ok-apply`.

Tool results:
- `check-duplicates.py`: 192 groups, none new or grown.
- `check-lib-callers.py`: clean (bigint.fs is planned, FE1i-4).

New words and callers:
- `cell-pair@`/`!`: 40+ callers;
- `cell-triple@`/`!`: 17;
- `ok-apply2`: 25;
- `slab-since`: 13.
- They are named and placed well: memory-order pair access beside `pair-at` and `record-at`, the step combinator beside `ok-apply`, the span beside `slab-count`.

New findings: B1 and B2.

Considered and not raised:
- `mrf-sides` (meta-tactic/goal.fs:272/274) is a whole-pair field (`2!`/`2@`) whose callers want the reverse order.
- The 123 mid-word guards are planned (9.4.8l AK).

## Re-entrancy
- No new VARIABLE, VALUE or written CREATE, and no new PICK or ROLL. The new words are pure.
- `snap-site-tables` (env-snapshot.fs) is an older module-level table, "one save at a time", unchanged in shape.

## Coverage and faults
- **The implementer's faults:** 66 new, 35 of them in lib, kernel, core and import. I spot-checked four (`cf-ck-again-any-why`, `cf2-layer-slots-turned`, `cf2-snap-start-swapped`, `cf2-ok-apply2-keeps-one`): all caught.
- **Mine, 26 planted on head copies.** Caught:
  - r1 `lay-from` swapped: env-import.fs;
  - r2 `entry-same?` swapped: env-import.fs;
  - r4 `lf-rmemo-kept` swapped: mixed-instantiate.fs;
  - r5 `lf-log-published!` swapped: derivation-log.fs;
  - r6 `snap-layer-slots!` with which and renum exchanged: env-import.fs;
  - r7 `lf-sought@` turned: terms.fs;
  - r8 `lay-count` one short: env-import.fs;
  - r13: heap-refusals.fs;
  - r18 and r19: reduce-nat.fs;
  - r21 `lf-log-cref-head!` rotated: derivation-log.fs;
  - r22 `lf-mdreq-claim@` swapped: mixed-definition-probe.fs;
  - r24 `rp-saved` swapped: run-record.fs;
  - r25 `lf-stmt-pop2` swapped: env-signature.fs and check-block.fs;
  - r27 `ok-apply2` running its step on failure: lib.fs.
- **Survived:**
  - kernel: r3 (M2); r10, r11, r12, r14, r15, r16, r17 and r20 (M1);
  - import: r23 (L3);
  - front: r26 (caught only by check_goals.py, L3).
- **Tests of the new words.**
  - In lib.fs and slab.fs:
    - stack effects (`rs-checked`);
    - layout against `2@`;
    - `ok-apply2` against the old text for every outcome and one outside the vocabulary;
    - `slab-since` at 0, at the count and above it.
  - infer.fs pins `if-ctor-kind`; defeq.fs pins the doubt record; derivation-log.fs pins the publish fields; check-declaration.fs pins the cache statistics.

## Forth style
`forth-metrics.py --words 10`, base → head:

| Measure | 61 changed src files | 22 kernel, core and import files |
|---|---|---|
| Words | 6496 → 6511 | 2774 → 2775 |
| 1-2 lines | 4513 → 4537 | 1868 → 1870 |
| 3-5 lines | 1935 → 1926 | 860 → 859 |
| 6-10 lines | 48 → 48 | 46 → 46 |
| >10 lines | 0 → 0 | 0 → 0 |
| Deep shuffles | 827 → 814 | 618 → 613 |
| Return-stack operations | 2710 → 2712 | 2034 → 2034 |
| Globals | 260 → 260 | 148 → 148 |
| Lines over 90 characters | 22 → 22 | 17 → 17 |
| Locals | 0 | 0 |

- The two extra return-stack operations are round 1's L4 (`>r … r>` in `ck-inputs-passing#`).
- **Not worse.** The forth-quality baseline is untouched.
- Style findings are B2, L2 (`lf-sx-const0`) and L4.
- The pair and triple accessors are one line each, and infer.fs is now 74 of 102 words in one or two lines.

## What I ran
Setup: `git archive` copies of ca867d82 and 3a5efff3 (plus src at e8e5062a, 821ec647, 21fee9ea and fa427115), Gforth 1.0.0 through scripts/gforth-strict.sh (LEANFORTH_GFORTH absolute), `ulimit -u 500`, stdin `/dev/null`.

- **26 test files as judges, all passing unfaulted on head:**
  - tests/core: derivation-log, env-import, defeq, whnf, check-declaration, constant-references, terms, env-snapshot, env-signature, iota, mixed-infer, mixed-infer-coverage, reduce-nat, mixed-definition-probe, run-record, ndjson-emit, ndjson, snapshot-tier, mixed-instantiate, mixed-shift, check-block, string-literals;
  - tests/front: infer, goals, defeq, whnf.
- **Wider judges for M1:** the 19 kernel test files listed above.
- **Library tests:** tests/lib/lib.fs, slab.fs, htab.fs and runs.fs, also on gforth-fast.
- **Loading:** every one of the 61 changed src files loads alone.
- **Python:**
  - tests/front/check_goals.py (head and r26);
  - tests/core/check_log_isolation.py at five commits, plus four planted writes;
  - check-duplicates.py and check-lib-callers.py on base and head;
  - forth-metrics.py;
  - `coverage.py --file` for whnf.fs, mixed-infer.fs, iota.fs and reduce-nat.fs over the 19 files, on base and head.
- **Probes:**
  - the M2 test line;
  - the B1 conversions;
  - markers in mixed-infer's failure arms;
  - the 10^7-call `ok-apply` micro-benchmark.

Not run:
- the implementer's suites, make targets and the coverage ratchet;
- Gforth 0.7.3;
- pinned Lean, Init and Mathlib. The coordinator is running the full tier with every pinned-Lean differential on this head.

Uncertainty: whether an end-to-end target (test_leanforth.py, the pinned-Lean differentials) catches the M1 survivors was not measured.

Note for the coordinator: the branch touches src/kernel, src/core and src/import, so the full tier applies.

This AI review does not replace the human review AGENTS.md requires for checker changes.
