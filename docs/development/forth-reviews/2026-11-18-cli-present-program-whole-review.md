# Whole-code Forth review, third pass: src/cli (rest), src/program, src/present (part)
**Range:** whole files at main `f90c71d9` (no BASE: not a diff review; `f90c71d9..f90c71d9`).
**Findings: 12.** BLOCKS 1 (B1). REUSE PASS 4 (R1-R4). Note 7 (N1-N7; N1 is high).
**What was run:** read-only, on a `git archive f90c71d9` scratch copy. About 20 `bin/leanforth` probes on Gforth 1.0.0 (GFORTH set to the pinned binary), 3 planted faults in print-names.fs (scratch only, restored and compared), `forth-metrics.py`, `check-duplicates.py`, `check-lib-callers.py`. No suite, no Lean. This AI review does not replace the owner's human review.

## For the owner (plain language)
- **Verdicts:** no path I read prints "accepted", a count or an axiom list that the kernel's slots do not hold. Text and `--json` agree on names, verdicts, counts and exit status for an accepted, a fuel-exhausted and four rejected exports. I did not have an unsupported one at hand.
- **One wrong number (B1).** The resource report and the JSON `fuel` field give a wrong "fuel used" for a declaration that ran out of fuel early. With `--fuel 50` it says 0, with `--fuel 100` it says 56; the header promises the whole budget. The verdict itself ("exhausted", exit 3) is right.
- **`leanforth verify` (program path):** the Forth side only translates Forth to the IR and refuses everything else: an unknown word, a redefined standard word, a number form the host might read differently, a path too long. It never runs the file's words. "Verified" is decided in Python and needs LeanForth to accept every declaration of the export. The receipt states assumptions A1-A7 and the trusted reader. I found no path where a receipt says verified without the checker's acceptance (scripts/program_receipt.py:334-348, read in part).
- **Printer:** names are chosen without capture. My three planted capture faults were all caught by the tests. Levels print as Lean's `Level.dec`/`Type u` rule. Every walk is a frame visit with fuel. Projections print as `Prod.1 p` and big literals as `(literal of N limbs)`: both are documented and not Lean's syntax.
- **Reuse:** a second Forth-to-IR translator (ir-reader.fs, 739 lines) is still loaded into every `leanforth` run. A hand-written JSON text sits beside lib/json-write.fs. Three copies of a bounded text buffer. leanforth.fs (1,745 lines) needs splitting: a plan is below.
- **Coverage:** I read 13 files whole and 4 in part. I did not read 14 present files or the 14 small front files (list at the end).

## Findings (ranked)
**B1 (BLOCKS: a wrong number told to the user; verdicts unaffected).** check-run.fs:552-562 `ck-decl-left`/`ck-used`.
- **Cause:** before step 4 the fuel left is read from `lf-check-left`. A check that runs out inside the constant-term check (step 1, `lf-cterm-check`) has not spent from that counter. So used = budget - left is too small.
- **Contradicts:** the header (:78-80, "one exhausted used the budget").
- **Probe:** `check --json --fuel N tests/cli/chain.ndjson`. N=50 gives verdict exhausted, fuel 0, step 1. N=100 gives fuel 56. N=200/300/400/485 give 200/300/400/485. Text `--resources` at N=50 prints "fuel: 0 steps in all", and "most fuel used" leaves the declaration out.
- **Fix:** an exhausted outcome used the whole budget: `: ck-used ( outcome d -- n ) over outcome-exhausted = if 2drop ck-fuel-budget exit then ...`. Better, read the counter the constant-term check spends.
- **Tests:** pin fuel 50 and 100 (used = budget) in tests/cli, and plant a fault on the new branch.

**R1 (REUSE PASS: a second translator in the product).**
- src/main.fs:51 loads program/ir-reader.fs, the IR 0.1 reader. verify-report.fs:21-22 calls it "the program words' earlier test oracle".
- Every `leanforth` process carries 739 lines and 13 planted faults of a translator that the product never calls. Its callers are tests and scripts only (tests/program/*.py, program_receipt.py:203, which names it as an assumption).
- verify-alias.fs is a second design "kept working beside" the owner's chosen mode shift (verify-alias.fs:1-3), and verify_check.py must keep the two equal.
- **Fix:** drop ir-reader.fs from main.fs and move it under tests/program as the oracle, or retire it. Retire verify-alias.fs or give it a plan row with a stated purpose (AGENTS.md: prefer retiring experiments).
- sha-words.fs is a verbatim copy of lib/sha256.fs words until stage SHA-2. It is in the duplicates baseline; keep the plan row.

**R2 (REUSE PASS, with a fail-silently defect).** leanforth.fs:844-861 `cli-info-build` writes the snapshot's information JSON by hand, beside lib/json-write.fs.
- `cli-info+` (:846-848) silently drops any part that does not fit in 512 bytes. A long but plain LEANFORTH_COMMIT or `version-string` then gives malformed JSON with no notice: the quotes are kept, the text dropped, and later parts drop or land out of place.
- **Fix:** a `json-writer:` sink into a heap block (as check-json.fs does to `type`). Refuse a text over 128 bytes as null, as non-plain texts already are.
- From reading only: bin/leanforth sets LEANFORTH_COMMIT itself, so no probe.

**R3 (REUSE PASS: bounded text buffers written 3 times, and a count written twice).**
- The three buffers: `ck-pl+` (check-run.fs:735-737), `cli-info+` (leanforth.fs:846), and `pv-clipped`/`pv-append` (verify-report.fs:211-213, 289). Each is "append c-addr u if it fits", with its own overflow rule.
- **Fix:** one `buf-append ( c-addr u buf -- flag )` in lib/bytes.fs, the caller choosing to clip, drop or fail.
- **The count:** `cli-from-snapshot#` (leanforth.fs:413) is `ck-saved#` (check-run.fs:1185) without its `ck-verdicts?` guard. Use `ck-saved#` and delete the copy.

**R4 (REUSE PASS: the 1,745-line leanforth.fs; old C1 and C4 causes).** Split by job:
- `cli/help.fs`: :1313-1477 (version, capabilities, help: about 165 lines of text words, including the 37-line `cli-check-usage.`).
- `cli/snapshot-report.fs`: :338-373, :579-616, :720-829, :970-997.
- `cli/text-command.fs`: :998-1160.
- `cli/report.fs`: :306-497 (tally, lines, summary, notes).

The five `cli-misuse-*` words (:945-969) each re-type "error: … / try: leanforth help". `cli-misuse-snap` (:977) already does that, so write `s" --jobs does not go with --record" cli-misuse-snap`. Then `check-command` (:1165, 11 lines) becomes the earlier review's `first-refusal` table. `ck-pline-parts` (check-run.fs:760) is the third counted table of R4/C1.

**N1 (note, high: text and JSON can disagree on axioms).**
- check-json.fs:137 `cj-axioms` and leanforth.fs:302 `cli-bits` drop lf-env-axioms' outcome. The text line prints "axioms: ?" when it is not ok (check-declaration.fs:426). JSON then writes axiomBits 0 and notProved false, and the summary counts no axiom ("axioms: none").
- This needs a slot whose outcome is ok while `lf-slot-accepted?` is false (environment.fs:1247-1249). I did not reach it.
- **Fix:** `cj-axioms` writes `"axiomBits": null` on a failed read. `cli-tally-proved` marks the summary "axioms: ?". Add a fault on the dropped outcome.
- program_receipt.py:355 `lean_agrees` would catch a wrong axiom list in a receipt.

**N2 (note: a stale comment).** check-run.fs:685-689 says the line word gives false for a NOT PROVED line, so that the report writes it later. leanforth.fs:394-398 `cli-stream` always gives true and names the axioms as it goes. Rewrite the check-run comment.

**N3 (note: `print --lf`).**
- leanforth.fs:1270 `lf-file-write drop`: the exit is 0 however many declarations were stubbed. print-lf.fs:134 `fl-write` also drops its outcome; that is safe only because the same print just succeeded, so say so there.
- print-lf.fs:5-6 says the runner reads the text back "to identical terms". The probe below shows `leanforth check` refuses it without `--env` (error 48, exit 4). State that a text with stubs needs `--env`, and print that on stderr with the summary.

**N4 (note).** check-run.fs:950-953 `ck-whole` drops read-file's count and hashes `size` bytes even after a short read (a manifest shrinking during the run). Fix: `r> read-file >r over <> r> or if …invalid`.

**N5 (note; old C2 still open).** Capabilities print a fixed claim from an earlier build (leanforth.fs:1373, "Mathlib: all 729,263 … on build b74a04d") and plan numbers (:1341, :1347, :1350-1352, :1366-1368, :1394). Move the measurement to docs with its date, and name features rather than plan rows.

**N6 (note: tests seen from the code).**
- No planted fault in present/print-levels.fs (the `Level.dec` rule, `lf-pp-always-zero?`), present/print-tokens.fs, program/program-depth.fs, examples.fs or clamp.fs.
- Suggested faults:
  - imax's decrement as `lf-pp-dec-max` without the `walk-children` arm (print-levels.fs:32);
  - `lf-pp-succ-step` counting from 0 (:87);
  - `lf-depth-before-add` without the max test (program-depth.fs:23).
- No test pins B1 or N1.

**N7 (note; old portability item still open).** `stdout`/`stderr` are used directly at check-run.fs:731 and :777 and print-lf.fs:90. Put them behind one host word in lib/portability.fs.

## The 2026-11-12 backlog review, in these files
- **Open:** C1 (R4: `ck-pline-parts`, `cli-entry-find`); C2 (N5); D3 (`ck-state`, a 60-field shared record with 19 globals beside it); the portability item (N7); the library candidates (R3's buffer, cli-entry).
- **Not re-verified:** B1-B7, T1-T6 (outside what I read).

## Forth style (`forth-metrics.py --words 10`, the 19 files read)
- **Summary:** 1,958 words; 73% of 1-2 lines, 24% of 3-5, 20 of 6-10, 4 longer. All 4 longer ones are in leanforth.fs: `cli-check-usage.` 37 lines, `cli-other-usage.` 13, `cli-snap-misuse` 12, `check-command` 11. No locals. 58 globals, 97 deep shuffles, 536 return-stack operations (term-printer.fs 178, by its frame-step design, which the header justifies).
- **Long words:** the usage texts are lists, so moving them to cli/help.fs (R4) is enough. `cli-snap-misuse` and `check-command` become the refusal table (R4).
- **Shuffles:**
  - verify-semantics.fs:142 `pv-digits` uses `2 pick` inside a `?do`. Keep base under the loop instead: `>r … r@ pv-digit+ … r> drop`.
  - term-printer.fs:158-159 `lf-pp-more?`/`lf-pp-shown?` (`2 pick`) keep app, info and i; the frame record already holds them (`lf-pp-save3`).
- **Idiom, good:**
  - name-text.fs is a clean range table (`in-ranges?`);
  - print-lf.fs's reason table has a load-time count check;
  - program-depth.fs and examples.fs are stack-only and reentrant;
  - verify-semantics.fs keeps every structure frame off the data stack, so no number can forge one.

## Reuse searched
- **Tools:** `check-duplicates.py`: "284 baseline groups, none new or grown". `check-lib-callers.py`: OK (bigint allowed, plan FE1i-4).
- **Greps:** callers of `lf-ir-read-file`/`lf-ir-feed` and `verify-alias` (src, tests, scripts); main.fs requires; `move … +!` appenders in src/lib (none general); `manifest-name-room` (manifest.fs refuses longer names, so check-run.fs:948's `min` cannot cut); `in-ranges?`; the snapshot origin counts; `json-writer:` users.
- **New** next to the three earlier passes: R1, R2, R3's three copies and the count, R4's split plan, N1-N4, N6's faults.

## Probes run (exit codes)
- **chain.ndjson `--fuel 1000`:** text exit 0, JSON exitStatus 0; the same.
- **`--fuel 50`:** text exit 3, JSON 3, fuel 0 (B1). The fuel ladder 100/200/300/400/485 gives 56/200/300/400/485.
- **tests/cli/bugs/{proj-of-stuck-prop, proj-of-subst-prop, rec-missing-ih, rec-of-subst-prop}.ndjson `--no-manifest`:** text and JSON agree on the last verdicts and every count. JSON exitStatus is 1 for each. The text exit was hidden by a pipe, so it is not recorded.
- **composition-huge-number.ndjson:** "error: full: number beyond 32 bits", JSON counts null.
- **print `--statement lean,leanforth` dependent.ndjson:** output read. Exit 141 is from `head`'s pipe.
- **print `--lf` dependent.ndjson:** exit 0, 7 declarations stubbed. Then `check` of that text: exit 4, error 48 (N3).
- **Planted faults in print-names.fs** (baseline: golden 0, term-printer.fs 0):
  - `lf-pp-clash?` always false: golden 1, term-printer 0;
  - the shadow rule ignoring body use: 1 and 1;
  - `lf-pp-outer` off by one: 1 and 1.

  All three are caught. The file was restored and checked with `cmp`.
- **Not run:** an unsupported or NOT PROVED declaration in text against JSON; `--strict-axioms`; Gforth 0.7.3; `verify` itself (needs pinned Lean).

## Files
- **Read whole (13):**
  - cli: leanforth.fs (the parts the first pass had not read, so now all of it), check-run.fs, check-json.fs, name-text.fs, print-lf.fs;
  - program: verify.fs, verify-report.fs, verify-semantics.fs, clamp.fs, examples.fs, sha-words.fs, program-depth.fs;
  - present: term-printer.fs, print-names.fs, print-levels.fs.
- **In part (4):** program/ir-reader.fs and ir-run.fs (headers, callers), verify-alias.fs (header), verify-runner.fs 134-194; plus scripts/program_receipt.py 334-420 and 640-700.
- **Not read** (stopped at about two thirds of context):
  - present: binder-table, latex-text (3 planted faults exist), print-notation, notation-table, note-table, print-forth, print-strings, print-tokens, print-job, print-analysis, statement-forms, proof-outline, log-view, log-check;
  - front: level-map, level-normalize, level-params, level-simp, constructions, cases-several, ctor-idx, expr-remap, lctx-views, goal-print, step-log, term-find, syntax, elab-keys.
- **Uncertainties:** B1's cause was traced to the step-1 counter from the code and the probe, not in the kernel's counters. N1's trigger was not built.
