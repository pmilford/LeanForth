# Forth review: layered-loads, layer entries and the checker's command line (2026-11-19)

Branch layered-loads, range d31fa83d..759b85d3 (10 commits: aae2a58f a6b98a16 e800f022 d4441b7e d965f340 7a8e5444 ddbaafcb 6be56e45 eedab1d2 759b85d3). The head 6ba6c9ca is a merge of main dded8b85, which adds no change under src/, bin/ or scripts/leanforth-run.sh. Reviewer: forth-reviewer (Opus), independent. This was a short review, limited to checks a-e the coordinator asked for.

Findings: 0 high, 2 medium (1 blocking), 7 low (0 blocking). **Verdict: merge after M1, and after M2 is fixed or the owner accepts it.** The Forth move is byte for byte, and the full load is unchanged apart from the 17 moved words' place. The two medium findings are in the shell and Python parts of the change.

## Findings

**M1 (medium, blocking: the exit-status contract).** A missing or unreadable `scripts/leanforth-run.sh` makes both launchers exit 1, which means "something rejected". It should be exit 5, an internal fault.
- Where: bin/leanforth:62 and bin/leanforth-checker:40, `. "$root/scripts/leanforth-run.sh"` with no check of its status.
- Why it matters: bin/leanforth's header promises that a failure of the tool is "an internal fault here, never a verdict". Before this branch, a broken checkout (for example a missing src/main.fs) gave exit 5.
- Reproduction: copy bin/ and scripts/start-limit.sh, but not leanforth-run.sh, then run `nors/bin/leanforth check x.ndjson`. It prints "No such file or directory" and exits 1. bin/leanforth-checker does the same. The old bin/leanforth with no src/ gives exit 5.
- Fix, in both launchers. The shared script always ends with `exit`, so the `||` branch runs only when it cannot be read:
  `. "$root/scripts/leanforth-run.sh" || { printf 'leanforth: internal fault: cannot read scripts/leanforth-run.sh\n' >&2; exit 5; }`
- Test: tests/scripts/test_start_limit.py or test_checker_launcher.py should copy bin/ without the shared script and expect exit 5. Add a planted fault that drops the `||` clause.

**M2 (medium: the product's evidence names a command that did not run).** `leanforth verify` now checks the export through bin/leanforth-checker, but the receipt still says bin/leanforth ran.
- What changed: scripts/program_receipt.py:640 now has `LEANFORTH = ["bash", ".../bin/leanforth-checker"]`, so the user's `bin/leanforth verify` checks its export with bin/leanforth-checker. This changes what the product runs. It is not covered by "no behaviour change".
- What still says bin/leanforth:
  - the receipt's evidence text, program_receipt.py:277: "LeanForth's checker (bin/leanforth check, …) checked every declaration";
  - program_receipt.py:21 and :665;
  - program_verify.py:26;
  - docs/programming/PROGRAM_RECEIPTS.md:14, :90 and :461.
- The verdict is the same: the same kernel files, and output pinned byte for byte by test_checker_launcher.py. The problem is that the receipt states a run that did not happen (AGENTS.md: "say exactly what was run").
- Fix, either of:
  - name what ran in the receipt and these texts, for example "bin/leanforth-checker check, the checker's load; bin/leanforth prints the same";
  - or keep bin/leanforth in the product path and let only the tests run the checker launcher.
- Fix it before the merge, or record the owner's acceptance.

**L1.** The refusal text "…checked by bin/leanforth (src/main.fs), not by this load" (src/cli/leanforth.fs:1141) uses the word "load", which users do not know. Suggested text: "error: bin/leanforth-checker checks exports and snapshots only; check a LeanForth text with bin/leanforth". The pinned string in tests/cli/checker-load.fs:20 and test_checker_launcher.py would change with it.

**L2.** bin/leanforth-checker's `help` and `capabilities` still advertise `check … FILE.lf` (help lines 17 and 32), because their output is byte-identical to bin/leanforth's by design. That is acceptable, but docs/user/COMMAND_LINE.md:549-555 should say so. Its "it starts a little sooner" also invites users to run it; say it is the launcher of the export-only tests, and that users run bin/leanforth.

**L3.** The comment "A text of only #check lines … (error 49) …" stayed at src/cli/leanforth.fs:1069 above `cli-checks-only`. It used to explain `cli-checks-only?` as well, which moved to src/cli/leanforth-text.fs:53 without it. Add one line there, pointing to the comment in leanforth.fs.

**L4.** src/cli/leanforth-text.fs gets lib/decimal.fs (`.decimal`), lib/outcome.fs (`outcome-text`), cli/tally.fs (`outcome>code`) and cli/check-run.fs (`ck-*`) only through ./leanforth.fs. Under the "require what you use" rule, require them directly. All four are already loaded at that point, so the load order does not change. The words used from front/ and author/ arrive through check-lf.fs and elab-decl.fs, as they did in the old leanforth.fs.

**L5.** scripts/forth-metrics.py does not count `defer` as a global: leanforth.fs's globals stay at 7 with the new `cli-text-run`. The style ratchet cannot see deferred hooks. Plan row: count DEFER.

**L6.** In tests/mutants/faults.d/layered-loads.toml, the three Forth and launcher faults (refusal exit code, `is` dropped, `lf_entry` swapped) and the Python faults are sound. No fault or test covers M1 (see its fix).

**L7.** The finder's `# inputs: named only:` declarations hide a path from a program's inputs. If a later edit starts running that path, the finder will not notice. Optional: have changed-tests.py refuse a NAMED_ONLY path that also appears as a subprocess argument literal.

## Checks a-e

a. **Byte-for-byte move.** I wrote a script that splits each file into definitions (a `:`/`:noname` line plus its indented lines) and compares the raw text and the token streams: old src/cli/leanforth.fs (main dded8b85, the merged base) against the new leanforth.fs plus leanforth-text.fs.
- All 510 old definitions are present.
- Raw text and tokens are identical except `cli-text-run`, which became `:noname ( -- )` followed by `is cli-text-run`.
- The 17 moved words are in their old relative order.
- Against 7a8e5444^, the only other difference is `cli-again#`, main's 98e0c436, which arrived through the merge.
- Outside definitions, leanforth.fs changed only by its four `require` lines and the new defer.

b. **The deferred word.**
- Re-entrancy: `cli-text-run` is the only new global. It is written twice, both while loading, by the default `is` at leanforth.fs:1143 and by leanforth-text.fs. Nothing in src/ writes it at run time: `is cli-text-run` occurs only in those two places, and there is no `defer!` or `action-of`.
- `context-sealed?` is 0 at the end of the full load (probed), so both writes come before the first `context-new`.
- It is read on the driver task through `['] cli-text-run cli-fed-run` (leanforth.fs:1180). A text is always checked serially, so no worker reads it.
- There is no seal guard, the same as the existing load-time hooks (front/elab-decl.fs:91, `' edc-fresh is lfa-declaration-fresh`). lib/ has no sealed-hook word to reuse. Not a finding under step 4a.
- Portability: `defer`, `is` and `:noname` are Forth-2012 CORE EXT, and 42 src files already use `defer`. lib/portability.fs needs no adapter.
- I ran tests/cli/checker-load.fs on Gforth 1.0.0 and on 0.7.3 (.claude/work/A/gforth073.sh): 0 cases failed on both. On 0.7.3 the message case is skipped, as there is no `>string-execute`.
- Can the product reach the default? Only if leanforth-text.fs fails to load. load/cli.fs requires it, so a failure would stop the load: Gforth's status is not 100-106, so the launcher reports exit 5. bin/leanforth always loads src/main.fs.
- Probes: `bin/leanforth-checker check tests/author/01-identity.lf` printed the refusal line and exited 4. With `--steps -` the result is the same, and nothing else is printed or created. Before the refusal, the misuse, file-open and `--env` checks run unchanged. Nothing is reported accepted. `bin/leanforth check` on the same text gives "accepted: 1", exit 0.

c. **Launchers.**
- `diff` of the old bin/leanforth body against scripts/leanforth-run.sh: identical except `"$root/src/main.fs"` became `"$lf_entry"`.
- Unchanged: the engine search (GFORTH, `.tools`, PATH), `--fast`/`--checked`, quoting (`"$@"`, `"${@:2}"`, `arguments=("$@")`), the `-ef` pairs, the commit lookup, `verify` (python3 -I, statuses 0-6, else 5) and the 10[0-6] status mapping.
- When sourced with no arguments, the script shares the caller's `$@`, and its `shift` acts on them, which is correct.
- bin/leanforth-checker's header matches bin/leanforth's: the same `set -u`, the same 254 trap, the same root discovery, start-limit.sh, and `GFORTH_ENV=off` set before the shared part. leanforth-run.sh is mode 644 (not executable).
- Problems found: M1, M2, L2.

d. **Layer entries.**
- Every src/load/*.fs holds only comments and `require` lines.
- `scripts/check-layers.py --gforth` (Gforth 1.0.0) on a scratch copy: "8 layer entries keep to their layers, and Gforth loads each alone within its closure", exit 0. Its ENTRIES table matches src/README.md, "Layer entries".
- load/kernel.fs requires exactly the two modules main.fs used to require (mixed-definition-probe.fs, check-declaration.fs). Its closure stays within lib/, core/ and kernel/.
- The checker entry is the only one that loads part of present/: the four name-text modules that import/run-record.fs needs.

e. **Load order.** I dumped forth-wordlist with `traverse-wordlist` after loading src/main.fs from main and from the head, on Gforth 1.0.0.
- Both have 23,155 names, as the same multiset.
- With the 17 moved words removed, the order is the same. The 17 now come last, in their old order.
- `unused` differs by 160 bytes.
- None of the 18 names is defined twice. No token in a moved body has a second definition in the load (only `(`), so every reference binds to the same word as before.
- No `marker`, no search-order change, and no `[defined]` test of a moved word in src/. The only one in the tests is the intended `false false` in checker-load.fs:14. The 56 changed test files have no `[defined]` guard on project words that could now skip cases silently.
- I did not repeat the README's claim that the comparison was also made on Gforth 0.7.3.

**Inputs declarations (sanity read).**
- program_receipt.py, test_program_verify.py, test_parallel_stress.py, clamp_mutants.py and tests/support/toolchain.py name bin/leanforth (and src/main.fs) only in text. None of them runs it; they run bin/leanforth-checker.
- verify_check.py's and failure_path_faults.py's `named only: src` hide only reads of the whole folder. The files they really load are named and followed.
- None of these declarations hides a real input.

## Reuse
- Searched:
  - `defer`/`is` hooks and `context-sealed?` across src/;
  - lib/ and docs/development/LIBRARY_WORDS.md for a sealed-hook word (none; cons.fs's `cons-hooks!` is a per-table record, not a load hook);
  - where every word the moved bodies use is defined;
  - `scripts/check-duplicates.py`: "192 baseline groups, … none new or grown", exit 0;
  - `scripts/check-lib-callers.py`: exit 0; its only note is bigint.fs, allowed by plan FE1i-4.
- The branch adds no general-purpose word. leanforth-text.fs holds only command-line words for text, moved unchanged. Reuse: none found.

## Forth style
- `forth-metrics.py --words 10` on src/cli/leanforth.fs, src/cli/leanforth-text.fs, src/load/*.fs and src/main.fs: 515 words; 61% one or two lines, 35% three to five, 2% six to ten, 3 over ten; globals 7, context members 1, deep shuffles 9, return-stack ops 21, lines over 90 characters 9.
  - leanforth-text.fs: 18 words, 0 long, 0 globals, 0 shuffles.
  - leanforth.fs: 497 words, against 514 on main. Long words, globals and shuffles are unchanged.
  - The longest words (`cli-check-usage.`, 37 lines; `cli-other-usage.`; `check-command`) are older than this branch and outside its change.
  - src/load/ and main.fs: 0 words.
- No style finding against the new code. The default refusal is a two-line `:noname` with the module's usual `exit-malformed cli-code!` ending. The moved words are unchanged.

## Coverage classes (changed words: `cli-text-run` and its default)
- Covered:
  - pass: the text is checked by bin/leanforth (test_checker_launcher.py Text, and the existing text tests);
  - fail: the refusal gives exit 4 and its message (tests/cli/checker-load.fs:16 and :21);
  - interface and stack: `text-check -> 4`;
  - state: a refusal followed by an export check gives `4 0`, so the worst code is reset;
  - workflow: the two launchers compared on 46 commands and 2 follow-on pairs;
  - faults: the three in layered-loads.toml.
- Missing: the resources class for the launcher pair (M1). Malformed input is unaffected: the misuse checks run before the refusal, unchanged.

## Run
Gforth 1.0.0 (.tools/gforth/bin/gforth) and 0.7.3 (.claude/work/A/gforth073.sh), on `git archive` copies of 6ba6c9ca and dded8b85 under the session scratchpad (ll-review/), with `ulimit -u 500`, stdin from /dev/null and GFORTH_ENV=off. Commands:
- the definition comparison script;
- word-list dumps of src/main.fs (main and head);
- bin/leanforth-checker and bin/leanforth on tests/author/01-identity.lf;
- tests/cli/checker-load.fs on both Gforths;
- the M1 probe;
- check-layers.py --gforth, check-duplicates.py, check-lib-callers.py and forth-metrics.py.

No suite was re-run, and no make target was run. AI review does not replace the owner's review.

## Fixes (2026-11-19, commit 5783f590 on branch layered-loads)

- **M1 fixed.** Both launchers exit 5 with "leanforth: internal fault: cannot read scripts/leanforth-run.sh" when the shared script is unreadable. Test: `BrokenCheckout` in tests/cli/test_checker_launcher.py (a copy of bin/ and scripts/start-limit.sh without the script, both launchers). Faults `ll-launcher-missing-run-script` and `ll-leanforth-missing-run-script`.
- **M2 fixed (owner's option 2, "m2 option 2", 2026-11-19).** A receipt names the launcher that ran: `LAUNCHER = "bin/leanforth-checker"` in scripts/program_receipt.py is the one name, used by `LEANFORTH` (what the check step executes) and by the A8 text; program_verify.py's step 6 text, docs/programming/PROGRAM_RECEIPTS.md, docs/design/VERIFY_COMMAND.md and docs/user/WORKFLOWS.md say it too (the texts that tell a user what to run still say bin/leanforth). Test: `StatedLauncher` in tests/program/test_receipts.py; fault `ll-receipt-names-other-launcher`. Recorded files changed (only A8's text; no hash, verdict or format field, no schema change, `schemaVersion` stays 0.3, noted in PROGRAM_RECEIPTS.md): tests/program/receipts/generated/lf-clamp.json and lf-clamp.md (regenerated by `scripts/program_receipt.py write`) and the golden receipts tests/program/verify/golden/{lf-checked-abs,lf-checked-add,lf-clamp,lf-in-range,wrong-checked-add-total,wrong-clamp-swapped,wrong-in-range-exclusive}.receipt.json.
- **L1 fixed.** The refusal reads "bin/leanforth-checker checks exports and snapshots only; check a LeanForth text with bin/leanforth" (tests/cli/checker-load.fs, test_checker_launcher.py updated). Fault `ll-text-refusal-accepts` quotes the neighbouring line and is unchanged.
- **L2 fixed.** docs/user/COMMAND_LINE.md says bin/leanforth-checker is a test launcher, its help is the product's, and no longer invites users to run it.
- **L3 fixed.** The comment for `cli-checks-only?` is restored in src/cli/leanforth-text.fs.
- **L4 fixed.** leanforth-text.fs requires lib/decimal.fs, lib/outcome.fs, cli/tally.fs and cli/check-run.fs directly; `words` of the full load is identical before and after.
- **L5, L7 planned**: items (14) and (15) of plan row 9.4.8n.
- **L6 and the reviewer's other notes**: no change needed.
