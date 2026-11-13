# Backlog Forth review FRP: src/cli, src/present, src/author, src/program (2026-11-12, main 3ac0558)

Reviewer: forth-reviewer (Sonnet), brief `.claude/work/briefs/FORTH-REVIEW.md`. Saved by the coordinator, lightly
condensed. Run: `scripts/forth-metrics.py --words 40` on the four folders; `scripts/check-portable-forth.py` (clean).
Read in full or large part: cli/tally.fs, cli/print.fs, cli/leanforth.fs 940-1260, cli/check-run.fs 640-760,
present/log-view.fs 140-380, present/print-notation.fs 30-169, author/build.fs 90-206, headers of program/ir-run.fs
and verify-semantics.fs; grep sweeps of all 46 files. Not read line by line: ir-reader.fs, print-forth.fs,
proof-outline.fs, verify-runner.fs, most of check-run.fs. Block coverage was not available (make coverage collected
no counts), so test gaps come from file names and `tests/mutants/faults.toml`. `make test`, mutants and 0.7.3 not run.

**Metrics** (46 files, 3,180 words): 70% of words 1-2 lines, 27% 3-5, 55 words 6-10, 9 over 10 (help/usage text or
dispatch in leanforth.fs, print-lf.fs, log-view `lf-lv-relates` 13, print-forth `lf-pf-node-by` 12). Every word has a
stack comment. 108 globals (42 author LFA-WORD table entries, 40 CREATE buffers/tables, 31 context records), 1 local,
292 deep shuffles, 1,282 return-stack operations, 38 lines over 90 characters. Shuffles / return-stack operations: cli
47/144, present 142/758, author 61/184, program 42/196.

## 1. Verdict

Better than feared: short words, universal stack comments, structures, context records and execution-token tables,
CASE dispatch, one shared outcome vocabulary (mapped once to exit codes in tally.fs); headers honest about trust (no
kernel file loads present/, author/ or program/). Defects are concentrated: (a) stack juggling in the pretty-printer
(words taking 4-5 items, `2 pick`/`-rot`/`>r` chains); (b) copy-pasted level/term twin code in log-view.fs; (c) four
raw field-offset spots; (d) two files too big (leanforth.fs 1,413 lines, check-run.fs 1,023); (e) test gaps for the
new notation, progress, --jobs and print-lf code. Worst files: present/log-view.fs, print-forth.fs, term-printer.fs,
print-notation.fs, log-check.fs, cli/print.fs, cli/leanforth.fs (size), cli/check-run.fs (size, raw offsets).

## 2. Refactoring batches (behaviour-preserving; none touches the checker's rules)

- **A, present/log-view.fs (low risk; outline goldens pin output).** A1 the level/term twins (lmark/tmark,
  -pair, -kids, build, ready, built?, unmark, new, copy; lines 260-380) are one algorithm over two accessors: pass
  the accessor as an xt (`: lf-lv-unmark-to ( made@-xt k -- ) 1+ 0 ?do i over execute lf-lv-unmarked loop drop ;`).
  A2 the `( tag first second )` triple threaded through lf-lv-node, -lfields, -tleaf, -tfields, -child-ref with
  `2 pick`/`rot drop rot`: a `/lv-node` record in the lf-lv context with accessors (removes ~10 of 25 deep shuffles).
  A3 lf-lv-premise/inference 146-152 counter under the loop index; lf-lv-relates (13 lines) as a table by rule.
- **B, present/print-notation.fs, term-printer.fs, print-analysis.fs, print-forth.fs (low-medium; goldens).** B1
  steps taking `( term row pos frames )` with `>r 2 pick 2 pick` (79-134): a `/pn-step` record saved with the frame.
  B2 split lf-pn-numeral? (90-96) into `lf-pn-ofnat?` and `lf-pn-literal-arg`, name the arity constant. B3 Neg of Neg
  prints `--a` (Lean `- -a`); notation-table.fs:68 load-time `variable lf-nt-fill` and :84 lf-nt-last invariant
  (props/tight mutate the previous row): a row-defining word taking all fields. B4 sup-digit CASE: a digit string
  table indexed by 3 bytes. B5 lf-pp-tag-step (397, 10 lines) and lf-pf-node-by (464, 12 lines) as CASE or xt tables.
  B6 proof-outline.fs:129-136, 693 raw offsets on `lf-ol-style`: a `/ol-style` structure. B7 log-check.fs:84,107 and
  note-table.fs:85 `pick`s: helper words taking the record address.
- **C, cli/leanforth.fs and cli/print.fs (low).** C1 split leanforth.fs: `cli/help.fs` (usage, codes, ~150 lines) and
  the `cli-entry` option table (1205-1260; a library candidate). C2 stale literals in user text: `cli-lacks.` (1082)
  prints "(0 of 729,263)" and plan numbers; `cli-codes.` (1161) restates tally.fs's exit codes: derive or test. C3
  `pr-form-bit` (print.fs:118-123) IF chain → table. C4 `pr-ends?` (77-80, three `pick`s) and `pr-item` (125-127) via
  `ends-with?`/`split-at` helpers; tests first (name longer than the text, empty component). C5 print-lf.fs:105,113
  `2 pick` chains; `fl-reason-text` (13 lines) as a message table.
- **D, cli/check-run.fs, check-json.fs (low-medium; --jobs/snapshot paths).** D1 `ck-lending` (472) stores four cells
  by raw offsets; `ck-lay-id-size` (930) is a record written as arithmetic: structures. D2 `ck-progress-line` (683-691)
  as a table of (label xt). D3 `ck-state` is a god record (18 globals, ~60 fields): group progress and snapshot fields
  (low value, last). D4 confirm `1000000 m*` on a huge `--progress=SECONDS` cannot wrap (test T2).
- **E, src/author (low).** E1 `lfa-shift` (build.fs:178-202) recurses on the host return stack, as deep as the term:
  a long `A B ->` chain may overflow and THROW instead of failing with a diagnostic (unverified: test a 5,000-arrow
  chain; if it fails, use lib/walk.fs). E2 lfa-copy-source/naming identical bodies → `lfa-copy-attr`; `lfa-copy`
  (105) CASE has no default arm: an unknown tag returns the term unshared; fail closed instead. E3 a test that every
  error constant has a catalogue row.
- **F, src/program (medium only for verify-semantics.fs and ir-run.fs, change only with the Lean differentials).**
  Best of the four folders (87% of words 1-2 lines). ir-run.fs:462 nested IF three deep → `irx-lit-fits?`; comment
  the `rot dup rot` chains at 782, 828.

## 3. Test gaps (coverage classes of TEST_COVERAGE_REVIEW.md)

No planted fault at all: author/constants, declarations, errors, namespaces, scopes, values; present/notation-table,
print-notation, note-table, print-names, print-tokens, print-job, print-levels (print-forth 1); cli/print-lf;
program/clamp, examples, program-depth, sha-words. Risky words without a fault: lf-pn-numeral?/sized/applies?,
pr-ends?/pr-named?, ck-lending/ck-moved?, tally worse-code/cli-severity, fl-reason-text, lfa-shift-var,
lfa-level-number, pv-alias. Missing tests: T1 (class 2-3) notation: Neg, mem, Iff, Ne, GT/GE, Nat.succ in Unicode,
¬(a ∧ b), 3-binder and ASCII Exists, big literal, over-application, loose bound variable, OfNat with a non-Nat
literal, truncated name pool, duplicate rows [tests/present/notation.fs]. T2 (class 3) `--progress`, `--jobs`,
`--memory-per-check`, `--fuel` at 0, negative, huge; `--name` empty, trailing dot, numeric part, longer than any
declaration [tests/cli/test_leanforth.py]. T3 (class 4) reexport onto the same file under two spellings or a symlink
may truncate the input (unverified): expect an error, input untouched. T4 (class 5) print when `lf-env-new` is full or
`lf-env-use` fails; print-lf stub listing (no test file names print-lf.fs). T5 (class 6) worker remade path,
"pool refused" serial fallback, a THROW inside a worker (check-run.fs:447) [tests/cli/jobs/]. T6 (class 7) a Gforth
0.7.3 run of the present and program tests. No dedicated test by name: present/note-table.fs, print-names.fs,
print-tokens.fs, cli/print-lf.fs, cli/check-json.fs.

## 4. Libraries

The `cli-entry` option/command table (leanforth.fs 1205-1260) is a general command-line parser → src/lib with tests.
present/latex-text.fs (TeX escaping) → src/lib. The progress/flush timing of check-run.fs (ck-after?, ck-flush-due?,
elapsed/eta) → `lib/progress.fs`. author/source.fs (positioned line reader) may be general; check its requires.

## 5. Portability

`stdout`, `stderr`, `flush-file` and `write-file` on stderr are used directly in cli/check-run.fs:664,694 and
cli/print-lf.fs:80 (Gforth names, not Forth-2012): define them in portability.fs or guard them. `[defined]` guards
are correct for getenv, utime/cputime, next-arg, version-string, (bye), warnings, fdepth, rec-forth; check-run.fs:273
degrades silently without a wall clock: say so in the header. UTF-8 literals in print-notation.fs depend on source
encoding, as before.

## Follow-ups from the review of batches A and B (2026-11-12, plan 9.4.5)

From [2026-11-12-refactor-present.md](2026-11-12-refactor-present.md), left for a later batch:
- **L2:** log-view's merged rebuild picks levels or terms with a true/false flag tested in nine words. Pass a
  `/lv-kind` record of execution tokens and offsets instead (the review gives the sketch).
- **L3:** the tag and rule dispatches (term-printer, print-forth, log-view) are chained CASEs split at arbitrary
  points. Use tables indexed by the validated tag or rule code, and stop lf-lv-relates depending on the catalogue's
  numbering.
- **I1:** /lv-node's reversed fields for `2@`.
