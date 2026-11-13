# Forth review: `leanforth verify` in help and capabilities (verify-b a1f13431), 2026-11-13

Reviewer: forth-reviewer (Opus), one short round, probe. Range 995a1c45..a1f13431 (one commit). Verdict: **not
blocking** (0 blocking, 0 high, 0 medium, 1 low).

1. **Low, `src/cli/leanforth.fs:1395-1396` (`cli-verify-usage.`):** help shows `--write-ir` as an optional extra on a
   full verify run, but `scripts/program_verify.py:543-558` treats it as a separate mode (writes the IR and stops,
   ignoring `--out` and `--detail`), as the driver's own docstring shows. Suggested: a usage line of its own,
   `verify SOURCE.fs --contract CONTRACT --write-ir`, which also drops the continuation line; the same wording in
   `docs/user/COMMAND_LINE.md:315`. A follow-up.

**Style.** `forth-metrics.py --words 10`: 415 words before, 419 after; lines per word 1-2: 244, 3-5: 158, 6-10: 13,
over 10: 4; globals 8, locals 0, deep shuffles 11, return-stack operations 25, lines over 90 characters 11 (as before
and as the baseline). The four new words are 1-3 lines, all `( -- )` with stack comments; the longest new line is 89
characters (`cli-usage.`). No style findings.

**What was run** (bundled Gforth 1.0.0, on `git archive` extracts of base and head): `bin/leanforth help` and
`capabilities` exit 0, no line over 80 characters, the only change in capabilities being the three verify lines in
"supported:" before "Mathlib:"; `bin/leanforth verify --help` exit 0 and lists every option; `scripts/mutants.py
--only` caught both of the commit's faults and four of the reviewer's own (the needs line dropped, the meaning line
dropped, `--rerun` removed from the replay usage, a missing `cr`). The test runs the real `bin/leanforth` and checks
the lines' places and exit 0; malformed input, resources and rollback do not apply. Trust wording is right: Lean
writes the proofs and this checker re-checks them. No suite runs repeated.

**Owner summary.** Help and capabilities now list `leanforth verify` and say it needs Python 3 and pinned Lean (V1
only). The text is accurate and tested; one small help-text fix is suggested and does not block the merge.
