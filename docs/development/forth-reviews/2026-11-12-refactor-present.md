# Forth review of branch refactor-present (00d3584..e9ce9ce), 2026-11-12 — not blocking

Reviewer: forth-reviewer (Opus), read-only, in worktree agent-a58fa3c12f31c8905. Scope: the seven present/ files (log-check, log-view, notation-table, print-forth, print-notation, statement-forms, term-printer), their tests, faults.toml and the baseline; 2990f42 only merges main. Brief: .claude/work/briefs/REFACTOR.md; source reviews FRP (batches A, B, T1) and demos-printer (findings 1-7, 9, 10). Findings: 0 high, 0 medium, 4 low, 4 info.

## Behaviour
- Traced old against new on every success and failure path:
  - log-view: premises (now lf-lc-premises), lf-lv-inference, encloses/binder, child-ref/parts, chars, the merged mark, read, fields, add, build, ready, built?, unmark, new and copy, rebuilt, redex, lifted, shifted, with-levels, relates.
  - log-check: start? through `within` (equal for s ≥ 0), term-copy?, count with 2>r, kinds? split.
  - notation-table: lf-nt-new, precs, places, row; the infix-at:, prop- and power: rows, including the old Membership lprec/rprec 50 and Not's props and tight.
  - print-notation: spell, sized-row, fitting, ofnat?/numeral? (arity 3 and a=1 now read from the row), pos, the step record on the frames (kept/taken/forget), infix, suffix, power, braced, raised, the superscript string, prefix, binders.
  - CASE splits in term-printer and print-forth: the default arms forward correctly.
- No stack or behaviour difference found except the intended `- -2`. Pinned Lean 4.35.0 prints `- -2 : Int`, `- - -2`, `2 - -3`, `fun a => - -a` and `-(-a + 1)`, which matches the new rule: a blank only when the symbol ends with '-' and the operand is an unparenthesized prefix row starting with '-'.
- No golden changed in the range. outlines.golden (927 lines), the 7 LaTeX fragments (pdflatex), fixtures.golden, print-deep, outline-block 5/5 and the DEMOS page check all pass.
- The level/term merge is safe: a term build nests level builds only (through a symbolic Sort or a reference's levels), each kind has its own walk and node record, and walk-run does not clear walk-arg.

## Findings
- L1, test gaps: my planted faults survived the tests named here.
  - (a) log-view.fs:477 lf-lv-redex-here with the release moved to the success branch survives derivation-log.fs and check_outline.py: no test has a damaged log whose redex body or argument cannot be rebuilt (class 6, rollback).
  - (b) print-notation.fs:86 lf-pn-left's followed flag `true`→`false` survives: no test has a binder as an infix row's left operand, e.g. `(∃ x, p x) ∧ q` or `(fun x => x) = f`.
  - (c) lf-pn-pos ignoring lf-nt-props survives: no test has a Pi as an operand of a connective (∀ inside ∧).
  - (d) notation-table.fs:88 lf-nt-end without `align` survives (unaligned access works on x86-64). Add a test that walks lf-nt-rows to lf-nt-rows-end with lf-nt-after and checks every row with `dup aligned =`.
  - Plant (a)-(c) once the tests exist.
- L2, style (FORTH_STYLE §1, FRP A1): the merged rebuild passes a true/false kind that nine words test with IF/ELSE (lf-lv-work, -made-at, -rec, -copies, -input?, -copy-node, -mark-kids, -fields!, -add). A kind record passed by address removes all nine:
  `begin-structure /lv-kind  field: lvk-walk  field: lvk-made  field: lvk-node  field: lvk-copies  field: lvk-valid  field: lvk-read  field: lvk-kids  field: lvk-fields  field: lvk-add  end-structure`
  `: lf-lv-made-at ( k kind -- addr ) lvk-made @ lf-lv + swap cells + ;`
  `: lf-lv-rec ( kind -- node ) lvk-node @ lf-lv + ;`
  `: lf-lv-copy-node ( k kind -- tag first second ) lvk-read @ execute ;`
- L3, style: the tag and rule dispatches are split into two chained CASEs to get under the length limit, and the split points are arbitrary. lf-pf-leaf-by's "leaves" omit bvar and constant, which are leaves too. lf-lv-relates depends on the catalogue's numbering (`lf-rule-resolve <`). Walkers dispatch through a table indexed by the tag or rule, which is validated first:
  `create lf-pp-steps lf-tag-limit cells allot`, filled at load,
  `: lf-pp-tag-step ( tag -- xt ) cells lf-pp-steps + @ ;`
  and the same for rule codes below lf-rule-limit (64), with lf-lv-decl as the default.
- L4, robustness: lf-pn-minus-end? (print-notation.fs) reads the byte before an empty spelling (`+ 1-` with u = 0). Today only spelt rows print, so this is unreachable. Guard it and simplify:
  `: lf-pn-last-char ( c-addr u -- c ) dup if + 1- c@ else 2drop 0 then ;`
  `: lf-pn-minus-end? ( row -- flag ) lf-pn-mode-sym lf-pn-last-char [char] - = ;`
  `: lf-pn-minus-start? ( row -- flag ) lf-pn-mode-sym if c@ [char] - = else drop false then ;`
- I1: /lv-node stores second before first so that `2@` gives ( first second ). This is correct and commented, but obscure; two `field:`s in order, read with plain `@`, would be clearer.
- I2: `defer lf-lv-level` is an internal forward reference for the level/term recursion, set once while loading. It is acceptable, but it is a process-global hook that the metrics do not count.
- I3: the load-time row builders take 4-5 numbers (lf-nt-new, lf-nt-row, lf-nt-places!). That is inherent to the table's row format and acceptable for defining words.
- I4: two of my faults have the same effect as the original code. A rebuilt constant's second field is set to 0, but the log copies constants with second 0 already (derivation-log.fs:790). And the `lf-pn-open? 0=` guard in lf-pn-minus-first? never applies, because Neg's operand at 75 is never parenthesized under Neg's 75. Mark both as known-equivalent or note them.

## Tests and planted faults
- Added tests: hand-written logs for log-check parts 6 and 9, every step-list line, premises and inference premises, rebuilding and damaging copies, every T1 notation case, and the note table's room.
- The 19 new faults and the retargeted printer-rebuilds-only-the-top are all caught; `mutants --check` reports 1164 entries, 0 stale.
- My 16 faults: 10 caught (swapped kind kids, sort level not rebuilt, binder name not copied, no unmark on failure, binder depth ignored, relates split moved, start? off by one, leaf copy unchecked, infix record left on the frames, spell pool not restored). 6 survived: L1 (a)-(d) and the two in I4.

## Metrics (forth-metrics, base 00d3584 → head e9ce9ce)
Columns: words, 1-2 lines, 3-5, 6-10, >10, globals, deep shuffles, return-stack ops, long lines.
- log-check: 39→56, 23→40, 14→16, 2→0, 0, 1→1, 6→2, 11→10, 0
- log-view: 155→180, 96→127, 55→53, 3→0, 1→0, 1→1, 25→7, 38→29, 2→0
- notation-table: 22→33, 19→32, 3→1, 0, 0, 3→1, 3→0, 21→18, 0
- print-forth: 148→149, 83→82, 61→64, 3→3, 1→0, 2→2, 24→24, 156→156, 3→0
- print-notation: 41→68, 19→48, 19→20, 3→0, 0, 0, 10→0, 56→45, 0
- statement-forms: 36→36, unchanged (comment only)
- term-printer: 120→122, 64→65, 54→56, 2→1, 0, 0, 8→8, 187→187, 1→0
- Total: 561→644 words; 6-10 lines 17→8; over 10 lines 2→0; globals 7→5; deep shuffles 82→47; return-stack ops 473→449; long lines 7→1.
- tests/forth-quality-baseline.json changes only downward (and word counts).

## Runs
- Gforth 1.0.0: tests/present/notation.fs, term-printer.fs, print-deep.fs, tests/core/derivation-log.fs, tests/author/author.fs, all exit 0.
- Gforth 0.7.3: notation, term-printer, derivation-log, author, all exit 0.
- Python: tests/present/check_outline.py, check_golden.py, test_outline_block.py and tests/demos/build_page.py --check all pass.
- Pinned Lean 4.35.0 `#check` of five negation forms (results above).
- `mutants.py --check` and `--only` / `--list` as above.
- Not run: make test/check, coverage, Init evidence (reports, fuel, CPU, memory), the printer differential, reference-demos. AI review is not the human review gate.
