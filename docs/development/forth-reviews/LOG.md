# Forth review log

Every change to Forth source under `src/` reaches `main` only after an independent Forth reviewer
([guide](../FORTH_REVIEWER.md); `.claude/agents/forth-reviewer.md`, `.codex/agents/forth-reviewer.toml`) has read
its commits. `scripts/check-forth-quality.py` (part of `make test`) fails on `main` when a commit after `3ac0558`
that changes `src/**/*.fs` lies in no range listed here. One row per review; the range is written
`` `BASE..HEAD` `` (the commits of `git rev-list BASE..HEAD`); the report is saved in this folder; "open" counts the
findings neither fixed nor turned into plan tasks. A row that raises the style baseline
(`tests/forth-quality-baseline.json`) says so.

| Date | Range | Scope | Reviewer | Report | Findings | Open |
| --- | --- | --- | --- | --- | --- | --- |
| 2026-11-12 | `390197d..af64e27` | notation printer and demos (branch demos) | forth-reviewer (Sonnet) | [report](2026-11-12-demos-printer.md) | 0 blocking, 3 low, 7 style/test/docs | 10, to the printer follow-up |
| 2026-11-12 | `fcce360..3ac0558` | backlog: whole of src/cli, src/present, src/author, src/program | forth-reviewer FRP (Sonnet) | [report](2026-11-12-backlog-cli-present-author-program.md) | 0 blocking; refactor batches A-F; test gaps T1-T6; libraries; portability | all, to the refactoring batches |
| 2026-11-12 | `fcce360..3ac0558` | backlog: whole of src/kernel | forth-reviewer FRK (Opus) | [report](2026-11-12-backlog-kernel.md) | 0 blocking; F1-F2 medium (scheduler use after free when full, reproduced; kernel requires import/ and present/), F3-F6 low, F7 docs; batches A-J; test gaps; libraries; portability | all, to the bug fixes and refactoring batches |
| 2026-11-12 | `fcce360..3ac0558` | backlog: whole of src/import, src/core, src/lib | forth-reviewer FRI (Opus) | [report](2026-11-12-backlog-import-core-lib.md) | 0 blocking; F1 medium (layer full reported invalid), F2 32-bit wraps, F3-F4 low, F5 portability; batches B1-B8; test gaps; libraries | all, to the bug fixes and refactoring batches |

## Backlog

Owner, 2026-11-12: Forth style reviews were not run for the changes merged between 2026-11-06 (`fcce360`) and
`3ac0558` (about 13,000 inserted lines in `src/`; only correctness reviews ran), and `make coverage` had silently
stopped collecting counts. The backlog review of the whole of `src/` (reviewers FRK: `src/kernel`; FRI: `src/import`,
`src/core`, `src/lib`; FRP: `src/cli`, `src/present`, `src/author`, `src/program`) is in progress; its reports and
the refactoring batches that follow are logged here as they land (plan task 9.4.5).
