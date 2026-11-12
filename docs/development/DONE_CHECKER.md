# The done checker: is it integrated and does it work?

Owner, 2026-11-12: "we need to develop a checking agent that checks that when work is called done it is integrated
and fully functional, this issue has repeatedly turned up in this project." Examples of the problem:

- 2026-11-10: the compact store and parallel checking were reported done while `leanforth check` did not use them.
- 2026-11-12: demos showed theorems "in LeanForth words" and progress reports said LeanForth "gives Lean's verdict on
  all of Mathlib". The owner understood that LeanForth-language theorems run end to end. They do not: the words were
  printed from Lean's export, `leanforth check` refuses LeanForth text, and every accepted proof was produced by Lean
  and re-checked by LeanForth.

The done checker is an independent agent (`.claude/agents/done-checker.md`, `.codex/agents/done-checker.toml`; keep
the two in sync) that tests a claim the way a user would meet it and reports the stage the work has really reached.
It never edits files and never takes the implementing agent's word for anything.

## Stages

Every status in `docs/project/PLAN_DRAFT.md`, `docs/project/PROJECT_PROGRESS.md`, the README, the user documents and
the coordinator's reports to the owner uses one of these stages, the highest one that has been shown:

| Stage | Means |
| --- | --- |
| designed | written down (ADR, plan row); no code |
| written | code exists; not run by any test |
| tested alone | its own unit or synthetic tests pass; no user-facing command uses it |
| integrated | a user-facing command (`bin/leanforth …`, a documented make target, a documented Forth word) reaches it with the documented invocation |
| works end to end | that command, run on the real input a user would give (a Lean export, a `.lf` file, Init, Mathlib), gives the documented result; the done checker has run it |
| **done** | works end to end, its documentation describes what actually happens, both CI jobs are green, any review gate is passed, every Forth change in it has a logged Forth review ([log](forth-reviews/LOG.md)) with no open blocking finding, and its new or changed words have tests in each applicable coverage class with coverage not dropped |

"Done" is written only with a done-checker report that says DONE; the plan row cites the report
(saved by the coordinator in [done-checks/](done-checks/2026-11-12-audit.md) as `<date>-<task>.md`).

## What the checker does for each claim

1. **State the claim as a user would read it**, in one sentence beginning "A user can …" (for example, "A user can
   write m + n = n + m and its proof in a LeanForth file and have LeanForth check it with no Lean tools"). Take the
   wording from the claim and from the documents a user reads (README, `docs/user/`), not from the implementer's notes.
2. **Find the entry point** the user would use and the input they would give it. If the claim names an input form
   (LeanForth text, a Lean file, Mathlib), that form must be the input: a substitute (an NDJSON export made by Lean
   when the claim is about LeanForth text; a test fixture when the claim is about a library) does not count.
3. **Run it** from a fresh shell at the repository root, copying the commands from the user documentation, on real
   input, outside any test harness. Record each command, its exit code and the decisive lines of its output.
4. **Look for the usual gaps:** placeholders (`import-stub`, hard-coded answers, golden files written by another
   tool); work done by another tool and only displayed by LeanForth; a path that only a test harness reaches; a
   narrower scope than claimed (five examples claimed as general support); sub-steps of the plan row still "not
   started"; documentation describing planned behavior as present.
5. **Check the wording** of the claim and of the documents against what the run showed. Flag words that promise more:
   "proved", "LeanForth version", "supports", "full", "all", "done". Until LeanForth text is checked by the kernel
   (plan 8.2.1c), a theorem is "checked by LeanForth from Lean's export", never "proved by LeanForth".

## Report

At most 60 lines; first line `DONE`, `NOT DONE: <stage reached>` or `MIXED` (for an audit of several claims). Then,
per claim: the "A user can …" sentence, the stage reached, the commands with exit codes and decisive output, the gaps,
and corrected wording for each overstated sentence (file:line). The coordinator saves it under `docs/development/done-checks/`,
corrects the documents, and tells the owner in plain language what works and what does not.

## When it runs

- Before any plan row, milestone, progress report or message to the owner calls work done.
- After each merge that changes a user-facing command or a user document's claims.
- As a periodic audit of every row marked done or implemented and of the README and user documents.
