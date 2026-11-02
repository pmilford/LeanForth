# LeanForth — Claude Code notes

The project rules live in `AGENTS.md` and are shared with Codex. They apply in
full; this file only adds Claude Code specifics. Do not duplicate or weaken
them here.

@../AGENTS.md

## History

Commits up to the `pre-claude` tag (`1db530d`, 2026-11-02) were developed with
OpenAI Codex. Codex-era docs (`docs/CODEX_HANDOFF.md`, `prompts/FIRST_CODEX_TASK.md`,
`.codex/`) remain the reference for intent; the first-task prompt is complete.

## Toolchain

- Gforth 1.0.0 is at `.tools/gforth/bin/gforth`; the Makefile picks it up
  automatically. CI uses Ubuntu's distribution Gforth (0.7.3), so behavior can
  differ between local and CI runs.
- Lean 4.35.0 lives under `.tools/elan`. **Never run `elan`, `lean` or `lake`
  without `ELAN_HOME` pointing there**: the elan proxy otherwise downloads a
  3 GB toolchain into `~/.elan`. `.claude/settings.local.json` sets `ELAN_HOME`
  and `LEAN` for this machine; on another machine, export them yourself:
  `ELAN_HOME="$PWD/.tools/elan" make <target> LEAN="$PWD/.tools/elan/bin/lean"`.
- `.tools/` is gitignored and machine-local (~3 GB).

## Checks

- CI suite (about 3 s locally; must pass before every commit):
  `make smoke test-harness test-core test-composition-fixture test-program`
- Lean oracle and differential targets (`make reference`, `make test-*-differential`)
  need Lean and are **not** run in CI. Run the ones relevant to a change and
  report exactly which ones ran.
- After pushing, check `gh run list --limit 3` and record the run URL and
  outcome, as `AGENTS.md` requires.

## Reviews

- `.claude/agents/forth-reviewer.md` is the Claude Code version of
  `.codex/agents/forth-reviewer.toml`; it follows `docs/FORTH_REVIEWER.md`.
  Keep the two agent definitions in sync. Use it for meaningful Forth changes.
- AI reviews never satisfy the human-review gates in `AGENTS.md`. Open human
  decisions are listed in `docs/CHECKED_ENVIRONMENT_REVIEW.md`.

## Git

- Push, remote changes and tag pushes need the user's explicit approval.
- Commit subjects follow the existing style: short imperative sentence, no
  prefix (for example "Diagnose mixed definition type and value pairs").
