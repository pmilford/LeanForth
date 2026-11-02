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

- Gforth 1.0.0 is at `.tools/gforth/bin/gforth` and Lean 4.35.0 at
  `.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`; the Makefile
  uses both automatically. Reinstall them with `scripts/install-gforth.sh` and
  `scripts/install-lean.sh` (see README).
- **Never run the elan proxies (`.tools/elan/bin/{elan,lean,lake}`) without
  `ELAN_HOME` pointing at `.tools/elan`**: elan otherwise downloads a 3 GB
  toolchain into `~/.elan`. `.claude/settings.local.json` sets `ELAN_HOME` on
  this machine. Prefer the toolchain binary above.
- `.tools/` is gitignored, machine-local (~3 GB) and the user's data. Never
  delete it or anything else that was not explicitly planned (see `AGENTS.md`).

## Checks

- `make test` — Forth and Python tests, about 3 s; run before every commit.
- `make check` — `make test` plus every pinned-Lean comparison, about 70 s.
- CI runs `make test` on Ubuntu's Gforth 0.7.3 and `make check` on pinned
  Gforth 1.0.0 and Lean 4.35.0. After pushing, check `gh run list --limit 3`
  and record the run URL and outcome, as `AGENTS.md` requires.

## Reviews

- `.claude/agents/forth-reviewer.md` is the Claude Code version of
  `.codex/agents/forth-reviewer.toml`; it follows `docs/FORTH_REVIEWER.md`.
  Keep the two agent definitions in sync. Use it for meaningful Forth changes.
- AI reviews never satisfy the human-review gates in `AGENTS.md`. Open human
  decisions are listed in `docs/CHECKED_ENVIRONMENT_REVIEW.md`.

## Git

- Commit and push to `main` automatically after each work session and at safe
  checkpoints once `make test` passes (owner instruction, 2026-11-02; see
  `AGENTS.md`). Then check CI. Never force-push or rewrite pushed history.
  Remote changes and new tags still need the user's approval.
- Commit subjects follow the existing style: short imperative sentence, no
  prefix (for example "Diagnose mixed definition type and value pairs").
