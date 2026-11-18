# LeanForth — Claude Code notes

The project rules live in `AGENTS.md` and are shared with Codex. They apply in
full; this file only adds Claude Code specifics. Do not duplicate or weaken
them here.

@../AGENTS.md

## History

Commits up to the `pre-claude` tag (`1db530d`, 2026-11-02) were developed with
OpenAI Codex. Codex-era docs (`docs/project/CODEX_HANDOFF.md`, `prompts/FIRST_CODEX_TASK.md`,
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

- Make runs 8 targets at a time by default (`JOBS=1` for one at a time); do
  not start several make commands at once. Timings of 2026-11-03 (10 cores,
  other agents running); per-target tables are in
  `docs/development/TESTING_STRATEGY.md`, "Running the suites".
- Inner loop: the focused test of what you change (the test file itself, its
  module's target, or `make test-changed`).
- `make test` — Forth and Python tests, about 8 s (36 s one target at a
  time; about 3 min at `JOBS=2`). Which suite a branch runs, once, at its
  end, follows the change tiers of `AGENTS.md` (owner, 2026-11-13, plan
  9.4.6): `make tier JOBS=2` runs them (`DRY_RUN=1` lists them) and records
  each pass per tree; never re-run a suite on a tree that already passed it
  (`make once GOALS=...` reuses the record).
- `make check` — `make test` plus every pinned-Lean comparison: about
  45 s when pinned Lean's runs are replayed from the shared Lean cache
  (`.claude/work/lean-cache` of the main checkout), about 70 s with an empty
  cache, about 75 s with `LEAN_CACHE=0` (as CI runs it); 345 s one target at
  a time without the cache; about 8 min at `JOBS=2`. Run it once, at the
  end of a branch whose tier needs it.
- Unit tests run on both engines, end-to-end tests once (owner,
  2026-11-14): `tests/test-classes.txt` classes every test target;
  `make test-unit` runs the unit ones (on gforth-fast with
  `GFORTH=.tools/gforth/bin/gforth-fast`), `make test-e2e` the others. A new
  test target needs a row there, or `make check-test-classes` (in
  `make test`) fails.
- Reviewers probe and plant their own faults; they do not repeat the
  implementer's recorded suite runs on the same head.
- GitHub CI is off at the owner's request (2026-11-11). Before every push run
  its jobs locally under `ulimit -u 500` and record the exit codes, as
  `AGENTS.md` requires: `scripts/push.sh` does this by change tier, its own
  tier only (a documentation push: the documentation and progress checks).
  Its full tier (owner, 2026-11-17) is the coverage ratchet of the touched
  source files over every target of `make test` that loads them
  (`make coverage-focus`, 2026-11-18), `make test`,
  `make test-unit` on gforth-fast and `make check-rest`, with the Lean cache,
  and each target's recorded pass is reused while the files it reads are
  unchanged (`scripts/tested-tree.py`); it picks `JOBS` (5, or 2 when other
  heavy runs are going or in CPU mode day; `JOBS=N` overrides).
  `scripts/push.sh --dry-run` shows the plan with estimated times.
- The cache-off full run is `make daily` (owner, 2026-11-17): once a night,
  by itself, and before a tag; it alone runs `make coverage-check` of every
  file and `make test-unit` on Gforth 0.7.3
  (`GFORTH=$PWD/.claude/work/A/gforth073.sh`); `make tag-check` must pass for
  the tree to be tagged. `scripts/push.sh` only reports its age and warns past
  36 hours.
- A branch that only adds a tactic plug-in (`scripts/check-tactic-plugins.py`
  finds it confined) gets the tactic tier: the front end's unit tests, every
  `.lf` end-to-end run and `reference-front`.

## Reviews

- `.claude/agents/forth-reviewer.md` is the Claude Code version of
  `.codex/agents/forth-reviewer.toml`; it follows `docs/development/FORTH_REVIEWER.md`.
  Keep the two agent definitions in sync. Run it on every branch that changes
  Forth source before merging, save the report in `docs/development/forth-reviews/`
  and log it there (`make test` enforces this on `main`). The same goes for
  `.claude/agents/done-checker.md` before anything is called done.
- An AI review alone never satisfies the review gates in `AGENTS.md`; the
  gate process and the owner's policy decisions are in `AGENTS.md` and
  `docs/project/OWNER_DECISIONS.md`. The owner is not a Lean expert: ask gate
  questions in plain language with a recommendation and reasons.

## Docs

- `docs/README.md` indexes all documentation by folder. Put new documents in
  the matching folder and add them to the index; `make check-docs` (part of
  `make test`) fails on broken links or missing `docs/` paths.

## Git

- Commit and push to `main` automatically at checkpoints (about every two to
  three hours, at session end, or when a needed branch lands; owner
  instructions 2026-11-02 and 2026-11-13; see `AGENTS.md`), after CI's two
  jobs pass locally; documentation-only commits ride with the next push. Never force-push or rewrite pushed history.
  Remote changes and new tags still need the user's approval.
- Commit subjects follow the existing style: short imperative sentence, no
  prefix (for example "Diagnose mixed definition type and value pairs").
