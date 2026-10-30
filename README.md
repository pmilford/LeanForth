# LeanForth — Codex starter handoff

**Status: design/handoff only, no LeanForth implementation has been written.**

LeanForth is a Forth-friendly mathematical theorem-proving **and verified-programming** system, with an independently trustworthy checker and efficient executable Forth backends. Its mathematical data and presentation notation must never redefine or ambiguously overload the Forth source grammar.

Start with **[docs/CODEX_HANDOFF.md](docs/CODEX_HANDOFF.md)**, then **[docs/IMPLEMENTATION_PLAN.md](docs/IMPLEMENTATION_PLAN.md)** and **[AGENTS.md](AGENTS.md)**. Launch the first Codex task from **[prompts/FIRST_CODEX_TASK.md](prompts/FIRST_CODEX_TASK.md)**. Follow **[docs/SETUP_WSL.md](docs/SETUP_WSL.md)** for the recommended Windows/WSL2 setup.

Proposed baseline: Windows 11 desktop; WSL2 Ubuntu development; Gforth 1.0 (reference implementation); Forth-2012 subset for portability; Lean 4.35.0 pinned as interoperability oracle; GitHub; Codex CLI or VS Code extension. CPU tensors first, using high-performance C/BLAS libraries behind a portable FFI; optional ArrayFire/GPU after measured need.

The initial Forth module and `make smoke` exercise the host; they do not prove
theorems or verify programs. Run `make smoke` from the repository root; it
uses `.tools/gforth/bin/gforth` if present, otherwise `gforth` on PATH. Override
with `make smoke GFORTH=/path/to/gforth`. A missing or failing host makes the
command fail. Lean is pinned in `lean-toolchain`; local installation details
and remaining reproducibility work are in [the installation log](docs/INSTALLATION_LOG.md).

GitHub CI has not run yet. Its Ubuntu job uses the distribution Gforth package
as an additional host smoke check; pinned Gforth 1.0 CI remains to be set up.
The project code is MIT licensed; Gforth is a separately licensed dependency.
