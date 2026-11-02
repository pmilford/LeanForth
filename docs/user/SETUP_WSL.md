# Windows → WSL2 setup

Recommended: Windows 11 with WSL2 Ubuntu; VS Code installed on Windows with its WSL extension; all Linux toolchains and the git working tree inside your Ubuntu home directory (for example `~/code/LeanForth`), not under `/mnt/c`. Development inside WSL is easier for Gforth, C compilers and Lean's Linux-specific sandboxing tools.

## On Windows: one-time actions

1. In **PowerShell as Administrator**, if WSL/Ubuntu is not yet installed: `wsl --install -d Ubuntu` (restart if prompted). If already installed, inspect using `wsl --list --verbose`; avoid replacing a working installation.
2. Install current **Visual Studio Code for Windows** and the **WSL** extension. Open Ubuntu from Windows Terminal; run `code .` from the Linux project directory to open it in WSL mode.
3. Obtain access to the project repository. GitHub authentication is only needed
   if the repository is private; it is not needed to run a local checkout.

## In the Ubuntu/WSL shell

```bash
sudo apt update
sudo apt install -y git gh build-essential make pkg-config curl python3 \
  m4 libtool-bin libffi-dev libltdl-dev zstd
git clone https://github.com/pmilford/LeanForth.git   # needs access if private
cd LeanForth
scripts/install-gforth.sh .tools/gforth
scripts/install-lean.sh .tools/elan/toolchains/leanprover--lean4---v4.35.0
bash scripts/check-env.sh
make test     # Forth and Python tests
make check    # adds every pinned-Lean comparison
```

The install scripts download the pinned **Gforth 1.0.0** source and **Lean
4.35.0** release, reject them unless their SHA-256 hashes match, and install
into the ignored `.tools/` directory. Nothing is installed system-wide apart
from the apt packages above, and no shell profile is changed. Ubuntu's own
`gforth` package (0.7.3) is older; CI uses it only as a portability check. Do
not rely on Gforth 1.0 extensions in portable kernel modules. Exact versions,
hashes and every install command run so far are recorded in
`docs/development/INSTALLATION_LOG.md` and `docs/development/VERSIONS.md`.

Lean can alternatively be managed with **elan**: install it with
`ELAN_HOME="$PWD/.tools/elan"` and `--no-modify-path`, as described in the
installation log. Always set `ELAN_HOME` when running elan's `lean` or
`lake`; otherwise elan downloads another toolchain into `~/.elan`. The
Makefile calls the toolchain binary directly and needs neither.

Use Linux `bubblewrap` (`bwrap`) if supported by the local WSL kernel to exercise `lake check --paranoid`. Test sandboxing explicitly; do not disable it to claim a secure check.

## Coding agents

The project rules for coding agents are in `AGENTS.md`. Both agents below
follow them; install whichever you use from its official documentation.

- **Claude Code** — run `claude` in the repository directory. It loads
  `.claude/CLAUDE.md`, which imports `AGENTS.md`.
- **Codex** — `npm install -g @openai/codex@latest`, then run `codex` in the
  repository directory. It reads `AGENTS.md` directly.

`prompts/FIRST_CODEX_TASK.md` was the first task given to Codex on
2026-10-30. It is complete and kept only as a historical record; do not
paste it as a new task.

## GitHub

GitHub CLI authentication is interactive and needs the user's authorization:
`gh auth login`. The project's repository already exists; creating, renaming
or changing remotes requires the owner's explicit approval.

Sources: https://learn.microsoft.com/en-us/windows/wsl/setup/environment , https://learn.microsoft.com/en-us/windows/wsl/tutorials/wsl-vscode , https://docs.github.com/en/github-cli/github-cli/quickstart , https://gforth.org/ , https://lean-lang.org/ .
