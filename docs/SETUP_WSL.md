# Windows -> WSL2 -> Codex startup

Recommended: Windows 11 with WSL2 Ubuntu; VS Code installed on Windows with its WSL extension; all Linux toolchains and the git working tree inside `~/src/LeanForth` in Ubuntu (not `/mnt/c`). Development inside WSL is easier for Gforth, C compilers and Lean's Linux-specific sandboxing tools.

## On Windows: one-time actions

1. In **PowerShell as Administrator**, if WSL/Ubuntu is not yet installed: `wsl --install -d Ubuntu` (restart if prompted). If already installed, inspect using `wsl --list --verbose`; avoid replacing a working installation.
2. Install current **Visual Studio Code for Windows** and the **WSL** extension. Open Ubuntu from Windows Terminal; run `code .` from the Linux project directory to open it in WSL mode.
3. Obtain access to the project repository. GitHub authentication is only needed
   if the repository is private; it is not needed to run a local checkout.

## In Ubuntu/WSL shell

```bash
sudo apt update
sudo apt install -y git gh build-essential make pkg-config curl wget unzip jq python3 python3-venv gforth
# Clone the authorized repository, then enter its directory.
bash scripts/check-env.sh
make smoke
```

The distro `gforth` apt package may be older than **Gforth 1.0.0**. It is suitable for the smoke check only. The observed 1.0 build, its dependencies, hash and unresolved installation issues are recorded in `docs/INSTALLATION_LOG.md`. A clean, reproducible 1.0 installer is still a project task; do not treat those machine-specific notes as a tested installer. Do not rely on newly added Gforth 1.0 extensions in portable kernel modules.

Install a supported **Node.js LTS and npm** in Ubuntu (Codex should validate required Node version against current official CLI docs). Then:

```bash
npm install -g @openai/codex@latest
codex --version
codex
```

Sign in to Codex with the ChatGPT account when prompted. Alternatively install Codex in the VS Code WSL context and use the IDE extension. Official overview: https://help.openai.com/en/articles/11369540-using-codex-with-your-chatgpt-plan.

GitHub CLI authentication is interactive and needs user authorization:

```bash
gh auth login
# after user review and permission:
git init -b main
# stage/commit after inspection of files and gitignore
gh repo create leanforth --private --source=. --remote=origin --push
```

**Do not run `gh repo create` until the user has authorized the target GitHub account, repo name, visibility and first push.** Check whether a `leanforth` repository name is available in the user's namespace; choose a different name if necessary. `gh auth login` should open the supported browser flow. GitHub connection to ChatGPT is separate and optional.

Install and pin Lean via official **elan** instructions (https://lean-lang.org/lean4/doc/setup.html or current Lean installation guide). The first oracle target is **Lean 4.35.0**, not moving `stable` or the 4.36 prerelease; keep version and export format lockfiles under version control. Use Linux `bubblewrap` (`bwrap`) if supported by the local WSL kernel to exercise `lake check --paranoid`. Test sandboxing explicitly; do not disable it to claim a secure check.

The setup process should first emit a version manifest and exact instructions for any unavailable component; do not proceed by claiming unexecuted tests passed.

## How to start Codex

Inside `~/src/LeanForth`:

```bash
code .                  # optional VS Code + WSL
codex                   # terminal coding agent
```

Paste the full text from `prompts/FIRST_CODEX_TASK.md` as the first task. This file supplies enough context that transferring the ChatGPT conversation history is unnecessary.

Sources: https://learn.microsoft.com/en-us/windows/wsl/setup/environment , https://learn.microsoft.com/en-us/windows/wsl/tutorials/wsl-vscode , https://docs.github.com/en/github-cli/github-cli/quickstart , https://gforth.org/ , https://help.openai.com/en/articles/11369540-using-codex-with-your-chatgpt-plan.
