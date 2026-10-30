# Observed versions

Inventory taken 2026-10-30 on Ubuntu 24.04.4 WSL2 x86-64; details and setup
commands are in `docs/INSTALLATION_LOG.md`.

- Gforth 1.0.0 amd64, locally built; basic invocation tested.
- Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb.
- Git 2.43.0; GitHub CLI 2.45.0; GCC 13.3.0; Python 3.13.2.
- Node 24.12.0; npm 11.6.2; Codex 0.166.0.
- `bwrap` not found; Lean sandbox and external checker have not been tested.
- GitHub Actions Smoke run 41120284014 passed on 2026-10-30 for commit
  `44ca571`. It uses Ubuntu's Gforth package, not the pinned local Gforth
  1.0.0 build. GitHub warned that checkout v4 targets deprecated Node 20.
