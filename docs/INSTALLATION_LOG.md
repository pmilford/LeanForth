# Installation and reproducibility log

Improve the installation experience for other users: develop a documented,
repeatable setup with pinned artifacts, verified checksums, minimal dependencies,
and clear diagnostics. Validate it on a clean Ubuntu/WSL environment before
claiming it works for others. Do not require GitHub authentication for local use.

## Initial setup: 2026-10-30

- Host: Ubuntu 24.04.4 LTS on x86-64 WSL2; inventory: `bash scripts/check-env.sh`.
- Existing tools: Git 2.43.0, gh 2.45.0, GCC 13.3.0, Python 3.13.2, Node 24.12.0, npm 11.6.2, Codex 0.166.0.
- User installed `m4 libtool-bin libffi-dev libltdl-dev pkg-config` with `sudo apt-get install -y` after the first Gforth build reported missing `m4`. Full clean-machine prerequisites remain to be established.
- Gforth source: `https://net2o.de/gforth-dist/Snapshots/1.0.0/gforth-1.0.0.tar.xz`; observed SHA-256 `79c880b68a4a9aa817b7067c21b79acd5b07149fad78f3f630320db410886fa6`. This is an observed hash, not independently authenticated.
- Extracted under `/tmp`, configured with `./configure --prefix=/home/peter/code/LeanForth/.tools/gforth`, and built with `make -j4`. Initial sandboxed build could not write Gforth configuration; the unrestricted build passed its bundled checks. `make install` initially failed trying to install optional Emacs files under `/usr/share`; a subsequent local-prefix install succeeded, though its optional `/etc/emacs` installation and info registration reported errors. Emacs is not required. Review upstream install targets to omit optional editor integration on a clean installation.
- `.tools/gforth/bin/gforth --version` reports `gforth 1.0.0 amd64`. A simple arithmetic invocation succeeded outside the sandbox; within the sandbox startup failed while creating its libcc configuration directory. This does not validate FFI or the LeanForth project.
- Downloaded the official elan installer from `https://elan.lean-lang.org/elan-init.sh`; ran it with `ELAN_HOME=/home/peter/code/LeanForth/.tools/elan`, `-y --no-modify-path --default-toolchain leanprover/lean4:v4.35.0`. Running `ELAN_HOME=/home/peter/code/LeanForth/.tools/elan .tools/elan/bin/lean --version` downloaded and reported Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Local `.tools/` is ignored; paths above are machine-specific and need parameterizing in a future installer. No shell PATH was changed.
- GitHub CLI was reauthenticated; the private `pmilford/LeanForth` repository
  was created. The first push required refreshing the token's `workflow` scope;
  the subsequent push succeeded.
- Initialized the local repository with `git init -b main`. `make smoke` passed
  using the local Gforth outside the sandbox; `make smoke GFORTH=false` exited
  nonzero as expected. GitHub Actions Smoke run 41120284014 passed for initial
  commit `44ca571`; it warned about checkout v4's Node 20 deprecation. GNU Make
  version is 4.3.
- `ELAN_HOME="$PWD/.tools/elan" make reference LEAN="$PWD/.tools/elan/bin/lean"`
  passed the Lean 4.35.0 composition oracle: the valid example was accepted and
  the incompatible application rejected. This is not a LeanForth kernel test.
- `make test-harness` passed with the local Gforth 1.0.0: the passing fixture
  exited zero, while wrong-value and wrong-depth fixtures exited nonzero with
  their expected diagnostics. Other Gforth installations have not been tested.
- The same pinned Lean reference command also passed identity and binder cases
  and a separate Lean integer-clamp proof experiment. These do not check a
  LeanForth program or a LeanForth kernel.
