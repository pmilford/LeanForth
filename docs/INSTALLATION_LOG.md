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
- `ELAN_HOME="$PWD/.tools/elan" make reference-export LEAN="$PWD/.tools/elan/bin/lean"`
  rebuilt the composition theorem and matched its bundled `leanexport` 3.1.0
  output with `tests/reference/composition.ndjson` (SHA-256
  `7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec`).
  The fixture was not independently checked. `lake help check` states that its
  normal checking mode requires `bwrap`, which is missing on this host; sandbox
  checks have not been bypassed.
- The reference suite additionally checks concrete universe classification,
  beta conversion and rejection of an incorrect clamp example. Command:
  `ELAN_HOME="$PWD/.tools/elan" make reference LEAN="$PWD/.tools/elan/bin/lean"`.
- `tests/reference/core-oracle.lean` constructs Lean core expressions directly
  and calls `Lean.Kernel.check` and `Lean.Kernel.isDefEq` on identity, wrong
  binder, invalid application, loose variable, sorts and beta conversion. The
  reference and export scripts require the exact pinned Lean revision. These
  oracle cases do not yet compare against a LeanForth implementation.
- Extended `tests/reference/core-oracle.lean` with direct kernel examples for
  impredicative and data Pi universes, beta substitution below a binder,
  function eta, proof irrelevance, and variables outside binder scope. The
  pinned Lean kernel accepted and rejected the cases as specified. These are
  oracle cases only and include features outside the proposed first fragment.
- `tests/reference/substitution-oracle.lean` checked pinned Lean expression
  operations on open terms, including cutoff handling, binder-domain traversal,
  capture avoidance and removal of an outer binder. These are not closed proof
  acceptance tests or LeanForth implementation tests.
- `tests/reference/transform-model.lean`, run through `make reference`,
  compared an untrusted Lean model of the draft shift and substitution rules
  with Lean 4.35.0 expression operations on 155 generated expressions: 2,480
  shift configurations and 8,525 instantiations. These finite tests do not
  prove the algorithm sound, cover Forth overflow, or constitute kernel review.
- `tests/reference/type-model.lean` ran with pinned Lean 4.35.0. For 105
  generated expressions, the untrusted model and Lean's kernel inferred
  definitionally equal types for 26 and both failed to produce types for 79;
  none was model-inconclusive in that corpus. Separate identity, composition,
  unsupported, resource and eta-incompleteness cases also passed. The model
  uses Lean's instantiation operation and is not a LeanForth proof checker.
- `make smoke test-harness test-core` passed locally with Gforth 1.0.0 after
  adding structural sort, variable, application, lambda and Pi storage tests.
  The structural tests do not check Lean typing or validate imported terms.
- Downloaded Ubuntu 24.04 packages `gforth`, `gforth-lib` and `gforth-common`
  version `0.7.3+dfsg-9build4.1` with `apt-get download` into `/tmp` and
  extracted them using `dpkg-deb -x` without installing. The older tester lacks
  `#ERRORS`; the test adapter uses `ERROR-XT` to throw on the first failure.
  `GFORTHPATH=.:/tmp/leanforth-gforth073/usr/share/gforth/0.7.3:/tmp/leanforth-gforth073/usr/lib/x86_64-linux-gnu/gforth/0.7.3 make smoke test-harness test-core GFORTH=/tmp/leanforth-gforth073/usr/bin/gforth-0.7.3`
  passed, including intentional assertion failures. CI has been updated to run
  these targets but the new workflow has not yet run remotely.
- `make test-program` passed on local Gforth 1.0.0 and on the extracted Ubuntu
  0.7.3 host. It checks sample cases and all 343 combinations of value and
  bounds from -3 through 3, including reversed bounds. It is not a proof.
- `ELAN_HOME="$PWD/.tools/elan" make test-program-differential LEAN="$PWD/.tools/elan/bin/lean"`
  compared 343 Lean and Gforth 1.0 clamp rows successfully. The same target
  passed on the extracted Gforth 0.7.3 host with `GFORTHPATH` and `GFORTH` as
  above. Running it with `GFORTH=false` exited nonzero, as expected. These are
  finite runtime comparisons and do not verify the host or implementation.
- `make test-core` passed on both local Gforth 1.0.0 and extracted Ubuntu Gforth
  0.7.3 after adding the untrusted scope traversal. Tests include invalid
  binders, deliberately corrupted nodes, forward/self references, and a shared
  DAG at its exact node-visit budget. This is not a Lean type checker.
- `ELAN_HOME="$PWD/.tools/elan" make test-scope-differential LEAN="$PWD/.tools/elan/bin/lean"`
  compared 64 structural cases to Lean's `Expr.hasLooseBVars` successfully
  using Gforth 1.0.0. The same comparison passed on extracted Ubuntu Gforth
  0.7.3 with the `GFORTHPATH` and `GFORTH` values above; `GFORTH=false` exited
  nonzero. These comparisons check scope only, not proof or type acceptance.
- `make test-core` passed on Gforth 1.0.0 and extracted Ubuntu Gforth 0.7.3
  after adding the experimental shift implementation and its negative/resource
  tests. `make test-shift-differential` with the pinned Lean toolchain compared
  80 shifts successfully on both hosts. This is finite differential evidence,
  not a proof or authorization for trusted kernel use.
- `make test-core` passed on both Gforth versions after adding experimental
  single-binder instantiation. `make test-shift-differential` and
  `make test-instantiate-differential` passed on both hosts against the pinned
  Lean revision, covering 80 and 25 cases respectively. Tests include resource
  exhaustion, malformed input and allocation-count rollback. No trusted
  substitution implementation or proof of correctness is claimed.
- `make test-core` passed on Gforth 1.0.0 and extracted Ubuntu Gforth 0.7.3
  after adding the untrusted weak-head beta prototype. Its basic cases and
  failure paths passed. The subsequent `make test-beta-differential` compared
  15 closed cases against pinned Lean's kernel weak-head normalization on both
  Gforth versions. A nonterminating untyped term exhausts the prototype's
  resources and restores the arena count in the regression suite.
- `make test-core` passed locally on Gforth 1.0.0 with the experimental
  comparison and its budget/rollback cases. `make test-compare-differential`
  passed on Gforth 1.0.0 and extracted Ubuntu Gforth 0.7.3 against pinned Lean
  on six closed cases, including a Lean-valid equality reported as unknown.
  This comparison is untrusted and is not a proof checker.
