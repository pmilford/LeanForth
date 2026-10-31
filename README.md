# LeanForth — Codex starter handoff

**Status: bootstrap and design; no theorem checker or program verifier exists yet.**

LeanForth is a Forth-friendly mathematical theorem-proving **and verified-programming** system, with an independently trustworthy checker and efficient executable Forth backends. Its mathematical data and presentation notation must never redefine or ambiguously overload the Forth source grammar.

Start with **[docs/CODEX_HANDOFF.md](docs/CODEX_HANDOFF.md)**, then **[docs/IMPLEMENTATION_PLAN.md](docs/IMPLEMENTATION_PLAN.md)** and **[AGENTS.md](AGENTS.md)**. Launch the first Codex task from **[prompts/FIRST_CODEX_TASK.md](prompts/FIRST_CODEX_TASK.md)**. Follow **[docs/SETUP_WSL.md](docs/SETUP_WSL.md)** for the recommended Windows/WSL2 setup.

Proposed baseline: Windows 11 desktop; WSL2 Ubuntu development; Gforth 1.0 (reference implementation); Forth-2012 subset for portability; Lean 4.35.0 pinned as interoperability oracle; GitHub; Codex CLI or VS Code extension. CPU tensors first, using high-performance C/BLAS libraries behind a portable FFI; optional ArrayFire/GPU after measured need.

The initial Forth module and `make smoke` exercise the host; they do not prove
theorems or verify programs. Run `make smoke` from the repository root; it
uses `.tools/gforth/bin/gforth` if present, otherwise `gforth` on PATH. Override
with `make smoke GFORTH=/path/to/gforth`. A missing or failing host makes the
command fail. Lean is pinned in `lean-toolchain`; local installation details
and remaining reproducibility work are in [the installation log](docs/INSTALLATION_LOG.md).

Run `make reference` with Lean 4.35.0 available on PATH to check the Lean
oracle's valid and invalid function and binder examples and its integer clamp
proof experiment. With this machine's local
elan installation, use:

```bash
ELAN_HOME="$PWD/.tools/elan" make reference LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make reference-export LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-scope-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-shift-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-instantiate-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-beta-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-compare-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-infer-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-declaration-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-level-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-level-assignment-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-level-compare-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-poly-specialization-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-program-differential LEAN="$PWD/.tools/elan/bin/lean"
```

These tests exercise Lean and untrusted Forth experiments; they do not test a
LeanForth theorem-checking kernel. The draft
[core ADR](docs/adr/0001-core-fragment.md) and [program example](docs/PROGRAM_EXAMPLE.md)
require human review before implementation.
The export check recompiles the composition theorem, uses the `leanexport`
bundled with Lean 4.35.0, and compares its output byte-for-byte with the checked-in
NDJSON fixture. It is not an independent proof check or an importer test.
See [starting the kernel](docs/KERNEL_START.md) for the remaining prerequisites.

`make test-harness` evaluates Gforth's bundled test harness with a passing
test and intentional wrong-value and wrong-stack-depth failures. It currently
requires a Gforth installation containing `test/ttester.fs`; it has been tested
locally with Gforth 1.0 and Ubuntu's Gforth 0.7.3. See
[the testing strategy](docs/TESTING_STRATEGY.md).
`make test-core` tests experimental term storage, structural scope and partial
type inference. These untrusted prototypes cannot authorize a theorem; inferred
indices are mutable data, not checked theorem handles. Their limits are in
[the prototype notes](docs/ARENA_PROTOTYPE.md).
`make test-composition-fixture` compares a manually built Forth DAG with 21
expression records in a pinned Lean export. It uses Python 3 for this test-only
inspection and stages the decoded nodes in Forth through a test-only data stream;
it also exercises an experimental declaration probe on the staged nodes. It is not a
general importer or proof checker.
The development-only [NDJSON preview](docs/NDJSON_PREVIEW.md) decodes a bounded
subset and reports unsupported records explicitly; its output is unchecked.
The scope differential target compares 64 bounded expression shapes with Lean's
loose-variable analysis; it does not compare type checking or theorem validity.
The shift differential target compares an untrusted Forth shift experiment with
Lean on 80 cases; neither target establishes proof-checker correctness.
The instantiation differential target compares an untrusted substitution
experiment with Lean on 25 cases; it likewise establishes no theorem validity.
The beta differential target compares untrusted weak-head reduction with the
Lean kernel on 15 closed cases, without verifying the implementation.
The comparison differential target checks six closed cases and preserves an
explicit unknown result for a Lean equality outside its conservative fragment.
The inference differential target compares seven inferred types with Lean and
checks that six Lean-rejected inputs do not succeed in the Forth experiment.
The declaration differential target compares five manually constructed cases:
one success, three Lean rejections, and one Lean-valid declaration reported
unknown by the Forth probe because binder-domain conversion is incomplete.
`make test-program` tests a host Forth clamp against sample cases and a small
finite input domain; it is not a proof of the program or its runtime.
The differential target additionally compares 686 small-domain and signed
32-bit boundary triples against the Lean integer model; it does not establish
Forth program correctness or execution on a 32-bit host.

GitHub CI passed for the initial commit. The updated Ubuntu job uses the
distribution Gforth package for smoke, harness, core and program tests; this updated job
has not yet run remotely. Pinned Gforth 1.0 CI remains to be set up.
The project code is MIT licensed; Gforth is a separately licensed dependency.
