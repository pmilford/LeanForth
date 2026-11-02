# LeanForth

**Status: bootstrap and design; no theorem checker or program verifier exists yet.**

See the [project progress report](docs/project/PROJECT_PROGRESS.md) for both product
tracks, importer limits, and a reproducible code inventory.
The [development roadmap](docs/project/DEVELOPMENT_ROADMAP.md) breaks each track into
ordered submilestones with dependencies and acceptance evidence.
New to Lean terminology? See [terms for new readers](docs/user/TERMS_FOR_NEW_READERS.md)
for plain-language explanations of levels, `Sort`, proofs and the kernel.
All documentation is indexed in [docs/README.md](docs/README.md), grouped
into user, programming, development, project, ADR and review folders.

LeanForth is a Forth-friendly mathematical theorem-proving **and verified-programming** system, with an independently trustworthy checker and efficient executable Forth backends. Its mathematical data and presentation notation must never redefine or ambiguously overload the Forth source grammar.

Start with **[docs/project/CODEX_HANDOFF.md](docs/project/CODEX_HANDOFF.md)** (the original project brief), then **[docs/project/IMPLEMENTATION_PLAN.md](docs/project/IMPLEMENTATION_PLAN.md)** and **[AGENTS.md](AGENTS.md)**. Coding agents follow `AGENTS.md`: Codex reads it directly, and Claude Code loads it through `.claude/CLAUDE.md`. Work up to the `pre-claude` tag was developed with Codex. Follow **[docs/user/SETUP_WSL.md](docs/user/SETUP_WSL.md)** for the recommended Windows/WSL2 setup.

Proposed baseline: Windows 11 desktop; WSL2 Ubuntu development; Gforth 1.0 (reference implementation); Forth-2012 subset for portability; Lean 4.35.0 pinned as interoperability oracle; GitHub; Codex or Claude Code. CPU tensors first, using high-performance C/BLAS libraries behind a portable FFI; optional ArrayFire/GPU after measured need.

## Where the code is

There is **no checker or command-line tool yet**. `src/main.fs` loads every
current module in dependency order (`gforth src/main.fs`); what it loads are
untrusted building blocks, exercised by the tests. Each test file loads the
modules it needs with `include`. [`src/README.md`](src/README.md) gives the
layout rules.

| Path | Contents |
| --- | --- |
| `src/main.fs` | The loader for all current code; later the command-line entry point. |
| `src/lib/` | General Forth tools with no Lean knowledge (result codes, records, stores, portability). Created as the refactor extracts them. |
| `src/core/` | The functional logic, current path, 23 untrusted modules: the term store (`terms.fs`), names, universe levels, sessions and stale-handle checks, constant references, and the `mixed-*` substitution, reduction, comparison, conversion, signature and inference passes. |
| `src/kernel/` | The trusted checker. Empty until code passes the review gate in `AGENTS.md`. |
| `src/import/` | Staging of decoded Lean exports into the term store. |
| `src/program/` | The program track: six executable example words (clamp, checked add, abs, factorial, gcd, in-range) and a stack-depth analyzer. |
| `src/legacy/` | 28 superseded earlier variants (plain and `tagged-*` passes, probes, `arena.fs`), kept only while tests use them; not loaded by `main.fs`. |
| `tests/` | Forth unit tests (`core/`, `program/`), Python tools that decode Lean exports for tests (`support/`), and Lean reference files (`reference/`). |
| `scripts/` | Install scripts, documentation and Lean-source checks, Forth style metrics and profiling. |

[The Forth library inventory](docs/development/FORTH_LIBRARY.md) describes
each component, its maturity and what is still missing.

## Installing the pinned tools and running the tests

The Forth modules and tests exercise the host; they do not prove theorems or
verify programs. Install the pinned toolchains into the ignored `.tools/`
directory (each script checks the download's SHA-256 and fails otherwise):

```bash
sudo apt-get install -y m4 libtool-bin libffi-dev libltdl-dev pkg-config zstd
scripts/install-gforth.sh .tools/gforth
scripts/install-lean.sh .tools/elan/toolchains/leanprover--lean4---v4.35.0
```

An existing elan installation under `.tools/elan`, as described in
[the installation log](docs/development/INSTALLATION_LOG.md), works too. Then, from the
repository root:

```bash
make test    # Forth and Python tests; needs only Gforth and Python 3
make check   # make test plus every pinned-Lean oracle and differential test
```

The Makefile uses `.tools/gforth/bin/gforth` and the Lean 4.35.0 toolchain
binary under `.tools/elan` when present, otherwise `gforth` and `lean` on PATH;
override with `GFORTH=...` or `LEAN=...`. It calls the toolchain binary
directly, so no `ELAN_HOME` is needed. Individual targets such as
`make reference` or `make test-scope-differential` can also be run on their
own; `make check` lists them all in `DIFFERENTIAL_TARGETS`. A missing or
failing tool makes the command fail.

`make test-program` includes clamp and [five additional executable Forth
examples](docs/programming/PROGRAM_EXAMPLES.md). They are runtime tested, not verified.

These tests exercise Lean and untrusted Forth experiments; they do not test a
LeanForth theorem-checking kernel. The draft
[core ADR](docs/adr/0001-core-fragment.md) and [program example](docs/programming/PROGRAM_EXAMPLE.md)
require human review before implementation.
The export check recompiles the composition theorem, uses the `leanexport`
bundled with Lean 4.35.0, and compares its output byte-for-byte with the checked-in
NDJSON fixture. It is not an independent proof check or an importer test.
See [starting the kernel](docs/development/KERNEL_START.md) for the remaining prerequisites.

`make test-harness` evaluates Gforth's bundled test harness with a passing
test and intentional wrong-value and wrong-stack-depth failures. It currently
requires a Gforth installation containing `test/ttester.fs`; it has been tested
locally with Gforth 1.0 and Ubuntu's Gforth 0.7.3. See
[the testing strategy](docs/development/TESTING_STRATEGY.md).
`make test-core` tests experimental term storage, structural scope and partial
type inference. These untrusted prototypes cannot authorize a theorem; inferred
indices are mutable data, not checked theorem handles. Their limits are in
[the prototype notes](docs/development/ARENA_PROTOTYPE.md).
The tagged symbolic inference and shifting experiments are likewise untrusted;
application inference currently uses conservative beta-aware type comparison,
so many valid Lean terms remain unsupported.
`make test-tagged-infer-differential` checks selected shared universe expectations
with pinned Lean, not the full Lean checker corpus.
`make test-tagged-binder-differential` compares selected actual inferred types
and unbound-variable rejections against pinned Lean at three universe instances.
`make test-tagged-application-differential` compares selected valid and invalid
applications in the same finite setting.
`make test-tagged-convert-differential` compares six conversion cases with Lean.
`make test-tagged-universe-differential` compares selected symbolic universe
conversions, including an equivalence the current implementation leaves unknown.
`make test-composition-fixture` compares a manually built Forth DAG with 21
expression records in a pinned Lean export. It uses Python 3 for this test-only
inspection and stages the decoded nodes in Forth through a test-only data stream;
it also exercises an experimental declaration probe on the staged nodes. It is not a
general importer or proof checker.
The development-only [NDJSON preview](docs/development/NDJSON_PREVIEW.md) decodes a bounded
subset and reports unsupported records explicitly; its output is unchecked.
A test-only bridge stages one Lean polymorphic identity export with its symbolic
universe and runs an untrusted type/value diagnostic; it cannot register a theorem.
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
The stack-model differential also compares 686 executions against a Lean-proved
finite stack-machine model; the handwritten model and host remain separate
assumptions, as described in [the program example](docs/programming/PROGRAM_EXAMPLE.md).

GitHub CI (`.github/workflows/ci.yml`) has two jobs: `make test` on Ubuntu's
distribution Gforth package as a portability check, and `make check` on the
pinned Gforth 1.0.0 and Lean 4.35.0 toolchains, which also runs every Lean
comparison. See [project progress](docs/project/PROJECT_PROGRESS.md) for recent run
results.
The project code is MIT licensed; Gforth is a separately licensed dependency.
