# LeanForth

**LeanForth today is only the checking half of Lean (the kernel): it re-checks proof terms that Lean produced and exported (NDJSON), including all of Lean's `Init`. It has none of Lean's front end, the larger half: no elaborator (implicit arguments, numerals, unification), no type classes or coercions, no tactics, no pattern matching or recursion compilation, no evaluation. So it cannot yet turn a written theorem into a proof; Lean does all of that before the export. Since 2026-11-12, `leanforth check [--env EXPORT] FILE.lf` also checks LeanForth text whose proofs are written by hand as kernel proof terms (plan 8.2.1a, c, d; the owner's gates pending). There is no program verifier. The front end is plan phase 8 ([docs/project/PLAN_DRAFT.md](docs/project/PLAN_DRAFT.md)), being re-planned from 2026-11-12.**

See the [project progress report](docs/project/PROJECT_PROGRESS.md) for both product
tracks, importer limits, and a reproducible code inventory.
The [development roadmap](docs/project/DEVELOPMENT_ROADMAP.md) breaks each track into
ordered submilestones with dependencies and acceptance evidence.
New here? The [user guide](docs/user/USER_GUIDE.md) says what LeanForth is
and is not, where the trust boundaries are and what to read next;
[concepts in three forms](docs/user/CONCEPTS.md) explains levels, `Sort`,
terms, theorems and the kernel with examples in mathematics, Forth and Lean,
and [terms for new readers](docs/user/TERMS_FOR_NEW_READERS.md) is a short
glossary.
All documentation is indexed in [docs/README.md](docs/README.md), grouped
into user, programming, development, project, ADR and review folders.

LeanForth is a Forth-friendly mathematical theorem-proving **and verified-programming** system, with an independently trustworthy checker and efficient executable Forth backends. Its mathematical data and presentation notation must never redefine or ambiguously overload the Forth source grammar.

Start with **[docs/project/CODEX_HANDOFF.md](docs/project/CODEX_HANDOFF.md)** (the original project brief), then **[docs/project/IMPLEMENTATION_PLAN.md](docs/project/IMPLEMENTATION_PLAN.md)** and **[AGENTS.md](AGENTS.md)**. Coding agents follow `AGENTS.md`: Codex reads it directly, and Claude Code loads it through `.claude/CLAUDE.md`. Work up to the `pre-claude` tag was developed with Codex. Follow **[docs/user/SETUP_WSL.md](docs/user/SETUP_WSL.md)** for the recommended Windows/WSL2 setup.

Proposed baseline: Windows 11 desktop; WSL2 Ubuntu development; Gforth 1.0 (reference implementation); Forth-2012 subset for portability; Lean 4.35.0 pinned as interoperability oracle; GitHub; Codex or Claude Code. CPU tensors first, using high-performance C/BLAS libraries behind a portable FFI; optional ArrayFire/GPU after measured need.

## Where the code is

The first checker is not through its review gate; `bin/leanforth check
FILE.ndjson` runs it on a Lean export of any size (all of Lean's `Init`)
and prints each declaration's verdict, with its axioms when accepted,
then a summary, with `--resources`
the time, memory and fuel used, and with `--json` all of it as JSON
([the command line](docs/user/COMMAND_LINE.md)). `src/main.fs` loads all
current code (`gforth src/main.fs`) by requiring the top modules; every
module and every test `require`s exactly the modules whose words it uses.
What it loads is unverified code in progress, exercised by the tests.
[`src/README.md`](src/README.md) gives the layout rules and the
[architecture page](docs/development/ARCHITECTURE.md) draws them.

| Path | Contents |
| --- | --- |
| `bin/leanforth` | The command line, version 0: `check` (with `--record`), `print`, `replay`, `count`, `reexport`, `version`, `capabilities`; exit statuses 0–6, 6 (NOT PROVED) only with `--strict-axioms`; `gforth-fast` is already the default engine (`--fast` is accepted and changes nothing). `check [--env EXPORT | --snapshot FILE] FILE.lf` checks LeanForth text, against a library export of Lean's such as `Init` ([manual](docs/user/COMMAND_LINE.md#checking-leanforth-text)). |
| `src/main.fs` | The loader for all current code, and the command line's Forth entry point (`src/cli/`). |
| `src/lib/` | General Forth tools with no Lean knowledge: bounded stores, tagged nodes, the shared outcome vocabulary, walk and frames records, per-task contexts, a worker pool, a line reader with UTF-8 checks and a JSON reader. |
| `src/core/` | Lean's data model, 10 modules: the term store (`terms.fs`), names, universe levels, sessions and stale-handle checks, constant references. |
| `src/kernel/` | The proof checker under development, 14 modules: universe substitution and comparison, signatures, and the `mixed-*` substitution, reduction, comparison, conversion and inference passes. Not verified until the owner declares it so after the review gate in `AGENTS.md`. |
| `src/import/` | The Forth reader of Lean's NDJSON exports (it decodes all of the pinned Mathlib export), its manifest check, a record-counting tool, the byte-exact re-exporter, and staging of a small export into the checker's input. |
| `src/program/` | The program track: six executable example words (clamp, checked add, abs, factorial, gcd, in-range), a stack-depth analyzer and the reader from Forth source to the program IR. |
| `src/present/` | The term printer: Lean notation, ASCII and LaTeX. Presentation only; the checker never loads it. |
| `tests/` | Forth unit tests (`lib/`, `core/`, `program/`, `present/`), Python tools that decode Lean exports for tests (`support/`), and Lean reference files (`reference/`). |
| `schemas/` | JSON Schema of the program receipt, version 0.1. |
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
`make reference` or `make test-constant-term-scope-differential` can also be
run on their own; `make check` runs every one listed in `DIFFERENTIAL_TARGETS`.
A missing or failing tool makes the command fail. Make runs 8 targets at a
time (`JOBS=1` for one at a time) and replays pinned Lean's runs on unchanged
inputs from a local cache (`LEAN_CACHE=0` runs Lean every time, as CI does);
the [testing strategy](docs/development/TESTING_STRATEGY.md#running-the-suites-parallel-jobs-and-the-lean-cache)
explains both.
[Running the checks](docs/user/RUNNING_THE_CHECKS.md) says what each target
shows and what it does not.

`make test-program` includes clamp and [five additional executable Forth
examples](docs/programming/PROGRAM_EXAMPLES.md). They are runtime tested, not verified.

These tests run the checker on Lean's exports and compare it with
pinned Lean; they do not show that it is correct. The checker re-checks proofs that Lean exported; LeanForth text
is checked by the same checker since 2026-11-12 (8.2.1a, c, d); 8.2.1b, e, f and g are not started. The
[core ADR](docs/adr/0001-core-fragment.md) and [program example](docs/programming/PROGRAM_EXAMPLE.md)
needed human review before implementation.
The export check recompiles the composition theorem, uses the `leanexport`
bundled with Lean 4.35.0, and compares its output byte-for-byte with the checked-in
NDJSON fixture. It is not an independent proof check or an importer test.
See [starting the kernel](docs/development/KERNEL_START.md) for the remaining prerequisites.

`make test-harness` evaluates Gforth's bundled test harness with a passing
test and intentional wrong-value and wrong-stack-depth failures. It currently
requires a Gforth installation containing `test/ttester.fs`; it has been tested
locally with Gforth 1.0 and Ubuntu's Gforth 0.7.3. See
[the testing strategy](docs/development/TESTING_STRATEGY.md).
`make test-core` tests experimental term storage, structural scope, and the
`mixed-*` substitution, reduction, conversion and inference passes with the
definition probe built on them. These untrusted prototypes cannot authorize a
theorem; inferred types are mutable data, not checked theorem handles. Their
limits are in [the prototype notes](docs/development/ARENA_PROTOTYPE.md).
Application inference uses conservative beta-aware type comparison, so many
valid Lean terms remain unsupported. The earlier plain and `tagged-*` variants
of these passes and their tests were retired on 2026-11-02, once the current
code had at least the same test coverage.
The composition fixture test compares a manually built Forth DAG with 21
expression records in a pinned Lean export. It uses Python 3 for this test-only
inspection and stages the decoded nodes in Forth through a test-only data
stream. It is not a general importer or proof checker.
The development-only [NDJSON preview](docs/development/NDJSON_PREVIEW.md) decodes a bounded
subset and reports unsupported records explicitly; its output is unchecked.
A test-only bridge stages four pinned Lean exports (identity, composition,
type identity and the universe-polymorphic identity) with symbolic universes
and runs the untrusted definition probe on each type/value pair; it cannot
register a theorem.
Besides the original `mixed-*` comparisons, `make check` runs the ports of the
retired comparisons, which compare the current passes with pinned Lean on
small finite tables: binder scope (64 cases, against
Lean's loose-variable analysis), shift (80), instantiation (25), weak-head
beta (15), conversion (15), inference (52), the definition probe (9),
universe substitution (48), constant specialization and inference (96), and
the polymorphic identity export (4 signatures, 8 definitions). The
[testing strategy](docs/development/TESTING_STRATEGY.md) lists each target.
Two Lean-valid cases are knowingly answered unknown. None of these targets
establishes proof-checker correctness or theorem validity.
`make test-program` tests a host Forth clamp against sample cases and a small
finite input domain; it is not a proof of the program or its runtime.
The differential target additionally compares 686 small-domain and signed
32-bit boundary triples against the Lean integer model; it does not establish
Forth program correctness or execution on a 32-bit host.
The stack-model differential also compares 686 executions against a Lean-proved
finite stack-machine model; the handwritten model and host remain separate
assumptions, as described in [the program example](docs/programming/PROGRAM_EXAMPLE.md).

GitHub CI (`.github/workflows/ci.yml`) is switched off at the owner's request
(2026-11-11). Its two jobs are run locally before every push: `make test` on Gforth
0.7.3 as a portability check, and `make check` on the pinned Gforth 1.0.0 and
Lean 4.35.0, which also runs every Lean comparison. See
[project progress](docs/project/PROJECT_PROGRESS.md) for the recorded results.
The project code is MIT licensed; Gforth is a separately licensed dependency.
