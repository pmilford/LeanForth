# LeanForth

LeanForth is a checker for Lean 4 proofs, written in Forth (developed on Gforth 1.0), that gives Lean 4.35.0's verdicts. A second product path, verified executable Forth programs, is started.

## What it does today

- **Re-checks Lean's exports.** `bin/leanforth check` reads a Lean 4.35.0 export (NDJSON) and checks each declaration with LeanForth's own kernel. It has accepted all of Lean's `Init`, and on build `d789e45f` (2026-11-13, the latest run [the progress page](docs/project/PROJECT_PROGRESS.md) records) all of Mathlib's export (729,263 of 729,263 declarations); later builds have not been run on all of Mathlib. The kernel has not yet passed its human review gate (`AGENTS.md`).
- **Checks theorems written in LeanForth.** LeanForth's own elaborator turns LeanForth text into kernel terms, and the kernel checks them as it checks an export. Slice S1 is done ([done check](docs/development/done-checks/2026-11-14-s1.md)): `theorem t 0 0 + 0 = := by by-rfl end t` is elaborated and accepted on all of `Init`. Slice S2 is done ([done check](docs/development/done-checks/2026-11-19-s2-done.md)): proofs by induction and rewriting, such as `tests/front/01-zero-add-rw.lf` (0 + n = n) and the proof set `tests/front/ps-*.lf`, are accepted on all of `Init`. These tactic words are on `main` (`by-intro`, `by-intros`, `by-exact`, `by-apply`, `by-rfl`, `by-rw[ ]`, `by-induction-with`, `by-case:`, `by-assumption`, `by-constructor`, `by-left`, `by-right`, `by-exfalso`, `by-clear`, `by-decide`, `by-sorry`), each a port of Lean's tactic compared with pinned Lean. `by-decide` proves closed facts about numbers by computation ([done check](docs/development/done-checks/2026-11-19-s3a-done.md)): `6 7 * 42 =`, `3 3 * 4 4 * + 5 5 * =`. Two pages show what LeanForth does on each theorem, beside the same proof in Lean: [induction and rewriting](docs/user/examples/s2-showcase.txt) and [by-decide](docs/user/examples/decide-showcase.txt). Not yet written: most of Lean's tactics, pattern matching and recursion compilation, evaluation. See [the elaborator page](docs/user/ELABORATION.md).
- **Verified Forth programs (second path).** `bin/leanforth verify SOURCE.fs --contract CONTRACT` checks one Forth word against a contract: pinned Lean writes the proofs and LeanForth's checker re-checks them ([manual](docs/programming/PROGRAM_VERIFY.md)). Its first slice (V1) is on `main`; the later slices are parked.

Correctness is relative to stated semantics and assumptions; the elaborator, parsers, tactics and printers are untrusted and can never make a wrong proof accepted. Current state, both tracks and limits: [project progress](docs/project/PROJECT_PROGRESS.md) (its "Now, next, later" list is the queue).

## Install

Requirements: Linux x86-64 or WSL2 (see [the WSL setup](docs/user/SETUP_WSL.md)), Python 3, a C compiler, `make`, `curl`. The two scripts download pinned releases, check their SHA-256 and install into the git-ignored `.tools/`:

```bash
sudo apt-get install -y m4 libtool-bin libffi-dev libltdl-dev pkg-config zstd
scripts/install-gforth.sh .tools/gforth     # Gforth 1.0.0, built from source: .tools/gforth/bin/gforth
scripts/install-lean.sh .tools/elan/toolchains/leanprover--lean4---v4.35.0   # Lean 4.35.0 toolchain
```

The Makefile and `bin/leanforth` find these automatically (override with `GFORTH=...` and `LEAN=...`). Lean is needed only for `make check` and `verify`; checking exports needs only Gforth. An existing elan installation under `.tools/elan` also works ([installation log](docs/development/INSTALLATION_LOG.md)).

## Run

```bash
make test    # Forth and Python tests; needs only Gforth and Python 3 (4 min 42 s at JOBS=4 on a fresh clone, 2026-11-20)
make check   # make test plus every pinned-Lean comparison (about 11 min at JOBS=4)
```

`make check` compares the front end on a slice of Mathlib only where a Mathlib export is present (it is 6 GB and not in the repository); without one it prints `check_mathlib_slice: SKIPPED, NOT RUN` and goes on. Installing took 97 s for Gforth and 13 s for Lean on a fresh clone (2026-11-20); `.tools/` then holds 3 GB.

**Check a Lean export:** `bin/leanforth check FILE.ndjson` prints each declaration's verdict and a summary; see [the command line](docs/user/COMMAND_LINE.md) for options, exit statuses and how to export Init or Mathlib. `bin/leanforth help` lists every command.

**Check a LeanForth file** on the small library slices in the repository. S1, the statement above (run on 2026-11-15: exit 0, `t: accepted; axioms: none`, ending `548 declarations: 548 accepted`):

```bash
bin/leanforth check --env tests/front/s1-slice.ndjson --elab-data tests/front/s1-slice.elab.ndjson tests/front/s1-rfl.lf
```

S2, 0 + n = n by induction and rewriting (run on 2026-11-15: exit 0, `zero_add'': accepted; axioms: none`, ending `580 declarations: 580 accepted`):

```bash
bin/leanforth check --env tests/front/s2-slice.ndjson --elab-data tests/front/s2-slice.elab.ndjson tests/front/01-zero-add-rw.lf
```

`by-decide`, closed facts about numbers such as 6 * 7 = 42 and 3² + 4² = 5² (run on 2026-11-20 on a fresh clone: exit 0, each theorem `accepted; axioms: none`, ending `1273 declarations: 1273 accepted`, 5 s):

```bash
bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson tests/front/tactics/decide/dc-ops.lf
```

The output first lists the slice's library declarations, then yours. A `sorryAx` line in the S2 slice's list is part of the library and is marked NOT PROVED, as the summary says.

## Where to go next

- [docs/README.md](docs/README.md): every document, by folder and audience.
- [User guide](docs/user/USER_GUIDE.md), [concepts in three forms](docs/user/CONCEPTS.md), [terms for new readers](docs/user/TERMS_FOR_NEW_READERS.md), [the elaborator](docs/user/ELABORATION.md), [the LeanForth syntax](docs/user/LEANFORTH_SYNTAX.md).
- [Demos](docs/user/DEMOS.md) and [running the checks](docs/user/RUNNING_THE_CHECKS.md).
- [Project progress](docs/project/PROJECT_PROGRESS.md), [roadmap](docs/project/DEVELOPMENT_ROADMAP.md), [implementation plan](docs/project/IMPLEMENTATION_PLAN.md).
- Coding agents follow [AGENTS.md](AGENTS.md) (Codex reads it directly, Claude Code through `.claude/CLAUDE.md`). Work up to the `pre-claude` tag was developed with Codex.

## Where the code is

`bin/leanforth check
FILE.ndjson` runs the checker on a Lean export of any size
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


## Testing notes

The Makefile uses `.tools/gforth/bin/gforth` and the Lean 4.35.0 toolchain
binary under `.tools/elan` when present, otherwise `gforth` and `lean` on PATH;
override with `GFORTH=...` or `LEAN=...`. It calls the toolchain binary
directly, so no `ELAN_HOME` is needed. A Lean is taken only from a
toolchain's own folder (its real path `.../toolchains/NAME/bin/lean`, with
`NAME/lib/lean` beside it) and never when it is elan or a copy of it:
`scripts/lean_pin.py check LEAN` judges it before anything runs it, since
an elan proxy run without `ELAN_HOME` downloads a 3 GB toolchain.
Individual targets such as
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

`make test-harness` evaluates Gforth's bundled test harness with a passing
test and intentional wrong-value and wrong-stack-depth failures. It currently
requires a Gforth installation containing `test/ttester.fs`; it has been tested
locally with Gforth 1.0 and Ubuntu's Gforth 0.7.3. See
[the testing strategy](docs/development/TESTING_STRATEGY.md).
`make test-core` tests term storage, structural scope, and the
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
