# LeanForth

LeanForth is a checker for Lean 4 proofs, written in Forth (developed on Gforth 1.0). It has its own kernel, which gives Lean 4.35.0's verdicts, and its own front end, in which theorems and proofs are written as Forth words. A second product path, verified executable Forth programs, is started.

This is early work. The kernel has not yet passed its human review gate (`AGENTS.md`), and only a small part of Lean's tactics exists. What is listed below as done has been checked by an independent done check that ran the command a user runs; each is linked.

## A first look

A theorem and its proof, written in LeanForth. The text is postfix, as in Forth: the operands first, then the operation.

```
theorem pythag
  3 3 * 4 4 * + 5 5 * =
:= by
  by-decide
end pythag
```

In Lean this is `theorem pythag : 3 * 3 + 4 * 4 = 5 * 5 := by decide`. LeanForth reads the statement, its tactic `by-decide` works it out by computation and builds a proof term, and LeanForth's kernel checks that term. A false statement is refused with Lean's own message: for `6 7 * 43 =`, "Tactic `decide` proved that the proposition 6 * 7 = 43 is false".

Two pages show, theorem by theorem, the LeanForth text, the same proof in Lean, what LeanForth did and the kernel's verdict:

- [by-decide](docs/user/examples/decide-showcase.txt): 23 closed facts about numbers, written with Lean's symbols, typed in ASCII, and with powers (Euler's factor of the fifth Fermat number, `2 32 ^ 1 +  641 6700417 * =`).
- [induction and rewriting](docs/user/examples/s2-showcase.txt): 15 theorems such as 0 + n = n and the commutativity of addition, each tactic step with its goals.

## What it does today

- **Re-checks Lean's exports.** `bin/leanforth check FILE.ndjson` reads a Lean 4.35.0 export and checks each declaration with LeanForth's own kernel. It accepts all of Lean's `Init` (59,349 declarations; run every night, in parallel about five times faster on eight jobs than on one). It accepts all of Mathlib's export, 729,263 of 729,263 declarations: last run on 2026-11-20 on build `677800d7`, the tree tagged `svfig-prepre-alpha` (2 hours 3 minutes with eight jobs, 22.2 GB at its peak; [the progress page](docs/project/PROJECT_PROGRESS.md) has the record). That sentence was added one commit after the tag; builds after `677800d7` have not been run on all of Mathlib. The same day it accepted all 129,845 declarations of OpenAI's Lean formalization of finite-time blowup for the Navier–Stokes and Euler equations (51 minutes). [One page](docs/user/examples/large-runs.txt) follows a proof from the idea to LeanForth's verdict in eight steps and gives the size and time of every step for both runs.
- **Checks theorems written in LeanForth.** LeanForth's own elaborator turns LeanForth text into kernel terms, and the kernel checks them as it checks an export. Done, each with its done check:
  - statements and `by-rfl` on all of `Init` ([S1](docs/development/done-checks/2026-11-14-s1.md));
  - proofs by induction and rewriting ([S2](docs/development/done-checks/2026-11-19-s2-done.md));
  - `by-decide` on closed facts about natural numbers and truth values ([S3a](docs/development/done-checks/2026-11-19-s3a-done.md), [operators](docs/development/done-checks/2026-11-20-ops-c1-done.md));
  - Lean's symbols as words, each also in a spelling a plain keyboard can type ([symbols](docs/development/done-checks/2026-11-20-ops-symbols-done.md)), and the word `divides` ([divides](docs/development/done-checks/2026-11-20-divides-done.md)).

  The tactic words on `main`: `by-intro`, `by-intros`, `by-exact`, `by-apply`, `by-rfl`, `by-rw[ ]`, `by-induction-with`, `by-case:`, `by-assumption`, `by-constructor`, `by-left`, `by-right`, `by-exfalso`, `by-clear`, `by-decide`, `by-sorry`. Each is a port of Lean's tactic, and its results are compared with Lean 4.35.0's, term by term, on true theorems and on deliberately wrong ones. [The language reference](docs/user/LANGUAGE_REFERENCE.md) describes every word.
- **Verified Forth programs (second path).** `bin/leanforth verify SOURCE.fs --contract CONTRACT` checks one Forth word against a contract: pinned Lean writes the proofs and LeanForth's checker re-checks them ([manual](docs/programming/PROGRAM_VERIFY.md)). Its first slice is on `main`; the later slices are parked.

The symbols a statement may use, and how to type them:

| Written | Typed | Meaning |
| --- | --- | --- |
| `+ - * / % ^` | as written | `a + b`, `a - b`, `a * b`, `a / b`, `a % b`, `a ^ b` |
| `= < >` | as written | `a = b`, `a < b`, `a > b` |
| `≤` `≥` | `<=` `>=` | `a ≤ b`, `a ≥ b` |
| `≠` | `Ne` | `a ≠ b` |
| `∧` `∨` `↔` | `/\` `\/` `<->` | `p ∧ q`, `p ∨ q`, `p ↔ q` |
| `¬` | `Not` | `¬ p` |
| `divides` | as written (or Lean's name `Dvd.dvd`) | "a divides b": b is a whole multiple of a. A statement, not the division `/`. Lean writes it with a sign that looks like the case bar; in LeanForth you type the word |

LeanForth prints goals in Lean's notation, where "divides" is a bar between two values, as in `⊢ 3 ∣ 12`. A bar at the start of a line of a proof, as in `| zero => by-rfl`, starts a case of an induction. The two bars are different characters that look the same; tell them by where they stand, and write divisibility with the word `divides` ([the language reference](docs/user/LANGUAGE_REFERENCE.md), "Divides and the case bar").

Correctness is relative to stated semantics and assumptions. The elaborator, parsers, tactics and printers are untrusted: whatever they build, the kernel checks, so they cannot make a wrong proof accepted. They can, if they have a fault, build a different statement than the text says; that is what the comparisons with Lean guard against.

## What is not there yet

- Most of Lean's tactics (`simp`, `omega`, `cases` and many more), pattern matching, structural recursion, and evaluation.
- In statements: implication (`->`), quantifiers and lambda in natural form, a minus sign in front of a number, numerals of more than nine digits.
- `by-decide` on statements with variables, on divisibility (`divides`), and with exponents above 256.
- The kernel's human review, and an outside audit.

Current state, both tracks and limits: [project progress](docs/project/PROJECT_PROGRESS.md) (its "Now, next, later" list is the queue).

## Install

Requirements: Linux x86-64 or WSL2 (see [the WSL setup](docs/user/SETUP_WSL.md)), Python 3, a C compiler, `make`, `curl`. The two scripts download pinned releases, check their SHA-256 and install into the git-ignored `.tools/`:

```bash
sudo apt-get install -y m4 libtool-bin libffi-dev libltdl-dev pkg-config zstd
scripts/install-gforth.sh .tools/gforth     # Gforth 1.0.0, built from source: .tools/gforth/bin/gforth
scripts/install-lean.sh .tools/elan/toolchains/leanprover--lean4---v4.35.0   # Lean 4.35.0 toolchain
```

Each script prints a few lines and ends with `install-gforth: OK: gforth 1.0.0 amd64 is installed at ...` or `install-lean: OK: Lean (version 4.35.0, ...) is installed at ...`; on a failure it says `FAILED while ...` and shows the end of its log. Gforth's own build output, several thousand lines with harmless warnings, goes to `.tools/gforth/install-gforth.log`. Run the three commands one at a time: `sudo` asks for a password and would swallow lines pasted after it.

The Makefile and `bin/leanforth` find these automatically (override with `GFORTH=...` and `LEAN=...`). Lean is needed only for `make check` and `verify`; checking exports needs only Gforth. An existing elan installation under `.tools/elan` also works ([installation log](docs/development/INSTALLATION_LOG.md)).

## Run

```bash
make test    # Forth and Python tests; needs only Gforth and Python 3 (4 min 42 s at JOBS=4 on a fresh clone, 2026-11-20)
make check   # make test plus every pinned-Lean comparison (about 11 min at JOBS=4)
```

**What you should see.** Both commands print thousands of lines. Many begin `error:`; those are the output of tests that feed LeanForth bad input on purpose and check that it refuses. What counts is the last line: `make test: PASSED. ...` or `make check: PASSED. ...`. After a failure there is no such line, and make's last lines name the failed target (`make: *** [Makefile:N: TARGET] Error ...`); `make -k test 2>&1 | grep '\*\*\*'` lists every failed target. On a machine with less than about 16 GB of memory or few cores add `JOBS=2`.

`make check` compares the front end on a slice of Mathlib only where a Mathlib export is present (it is 6 GB and not in the repository); without one it prints `check_mathlib_slice: SKIPPED, NOT RUN` and goes on. Installing took 97 s for Gforth and 13 s for Lean on a fresh clone (2026-11-20); `.tools/` then holds 3 GB.

**Check a Lean export:** `bin/leanforth check FILE.ndjson` prints each declaration's verdict and a summary; see [the command line](docs/user/COMMAND_LINE.md) for options, exit statuses and how to export Init or Mathlib. `bin/leanforth help` lists every command.

**Check a LeanForth file** on the small library slices in the repository. S1, 0 + 0 = 0 by `by-rfl` (run on 2026-11-15: exit 0, `t: accepted; axioms: none`, ending `548 declarations: 548 accepted`):

```bash
bin/leanforth check --env tests/front/s1-slice.ndjson --elab-data tests/front/s1-slice.elab.ndjson tests/front/s1-rfl.lf
```

S2, 0 + n = n by induction and rewriting (run on 2026-11-15: exit 0, `zero_add'': accepted; axioms: none`, ending `580 declarations: 580 accepted`):

```bash
bin/leanforth check --env tests/front/s2-slice.ndjson --elab-data tests/front/s2-slice.elab.ndjson tests/front/01-zero-add-rw.lf
```

`by-decide`, nine closed facts about numbers written with Lean's symbols, such as 3² + 4² = 5² and `20 10 >  10 10 ≥  3 4 ≠  ∧ ∧` (run on 2026-11-20: exit 0, each theorem `accepted; axioms: none`, ending `1272 declarations: 1272 accepted`, about 10 s); `dc-ascii.lf` beside it is the same file typed on a plain keyboard:

```bash
bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson tests/front/tactics/decide/dc-symbols.lf
```

The output first lists the slice's library declarations, then yours. A `sorryAx` line in the S2 slice's list is part of the library and is marked NOT PROVED, as the summary says.

## Where to go next

- [docs/README.md](docs/README.md): every document, by folder and audience.
- [The language reference](docs/user/LANGUAGE_REFERENCE.md), [user guide](docs/user/USER_GUIDE.md), [concepts in three forms](docs/user/CONCEPTS.md), [terms for new readers](docs/user/TERMS_FOR_NEW_READERS.md), [the elaborator](docs/user/ELABORATION.md), [the command line](docs/user/COMMAND_LINE.md).
- [Demos](docs/user/DEMOS.md) and [running the checks](docs/user/RUNNING_THE_CHECKS.md).
- [Project progress](docs/project/PROJECT_PROGRESS.md), [the owner's decisions](docs/project/OWNER_DECISIONS.md), [roadmap](docs/project/DEVELOPMENT_ROADMAP.md).
- Coding agents follow [AGENTS.md](AGENTS.md) (Codex reads it directly, Claude Code through `.claude/CLAUDE.md`). Work up to the `pre-claude` tag was developed with OpenAI Codex, the work since with Claude Code.

## Where the code is

`bin/leanforth` runs `gforth src/main.fs`, which loads every current module. Each module requires exactly the modules whose words it uses; [`src/README.md`](src/README.md) gives the layout rules and [the architecture page](docs/development/ARCHITECTURE.md) draws them. Nothing here is verified code; the kernel becomes trusted only when the owner declares it so after its review gate.

| Path | Contents |
| --- | --- |
| `bin/leanforth` | The command line: `check` (an export, a snapshot, or a LeanForth text), `print`, `replay`, `count`, `reexport`, `verify`, `version`, `help`; exit statuses 0 accepted, 1 rejected, 2 not supported yet, 3 out of a resource, 4 invalid input, 5 internal fault, 6 (with `--strict-axioms`) not proved. |
| `src/lib/` | General Forth libraries with no Lean knowledge (38 files): bounded stores, hash tables, sorting, big numbers, JSON, SHA-256, UTF-8, the shared outcome vocabulary, per-task contexts, a worker pool. Each loads alone and can be used by other Forth programs ([inventory](docs/development/FORTH_LIBRARY.md)). |
| `src/core/` | Lean's data model (33 files): the term store, names, universe levels, literals, constant references. |
| `src/kernel/` | The proof checker (42 files): type inference, definitional equality, reduction, inductive types and recursors, quotients, the checked environment. |
| `src/import/` | The reader of Lean's NDJSON exports, its manifest check, snapshots of a checked environment (13 files). |
| `src/author/` | The authoring layer (14 files): theorem text run line by line by Forth's own interpreter, its vocabulary and its error catalogue. |
| `src/front/` | The front end (58 files and the tactics): the reader of statements, the elaborator (instance search, unification, the Meta-level reducer), the tactic library and one file per tactic in `tactics/`. Untrusted. |
| `src/present/` | Printing (18 files): terms in Lean's notation, in LeanForth's postfix form, ASCII and LaTeX. Untrusted; the checker never loads it. |
| `src/program/` | The program track (10 files): example words, the stack-depth analyzer, the program IR and its interpreter. |
| `src/cli/`, `src/load/` | The command line's Forth side, and the layer entries that load one layer alone. |
| `tests/` | Unit tests beside each module, end-to-end runs, the Lean files LeanForth is compared with, and the planted faults (`tests/mutants/`). |
| `scripts/` | Install scripts, the checks run before every push, coverage, the planted-fault runner. |
| `schemas/` | JSON Schemas of the check report, the elaboration data, the export manifest and the program receipt. |

## How it is tested

- **Unit tests** of every module run on two Gforth engines, and nightly on Gforth 0.7.3.
- **Comparisons with pinned Lean 4.35.0** (`make check`): the kernel's verdicts on accepted, rejected and deliberately broken declarations; the front end's terms node for node; tactic results and error messages.
- **Planted faults**: about 3,200 deliberate one-line breaks of the source, each of which a named test must catch (`scripts/mutants.py`). All of them were run on 2026-11-20.
- **Coverage**: every line a change adds must be run by a unit test before it is merged; a nightly run checks every file.
- **Reviews**: every change to Forth source is reviewed by an independent reviewer before it reaches `main` ([reports](docs/development/forth-reviews/LOG.md)); changes to what the checker accepts need the owner's approval ([decisions](docs/project/OWNER_DECISIONS.md)).

GitHub CI is switched off at the owner's request (2026-11-11); the same checks run locally before every push and are recorded in `docs/development/ci-results.log`. [The testing strategy](docs/development/TESTING_STRATEGY.md) and [running the checks](docs/user/RUNNING_THE_CHECKS.md) say what each target shows and what it does not.

## Licence

The project code is MIT licensed ([LICENSE](LICENSE)). The test data derived from Lean 4 keeps Lean's Apache-2.0 licence, and Gforth and Lean are separately licensed tools the install scripts download ([NOTICE](NOTICE)).
