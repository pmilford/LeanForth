# Testing strategy

LeanForth aims for deliberately extensive tests across units, interfaces,
functional behavior and regressions. Coverage percentages are useful for
finding gaps, but cannot exceed 100% and do not establish correctness. Review
test quality, requirements coverage and adversarial cases as well as metrics.

## Forth test harness

Gforth 1.0 ships `test/ttester.fs`, derived from the established Forth test
suite. Its `T{ code -> expected }T` form checks both stack depth and contents;
it also supports floating-point cases. Investigate using it as the common
unit-test vocabulary instead of inventing a new framework. The installed Gforth
1.0 has a copy, but availability on other hosts and license terms must be
checked before depending on or distributing it. The bundled file requires its
copyright notice to remain if redistributed.

Printing an error alone is insufficient for CI. The test adapter assigns the
tester's `ERROR-XT` to print the assertion and throw, so the process fails on
the first error. `make test-harness` checks a passing test and two deliberate
failures. This adapter and the core tests pass locally with Gforth 1.0.0 and
the Ubuntu 24.04 Gforth 0.7.3 package extracted into a temporary directory.
CI runs `make test` on Ubuntu's Gforth package and `make check`, which adds
every pinned-Lean comparison, on pinned Gforth 1.0.0 and Lean 4.35.0. Both are
the same x86-64 Linux platform; test other hosts before claiming support.

## Layers

- Unit: each word's stack effect, expected behavior, edge cases and failure
  paths, including malformed data and resource limits.
- Interface: API and serialization schemas, stack contracts, error codes,
  deterministic behavior and supported/unsupported version boundaries.
- Functional: real end-to-end theorem and executable-program workflows once
  implemented, with correct proof artifacts and explicit runtime assumptions.
- Regression: preserve every fixed bug and previously observed discrepancy as
  a reproducible test; distinguish unsupported behavior from rejection.
- Differential and adversarial: compare supported terms with pinned Lean,
  test both false acceptance and false rejection, fuzz malformed inputs, and
  plant faults (`make mutants`, below) to check that the tests catch them.
- Portability: run portable tests on supported Forth hosts; record exact host
  versions and separate host assumptions from tested LeanForth behavior.

CI must fail closed on missing prerequisites, crashes, timeouts, malformed
inputs and failed assertions. Coverage tooling, additional packages and test
fixtures must be assessed for portability and license compatibility before
adoption. No test suite replaces human review of kernel rules or proof of
compiler and runtime correctness.

## Fail-closed safeguards (added 2026-11-02)

- **No proof by `sorry`.** Every Lean invocation in the test scripts passes
  `-DwarningAsError=true`, so `sorry` and other warnings fail the run.
  `tests/reference/sorry-must-fail.lean` is a false theorem proved with
  `sorry`; `make reference` requires Lean to reject it.
- **Static Lean guard.** `make check-lean-sources` (part of `make test`, no
  Lean needed) fails if a Lean test file uses `sorry`, `admit`,
  `native_decide`, a `warningAsError` override or an `axiom` outside the
  allowlist in `scripts/check-lean-sources.py`, or if a script runs Lean on a
  file without the strict flag.
- **Timeouts.** Every Make recipe runs its command under
  `timeout $(TEST_TIMEOUT)` (default 600 s), and each CI job has a
  `timeout-minutes` limit, so a looping test fails instead of hanging.
- **Size guards.** Differential scripts check both tables' line counts and
  exit on mismatch before comparing them.
- **Documentation links.** `make check-docs` fails on broken links.

The 2026-11-02 coverage review and its open items are recorded in
[the test coverage review](TEST_COVERAGE_REVIEW.md).

## Failure paths and allocation-failure injection (plan tasks 2.2.4, 1.4.6)

Added 2026-11-03. The first checker must fail closed wherever it runs out
of fuel or room, or a word throws: nothing that fails may be stored,
published, given a handle or printed as accepted.

**The hook.** `src/lib/store.fs` has one test-only hook. A program that
defines the word `store-fault-hooks` before the store library loads gets
`store-refuse? ( store -- flag )`, a `DEFER` that `store-open?` asks about
every allocation that would otherwise go ahead, in every store: the term,
level, name, reference and input stores of each context and the checked
environment's dependency pool (`store-new`, and the name table's
`store-open?` then `store-claim`). True refuses the allocation as if the
store were full, changing nothing; the word may also `THROW`. Without
`store-fault-hooks`, `store-open?` is compiled exactly as before: no
`DEFER`, no extra call, no cost. LeanForth never interprets its input as
Forth and `src/main.fs` never defines that word, so no input can turn the
hook on or reach it. `tests/support/alloc-fail.fs`, loaded before anything
else, defines it and makes the k-th allocation after `af-arm` (or
`af-arm-throw`) fail, counted across every store; only that one fails.

**The suite.** `tests/core/failure-paths.fs` (in `make test`, under a
second on either Gforth) runs check-declaration through the publisher on
the five pinned fixtures and on 18 cases in the first-checker driver's
text, most of them rows of `tests/core/check-declaration.fs`, that end
rejected, unknown, unsupported, invalid or full at each step. For
each case it records a baseline, then refuses allocation k for every k,
sweeps the fuel from 0 until the baseline returns, and throws at
allocation k for every k (each run in a new context, with a maker that
loads the same input into another one, so that the run goes on; and twice
with no maker, so that it stops). After every step it checks that only
that declaration's slot changed, that the dependency pool grew only by an
accepted declaration's dependencies (a failed publication takes its
entries back) and that every input store is back at its mark with the
input's fingerprint unchanged; after every run, that a slot is accepted
only where its baseline is and every slot it depended on is accepted now,
that the slot an injected failure reached is full (refused), invalid
(thrown) or, when the publisher failed, open and cleared with the run
stopped, that later slots keep their baseline outcome or become unknown
(K5) when an earlier one changed, that handles and printed verdicts agree
with each slot's outcome (an axiom bit planted in an accepted slot must
print), and that a refusal or fuel never spends a context while a `THROW`
in a check does. It also checks that the publisher's re-check publishes a
passed check with a false claim as invalid. About 4,500 injected runs.

It prints the outcomes reached per check step and fails unless they are
exactly these (2026-11-03):

| Step | Outcomes reached |
| --- | --- |
| 0 before a snapshot | invalid |
| 1 audit | invalid, exhausted, unsupported |
| 2 name (N2) | unknown, rejected, unsupported |
| 3 parameters (L3) | rejected |
| 4 declared type's type | invalid, exhausted, unknown, rejected, unsupported, full |
| 5 a Sort (S1) | unknown, rejected |
| 6 a proposition (S3) | exhausted, rejected |
| 7 value's type | invalid, exhausted, unknown, rejected, unsupported, full |
| 8 comparison (D1–D5) | invalid, exhausted, unknown, rejected |
| 9 every step done | ok, invalid (a failed publication) |

No run of these cases reaches the empty cells: steps 2, 3, 5 and 6
allocate nothing and steps 2 and 3 use no fuel; step 5 runs out of fuel
only in its search for a rejection, which then leaves it *unknown* (ADR
0011); a `THROW` can be injected only at an allocation; and step 8
allocates only in its search for a rejection, where a refused allocation
leaves the step *unknown* as well, not *full*: weaker than Lean's
rejection and than ADR 0008's *full*, never accepted.

**Planted faults.** `tests/core/failure_path_faults.py` (also in `make
test`, about 2 s) runs the suite in a temporary copy of the tree with one
fault planted at a time, and requires it to fail on each of nine: the
publisher marking a slot final before writing its record, a check accepted
before its comparison, a step's *full* turned into ok, the level store's
rollback and the pool's rollback after a failed publication forgotten, a
check that ends full finished ok, "axioms: none" printed without reading
the slot, the hook switched off, and a `THROW` in a check that no longer
spends its context. All nine are caught.

## Planted faults (`make mutants`)

A planted fault (a *mutant*) is a small deliberate bug: if no test fails
with it in place, the tests do not check what that code does. Reviews used
to plant faults in throwaway scripts that were then lost; `make mutants`
(plan task 1.4.2) keeps them as a checked-in list,
`tests/mutants/faults.toml`, run by `scripts/mutants.py`. Each entry names:

- `file`, the file it changes, and `old`, an exact text that must occur
  there exactly once, with `new`, its replacement;
- `test`, the shell command that must catch it (`$GFORTH` names the Gforth
  of the run), and `reason`, one line on what it breaks;
- optionally `equivalent`, why no test can tell it from the original, or
  `gap`, the missing test that would catch it; both are expected to survive;
- optionally `quick = true`, for the sample `make mutants-quick` runs.

The runner first checks every entry's `old` text: one that no longer
occurs exactly once is *stale* (the code changed under it), which fails
the run; re-target such a fault at the new code rather than deleting it.
Then it copies the tree's files (git's tracked and new files) into a new
temporary directory outside the tree, runs every distinct test once on the
unchanged copy (each must pass), and plants each fault in turn: it writes
the change, checks that the changed file still loads (a Forth module on its
own and silently, as `make smoke` requires; a Python file must parse; a
change that does not load would prove nothing and fails the run), runs the
test and restores the file. It reports each fault as caught or survived and
exits nonzero when a fault expected to be caught survives, a fault listed
as equivalent or as a gap is caught (correct the entry), or an entry is
stale. It never writes the working tree: it hashes every file of the tree
before and after the run and fails if anything changed, and
`make test-mutants` (part of `make test`) checks every verdict and exit
status on a small tree, and that the tree is untouched after each run.

| Target | What it runs |
| --- | --- |
| `make mutants` | every fault (about 25 s on Gforth 1.0; not part of `make test` or `make check`) |
| `make mutants-quick` | the faults marked `quick`, one or two per module |
| `make mutants-check` | only the stale-entry check, without running anything (part of `make check`, so the list cannot go stale unnoticed) |
| `make test-mutants` | the runner's own tests (in `make test`) |

Run it with `GFORTH=...` for another host. On 2026-11-03 (Gforth 1.0) the
list held 135 faults over `check-declaration.fs`, the checked environment
(`environment.fs`, `env-publish.fs`, `env-signature.fs`), the rejection
rules (`mixed-infer.fs`, `mixed-head.fs`, `level-value.fs`), comparison and
conversion, the NDJSON reader, the program reader, `lib/context.fs`,
`lib/json-write.fs` and the runner itself. They re-create the faults that
earlier reviews planted by hand in scratch scripts since lost (those of
check-declaration and the rejection rules, all 9 of the checked
environment's fourth review, some of the JSON writer's), and add new ones.
132 were caught; 2 survive as known gaps and 1 as equivalent, each with
its reason in the list. The gaps are tests that do not exist yet: a
binder whose two domains infer differently (`rej-d4-left-domain`) and two
Sorts whose levels differ only in a parameter (`cmp-level-params-equal`).
Eight earlier gaps now have tests: names that differ only in a numeric
component; metadata that differs from the pinned versions only in the
format or the Lean version; an upper-case `Z` in program source; an
environment record whose identity is 0; and, in check-declaration, a case
that needs the room step 7 gives back (`value-room`), one whose rejection
holds only while inference run aside records no dependency
(`aside-deps`), and the axiom label, which no phase-2 input can show
(axioms are unsupported) and the failure-path suite tests by planting a
bit in each accepted slot.

Some test suites plant faults of their own and must keep doing so: the
big-number differential (`tests/lib/bignum_differential.py`, 20 faults, in
`make test`), the IR interpreter's differential
(`tests/program/ir_run_differential.py`, 2 faults in its primitive table),
the receipt validator's test (`tests/program/test_receipts.py`), the
verification-condition check (`tests/program/vc_check.py`, faults Lean must
reject, in `make check`) and the authoring words' round trips
(`tests/author/check_author.py --faults`, 7 faults, in `make check`). The
JSON writer's and the packed-field module's reviews planted their faults by
hand (`FORTH_LIBRARY.md`); the list above re-creates some of them.

## Block coverage (`make coverage`)

`make coverage` (plan task 1.4.1) reports which Forth code `make test`
runs. `scripts/coverage.py` runs `make test` with `GFORTH` set to
`scripts/coverage-gforth.sh`, which starts Gforth 1.0 with
`scripts/coverage-prelude.fs` before the test's own arguments; the Python
tests' Gforth runs go through it too. The prelude loads Gforth 1.0's
`coverage.fs`, which puts a counter on every basic block compiled after it
(at each colon definition's start, each control-flow word and each source
line inside a definition), and writes the counts when Gforth ends, also
after an error (`BYE`, `(BYE)`, an uncaught `THROW` out of a command-line
argument, `DOERROR`). The script then joins the counts of all runs and
prints, for each folder of `src/`, the blocks compiled in any run and how
many ran at least once; `make test`'s smoke check loads every module on its
own, so modules that no test runs count too. Options: `--files` prints
every file, `--uncovered FILE` writes each block that never ran as
`file:line:column`, `--keep DIR` keeps the raw counts.

It needs Gforth 1.0 (`.tools/`; Gforth 0.7.3 has no `coverage.fs`) and
takes about 50 s. It is not part of `make test` or `make check`. Runs on
copies of the tree outside it (the big-number planted faults) are not
counted. On 2026-11-03 it reported:

| Folder | Blocks | Ran | Coverage |
| --- | --- | --- | --- |
| `src/author` | 1,085 | 1,024 | 94.4% |
| `src/core` | 1,008 | 995 | 98.7% |
| `src/import` | 796 | 767 | 96.4% |
| `src/kernel` | 3,180 | 3,096 | 97.4% |
| `src/lib` | 2,595 | 2,531 | 97.5% |
| `src/present` | 2,164 | 2,021 | 93.4% |
| `src/program` | 1,265 | 1,246 | 98.5% |
| total | 12,093 | 11,680 | 96.6% |

A block that ran is not a tested block: coverage finds code no test
reaches and says nothing about whether the tests check what the code does,
which is what `make mutants` asks. The 2026-11-02 review's figure (90.7% of
5,532 blocks) measured `make test-core` alone, over the code of that day.

## Self-verification

LeanForth's program correctness system should eventually verify selected
LeanForth components against explicit specifications, including checker and
runtime operations where practical. First validate the verifier with independent
tests and Lean comparisons, then apply it to narrowly specified components and
retain independent regression and adversarial tests. A verifier checking itself
does not independently establish its own soundness; record the trusted kernel,
host, compiler and runtime assumptions separately.

## Source and test filenames

Matching filenames under `src/` and `tests/` intentionally pair an
implementation module with its tests; the directory is part of the path.
For example, `src/kernel/mixed-infer.fs` defines experimental words,
while `tests/core/mixed-infer.fs` includes that module and exercises it.
Likewise `src/program/clamp.fs` is a Forth word and `tests/program/clamp.fs`
is its test suite. The two `check.sh` files run different harness and Lean
reference checks. Same names do not mean the files are copies; use full paths
in documentation, commands and review comments to avoid ambiguity.

## Retired tests of superseded code

Until 2026-11-02 the superseded plain and `tagged-*` modules had their own
tests beside them, run by `make test-legacy` and, for 18 pinned-Lean
comparisons, by `make check`. The [owner approved](../project/OWNER_DECISIONS.md)
deleting that code once the current code had at least the same test
coverage. Every coverage gap was first closed with tests of current code;
then the superseded modules and their tests (119 files) were deleted
together with their Make targets ([decisions record](../project/DECISIONS.md),
"Legacy retired — 2026-11-02"). The tests that had exercised current modules
through a superseded helper were rebuilt on current code in `tests/core/`:
the NDJSON preview suite (`tests/core/test_ndjson_preview.py`) checks the
`src/import/load.fs` staging round trip without a checker,
`tests/core/test_export_definitions.py` runs the current definition probe on
the pinned exports, and `tests/core/tagged-sort-boundary.fs`,
`declaration-chain-test.py` and `context-constant-fixture-test.py` were
rebuilt on current modules only.

### Ports of the legacy pinned-Lean comparisons

`tests/core/lean-differential.py NAME` compares a Forth table of current code
with a Lean 4.35.0 table in `tests/reference/`; each `NAME` has a Make target
in `DIFFERENTIAL_TARGETS`, so `make check` runs them all. They port the
legacy comparisons onto the current passes, with every Sort symbolic (a
concrete universe n is the level succ^n zero):

| Make target | NAME | Forth side | Lean side | Cases |
| --- | --- | --- | --- | --- |
| `test-constant-term-scope-differential` | `scope` | `constant-term-scope-table.fs` | `scope-table.lean` | 64 |
| `test-mixed-shift-plain-differential` | `shift` | `mixed-shift-plain-table.fs` | `shift-table.lean` | 80 |
| `test-mixed-instantiate-plain-differential` | `instantiate` | `mixed-instantiate-plain-table.fs` | `instantiate-table.lean` | 25 |
| `test-mixed-beta-plain-differential` | `beta` | `mixed-beta-plain-table.fs` | `beta-table.lean` | 15 |
| `test-mixed-convert-plain-differential` | `convert` | `mixed-convert-plain-table.fs` | `convert-table.lean` | 15 |
| `test-mixed-infer-plain-differential` | `infer` | `mixed-infer-plain-table.fs` | five tables | 52 |
| `test-mixed-definition-differential` | `definition` | `mixed-definition-table.fs` | `definition-table.lean` | 9 |
| `test-mixed-level-substitute-plain-differential` | `level-substitute` | `mixed-level-substitute-plain-table.fs` | `term-level-substitute-table.lean` | 48 |
| `test-mixed-infer-constant-differential` | `constant` | `mixed-infer-constant-table.fs` | `term-level-substitute-table.lean` | 96 |
| `test-export-signature-differential` | `signature-fixture` | `export-signature-stream.fs` | `signature-fixture.lean` | 4 |
| `test-export-specialization-differential` | `poly-specialization` | `export-definition-stream.fs` | `poly-specialization-table.lean` | 8 |

Rows must agree exactly, except that an ill-typed term may be invalid or
unknown and that `KNOWN_UNKNOWN` in the driver lists the two cases where the
current code is knowingly more conservative than Lean (it answers unknown
where Lean accepts): `max u v` against `max v u`, and a binder domain whose
type is an unreduced redex. Any other difference fails.
