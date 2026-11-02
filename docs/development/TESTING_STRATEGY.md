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
  consider mutation testing to evaluate whether tests catch faults.
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
