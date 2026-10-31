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
the Ubuntu 24.04 Gforth 0.7.3 package extracted into a temporary directory. The
updated CI workflow has not yet run. Test other hosts before claiming support.

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

## Self-verification

LeanForth's program correctness system should eventually verify selected
LeanForth components against explicit specifications, including checker and
runtime operations where practical. First validate the verifier with independent
tests and Lean comparisons, then apply it to narrowly specified components and
retain independent regression and adversarial tests. A verifier checking itself
does not independently establish its own soundness; record the trusted kernel,
host, compiler and runtime assumptions separately.
