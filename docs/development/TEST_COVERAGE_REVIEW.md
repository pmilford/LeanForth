# Test coverage review — 2026-11-02

Three independent reviews examined the tests of the theorem-checking Forth
code, the Lean NDJSON import and Lean compatibility, and the
program-correctness track. The owner's goal is "110% coverage": not only
lines, but every behaviour class — pass, fail, bad input, interfaces,
subsystems, input and output, resource exhaustion, and regressions for
positive, negative and incomplete outcomes. This document records what was
found and the status of each item: **fixed**, **in progress** or **later**.
It is a review of tests, not evidence that any code is correct.

## Headline measurements

- **Theorem path (Forth).** Gforth 1.0.0's `coverage.fs` reports 90.7% of
  code blocks (5,017 of 5,532) executed by `make test-core`, and all 410
  colon definitions entered. Of 15 deliberately planted faults (mutants),
  **14 passed the tests**; three of those are reachable through public words
  and give a wrong answer (a false "equal", an out-of-bounds index write, a
  stale handle accepted). After the fixes below, 7 of the 15 are caught,
  including all three reachable ones, and block coverage is 92.5%. Of the 8
  left, 3 need the deferred tests T7 and T8, 3 guard paths the public words
  do not seem to reach, and 2 are in superseded code.
- **Program track.** Of 46 mutants of the six example words and the depth
  analyzer, 39 were caught and 7 survived (2 behave identically to the
  original). 13 were caught only by the unit tests, not by the Lean
  comparisons. Nothing has run on a 32-bit host. After the fixes below, 43
  of 46 are caught: the two equivalent mutants and one that needs P9.
- **NDJSON import.** The Python preview supports 15 of the 24 record kinds in
  Lean's export format v3.1.0 and reports the other 9 as unsupported. Any real
  export that mentions `Nat`, `Bool` or `Eq` contains an unsupported
  `inductive` record, so real-world reach beyond toy fixtures is 0%.
- **Lean compatibility.** 29 paired comparison targets compare 774 rows (630
  distinct Lean results). For every declaration Lean rejects, LeanForth answers
  *unknown*; it never definitively rejects one. Kernel-level negative oracles
  accept any Lean error without checking the reason.

## Owner's coverage classes

Every module should eventually have tests in each applicable class:

1. Pass and fail cases, and the three outcomes *accepted*, *rejected* and
   *unsupported/unknown*, with no failure ever reported as success.
2. Malformed input, including truncation, wrong types, out-of-range values,
   duplicates and cycles.
3. Interfaces: stack effects, status codes and mappings between modules.
4. Subsystems and whole workflows; input and output streams.
5. Memory and resources: arena, index and stack exhaustion, fuel, overflow and
   cell width (32- and 64-bit).
6. State: rollback after partial failure, stale handles, repeated calls.
7. Regression pins for positive, negative and incomplete results.
8. Lean compatibility: Lean-accepted and Lean-rejected inputs per feature.

Classes the reviews add: **mutation testing** (do the tests catch planted
faults?), **fuzzing**, **determinism**, **portability** (other Forth hosts,
32-bit cells, number base), **timeouts**, and **harness self-tests** (each
comparison must reject a known-wrong table).

## Findings and status

### Cross-cutting

| ID | Finding | Status |
| --- | --- | --- |
| X1 | Lean reference checks accepted `sorry`: a false theorem proved with `sorry` exited 0 | **Fixed**: `-DwarningAsError=true` on every Lean run, `sorry-must-fail.lean`, `make check-lean-sources` |
| X2 | No timeouts; one mutant made a test loop ~2^63 times, which would hang CI | **Fixed**: `timeout` on every Make recipe, CI `timeout-minutes` |
| X3 | `memory-reference-differential.sh` size guard could not fail (`[ ] && [ ]` under `set -e`) | **Fixed** |
| X4 | No mutation testing in the suite | **Fixed** 2026-11-03: `make mutants` runs the checked-in planted faults of `tests/mutants/faults.toml`, with known-equivalent and known-gap entries ([testing strategy](TESTING_STRATEGY.md#planted-faults-make-mutants)) |
| X5 | No coverage measurement in the suite | **Fixed** 2026-11-03: `make coverage` reports per-folder block coverage of `src/` over `make test` with Gforth 1.0's `coverage.fs` ([testing strategy](TESTING_STRATEGY.md#block-coverage-make-coverage)) |
| X6 | No fuzzing of Forth stream readers, DAG inputs or the NDJSON preview | Later |
| X7 | Only 64-bit x86 Linux tested; no 32-bit host; number base never varied | Later |
| X8 | Comparison scripts have no self-test that a known-wrong table is rejected | Later |
| X9 | Status 0 means success but is also Forth `false`; nothing checks statuses are never used as flags | Later |
| X10 | `>=` (74 uses in 40 files) and `<=` (11) are Gforth extensions, not Forth-2012; CI's Gforth 0.7.3 also has them, so nothing detects the dependency | Later: a small portability adapter, or `< 0=` / `> 0=` |

### Theorem path (Forth)

| ID | Finding | Status |
| --- | --- | --- |
| T1 | Depth guard at `tests/core/mixed-definition-probe.fs:169` pops an extra cell, so a leftover `0` passes; `mixed-infer.fs` and `tagged-application.fs` tests lack depth guards | **Fixed**: shared `run-case` helper in `tests/support/checks.fs` stops on any leftover cell |
| T2 | Constants differing only in universe-argument count can compare *equal* under a one-token fault (M4); untested | **Fixed**: unknown in both orders, and through the definition probe |
| T3 | Signature index capacity: an off-by-one lets a 33rd entry write past the arrays (M7); untested | **Fixed**, with bad fuel, arity and name cases |
| T4 | Stale level handle after reset accepted under a one-token fault (M8); untested | **Fixed**, with constructors called outside a session |
| T5 | Binder domain or Pi body that is not a type: unknown and rollback untested | **Fixed** in `mixed-infer`, the definition probe and `tagged-infer` |
| T6 | 19 of 34 status-mapping words have no direct test; 103 mapping arms never run | **Fixed** for every mapping word; mappings written inline in five larger words remain untestable until factored out (later, with the style work) |
| T7 | Level, reference and term arena exhaustion inside `mixed-*` inference never exercised | Later |
| T8 | Corrupted global counts, generation saturation, inactive index token | Later |
| T9 | Stream drivers: only 59 of 249 throw guards are exercised; no malformed stream bytes | Later |
| T10 | `compare-` and `mixed-convert-differential.sh` allow every row to become *unknown* | Later: pin per-row verdicts |
| T11 | The API has no *rejected* status — a wrong value returns *unknown* — so the owner's three outcomes cannot all be tested | Later: design decision for the checker |
| T12 | `tests/support/tester.fs` never checks the return stack | Later |
| T13 | `tests/core/mixed-infer.fs`: no test checks the level of a Π term's type (`imax`), reaches the Prop shortcut, an arity mismatch, a stale root or the identity function; the fuel sweep covers one root only (found by the Forth reviewer; its scratch probe passed all of them) | Later |

### NDJSON import and Lean compatibility

| ID | Finding | Status |
| --- | --- | --- |
| N1 | Invalid UTF-8 accepted; byte-order mark and CRLF accepted silently | **Fixed**: strict UTF-8 framing; BOM, CR, blank lines, missing final newline and escaped lone surrogates are malformed |
| N2 | Many malformed records reported as *unsupported* (unknown kinds, extra keys, second `meta`, bad `binderInfo`, `all: []`, …) | **Fixed**: all reclassified; the nine unsupported kinds are shape-checked first (validated on 142 real records). `mdata` payloads stay unchecked: no export produced one |
| N3 | Lean-valid values of 2^31 or more rejected as malformed instead of a limit | **Fixed** |
| N4 | Only 7 of ~35 negative preview tests check the error code | **Fixed** in the preview tests; three bare assertions remain in `test_tagged_poly_fixture.py` and `constant-term-fixture-test.py` (later) |
| N5 | About 40% of malformed-input classes tested only on a separate hard-coded inspector, not the preview | **Fixed** |
| N6 | Limits `MAX_TOTAL`, `MAX_NAMES`, `MAX_DECLARATIONS` and the 4095/4096-byte line boundary untested | **Fixed**: every limit tested at and one past its boundary |
| N7 | CLI success output, exit codes and determinism untested; only 1 of 5 fixtures hash-pinned | **Fixed**: exact output for all fixtures (preview version 0.4), distinct exit codes per outcome, byte-identical across hash seeds, all fixtures pinned. A JSON Schema for the output is later |
| N8 | No real-export fixtures for unsupported kinds (axiom, inductive, quot, opaque, let, proj, literals, mutual) | Later |
| N9 | Mutated NDJSON is not checked by Lean itself (replay through Lean's kernel) | Later |
| N10 | Kernel negative oracles accept any Lean error; the reason is not checked | Later |
| N11 | No differential cases for η, proof irrelevance, definition unfolding, universe-arity mismatch, undeclared universe parameters | Later |
| N12 | No round-trip test, corpus-scale inventory (Init, Std, Mathlib), streaming of large exports, or second referee (lean4checker, nanoda, lean4lean) | Later |
| N13 | About 11 Forth stream readers each re-implement the same framing | Later: one shared reader |

### Program track

| ID | Finding | Status |
| --- | --- | --- |
| P1 | `lf-checked-add`: exact overflow thresholds missing from the portable tests; a fault rejecting valid large sums survives | **Fixed**: thresholds and host-derived half-range cases in `tests/program/examples.fs` |
| P2 | `lf-gcd`: no worst-case (consecutive Fibonacci) inputs; a fault capping the loop at 8 iterations survives | **Fixed**: F(46)/F(45), 7·F(30)/7·F(29), extremes; F(92)/F(91) on 64-bit cells |
| P3 | No golden answers independent of Lean (20!, gcd of Fibonacci pairs) | **Fixed**: 13!, 20!, 21! overflow and the gcd pairs above |
| P4 | `lf-in-range` uses the return stack but no test checks it is preserved | **Fixed**: data- and return-stack caller cells checked over 343 triples |
| P5 | Depth analyzer: misalignment test does not detect removal of the alignment check | **Fixed** (alignment and size overflow); a negative-count fault still survives until P9's read-count seam exists |
| P6 | Wrong contracts are rarely refuted in Lean (only `brokenCode`, a swap and a commute counterexample); the swapped-endpoints clamp required by `PROGRAM_EXAMPLE.md` is missing | **Fixed**: off-by-one and swapped-endpoint refutations for clamp, checked add, in-range and gcd; `check.sh` requires all four wrong clamp claims to fail |
| P7 | Underflow (calling a word with too few stack items) untested | **Fixed** as a host observation: each word throws −4 on an empty stack under Gforth 1.0.0 and 0.7.3. Silent consumption of caller cells is not detectable and remains a documented assumption |
| P8 | Comparison tables print only results, not flags, depth or return-stack markers | Later |
| P9 | Depth analyzer cannot show it rejects before reading; running out of fuel returns the same result as invalid input | Later |
| P10 | Nothing ties the Forth source of `lf-clamp` to the Lean model `clampCode` | Later |
| P11 | The memory model's `trace` function is not proved equal to the `execute` the proofs use | Later |
| P12 | No seeded random property tables; no end-to-end *specify → check → run → receipt* tests (no such workflow exists yet) | In part (2026-11-13, plan 8.4.1b): *specify → check → receipt* runs end to end for every committed contract (`scripts/program_verify.py`, `tests/program/verify_lean_check.py`; clamp and a wrong contract in `make check`, every outcome with stand-in tools in `make test`); *run* waits for 8.4.2, the random tables for later |

## Duplicate experimental code (roadmap Q9)

The `mixed-*` modules are the current path. `tagged-*` and the plain
variants are superseded but still used by tests, fixtures and 14 Lean
comparison targets, so they can only be retired after those are migrated.
`src/legacy/arena.fs` and the unsafe `symbolic-infer.fs` draft have no
dependants. On 2026-11-02 the owner decided to keep them for now and mark
them for possible later removal (roadmap Q9); the Lean oracle
`tests/legacy/symbolic-infer-oracle.lean` must stay either way because
`tagged-infer-differential.sh` uses it. Update (later on 2026-11-02): a copy,
`tests/reference/symbolic-infer-oracle.lean`, is now run against the current
`lf-mixed-infer` by `make test-mixed-infer-plain-differential`, so the oracle
stays when `tests/legacy/` is deleted. Resolved 2026-11-02: once every
coverage gap had been closed with tests of current code, the owner's approval
was applied and the superseded modules, their tests and their 18 Lean
comparison targets were deleted (roadmap Q9 done; [decisions
record](../project/DECISIONS.md), "Legacy retired — 2026-11-02").

## How the reviews were run

Each reviewer read the code and tests, ran `make test` and the relevant Lean
comparisons with Gforth 1.0.0 and Lean 4.35.0, and planted faults in scratch
copies (never in the repository). Not run: Gforth 0.7.3 comparisons, 32-bit
hosts and CI. The scratch tools (coverage wrapper, mutation scripts, probes)
are outside the repository; turning them into project tooling is X4 and X5
(done 2026-11-03: `make mutants` and `make coverage`).
