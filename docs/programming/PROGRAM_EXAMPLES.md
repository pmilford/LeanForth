# Executable Forth examples

`make test-program` routinely runs the clamp tests, the five examples below,
and the stack-depth diagnostic tests. The CI workflow invokes
that target. These are tested host Forth programs, not verified programs: no
LeanForth proof connects them to a specification or runtime yet.
The [independent Lean reference](PROGRAM_EXAMPLES_REFERENCE.md) proves
properties of mathematical models for two examples; it does not prove the
Forth implementations correspond to those models.
The [factorial reference](FACTORIAL_REFERENCE.md) proves bounded mathematical
factorial properties; it uses a different algorithm and does not prove the
Forth word equivalent.
The [gcd reference](GCD_REFERENCE.md) proves termination and mathematical
properties of Euclid's algorithm, without establishing Forth correspondence.
The [checked-add reference](CHECKED_ADD_REFERENCE.md) also proves the modeled
overflow checks and their arithmetic bounds, subject to the same limitation.

| Word | Behavior and failure |
| --- | --- |
| `lf-checked-add` | Adds two signed cells; rejects overflow. |
| `lf-checked-abs` | Returns a magnitude; rejects the minimum signed cell. |
| `lf-factorial` | Computes a nonnegative factorial; rejects negatives and overflow. |
| `lf-gcd` | Computes the greatest common divisor of nonnegative cells, with `gcd(0,0) = 0`; rejects negatives. |
| `lf-in-range` | Tests inclusive interval membership; rejects reversed bounds. |

See [the source](../../src/program/examples.fs) for stack effects and signed-cell
assumptions. Tests cover boundary and error cases, stack preservation, and
small input domains. They run on the installed Gforth host; other Forth hosts
and cell representations have not been established by these tests.

The portable suite in `tests/program/examples.fs` derives its boundary cases
from the host cell rather than from 32- or 64-bit literals, except where noted:

- `lf-checked-add`: sums exactly equal to the maximum or minimum are accepted
  in both argument orders (for example `max-1 + 1` and `0 + min`), and
  half-range operands `h = max/2 + 1` check that `h + (h-1)` is the maximum
  while `h + h` overflows, with the mirrored negative cases. These catch
  off-by-one threshold comparisons in `make test` itself, not only in the
  64-bit Lean differential.
- `lf-gcd`: `(0, min)`, `(min, 0)` and `(0, -1)` are rejected; `(max, max-1)`
  in both orders returns 1. Consecutive Fibonacci numbers F(46) and F(45), and
  F(30) and F(29) scaled by 7, exercise Euclid's longest remainder chains that
  fit a signed 32-bit cell. On 64-bit cells only (guarded with `[IF]`), the
  suite also checks F(92) and F(91), 13!, 20! and the overflow at 21! against
  independently known values.
- `lf-in-range`: two caller data-stack cells and two caller return-stack cells
  must survive all 343 triples in `[-3, 3]`, with canonical flags.
- Stack underflow: each example word run with one input missing on an
  otherwise empty data stack must throw -4. This records the observed
  behavior of Gforth 1.0.0 and the Ubuntu Gforth 0.7.3 package, not a
  LeanForth guarantee: if a caller's own cells are present, a word consumes
  them silently, and other hosts or engines may not detect underflow.

On 2026-11-02 `make test-program` passed with Gforth 1.0.0, and the three
program test files also passed with Ubuntu's Gforth 0.7.3 package extracted
into a scratch directory, both on x86-64 Linux with 64-bit cells. No 32-bit
host has been tested.

Separately, `make test-program-values-differential` uses pinned Lean to compare
actual Forth stack results for 15,624 finite sequences of push, duplicate and
addition against an abstract Lean interpreter. It bounds values to avoid host
overflow; it does not prove the host or the five example words correct. Run it
after setup with:

```sh
ELAN_HOME="$PWD/.tools/elan" make test-program-values-differential LEAN="$PWD/.tools/elan/bin/lean"
```

`make test-example-reference-differential` also compares `lf-in-range` with
its Lean model on 686 finite triples, including signed 32-bit boundary values.
That optional boundary test requires cells of at least 64 bits. It is runtime
evidence, not a proof of Forth semantics or compiler behavior.

`make test-add-reference-differential` compares `lf-checked-add` with its
Lean model on 410 small and signed 32-/64-bit boundary pairs, including
overflow and stack-sentinel cases. This optional test requires 64-bit cells;
it does not prove host arithmetic, the compiler, or the Forth implementation.

`make test-abs-reference-differential` compares `lf-checked-abs` with its
Lean model on 263 small and signed 64-bit boundary inputs, including the
minimum-cell failure and stack sentinel. This optional test requires 64-bit
two's-complement cells; it is finite evidence, not a runtime proof.

`make test-factorial-reference-differential` compares `lf-factorial` with its
Lean model on 152 inputs, including the first signed 64-bit overflow. The
optional test requires Gforth 1.0.0 and 64-bit two's-complement cells. It
does not prove the algorithms equivalent or verify the Forth runtime.

`make test-gcd-reference-differential` compares `lf-gcd` against the Lean
model on 150 finite input pairs, including negative and signed-cell boundary
inputs. It requires 64-bit cells and is not a runtime or compiler proof.

`make test-range-64-differential` compares interval membership on 343 triples
drawn from signed 64-bit boundaries. It also checks canonical flags and caller
stack preservation; it is finite testing and requires 64-bit cells.
