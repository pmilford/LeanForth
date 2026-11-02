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

See [the source](../src/program/examples.fs) for stack effects and signed-cell
assumptions. Tests cover boundary and error cases, stack preservation, and
small input domains. They run on the installed Gforth host; other Forth hosts
and cell representations have not been established by these tests.

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
