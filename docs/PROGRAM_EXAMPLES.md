# Executable Forth examples

`make test-program` routinely runs the clamp tests, the five examples below,
and the stack-depth diagnostic tests. The existing CI smoke workflow invokes
that target. These are tested host Forth programs, not verified programs: no
LeanForth proof connects them to a specification or runtime yet.
The [independent Lean reference](PROGRAM_EXAMPLES_REFERENCE.md) proves
properties of mathematical models for two examples; it does not prove the
Forth implementations correspond to those models.
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
