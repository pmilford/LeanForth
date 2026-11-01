# Factorial arithmetic reference

[`factorial-reference.lean`](../tests/reference/factorial-reference.lean) is an
independent Lean model motivated by `lf-factorial` in
[`examples.fs`](../src/program/examples.fs). It is a mathematical reference,
not a proof of the Forth source or its execution.

The model takes a mathematical signed integer input and a natural-number upper
bound `limit`. For comparison with a signed Forth cell, assume the input is
representable, the cell maximum is `limit`, and the minimum is `-limit - 1`.
The Forth example additionally assumes two's-complement signed cells, logical
right shift, standard signed comparisons and division, and sufficient stack
space. The Lean function itself does not enforce cell representability or
model those host operations. It uses unbounded arithmetic and detects overflow
by comparing the exact product with `limit`, rather than allowing wraparound.

The recursive `factorial` is defined independently of the bounded function,
with `0! = 1` and `(n+1)! = n! * (n+1)`. `bounded` builds the result in
ascending factor order and returns `none` as soon as a checked intermediate
product exceeds `limit`; it checks the initial value 1 as well. `checked`
rejects negative inputs before converting a nonnegative input to a natural.
Unlike the model's ascending recursion, the Forth word multiplies in
descending order and uses a division threshold. No equivalence between those
algorithms or their checks is established here.

Lean proves, for every natural `limit` and integer input:

- `negative_rejected`: a negative input returns `none`.
- `success_iff`: for nonnegative input, the model returns `some result`
  exactly when the mathematical factorial is at most `limit` and `result`
  equals that factorial. Thus the returned value fits the modeled upper bound.
- `overflow_iff`: for nonnegative input, the model returns `none` exactly
  when the mathematical factorial exceeds `limit` (including the artificial
  case `limit = 0` and input 0).
- `bounded_exact` establishes the result for all natural inputs and bounds;
  `previous_le` supports completeness when an earlier product overflows.

Concrete checked examples include negative input, zero, a fitting product,
overflow, and a product exactly at its bound. These are model checks, not
tests of the Forth word. No `sorry`, new axiom, LeanForth certificate, source
semantics, compiler verification, runtime validation, or general Forth
verification is supplied by this reference. Lean's own kernel and imported
Lean libraries are part of the reference proof's trust boundary.

Run the pinned local Lean independently from the repository root:

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --version
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --githash
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean tests/reference/factorial-reference.lean
```

The repository pin is Lean 4.35.0, revision
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. This reference is included in
`make reference`; CI execution of this revision has not been established.
