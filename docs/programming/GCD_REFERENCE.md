# Euclidean gcd mathematical reference

[`gcd-reference.lean`](../../tests/reference/gcd-reference.lean) defines an
independent mathematical model inspired by `lf-gcd` in
[`examples.fs`](../../src/program/examples.fs). It proves properties for all
natural inputs, including zero, using Lean 4.35.0 and its standard library.

`euclid a b` returns `a` when `b = 0`; otherwise it recurs on
`(b, a % b)`. Lean checks that the second argument strictly decreases, by
`Nat.mod_lt`, so the definition terminates for all natural inputs. The
`euclid_correct` theorem proves its result equals `Nat.gcd a b` using the
standard library's gcd recurrence. `divides_both` and `greatest` establish
the common-divisor and greatest-common-divisor properties explicitly;
“greatest” here means every common divisor divides the result, including
the `(0, 0)` case, where the result is zero.

`checked` takes mathematical integers, rejects either negative input, and
otherwise converts both to naturals and returns the result. Theorems prove
rejection and the exact result for every nonnegative input; examples cover
both argument orders, zeros, coprime inputs and negative inputs. Integers and
naturals are unbounded in this model. To compare it with signed Forth cells,
assume the inputs are representable, the host supplies the intended signed
comparisons and nonnegative `mod` behavior, and there is sufficient stack
space. The model neither formalizes nor validates those assumptions.

This is **not a proof of the Forth source or its runtime**, and it establishes
no compiler, host, overflow, stack, or backend correctness. It produces no
LeanForth certificate and does not exercise the LeanForth kernel. The proof
relies on Lean's kernel and imported library, including its gcd theorems;
`#print axioms` reports `propext` and `Quot.sound` for the main correctness
theorem, and `propext` for negative rejection. There are no new axiom
declarations or admitted proofs in this file.

`GcdContract` is the word's contract, in the style of `ClampContract`
(plan task 1.5.3). `GcdSpec a b r` requires no result if `a` or `b` is
negative, and otherwise a natural `g` that divides both and that every
common divisor (an integer) divides; it does not mention Euclid's
algorithm or `Nat.gcd`. `natGcd_spec` proves that Lean's `Nat.gcd` of the
inputs, rejecting negative ones, meets it, and `checked_contract` that the
model does. Two deliberately wrong variants are refuted:
`checkedBothNegative`, a guard that rejects only when both inputs are
negative, at `(-1, 2)`; and `checkedOne`, which answers 1, a common divisor
of any two numbers, so that only the clause "every common divisor divides
g" rejects it, at `(2, 2)`. [`program-ir.lean`](../../tests/reference/program-ir.lean)
copies the contract and proves that the IR of `lf-gcd` meets the same
clauses, through a stated invariant of Euclid's loop
(`gcd_meets_contract`; see
[program IR](PROGRAM_IR.md#contracts-of-the-five-other-words)). `#print
axioms` reports `propext`, `Classical.choice` and `Quot.sound` for
`checked_contract`, `propext` for `checkedBothNegative_violates`, and
`propext` and `Quot.sound` for `checkedOne_violates`. The Forth unit tests in
`tests/program/examples.fs` separately exercise Euclid's long remainder chains
with consecutive Fibonacci inputs and the signed-cell extremes beside zero;
those are runtime tests, not consequences of this model.

Run from the repository root:

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --version
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --githash
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean tests/reference/gcd-reference.lean
```

The local run succeeded with Lean 4.35.0, revision
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. This reference is included in
`make reference`; CI status for this revision has not been established.
