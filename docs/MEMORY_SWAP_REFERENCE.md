# Abstract memory-swap reference

`tests/reference/memory-swap-reference.lean` models a program that reads two
cells and writes their values to the opposite addresses. Pinned Lean checks
that, when both addresses are in bounds, it preserves the complete stack,
exchanges the values and leaves all other cells unchanged. Aliased addresses
leave memory unchanged. Either out-of-bounds read fails even when followed by
more instructions, and a concrete negative case refutes a copy-like result.

Run it through `make reference` (Lean 4.35.0 is pinned by that target). These
claims concern the handwritten abstract model with natural-number addresses
and mathematical integer values. They are not proofs of Forth runtime,
compiler, byte layout, finite-width addresses or hardware behavior. No new
axioms or `sorry` are introduced; execution proofs use Lean's existing
`propext` and `Quot.sound` foundations. Human review remains required before
using any model across the trusted verification boundary.
