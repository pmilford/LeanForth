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

`tests/reference/memory-sequence-reference.lean` combines the modeled copy
and swap operations. Its Lean proofs cover arbitrary address aliasing,
preservation of the remaining stack and unaffected cells, success exactly
when the four addresses are in range, and failures through a continuation.
It is checked by `make reference` and has the same abstract-model limits.

`tests/reference/memory-swap-involution.lean` proves that applying the modeled
swap twice restores the original abstract memory and stack when the addresses
are in bounds, including aliases. Out-of-bounds inputs fail through any
continuation. This reference is also included in `make reference`.

`make test-memory-frame-differential` compares 1,296 finite copy-then-swap
observations between the Lean step model and a test-only Gforth bounded-memory
fixture, including aliased and out-of-bounds addresses. On failure, it compares
the memory present immediately before the failing access; earlier writes are
not claimed to roll back. This is not a proof of the runtime or a general
comparison of Forth programs. It currently requires Gforth 1.0.0 and pinned
Lean 4.35.0; set `GFORTH`, `LEAN` and `ELAN_HOME` as needed. Because each swap
address is read before it is written, the two later swap-store failure paths
are unreachable in this fixture and are not covered by the table.
