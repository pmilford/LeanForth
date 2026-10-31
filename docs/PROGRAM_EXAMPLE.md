# Proposed verified program: bounded clamp

Status: specification for review; a host Forth implementation exists and is
tested, but it is not verified.

The separate Lean oracle `tests/reference/clamp.lean` proves the range,
in-range and endpoint properties for an unbounded integer definition using Lean
4.35.0. A negative example checks that a faulty clamp cannot satisfy its bound.
It is a reference experiment, not a LeanForth implementation, a proof of a
Forth program, or evidence that the future importer supports these proofs.

`tests/reference/stack-clamp.lean` separately defines a finite stack-machine
semantics for the operations in the host word. Pinned Lean checks that this
model implements the clamp specification and preserves arbitrary modeled data
and return-stack suffixes; for ordered bounds it also proves the result is in
range. Model underflow returns `none`, a model policy rather than a claim about
host behavior. The model assumes signed mathematical integers, zero as false,
and `-1` as true. `#print axioms` on both model theorems reports Lean's
`propext`, `Classical.choice`, and `Quot.sound`; no LeanForth axiom is added.
The reference file's SHA-256 at this checkpoint is
`a418e7ccc979cd972453b96a235b3299c3518d31a877b652193e7a2531187563`.

This is a handwritten model, not a semantics-preserving translation from Forth
source. It abstracts return addresses, control flow, finite stack capacity and
host word behavior. The Lean proof establishes the model's result under its
semantics, not the compiled Forth word or the LeanForth kernel.

For mathematical integers `lower`, `upper`, and `value`, assume
`lower <= upper`. Define the result as `lower` if `value < lower`, `upper` if
`value > upper`, and `value` otherwise. A successful verification should show:

- The result lies between `lower` and `upper`, inclusive.
- If the input lies within those bounds, the result equals the input.
- If the input is below or above the interval, the result equals the
  corresponding endpoint.
- The computation terminates for every input satisfying the precondition.

Negative cases must reject an implementation that swaps endpoints or returns
an input outside the interval. A reversed interval is a failed precondition,
not a verified result. Proof artifacts must identify the exact specification
and assumptions.

The initial mathematical model uses unbounded integers. A Gforth execution
example must separately state the host cell range, conversion and comparison
semantics, input representation, and the assumed correctness of the host.
The ordinary Forth word `lf-clamp` in `src/program/clamp.fs` uses signed host
cell comparisons; reversed bounds return `false` without a result. Run
`make test-program` for sample tests. The Lean proofs do not establish the
behavior of this word or its host. Sample executions are tests, not proof that
compiled code implements the model.

`make test-program-differential` compares the Lean model and Forth word on
343 triples in `[-3, 3]` and 343 triples drawn from signed 32-bit endpoints,
their neighbors, and `-1`, `0`, and `1`, including reversed bounds. It requires
pinned Lean and Gforth; see the README for
local toolchain selection. This provides finite cross-runtime evidence only:
it does not connect the Lean proof to the Forth source, prove cell arithmetic or
the compiler, or cover inputs outside those sets. The endpoint cases were run
on the available Gforth hosts; they do not establish execution on a 32-bit host.
The program model, proof rules and connection to execution require human review.
`make test-program-stack-differential` compares 686 executions of the proved
stack model with the Gforth word. Host tests also exercise preservation of one
data-stack prefix and a caller's return-stack value on both branch paths. These
are finite runtime tests, not a proof of the host or compiler.
