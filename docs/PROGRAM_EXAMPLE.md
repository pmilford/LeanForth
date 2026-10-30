# Proposed verified program: bounded clamp

Status: specification for review; not implemented or verified.

The separate Lean oracle `tests/reference/clamp.lean` proves the range and
in-range properties for an unbounded integer definition using Lean 4.35.0.
It is a reference experiment, not a LeanForth implementation, a proof of a
Forth program, or evidence that the future importer supports these proofs.

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
Sample executions are tests, not proof that compiled code implements the model.
The program model, proof rules and connection to execution require human review.
