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
range. For ordered bounds, `clampCode_idempotent` proves that feeding the
first result back into the modeled clamp with the same bounds returns that
result again, preserving arbitrary surrounding stacks in both executions.
`clampCode_monotone` proves that two ordered inputs clamped to the same
ordered interval produce ordered results, even when either input is outside
the interval; the executions may have different surrounding stacks. This
supports reasoning about composition with order-sensitive modeled code.
`clampCode_nested` proves that, when one ordered interval is contained in
another, clamping first to the wider interval and then to the narrower one
produces the same result as clamping directly to the narrower interval. It
also preserves the modeled data-stack suffix and return stack at every call;
the caller removes each success flag before supplying the next input.
A further theorem proves that every modeled data stack with fewer than
three cells returns `none`, regardless of its values and return stack. Model
underflow is a policy rather than a claim about host behavior. The model assumes signed mathematical integers, zero as false,
and `-1` as true. `#print axioms` on the idempotence, monotonicity, and nested-interval theorems
reports Lean's `propext`, `Classical.choice`, and `Quot.sound`; no LeanForth
axiom is added.
The reference file's SHA-256 at this checkpoint is
`70ae7e84f9555160655cecd2dbb0c49e0da49b69102ec3b2cd7229508e8f8d9f`.

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
`make test-program` also checks host-word idempotence by feeding each successful
result back through `lf-clamp` with the same bounds for all 196 ordered triples
in `[-3, 3]`. Both success flags and the repeated result are checked; reversed
bounds are covered separately and are excluded from this composition test.
It also exercises `clampCode_nested`'s composition property on the host for
all 1,470 combinations of a value and nested intervals with endpoints in
`[-3, 3]`, including equal endpoints and equal intervals. Each of the three
calls must succeed, the composed and direct results must agree, and a
data-stack prefix must survive. This is finite regression evidence under the
host's signed-cell comparison and stack behavior assumptions, not a proof that
the host word implements the Lean model; return-stack preservation for nested
calls is not established by this test.

The host suite also tests the model's `clampCode_monotone` property for all
784 combinations of ordered intervals and ordered input pairs in `[-3, 3]`,
including equal values and values outside the interval. Both calls must return
the canonical true flag, preserve their distinct data-stack and return-stack
markers, and produce ordered results. This is finite host regression evidence;
it does not establish the modeled property for all host cells or prove that
the host implementation follows the Lean model.
