# Proposed verified program: bounded clamp

Status: specification for review; a host Forth implementation exists and is
tested, but it is not verified.

The separate Lean oracle `tests/reference/clamp.lean` proves the range,
in-range and endpoint properties for an unbounded integer definition using Lean
4.35.0. A negative example checks that a faulty clamp cannot satisfy its bound.
It is a reference experiment, not a LeanForth implementation, a proof of a
Forth program, or evidence that the future importer supports these proofs.

`ClampContract` in `clamp.lean` combines the four properties as a predicate on
candidate functions; `clamp_contract` proves the model meets it. Two
deliberately wrong candidates are refuted by proof:
- `aboveEscapesClamp_violates_bounds` shows that returning an input above the
  interval violates the `clamp_bounds` statement.
- `swappedClamp_violates_contract` shows that returning the opposite
  endpoint violates the contract. `swappedClamp_in_range` proves that variant
  still stays in range, so the bound alone cannot reject it; its endpoint
  clauses do.

`tests/reference/clamp-invalid.lean` must be rejected by `make reference`. It
claims the `clamp_bounds` statement for the escaping clamp, using the proof
script that succeeds for the correct clamp, and states three false concrete
instances that `decide` rejects. These are Lean-model checks; no Forth
mutant is checked by them.

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
`clampCode_nonexpansive` additionally proves that for ordered inputs and
ordered bounds, their output distance is nonnegative and no greater than
their input distance, with independent modeled stack contexts. Distances use
unbounded integer subtraction; this does not establish finite-cell arithmetic.
`clampCode_nested` proves that, when one ordered interval is contained in
another, clamping first to the wider interval and then to the narrower one
produces the same result as clamping directly to the narrower interval. It
also preserves the modeled data-stack suffix and return stack at every call;
the caller removes each success flag before supplying the next input.
A further theorem proves that every modeled data stack with fewer than
three cells returns `none`, regardless of its values and return stack. Model
underflow is a policy rather than a claim about host behavior. The model assumes signed mathematical integers, zero as false,
and `-1` as true. `#print axioms` on the idempotence, monotonicity, nonexpansiveness, and nested-interval theorems
reports Lean's `propext`, `Classical.choice`, and `Quot.sound`; no LeanForth
axiom is added.

The more general `step_frame` and `execute_frame` theorems apply to every
instruction and finite program in this model, including branches and transfers
between the two stacks. If execution succeeds on a state, appending arbitrary
suffixes to its data and return stacks yields the same result with those
suffixes preserved. The success premise is essential: a program that
underflows on the original state can consume a cell from an appended suffix;
examples demonstrate this for `drop` and `fromReturn`. This result does not
assert isolation after failure or model finite stack capacity. Lean's axiom
audit reports `propext` for `step_frame` and `propext`, `Classical.choice`,
and `Quot.sound` for `execute_frame`.
The reference file's SHA-256 at this checkpoint is
`d010a8945e32f32acc17a5ed228e39a2d88e8301e5b42abf6159749cd8b971ce`.

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

The host suite also checks nonexpansiveness for those 784 ordered input and
interval combinations. It checks both success flags and computes the input and
output differences only over `[-3, 3]`, where subtraction cannot overflow a
standard Forth cell. This is finite runtime evidence, not a Forth proof.
It also checks three distinct data-stack cells and three return-stack cells
for each of the 343 small-domain triples, including both ordered and reversed
bounds; it checks the result and canonical flag before checking the markers.
This assumes adequate host stack space and provides finite evidence for this
word only, not the general frame theorem on arbitrary Forth programs.
At this checkpoint, `ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean
tests/reference/stack-clamp.lean` passed with Lean 4.35.0 revision
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; `XDG_CACHE_HOME=/tmp make
test-program` passed with Gforth 1.0.0 amd64. The stack differential also
passed with `XDG_CACHE_HOME=/tmp ELAN_HOME="$PWD/.tools/elan" make
test-program-stack-differential LEAN="$PWD/.tools/elan/bin/lean"` (686 cases).
CI was not run for this checkpoint. The Forth
test file SHA-256 is
`8a165216badb90969b8f037e78c544378a6cb9cffe64e3d6572c4ffd076bc4fe`.

On 2026-11-02 the host suite was extended at the actual cell width. The
differential samples only signed 32-bit values, which are mid-range on a
64-bit host, so these cases add the host extremes it misses:
- the reference check and the six-cell frame check run on all 343 triples
  drawn from `min`, `min+1`, `-1`, `0`, `1`, `max-1` and `max` of the host
  cell, including equal and reversed bounds;
- idempotence is checked for every ordered triple from that set;
- all of these checks use comparisons only, so no test arithmetic can wrap.

These cases reject implementations that compare by subtraction or truncate
values to 32 bits, which the Lean differential alone would accept. The suite
also records host behavior on underflow: `lf-clamp` with one of three inputs
missing, on an otherwise empty data stack, must throw -4. This holds on
Gforth 1.0.0 and the Ubuntu Gforth 0.7.3 package. It is not a LeanForth
guarantee: with caller cells present the word would consume them silently.
`make test-program` passed with Gforth 1.0.0, and the same file passed with
an extracted Gforth 0.7.3, both on x86-64 Linux.
