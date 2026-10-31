# ADR 0004: symbolic universe representation — proposal

Status: **draft for human review; not approved for a trusted kernel**. This
proposal extends the concrete-only scope in ADR 0002 and does not resolve its
conversion soundness obligations. The current Forth experiments store syntax
and evaluate concrete graphs; they cannot check a polymorphic declaration.

## Motivation and proposed syntax

Lean declarations and Mathlib use named universe parameters. Propose finite
acyclic DAGs with nodes `zero`, `succ(u)`, `max(u,v)`, `imax(u,v)`, and
`param(name)` corresponding to Lean 4.35.0 `Level`. Successor and binary edges
point to earlier nodes; parameter names must resolve to entries in the
declaration's explicit parameter list. Name equality must use Lean's structured
names, not mutable host addresses or merely arbitrary numeric indices.
Lean level metavariables are outside this proposed declaration subset and must
be reported as unsupported rather than interpreted as parameters or zero.

For concrete natural-valued assignments, `succ(u)` adds one, `max` chooses the
maximum, and `imax(u,0)=0` while `imax(u,v)=max(u,v)` for positive `v`. These
equations do not specify Lean's full symbolic level equivalence or conversion.
Expressions must retain symbolic structure and parameter scope; substituting an
arbitrary number for an unknown parameter does not establish a polymorphic
claim. A future checker needs Lean-compatible level instantiation, equality and
normalization, universe-context validation, overflow/resource handling, and a
soundness argument for their use in sort and Pi typing.

## Experiment and trust boundary

`src/experimental/levels.fs` allocates a separate global 64-node arena with an
implicit zero at index zero and opaque positive numeric parameter identifiers.
Its constructors check basic bounds and backward references; they do not
establish name identity, parameter binding, well-formedness after raw mutation,
level equivalence or typing. Reset invalidates handles, storage is mutable and
host-specific, and no serialized format or trusted API is defined. It is not
connected to expression `Sort` nodes, inference or the declaration probe.
The prototype uses `2drop` and `0<=` in addition to basic Forth words; these
host requirements must be accounted for when targeting another Forth system.
`src/experimental/level-scope.fs` experiments with bounded shape and parameter
ID checks; it does not provide structured-name identity or an immutable context.
`src/experimental/level-value.fs` evaluates concrete graphs only; symbolic
graphs return unknown unless its separate instance evaluator receives explicit
numeric assignments. An instance is not a polymorphic equality judgment.
`src/experimental/level-compare.fs` explores a conservative equality rule:
after checking both graphs, identical syntax under one ID-to-name mapping may
match; otherwise two unassigned, concrete evaluations may match if their values
are equal. All other cases are unknown. No finite assignment sampling may
authorize symbolic equality. This is a proposal and untrusted diagnostic, not a
reviewed kernel conversion rule. The mapping from opaque IDs to Lean names,
context ownership and its interaction with typing remain unresolved.
An independent AI review of this later scope experiment was requested but did
not complete because the reviewer hit its usage limit. No review or approval
of that experiment should be inferred from the earlier level-arena review.

The development NDJSON preview preserves a symbolic graph and a real pinned
polymorphic export as unchecked data. Its concrete-only transport rejects that
fixture. Neither the preview nor this Forth arena grants theorem validity.

## Questions and evidence for review

- Does the proposed representation preserve Lean names, parameters, sharing,
  instantiation and sort semantics across import and storage? How are parameter
  scopes represented independently of untrusted mutable indices?
- What level equivalence and simplification rules are sound and complete enough
  for the intended fragment, particularly `imax` with symbolic right operands?
  How does this interact with Lean's kernel conversion and its resource limits?
- How are stale handles, cyclic or corrupted nodes, resource exhaustion and
  concurrent mutation excluded from a trusted declaration boundary?
- Which Lean differential, malformed-input, round-trip and soundness evidence
  is necessary before any rule or implementation can confer theorem validity?

Human review of these rules and the actual implementation is required before
trusted use. Current storage tests and concrete-level differential examples are
finite evidence only; they are not a proof of symbolic compatibility.
