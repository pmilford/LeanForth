# ADR 0001: initial core fragment

Status: proposed; human review required before kernel implementation.

Approval status: status unclear (no owner decision found); the ADR's own text says proposed

## Goal

Check proof terms for dependent functions and use the same logical core to
support specifications of executable programs. Lean 4.35.0 is a differential
reference; this initial fragment is not a claim of Lean compatibility.

## Proposed scope

Consider sorts, de Bruijn variables, dependent function types, lambda
abstraction and application. Specify universe levels, contexts, well-formedness,
substitution, conversion and resource limits formally before implementing them.
The fragment must not accept undeclared constants, unbound variables or malformed
terms; features not explicitly supported must produce an unsupported diagnostic.
There are no added axioms. Do not conflate the host Forth stack with the logical
context. Kernel-accepted theorem handles must originate only from checked terms.

## Representation alternatives

An indexed arena makes handles compact, supports sharing and can be serialized
without host pointers, but requires checked indices, lifetime rules and bounds
on allocation. Pointer-linked nodes make early traversal simple, but complicate
portable serialization, ownership and validation. Prefer an indexed arena for
experimentation; its layout, sharing and reclamation are not yet approved.
Per-check arenas simplify lifetime reasoning; reference counting can reclaim
individual nodes but increases trusted bookkeeping and risks cycles. Benchmark
only after correctness and limits are specified. Serialization is untrusted input
and must be validated before terms reach the checker.

## Acceptance and review

- Accept the function-composition example in `tests/reference/` and reject the
  mismatched intermediate type; compare corresponding results with Lean.
- Cover identity, unbound variables, malformed terms, variable capture, wrong
  application types and resource exhaustion with positive and negative cases.
- Define exact universe and conversion rules and the Lean subset being compared;
  document any unsupported cases rather than accepting them as axioms.
- Have a human review the rules, tests, trusted boundary and axiom policy before
  kernel semantics are implemented or merged.

## Executable-program boundary

The proposed bounded clamp example must specify the integer model, bounds and
input assumptions. A proof about that model does not prove that host cell
arithmetic, generated Forth, an FFI or a native backend implements it. Report
those runtime assumptions separately; no verifier or runtime proof exists yet.
