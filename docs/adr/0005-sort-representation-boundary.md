# ADR 0005: distinguish concrete and symbolic Sorts — proposal

Status: **proposed; human review required before trusted implementation**.
This extends ADR 0004. It does not approve a kernel, importer, or theorem.

## Problem

Concrete inference interprets `lf-tag-sort`'s payload as a universe number.
The excluded symbolic draft interprets that same tag and payload as an index
into a mutable level arena. If index 1 refers to parameter `u`, the node
`(sort, 1, 0)` cannot reveal whether it means `Sort 1` or `Sort u`. A consumer
can silently apply the wrong rule. Comments and equal numbers cannot establish
polymorphic correctness.

## Proposed boundary

1. Give concrete and symbolic Sorts distinct tags and constructors. Retain
   structured symbolic levels; a tag alone does not validate a level graph.
2. At each semantic operation's public boundary, validate every reachable
   term in every input for its expected representation, node shape and child
   ordering, with a finite shared budget. Reject mixed representations even
   inside subterms that reduction might discard. Sort-free terms can be used
   by either mode. Fail closed on malformed data or exhaustion.
3. Scope, shifting, substitution and reduction may share representation-neutral
   internals that preserve either tag, but public entry points must declare the
   expected mode and validate all operands. Comparison must distinguish tags;
   symbolic equality may only use validated live level references and sound
   level rules. Unknown is not equality or theorem acceptance.
4. Bind symbolic term storage to a level-arena generation. Reset, generation
   saturation, context ownership and stale term handles must fail closed; a
   reused integer index is not evidence of the same universe. Mutable global
   arenas and raw memory writes remain experimental host assumptions.
5. Concrete inference, declaration probes and the current concrete staging
   path reject symbolic Sorts. A symbolic path validates its own parameter
   context and level graphs; specialization explicitly evaluates levels
   before constructing concrete terms. Representation validation alone does
   not accept a proof.

An implicit global mode cannot authenticate mixed terms. Replacing parameters
with sampled numbers does not establish a polymorphic judgment. Separate
complete arenas could provide stronger separation but duplicate traversal and
lifetime logic; they remain an option if tagged storage cannot be audited.

## Required evidence and review

Test both modes with equal numeric payloads, wrong tags at every child position,
both inputs of multi-root operations, malformed references, stale generations,
context changes, exhaustion and rollback. Compare supported universe typing
cases with pinned Lean 4.35.0; finite differential cases do not prove soundness.
An independent AI review identified the tag, validation and generation
requirements; it is not human approval. A human must review this proposal and
the actual implementation before kernel semantics are accepted or merged.

The opt-in `make test-symbolic-infer-draft` exercises the existing **unsafe**
draft and checks a symbolic Pi universe against Lean. It intentionally does not
establish this proposed boundary. The draft remains outside the standard suite.

`src/experimental/tagged-sort-boundary.fs` separately tests a tagged Sort and
a bounded reachable-syntax representation validator. Its results are not wired
into symbolic inference, level checking, or declaration acceptance. In
particular, symbolic indices are not bound to a level arena generation, and
the validator checks neither level scope nor type correctness. Existing concrete
inference and shift tests reject the new tag, but this does not show that every
consumer enforces the proposed boundary. Unreachable nodes are intentionally
outside the syntax check; shared nodes cost fuel on each visit.
