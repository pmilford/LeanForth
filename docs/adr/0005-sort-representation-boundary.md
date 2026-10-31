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
into symbolic inference or declaration acceptance. The syntax validator alone
checks neither level scope, generation nor type correctness. Existing concrete
inference and shift tests reject the new tag, but this does not show that every
consumer enforces the proposed boundary. Unreachable nodes are intentionally
outside the syntax check; shared nodes cost fuel on each visit.

`src/experimental/symbolic-session.fs` now combines tagged syntax checks with
reachable level/context checks and captures the term, level and parameter-context
generations at session start, which requires an empty term arena. A reset or
context change invalidates the session. This is an untrusted development
consumer, not yet integrated with symbolic inference. Term resets now advance
an experimental term generation and saturate instead of wrapping. A bare term
index reused in a later newly started session is still indistinguishable from
an old caller handle; a stale bare level index used to construct a Sort in a new
session has the same problem. Raw mutation of arena counters and slots is also
outside the session assumptions. No immutable ownership or production handle contract
has been established. Term syntax passes, term level passes, and level graph
visits share fuel; bounded quadratic context validation is outside that budget.

The untrusted `generation-handles.fs` experiment now returns pairs of index and
non-repeating allocation identity. Term and level identity serials never
roll back and fail rather than wrap; the implicit zero level gets a new identity
on reset. Tests exercise reset, rollback and reuse, and counter saturation.
The pair is forgeable and has no arena-kind tag. The handle-based term checker
now separately records the allocation identity of every Sort created with its
constructor, and checks it on every reachable Sort. A cross-arena level rollback
and replacement is rejected even if the replacement is otherwise valid. Raw
Sorts lack this stamp and fail this handle-based check. This does **not** protect
the raw session or inference paths, which still use bare level indices. Under
append-only allocation and suffix rollback, same-arena parents cannot survive
the removal of earlier children; arbitrary count restoration and raw mutation
are outside this assumption. All raw Forth words remain accessible, and no
consumer may treat this development check as a trusted interface.

`tagged-infer.fs` now uses the handle-based input check for a restricted
Sort, Pi, bound-variable, lambda and application fragment. An application
requires a directly visible Pi and a conservative syntax-only argument-type
comparison; other cases return `unknown`. Tagged shifting and substitution
preserve Sort stamps. These components are untrusted, and separate calls have no shared outer
transaction or enforced combined budget for separate public calls. Within one
inference, binder shifts use its remaining budget and failure restores both
arena counts. The tagged inference test and pinned Lean oracle check limited
Sort/Pi universe expectations; the binder differential compares 18 finite
actual inferred types and rejections at three concrete universe assignments;
the application differential adds 12 finite valid and invalid cases.
These are not broad Lean compatibility results or a proof of soundness.
