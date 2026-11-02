# Checked declaration environment: proposal for human review

**Status: proposed; not approved or implemented.** An expert human review is
required before trusted implementation or merge. This document presents
[ADR 0006](adr/0006-constant-environments.md) for decision; it does not grant
approval or establish that LeanForth can accept a theorem.

## Decision and trust boundary

The proposed first checked environment is a protected, immutable collection
of named declarations: initially, safe nonrecursive definitions and theorems.
A declaration records its full structured name, universe parameters, type,
value, kind, safety, dependencies and axiom provenance. A universe parameter
describes a level in Lean's hierarchy of types; a `Sort` is a type at such a
level. A theorem is a proposition together with a proof term. The kernel is
the small trusted checker that must establish that the term has the claimed
type. Both the theorem and verified Forth program paths ultimately need this
shared checking infrastructure.

The kernel must check each declaration against an already checked environment
before adding it. Names are unique; references must resolve to earlier checked
records or specifically authorized axioms. Parsing, export order, hashes,
candidate signatures, tactics, LLM output and diagnostic success provide no
such authority. The proposed first scope rejects or reports unsupported
recursive and mutual declarations, unsafe or partial declarations,
inductives, recursors, quotients and other unreviewed forms. Unsupported or
resource-limited checks never become accepted results. This restricted start
does not change the goal of using the full Mathlib library.

For every declaration, the proposed checker validates closed terms and
universe scope, checks that the declared type itself has a sort, checks the
value against the declared type and, for a theorem, checks that its type is a
proposition. References must supply exactly the number of universe arguments
declared by the target. Substitution is simultaneous and respects the separate
caller and callee scopes, including levels inside nested constants and sorts.
Conservative conversion may return unknown; definition unfolding is a
separate review decision, and theorems, axioms and opaque declarations are not
unfolded under this proposal.

## Transactions and snapshots

A snapshot is the complete environment seen by a check. The proposed operation
checks and allocates a candidate in isolated staging against one prior
snapshot. Only after every check succeeds does it atomically publish a new
immutable snapshot and a checked handle. Rejection, unsupported input,
exhaustion or interruption publishes neither; the prior snapshot remains
unchanged. Earlier snapshots and their handles must remain valid while in use,
or their handles must be explicitly invalidated. Handles and caches must bind
to snapshot identity and non-reused lifetimes; stale or cross-snapshot uses
fail closed. Cache keys also include relevant context, universe substitution
and policy, and an inconclusive result cannot be cached as success.

For example, suppose snapshot `S0` contains a checked polymorphic identity
definition `id` with type `∀ A : Sort u, A → A`. A proposed definition `useId`
that refers to `id` with exactly one well-scoped universe argument and whose
body checks against its declared type may be published as `S1`. A later check
using `S1` can refer to `useId`; a check using `S0` cannot. This example
assumes all required core typing and conversion rules have been reviewed and
implemented; it is not a claim of current LeanForth acceptance.

If a candidate instead refers to `id` with zero universe arguments, or refers
to itself before it has been accepted, the transaction rejects it. No `useId`
entry or checked handle appears, and `S0` remains usable and unchanged. A
failed allocation or interrupted check has the same publication outcome;
unsupported conversion is inconclusive rather than evidence that a valid Lean
declaration is false. Snapshots do not by themselves specify memory ownership,
concurrency or crash recovery; those designs require review.

## Axiom policy

Start with an empty allowlist. An axiom is an assumed declaration rather than
a proved theorem. A future entry requires explicit human approval of its full
structured name, ordered universe parameters, exact type, safety and
provenance, under a versioned, auditable policy. Its type must itself be
well formed in the prior environment. A matching name alone is insufficient;
changed types and unauthorized entries are rejected. Each accepted result
must report the complete transitive set of axioms on which it depends. Lean's
standard axioms are not silently authorized, and unsupported declarations are
not converted into axioms. The empty initial policy limits which legitimate
Lean and Mathlib results can be accepted until particular assumptions are
reviewed.

## Decisions requested from reviewers

1. Are the initial declaration kinds, dependency ordering, closure and
   proposition checks sufficiently precise and sound? Which unsupported cases
   must be rejected versus reported as unsupported?
2. Are exact universe arity, scope, simultaneous substitution and symbolic
   equality rules correct, including caller/callee name collisions? What
   precise symbolic conversion rules may be trusted initially?
3. Is the conservative conversion boundary acceptable, and should checked
   safe definition unfolding be deferred to a separate reviewed extension?
   How will its work bounds and Lean's definition hints versus opaque
   declarations be handled?
4. Is the empty initial axiom policy and exact, versioned authorization and
   transitive reporting procedure acceptable? Who approves future entries and
   how are policy changes and existing results audited?
5. What concrete snapshot identity, ownership, lifetime, invalidation,
   generation-overflow, concurrency and recovery design provides atomic
   publication and prevents stale handles, cache reuse or partial commits?
6. What evidence and review of the actual trusted implementation and import
   boundary are required before use or merge? Approve a test matrix covering
   the positive and negative cases in ADR 0006, including fault injection and
   a valid proof and invalid proof, plus pinned Lean kernel comparisons.

These are requests for decisions, not a record of decisions made. An expert
human must review semantics, implementation and evidence; AI review and finite
tests cannot replace that review.

## Evidence, gaps and tradeoffs

ADR 0006 records direct pinned Lean 4.35.0 kernel oracle cases for selected
valid and invalid declarations, constant references and universe substitution.
It also records experimental untrusted mixed-term operations and finite Lean
comparisons. The current mixed inference diagnostic can infer a fixture only
conditional on an assumed signature; it neither checks that dependency nor
creates a checked declaration. The NDJSON preview and test-only fixture
transport do not import or independently validate declarations. The Lean
source observations in the ADR are useful evidence, but are not a direct
audit of the kernel implementation. None establishes a trusted LeanForth
checker, transactional checked environment or general Lean compatibility.

The [project status](PROJECT_PROGRESS.md) snapshot dated 2026-11-01 reports
zero of four full NDJSON importer acceptance tasks complete and zero of five
full Mathlib acceptance tasks complete; no Mathlib declaration has been
independently accepted by LeanForth. The full declaration denominator is not
pinned. These task counts are not estimates of remaining effort. The program
track has Lean reference models and finite runtime comparisons, but no shared
trusted LeanForth checker or proof of source-to-runtime correspondence.

Open tradeoffs include conservative conversion's false inconclusives versus
the complexity of Lean-compatible conversion; retaining old snapshots versus
explicit handle invalidation and memory cost; and an initially empty axiom
policy versus compatibility with results that rely on reviewed assumptions.
The concrete transaction identity scheme, general symbolic level equality,
broader declaration forms, scalable library import and resource limits remain
unresolved. Required differential tests, malformed-input and failure-path
tests, lifetime and policy tests, implementation review and human approval
remain future work. This document reports existing recorded evidence; no tests
or CI runs were performed to prepare it.
