# ADR 0003: candidate conservative conversion

Status: proposed for human technical review. No theorem may be accepted using
this design until the rules, implementation and tests have been reviewed.
This describes a deliberately incomplete step toward Lean 4.35.0, not Lean's
complete definitional-equality algorithm.

## Purpose and inputs

The type checker needs to establish that two types agree. The candidate
procedure operates only on previously validated terms in a well-formed
context and the concrete-sort, variable, application, lambda and Pi fragment
of ADR 0002. Open subterms are interpreted under their current binder context;
the outer declaration type and value must be closed. Inputs, context,
allocation and result handles must be protected from concurrent mutation.

"Validated" here must mean more than syntactically scoped: before a comparison
can authorize a type-checking step, both compared expressions must be known to
be well typed in the same well-formed context. The type checker and conversion
procedure are mutually dependent; their ordering and termination argument are
still a review obligation, not established by the current prototype. In
particular, do not treat a successful untrusted scope scan as this precondition.
The reference oracle demonstrates why: Lean's `Kernel.isDefEq` reports an
ill-typed application equal to itself, while `Kernel.check` rejects it. Equality
alone is not evidence that either operand is well typed.

It returns `equal`, `unknown` or `resource-exhausted`. `equal` is intended to
be a sound sufficient condition for Lean definitional equality. `unknown` is
not inequality: the terms may be equal in Lean. A caller must never translate
`unknown`, a crash, a resource limit, or a failed check into `equal` or a
checked theorem. Malformed data and unsupported expression forms are handled
before this procedure, with their own diagnostics.

## Candidate algorithm

1. `whnf(t)` leaves a sort, variable, lambda or Pi at the head unchanged. For
   `App(f, a)`, first compute `whnf(f)`. If its result is `Lam(A, body)`,
   instantiate `body` with `a` using the capture-avoiding operation in ADR
   0002 and continue with the result. Otherwise retain `App(whnf(f), a)`.
   Subterms need not be normalized until comparison requires them.
2. `compare(t, u)` computes `whnf` on both. For two `Sort` nodes, return
   `equal` only if their concrete levels are identical. For two `Var` nodes,
   return `equal` only if their de Bruijn indices are identical. For two
   applications, recursively compare functions and arguments. For two lambdas
   or two Pi nodes, first require the domains to be structurally identical
   without reduction, ignoring binder names and annotations. If they are not,
   return `unknown` even if Lean could establish equality. Otherwise compare
   the bodies under the shared context extended by that domain. Return `equal`
   for these compound forms only when the required comparisons succeed.
3. Every other result, including different constructors, different indices,
   different levels or an inconclusive child comparison, is `unknown`. Propagate
   `resource-exhausted` when a required operation cannot finish within budget.
   Binder names and binder annotations do not affect this structural comparison.

The stricter binder rule avoids attempting body comparison when domains differ
syntactically, even if they are beta-convertible. For domains identical after
erasing binder names and annotations, the proposed representative is the left
domain; the equivalence of those contexts and preservation of body typing still
require human review. This is not a proof of soundness or a resolution of the
type-checking/conversion ordering obligation. A future extension to compare
merely convertible domains needs a separately reviewed context-conversion
argument. This change is newer than the owner's recorded review.

This intentionally does not return a general `not equal` verdict. Lean's
function eta and proof irrelevance can equate expressions that are not equal by
these structural and beta rules. Unfolding definitions, lets, recursors,
quotients, projections and symbolic universes is also outside this fragment.
Those require their own reviewed extensions. A type mismatch may only be
reported as Lean-invalid when independently justified by a reviewed rule;
otherwise a non-match is `unsupported`.

## Limits and state

All recursive traversal, beta steps, substitution, shifts and allocations draw
from explicit finite per-check budgets. Detect overflow before incrementing
indices or depths, and roll back or isolate temporary allocations on any
failure. Do not use the host call stack without a documented bound. The result
must be deterministic for a fixed term, context, limits and version. Any cache
must include the terms, binder context, relevant environment and resource
policy, and cannot turn an incomplete or exhausted result into `equal`.

The untrusted scope prototype and its raw mutable arena do not supply these
guarantees. They cannot be promoted to the trusted boundary without separate
review. No importer, Forth word, tactic or explanation can manufacture an
accepted theorem handle.

## Evidence and review

`tests/reference/core-oracle.lean` asks the pinned Lean kernel about beta,
dependent beta, binder names and annotations, function eta and proof
irrelevance. `tests/reference/substitution-oracle.lean` exercises open-term
shifts and instantiation. These tests characterize examples of Lean behavior;
they do not prove the candidate algorithm sound or test a LeanForth checker.

Before implementation, review the soundness of every `equal` case, binder
context handling, substitution and overflow, conversion callers, resource
limits and error propagation. Add positive and negative Lean comparisons and
tests that force each resource failure. In particular, confirm that the
candidate cannot make an ill-typed term or an unsupported Lean feature into an
accepted theorem. An expert human review is required by the project gate.
