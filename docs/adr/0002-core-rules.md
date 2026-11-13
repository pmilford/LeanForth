# ADR 0002: candidate first typing rules

Status: draft for human technical review; not approved or implemented. This
document describes a possible initial subset of Lean 4.35.0, not the complete
Lean kernel. The implementation must not confer theorem validity on the basis
of this draft before review. Follow the Lean reference and pinned implementation
when resolving any discrepancy.

Approval status: status unclear (no owner decision found); the ADR's own text says draft, not approved

## Inputs and boundaries

Terms are finite trees or acyclic DAGs constructed from `Sort(n)`, `Var(i)`,
`Pi(A, B)`, `Lam(A, body)`, and `App(fn, arg)`, where `n` and `i` are natural
numbers. A Pi or lambda binds one variable in its body, not in its domain.
Binder names and implicit/explicit annotations are presentation metadata;
they do not change the core typing rules. `Var(0)` means the nearest binder.
The root declaration type and value must be closed. Terms, indices, context
depths and levels are bounded by explicit resource limits; overflow, cycles,
unbound variables, invalid tags and truncated input fail closed.

This subset has no constants, axioms, declarations in context, inductives,
recursors, quotients, let expressions, projections, universe parameters or
symbolic level expressions. They must not be imported as trusted assumptions;
return `unsupported` until explicitly implemented and reviewed. The initial
axiom allowlist for these closed terms is empty.

## Candidate typing rules

Write `Γ ⊢ t : T` for term `t` having type `T` in a well-formed context Γ.
`Γ, A` extends Γ by a variable whose type is `A` in Γ. Type comparison below
means the supported conversion procedure, not pointer or source-text equality.

1. **Sort:** `Γ ⊢ Sort(n) : Sort(n+1)` if the level increment is in range.
   Lean's universes are not cumulative: a type at one level is not automatically
   accepted at a larger level.
2. **Variable:** If index `i` addresses the ith innermost context entry,
   `Γ ⊢ Var(i) : lift(i+1, Γ[i])`. Here each stored entry is represented in
   the context that existed before that entry was added. Lifting avoids capture
   when transporting its type into the full context. Index `i` outside Γ fails.
3. **Dependent function:** If `Γ ⊢ A : Sort(u)` and
   `Γ, A ⊢ B : Sort(v)`, then `Γ ⊢ Pi(A, B) : Sort(imax(u,v))`, where
   `imax(u,0)=0` and `imax(u,v)=max(u,v)` for positive concrete `v`. This
   accounts for Lean's impredicative `Prop = Sort(0)`.
4. **Lambda:** If `Γ ⊢ A : Sort(u)` and `Γ, A ⊢ body : B`, then
   `Γ ⊢ Lam(A, body) : Pi(A, B)`. Validate the constructed result and its
   context invariants; do not assume an imported binder is well-formed.
5. **Application:** Infer `fn`'s type and expose a Pi by supported reduction.
   If it is `Pi(A, B)`, infer `arg` and compare its type with `A`. On a
   supported match, the result type is `B[arg/Var(0)]` with capture-avoiding
   substitution. On a proven mismatch reject; if deciding requires an
   unsupported conversion or exceeds resources, return `unsupported` or
   `resource-exhausted`, never acceptance.

`lift(k, t)` means `shift(t, cutoff=0, amount=k)` using the candidate algorithm
below. For application, `instantiate(B, arg, depth=0)` substitutes the argument
and removes the consumed binder. These algorithms describe intended behavior,
not executable code; they require human review before kernel use.

### Candidate shift and single-variable instantiation

For `shift(t, cutoff, amount)`, a sort stays unchanged; `Var(i)` stays unchanged
when `i < cutoff` and otherwise becomes `Var(i + amount)`. Recurse into both
application children at the same cutoff. For `Lam(A, body)` and `Pi(A, body)`,
recurse into `A` at the same cutoff and into `body` at cutoff plus one.

For `instantiate(t, replacement, depth)`, a sort stays unchanged. For `Var(i)`:

- if `i < depth`, keep it because it refers to a locally traversed binder;
- if `i = depth`, replace it with `shift(replacement, 0, depth)`;
- if `i > depth`, use `Var(i-1)` because one outer binder is removed.

Recurse into both application children at the same depth; in a lambda or Pi,
visit the domain at the same depth and the body at depth plus one. Reject or
report resource exhaustion if index addition, depth, recursion, allocation or
work limits are exceeded; never wrap an index or accept a partial result. A DAG
node may occur at different binder depths, so any memoization key must include
the relevant cutoff or depth and substitution state.

### Candidate declaration acceptance

For the first closed, axiom-free fragment, a theorem request contains a declared
type `T` and value `v`. Before creating any handle, validate the representation
and closure of both terms; infer `T` and establish that its type converts to
`Sort(0)`; infer `v` and establish that its inferred type converts to `T`.
Only if every required check returns a supported, definite success may the
checker issue a theorem handle bound to that exact immutable claim and value.
For a definition rather than a theorem, the inferred type of `T` must instead
convert to some supported `Sort(n)`; a definition must not be labeled a theorem
unless its declared type is a proposition. Name uniqueness, atomic registration,
trusted storage and persistence still need a separate reviewed design.

The entire operation fails closed: an invalid structure, failed inference,
unsupported form, conversion `unknown`, allocation failure, timeout or other
resource exhaustion produces no theorem handle and leaves the previous
environment unchanged. No side channel, explanation, test result or importer
status may set the checked bit. This proposal is not an implementation.

`tests/reference/declaration-oracle.lean` calls Lean's kernel declaration API
with checking enabled. It tests a valid closed identity theorem, a mismatched
proof, a non-type used as a declared type, a non-proposition theorem, and the
same non-proposition as a valid definition. These are Lean reference results,
not tests of a LeanForth declaration interface.

The Lean reference `tests/reference/substitution-oracle.lean` exercises shifts
and instantiation on deliberately open expressions using the pinned Lean
toolchain's expression operations. Those are syntax-manipulation tests, not
Lean kernel acceptance of the open expressions and not LeanForth tests.
`tests/reference/transform-model.lean` also implements these candidate rules as
an untrusted Lean test model and compares them with Lean's operations across
155 generated expression shapes, 16 shift configurations per shape, and 55
replacement terms per shape. This finite comparison does not prove the rules,
handle Forth cell limits, or approve an implementation for the trusted kernel.
Untrusted Forth shift and single-binder instantiation experiments are compared
with Lean on 80 and 25 cases respectively and have separate resource and
malformed-input tests. They have not been reviewed for trusted use.

## Conversion and incompleteness

At minimum, conversion must account for structural identity ignoring binder
names, concrete-level equality, and beta reduction with capture-avoiding
substitution. Lean's full definitional equality also includes function eta,
proof irrelevance, and reductions involving declarations, inductives, lets and
quotients. These rules are not specified here. An incomplete conversion engine
must not claim that a failed comparison means Lean would reject the declaration;
report `unsupported` unless mismatch is established within the supported
fragment. Resource exhaustion is distinct from both rejection and acceptance.
Lean's definitional equality has subtleties, including non-transitivity in the
full system; do not replace it with an assumed equivalence relation.
The conservative initial proposal may still return `unknown` for beta-equivalent
binder domains when their syntax differs; beta support does not imply that all
Lean beta equalities are recognized.

## Review and test gates

Before implementing these semantics, a human reviewer must inspect these rules,
the representation of contexts and binder shifts, the concrete conversion
algorithm, failure classifications, axiom handling and the trust boundary.
Compare positive and negative cases with pinned Lean, including non-cumulative
sorts, impredicative Pi, identity, composition, binder selection, substitution
under binders and beta conversion. Malformed DAGs and resource limits additionally
need host-level tests. The current Lean source cases and NDJSON fixture establish
only reference behavior; they do not yet test a LeanForth kernel.
`tests/reference/core-oracle.lean` additionally exercises constructed core
expressions through Lean's kernel API without relying solely on source
elaboration; its results still are not LeanForth differential tests. That
oracle also exercises function eta and proof irrelevance, which this candidate
fragment does not yet specify and must not silently reject as Lean-invalid.

`tests/reference/type-model.lean` is an untrusted executable model of parts of
the draft rules. It compares inferred types with `Lean.Kernel.check`, including
identity and composition and 105 generated cases. The observed generated run
had 26 matching inferred types, 79 cases where neither produced a type, and no
case where only the model was inconclusive. This is finite evidence, not a
proof of the rules or a LeanForth implementation. The model delegates beta
instantiation to Lean, uses unbounded natural numbers and recursion-depth fuel,
and does not implement a shared total-work budget or a declaration interface.
Its conversion preconditions and binder-context obligations remain open.

References: Lean 4.35.0 `Lean/Expr.lean` distributed with the toolchain;
https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/ and
https://lean-lang.org/doc/reference/latest/The-Type-System/ . Reference URLs are
moving documentation; pin or archive the exact version before treating them as
the reviewed normative specification.
