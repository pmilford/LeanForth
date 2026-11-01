# ADR 0006: constant environments — proposal

Status: **draft for human review; not approved or implemented**. This proposes
a conservative extension of ADRs 0002–0005, not full Lean compatibility.
The existing experimental probes and NDJSON preview do not validate or
register declarations. No theorem may be accepted on this proposal alone.

## Candidate contract

- A check uses one protected, immutable environment snapshot mapping full
  structured Lean names (ADR 0005) to immutable declaration records: kind,
  ordered distinct universe parameters, closed type, value where applicable,
  safety, dependencies and axiom provenance. No shadowing or duplicate names.
  Lookup of `Const(name, levels)` requires an existing record validated under
  this snapshot's prior environment, or an explicitly authorized axiom below.
  Unknown, forward, self, cyclic and unsupported references cannot be assumed.
  Start with nonrecursive safe definitions and theorems; reject or report
  unsupported for mutual blocks, unsafe/partial declarations, inductives,
  recursors, quotients and other unreviewed features. A later extension needs
  its own rules rather than interpreting those records as axioms.
- Validate each parameter list and all level expressions in the declaration's
  type and value: names are distinct, each parameter occurrence is in scope,
  and unsupported metavariables, malformed graphs and overflow fail closed.
  Parameters may be unused. A reference supplies **exactly** as many levels as
  the target has parameters: monomorphic means zero, polymorphic means the
  ordered list length, independent of the number of term arguments. Validate
  actual levels in the *caller's* universe context before inference.
- Infer the constant's type by simultaneously substituting actual levels for
  the target's formal parameters by structured name and position throughout
  the stored type, including sorts and universe arguments of nested constants.
  Actual levels may themselves contain caller parameters; do not recursively
  substitute within a replacement or confuse same-named caller and callee
  scopes. Preserve `succ`, `max`, `imax` and symbolic structure; arbitrary
  concrete instantiations do not prove a polymorphic declaration. Apply the
  same substitution to a definition's value when unfolding. Level equality
  remains governed by reviewed symbolic conversion, not syntactic sampling.
- Check each proposed declaration against the prior snapshot, never itself:
  validate closed terms and universe scope, infer that its declared type is a
  sort, check its value against that type, and require a theorem's type to be
  a proposition as in ADR 0002. Publish only after all checks succeed. A
  definition or theorem may depend only on already accepted records, with
  transitive assumptions computed from those records. Imported names, export
  order, hashes and successful parsing are not proof of validation.
- Keep the initial axiom allowlist empty. Any later entry requires explicit
  human approval of its structured name, exact universe parameters and type,
  safety and provenance, with versioned policy and an audit trail; a name alone
  is insufficient. Check that an authorized axiom's type is well formed in
  the prior environment, reject altered or unauthorized entries, and record
  and report the complete transitive axiom set with each accepted result.
  Do not silently authorize Lean's standard axioms or turn unsupported
  declarations into axioms.

## Conversion and state

Initially permit constant typing with conservative conversion: identical
constant heads may compare equal only with reviewed equality of all universe
arguments; unknown remains unknown. Definition unfolding is a separately
reviewed extension: unfold only a previously checked safe definition, with its
instantiated value and bounded work. Axioms, theorems and opaque declarations
must not be unfolded in this proposed kernel conversion. In Lean's source,
`.opaque` *reducibility hints on definitions* guide unfolding order and do not
make a definition opaque; elaborator transparency attributes are distinct.
Do not mistake either for an opaque declaration. Missing delta, eta, proof
irrelevance or symbolic equality can make a valid Lean case inconclusive.

Make registration transactional: validate and allocate in isolated staging,
then atomically publish the complete immutable snapshot and checked handle.
On any rejection, unsupported operation, resource exhaustion or interruption,
publish nothing and leave the previous snapshot unchanged. Handles and caches
must bind to snapshot identity, arena kind and non-reused generation/lifetime;
stale or cross-environment references fail closed even after rollback, reset,
reuse or generation exhaustion. Preserve old snapshots while live handles use
them, or explicitly invalidate those handles. Include environment, universe
substitution, context and policy in cache keys; never cache inconclusive or
exhausted results as success. Serialized references encode structure, not host
pointers or unauthenticated arena indices. Ownership, concurrency, generation
overflow and recovery need a concrete reviewed implementation design.

## Required tests and review

Before trusted implementation, add direct pinned Lean kernel oracle and
LeanForth differential cases for zero, exact, too few and too many levels;
unknown, duplicate, forward and self names; earlier valid/invalid dependencies;
and invalid type/value versus valid definition/theorem. Exercise two parameters
in swapped order, nested `max`/`imax`, levels in nested constants and sorts,
caller/callee name collisions, unused and unbound parameters, and repeated
substitution without capture. Compare inferred types and accept/reject results,
distinguishing Lean acceptance from LeanForth `unsupported`.

Add conversion tests for checked definitions at concrete and symbolic levels,
opaque/theorem non-unfolding, hints versus opaque declarations, and cases
requiring unsupported conversion. Test exact allowlist matches, altered types,
unauthorized axioms and transitive assumptions. Independently test malformed
DAGs, invalid IDs, policy changes, interruption, every allocation/budget failure,
rollback, reset/reuse, cross-snapshot and stale cache/handle rejection, and
deterministic replay. Include both accepted proof and rejected invalid proof;
verify no failure path issues a handle or mutates an existing snapshot.

An expert human must review the semantic rules, substitutions, conversion
soundness and ordering, axiom policy, declaration import, lifetimes, atomicity,
tests and actual trusted implementation before use or merge. AI review and
finite differential tests do not replace that gate. A concrete transaction
identity scheme, formal symbolic level equality and the exact handling of
Lean's broader declaration forms remain open.

## Local evidence and reproducibility

The installed `lean-toolchain` pins Lean 4.35.0; `ELAN_HOME="$PWD/.tools/elan"
.tools/elan/bin/lean --version` reported commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. In its distributed source,
`Lean/Meta/InferType.lean:121` checks arity before instantiating the type;
`Lean/Environment.lean:1216` instantiates type and value;
`Lean/Util/InstantiateLevelParams.lean:18` substitutes in sorts and constant
levels. Its general substitution helper truncates unequal lists, so arity must
be checked separately. `Lean/Declaration.lean:16` describes definition hints;
`:95` and `:470` distinguish declaration records and reducible values.
These Lean-level APIs and comments are evidence, not a direct audit of the
kernel C++ implementation: the installed `src/lean/kernel` directory is empty.
The meta checker is not itself the kernel oracle. Existing
`tests/reference/declaration-oracle.lean` and `constant-fixture.lean` cover
limited examples; no new tests or CI were run for this documentation draft.

Subsequently, `tests/reference/constant-environment-oracle.lean` added direct
`Kernel.Environment.addDeclCore` cases for a checked polymorphic identity,
aliases, a concrete specialization, exact level arity, unknown and self
references, duplicate names, an unbound universe, swapped two-parameter
substitution and a nested `max`/`imax` argument. The valid and invalid cases
are checked independently against immutable prior kernel environments. Its
SHA-256 is `2332d01b9952754a30186b1130fd9e76686d9ffc5c8c13f51730d2a860df5466`.
It runs as part of `make reference` with the pinned Lean version and revision.
This is a limited reference suite, not a LeanForth differential test or
evidence that a LeanForth declaration environment exists.

The separate untrusted `constant-references.fs` data structure stores a
structured-name ID and up to eight ordered level handles. It checks name-table
generation and level allocation identities on access; it does not validate
level graph shape or scope, enforce declaration arity, integrate constants
into terms, or infer types. Its limits, forgeable instance-local handles and
single-threaded ownership assumptions preclude treating it as a checked Lean
environment. Eight arguments is a current experimental capacity, not a
restriction on the intended Lean or full Mathlib compatibility.

The experimental `constant-term-boundary.fs` supports mixed syntax graphs
containing constant references, symbolic sorts, variables, applications and
binders. It checks reachable node and level structure, scope of levels and
captured identities, but does not check binder scope, declaration existence,
typing or proofs. The ordinary inference and substitution experiments do not
consume these nodes. A test-only transport stages 19 nodes from the pinned
constant fixture; staging and structural validation do not import or check
its declarations.
`constant-term-scope.fs` adds a bounded binder-scope traversal for these mixed
graphs, auditing all reference identities and levels before scope traversal.
It does not establish that binder domains are types or resolve constants. This
is groundwork for a definition diagnostic whose body contains constants, not
an implemented constant-aware type checker.

The untrusted `constant-signature-probe.fs` bridge looks up a reference's
name and ordered level handles in the candidate metadata and specializes the
stored signature with exact arity. It does not make constants term nodes,
infer their type, validate declarations or confer theorem validity. Its
session, lifetime and mutation assumptions are inherited from its components.
`make test-constant-signature-differential` compares 48 finite syntax
observations with pinned Lean, not general declaration acceptance.

`constant-term-type-probe.fs` connects a single validated constant node to
the candidate-signature bridge. Its output is an untrusted specialized term,
not a typing judgment: candidate declarations and their signatures are not
checked. It does not infer applications or resolve nested constants. Boundary
fuel and signature fuel are separate, and the latter is applied independently
to lookup and substitution. `make test-constant-term-type-differential`
compares 48 finite substitution syntax observations with pinned Lean; the
synthetic candidates in this comparison are not established as valid types.

`constant-application-probe.fs` composes the experimental operations for one
constant root applied to one closed ordinary symbolic argument. Its result is
conditional on the unchecked candidate signature and is not a typing judgment
or proof. It checks candidate closure before reduction; arguments containing
constants are currently classified as invalid even when valid Lean syntax.
It uses fixed, separate per-operation budgets and restores arena counts on
failure, without rewinding identity serials. Existing inference and conversion
still do not support nested constants or general constant-bearing graphs.
`tagged-context-infer.fs` separately extends the ordinary symbolic inference
experiment to explicit oldest-first binder domains. It checks representation,
allocation identities and de Bruijn scope relative to preceding binders, but
does not establish that domains are well-formed types. Its results depend on
that unchecked assumption and are not typing judgments or theorem receipts.
It is not yet integrated with the constant-application diagnostic.
The untrusted `constant-spine-probe.fs` extends that diagnostic to zero through
eight ordered, closed ordinary arguments, validating all argument handles
before allocation and restoring both arena counts on any failure. Results are
still conditional on unchecked candidate signatures. Constants in arguments
and candidate types are unsupported; `invalid` in that case is not a claim
that Lean rejects the expression. The fixed per-operation budgets and eight
argument limit are experimental, not restrictions on the final system.
The untrusted `context-constant-spine.fs` experiment accepts explicit
oldest-first binder-domain handles and open arguments. It validates all domain
and argument structures and scopes before allocation, then performs conditional
argument inference and substitution under the supplied context. Candidate
signatures and context-domain typing remain assumptions. Input arrays and all
mutable scratch/arena storage must be disjoint; failures restore arena counts,
not serials. A test-only bridge stages the pinned constant fixture and obtains
the expected `#1` result for `fixtureId A x` under binders `A` and `x`. It does
not independently check the declaration or its proof, and arbitrary nested
constants and general elaboration remain unsupported.

The untrusted `context-validation-probe.fs` checks each supplied binder domain
in its preceding context using limited inference. It audits all handles and
scope before allocating, checks for a syntactic inferred Sort, and reports
unknown when that form is inconclusive. Arena counts are restored on all
outcomes, while identity serials advance. `validated-context-spine.fs` composes
this with the context-aware constant diagnostic after prevalidating all input
handles. The fixture test now uses that composition. This reduces one explicit
context assumption but does not check the candidate declaration, establish
general context well-formedness, or authorize theorem validity; nested constants
and definitional reductions remain incomplete and human review is required.

`candidate-definition-probe.fs` is an untrusted diagnostic for an ordinary
closed symbolic type/value pair: it infers that the claim has a Sort, infers
the value and conservatively compares the resulting type. It restores both
arena counts after every outcome. It neither registers nor independently
certifies a declaration, and cannot infer constant-containing values. The
fixture test applies it to the exported `fixtureId` type and value and checks
that a mutated value does not succeed; subsequent use still assumes candidate
metadata because no trusted environment or theorem receipt exists.
`tests/reference/constant-application-oracle.lean` records Lean kernel
acceptance of a polymorphic identity applied to `Prop` and rejection of a wrong
argument or missing constant; these observations do not check LeanForth.
`tests/core/constant-application-oracle.fs` reconstructs the positive case by
calling the candidate-specialization, inference, conversion and substitution
experiments separately. It obtains the same result syntax, while the wrong
argument yields `unknown` in conservative conversion. Its signature is an
unchecked assumption, and it neither implements application inference nor
checks a declaration or proof. The Lean negative cases assert kernel rejection
but do not inspect the reason, and the Forth test does not construct an
application or cover Lean's missing-constant case.

The untrusted candidate-signature index exposes an index-lifetime generation
through `lf-rawdecl-token`. Each begin attempt advances it and clears the
index; saturation disables further begins rather than reusing an old token.
Consumers must explicitly capture and compare the token and all relevant
session identities; the index does not enforce that external metadata does so.
Tokens are unique only within one loaded module instance, not across reloads
or processes, and identify lifetimes rather than content revisions: insertions
do not invalidate caches. Cross-instance or content-sensitive consumers need
separate identities or invalidation.

The untrusted `raw-signature-specialize.fs` experiment associates copied,
ordered formal IDs with a candidate in that index lifetime and requires exact
arity when specializing its stored term. Insertion checks that the formal
list covers the source levels by a temporary substitution; arena counts are
restored but allocation serials advance, and resource exhaustion can reject
an otherwise adequate list. It remains bounded and session-local:
the index requires candidate levels and actual levels to share its session
context. It is not an implementation of the reviewed declaration environment,
does not establish typing, scope of term binders or proof validity, and cannot
register any declaration. Its metadata must not be persisted across processes.
`make test-signature-fixture-differential` stages the pinned polymorphic
identity NDJSON fixture as untrusted test data and compares its specialized
type shape at two universe instances to pinned Lean. It does not import or
check the declaration, its value, or other NDJSON records in general.
The token is forgeable, does not validate a declaration, and does not make
bare name IDs safe across name-table resets. This is not a checked environment.

The untrusted `src/experimental/level-substitute.fs` implements a bounded
simultaneous substitution of level DAGs. Its formal parameter IDs and actual
level roots are caller-owned cell arrays; actual roots must be valid in the
current caller level context. Its public word `lf-lsubst` takes
`( root formal-addr actual-addr count fuel -- result ok | status )`. It does
not recursively substitute inside replacement levels. Its inputs are raw
arena indices, not generation-bound handles: callers must protect lifetimes,
memory and mutation. The caller must supply aligned, accessible input arrays
disjoint from arena, context and module scratch storage; overlap is not
detected. Invalid inputs and resource exhaustion do not append
nodes, subject to these ownership assumptions. This experiment is not wired
into declaration checking and has not received the human semantic review
required for trusted use. `make test-level-substitute-differential` compares
48 finite concrete observations to pinned Lean, which does not prove general
symbolic equivalence or establish kernel compatibility.

The experimental `src/experimental/term-level-substitute.fs` applies this
operation to Sorts in a bounded symbolic term DAG containing variables,
applications, lambdas and Pi nodes. Formal IDs are scoped separately from
the caller context of the actual levels. It checks allocation identities,
reuses unchanged nodes, and restores both arena counts on failure without
rewinding allocation serials. Input arrays must be aligned, accessible and
disjoint from arena, context and scratch storage; session and arena mutation
must be excluded. Raw and forgeable identities are not capabilities. Constants,
typing, binder scope and declaration checking are not supported. The
`make test-term-level-substitute-differential` target compares 48 finite
observations with pinned Lean; it does not establish general correctness.

Reproduction: inspect the cited files and ADRs; run the version command above
and `sha256sum lean-toolchain` plus the four cited Lean source files. SHA-256:
`lean-toolchain` ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c;
`Declaration.lean` 1cf2f06d848086f165b3df0afe494924ae26aaea248d5e0135d5efc2d588948f;
`InstantiateLevelParams.lean` a18331b9ac993ffb11dac917c03df342df962de31321340e07749c606f9d1aa4;
`Meta/InferType.lean` ed92098c36a75443312d2d474b4ad7a5c12434cd78bf1a7453e91c876880859e;
`Environment.lean` 6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43.
# Follow-up: mixed-term inference diagnostic

An independent AI review on 2026-11-01 found that composing the existing
constant-spine and ordinary definition diagnostics is insufficient for
constants inside binder domains, arguments, or general application trees.
The next diagnostic needs mixed-term transformations and conservative
conversion, not only constant lookup. This review is advisory and does not
replace human review of kernel or declaration semantics.

Before inference allocates, audit both roots and any external context and
metadata handles, including their scope and universe references. Preserve a
single documented fuel policy and restore both arena counts on every outcome
without rewinding serials or exposing rolled-back handles. Distinguish input
nodes from generated specialized signatures, which the existing ordinary
inference walker cannot simply revisit. Context domains are scoped before
their binder; substitution must avoid capture; missing metadata or unsupported
conversion must not become success. Candidate signatures are assumptions
until independently checked, and successful diagnostics confer no theorem.

Tests should include constants in domains and arguments, nested dependent
binders, shared nodes at distinct depths, stale later inputs, missing metadata,
wrong universe arity, capture-sensitive substitution, resource exhaustion and
rollback after allocations in both arenas. Compare supported cases with the
pinned Lean kernel; obtain the required human review before trusted use.

`src/experimental/mixed-shift.fs` now provides one prerequisite: bounded
de Bruijn shifting across mixed syntax, reusing constant and Sort leaves
after validating their identities and universe scopes. It is untrusted syntax
manipulation, not inference or declaration checking. It shares fuel between
the audit and traversal, and rolls back appended terms on failure without
rewinding allocation serials. `make test-core` exercises error and rollback
cases; `make test-mixed-shift-differential` compares 45 finite observations
against pinned Lean's `Expr.liftLooseBVars`. Those observations do not prove
correctness for all inputs. Mixed substitution, conversion and inference
still need implementation, tests and review.
