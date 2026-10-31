# Structural arena prototype

`src/core/arena.fs` is a bounded experiment in storing integer-indexed nodes.
It does not represent Lean expressions, validate terms, check types, issue
theorem handles or establish mathematical truth. It is not a kernel API.

The arena stores at most 64 nodes. An atom contains an opaque cell payload; a
pair contains two indices of already allocated nodes, so constructed pairs
cannot reference later nodes. Constructors return an index and true on success,
or false on invalid references or exhaustion, without advancing the count.
`lf-arena-reset` invalidates all existing indices; an index may be reused and
must never be retained across a reset. The prototype is global, mutable and not
thread-safe. Its raw address word assumes a valid index; it must not be exposed
to untrusted inputs. Cell layout is host-specific and is not serialization.

`make test-core` exercises construction, cell layout, invalid references,
capacity and reset through the Gforth test harness. Future designs must address
ownership, stale handles, input validation, portability, resource limits and
an audited logical representation. Any change that confers proof validity
requires the kernel review gate.

`src/core/terms.fs` is a separate experiment representing concrete sort levels,
de Bruijn indices, application, lambda and Pi nodes. Constructors validate
nonnegative payloads, known binary tags, backward child references and capacity.
These checks establish storage shape only: they do not establish scope, universe
well-formedness, type correctness, or Lean compatibility. In particular, a
nonnegative variable index may still be unbound. Binder names, annotations,
symbolic universe levels, other Lean expression forms and import are not
implemented. It uses its own global arena with the same reset, thread-safety,
raw-memory, stale-index and serialization limitations described above.

`tests/core/terms.fs` covers field ordering, invalid tags and indices, capacity,
reset and construction of an identity-shaped DAG. The identity-shaped example
is not a proof acceptance test. The final kernel's representation and handling
of untrusted inputs remain subject to review; prototype internals must not be
exposed as a theorem-checking interface.

`src/experimental/load.fs` stages already-decoded integer records into that
arena in a bounded batch. Record indices and child references are batch-local;
invalid records or allocation failure discard the batch while preserving prior
nodes, assuming no outside mutation. It is neither a JSON decoder nor a
declaration importer. It does not resolve Lean universe references, validate
scope or types, or issue theorem handles. Its transactional behavior is an
untrusted prototype and needs review before use at the declaration boundary.
`make test-core` covers successful staging, malformed records, abort, preexisting
nodes and capacity exhaustion.

`src/experimental/scope.fs` performs a separate, untrusted structural traversal
with explicit success, malformed, and budget-exhausted statuses. It checks
binder depth, node tags, nonnegative leaf payloads, backward child references,
and bounded work; tests deliberately corrupt storage and exercise a shared DAG
at the visit-budget boundary. A successful scope result is not type checking:
the tests include a closed application of a sort that passes this scope scan
but Lean rejects as ill typed. This global prototype assumes no concurrent
mutation and has no importer or theorem-registration interface. Review remains
necessary before any part is used in the trusted kernel.

`make test-scope-differential` separately constructs matching terms in Lean
and Forth, then compares the prototype's closed-scope status to Lean's
`Expr.hasLooseBVars` on 64 bounded cases. This includes ill-typed expressions
because scope is a syntactic property. It is not a comparison with Lean's type
checker, and it does not establish correctness beyond the tested shapes.

`src/experimental/shift.fs` implements an untrusted, bounded de Bruijn shift
experiment. It checks source-node references, detects signed-cell overflow,
limits recursion and visit work, and rolls the arena allocation count back on
failure. The arena is mutable, global and non-reentrant; resetting the count is
not secure erasure or an immutable transaction. The prototype does not check
typing, create a theorem, or implement substitution. It has not been reviewed
for trusted use, and its reliance on host cells, return-stack space and Forth
runtime behavior remains an assumption.

`make test-shift-differential` compares 80 bounded shifts on five expression
shapes against pinned Lean's `Expr.liftLooseBVars`. `make test-core` also tests
invalid references, malformed fields, exhaustion, rollback and signed-cell
overflow. These are finite tests, not a proof of the transformation.

`src/experimental/instantiate.fs` is a separate untrusted experiment for
single-binder instantiation. It validates the replacement through a zero shift,
shares a visit budget with shifts, and restores the allocation count on failure.
Like the shift module, it uses global mutable state and bounded host recursion;
neither rollback nor returned indices provide protected immutable storage. It
does not infer types or produce a proof judgment. The preflight can consume
arena capacity even for an unused replacement, so resource exhaustion is a
possible conservative result.

`make test-instantiate-differential` compares 25 open-expression cases against
Lean's `Expr.instantiate1`. `make test-core` tests capture avoidance, lowering,
invalid source and replacement nodes, allocation failure, fuel exhaustion and
rollback. This finite evidence does not constitute a soundness proof or human
review for trusted kernel use.

`src/experimental/infer.fs` combines the untrusted transformations and
comparison to experiment with type inference for concrete sorts, bound
variables, Pi, lambda and application. Its results are mutable arena indices,
not checked theorem handles. It assumes global, single-threaded host state and
bounded host recursion; it is not a reviewed trusted kernel or a declaration
checker. Unknown comparisons, malformed nodes and exhausted resources do not
produce successful inference. The full Lean/Mathlib feature set is unsupported.

The local Forth suite tests identity, universe cases, invalid inputs and a
manually constructed composition DAG. `make test-composition-fixture` uses a
test-only Python inspector to compare its 21 node records with the pinned Lean
NDJSON fixture. This inspector is not a general importer, does not register
declarations and cannot confer theorem validity. A separate human review is
required before these experiments can be used in a trusted kernel.

The fixture test also sends those decoded node fields to the Forth staging
interface through a test-only byte stream, and compares the resulting arena
records. It also infers the staged value's type and experimentally compares it
with the staged claim; a deliberately altered value fails this test. The
stream is data, not executable Forth; truncated and malformed streams must fail
without printing staged records. This covers one fixture and does not validate
general NDJSON, declaration metadata, or theorem correctness. In particular,
this test does not check that the claim itself is a proposition or register a
declaration, and the inference and conversion code remains untrusted.

`make test-infer-differential` compares seven inferred types with the pinned
Lean kernel and checks six Lean-rejected cases for invalid or unknown results.
Successful inference retains intermediate arena allocations, so repeated checks
can exhaust the 64-node arena. Ownership, reclamation, and preservation of
indices need a reviewed design before this can support trusted checking.
The core tests repeatedly infer an identity term until exhaustion, checking that
failure restores the preceding count and that an earlier result remains readable.
These checks assume callers do not mutate the arena or reset it between calls.

`src/experimental/beta.fs` prototypes weak-head beta reduction using the
experimental instantiation and shift modules. It validates input structure,
tracks a finite visit budget and rolls back allocation count on failure. Its
global mutable state, bounded host recursion and host-cell assumptions remain
untrusted. `tests/core/beta.fs` checks identity reduction, stuck applications,
unreduced lambda bodies, a nonterminating untyped term and several failure paths
on two Gforth versions. `make test-beta-differential` compares 15 closed,
Lean-kernel-type-checked cases with `Lean.Kernel.whnf`. This finite comparison
does not prove reduction correct. Reduction of syntax alone is not evidence that
a term is well typed or a proof.

`src/experimental/compare.fs` experiments with the conservative comparison in
ADR 0003, using beta reduction and exact binder-domain syntax. It returns
`equal`, `unknown`, `invalid`, or `exhausted`; `equal` is not proof that its
inputs are well typed and must not authorize a theorem. Its global mutable
storage, host recursion, budget accounting and semantics remain unreviewed for
trusted use. `make test-compare-differential` checks six closed examples against
Lean's kernel, including a Lean equality intentionally reported as unknown.
This finite test is not a soundness proof or evidence of full Lean compatibility.
