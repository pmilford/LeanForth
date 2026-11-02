# Structural arena prototype

`src/core/names.fs` interns structured byte-string and numeric name
components in bounded global storage. It is not connected to declaration or
level checking and does not validate UTF-8 or protect against raw mutation or
stale IDs. See `docs/adr/0005-structured-names.md` for the proposed review
boundary and `make test-name-differential` for nine selected Lean comparisons.

`src/core/levels.fs` separately stores symbolic universe syntax:
zero, successor, max, imax and opaque parameter identifiers. Constructors
check basic allocation and backward references but do not check parameter scope,
level equality or types, and the arena is not connected to the term checker.
See the unapproved symbolic-universe proposal in `docs/adr/0004-symbolic-universes.md`.
`src/core/level-scope.fs` adds a bounded, untrusted traversal checking
reachable node shape and opaque parameter IDs against an explicit context. It
also checks the distinguished zero slot and rejects corrupted counts, fields,
cycles and forward references. Repeated shared nodes consume repeated visit
fuel; context validation has a separate bounded quadratic cost. Opaque IDs are
not Lean name equality, and structural success is not a type or proof judgment.
`src/kernel/level-value.fs` evaluates validated concrete level DAGs
using bounded fuel; symbolic parameters return unknown. The concrete result is
not a level equality judgment or theorem. Validation and evaluation share visit
fuel, while bounded context processing is separate; the global mutable arena
and bounded host recursion remain assumptions. A separate entry point evaluates
one explicit map of parameter IDs to nonnegative host-cell values; missing
assignments remain unknown, and evaluation of an instance does not prove a
polymorphic property. Arena resets and context changes invalidate that map via
generation snapshots; generation saturation fails closed. These global mutable
snapshots do not protect against raw memory mutation or establish name identity.
Assigned maximum-cell successors exercise the overflow
guard, which was unreachable using concrete constructor chains alone.
`make test-level-assignment-differential` compares 36 instances of one nested
symbolic expression with Lean's parameter instantiation and normalization.
The test-only `make test-export-specialization-differential` specializes an
actual polymorphic Lean export for four explicit levels and compares the
untrusted definition probe's diagnostics with Lean's kernel. This does not
check the original polymorphic declaration or create any theorem handle.
`src/kernel/level-compare.fs` compares scoped level graphs using a few
literal-zero rewrites and structural comparison, and falls back to unassigned
concrete evaluation; it reports unknown for many
Lean equalities. Equal is an untrusted diagnostic dependent on stable opaque ID
identity, not a theorem or type judgment. `make test-level-compare-differential`
compares fifteen selected cases with Lean, including deliberate unknowns.

`src/core/terms.fs` is an experiment representing concrete sort levels,
de Bruijn indices, application, lambda and Pi nodes. Constructors validate
nonnegative payloads, known binary tags, backward child references and capacity.
These checks establish storage shape only: they do not establish scope, universe
well-formedness, type correctness, or Lean compatibility. In particular, a
nonnegative variable index may still be unbound. Binder names, annotations,
symbolic universe levels, other Lean expression forms and import are not
implemented. Its store is global and mutable and not thread-safe; a reset
invalidates every index, which may be reused and must never be retained
across a reset; its cell layout is host-specific and is not serialization.
Future designs must address ownership, stale handles, input validation,
portability, resource limits and an audited logical representation. Any
change that confers proof validity requires the kernel review gate.

`tests/core/terms.fs` covers field ordering, invalid tags and indices, capacity,
reset and construction of an identity-shaped DAG. The identity-shaped example
is not a proof acceptance test. The final kernel's representation and handling
of untrusted inputs remain subject to review; prototype internals must not be
exposed as a theorem-checking interface.

`src/import/load.fs` stages already-decoded integer records into that
store in a bounded batch. Record indices and child references are batch-local;
invalid records or allocation failure discard the batch while preserving prior
nodes, assuming no outside mutation. It is neither a JSON decoder nor a
declaration importer. It does not resolve Lean universe references, validate
scope or types, or issue theorem handles. Its transactional behavior is an
untrusted prototype and needs review before use at the declaration boundary.
`make test-core` covers successful staging, malformed records, abort, preexisting
nodes and capacity exhaustion. It stages Sorts only as concrete numbers, which
no current checker pass accepts; the owner decided on 2026-11-02 to keep it,
with its round-trip tests, until the Forth NDJSON reader replaces it.

`make test-composition-fixture` (part of `make test`) uses a test-only Python
inspector to compare the 21 node records of a manually constructed
composition DAG with the pinned Lean NDJSON fixture. This inspector is not a
general importer, does not register declarations and cannot confer theorem
validity. The fixture test also sends those decoded node fields to the Forth
staging interface through a test-only byte stream and compares the resulting
store records. The stream is data, not executable Forth; truncated and
malformed streams must fail without printing staged records. This covers one
fixture and does not validate general NDJSON or theorem correctness. The
fixture inspector rejects duplicate JSON keys, unexpected expression and
theorem fields, invalid binder metadata, and unexpected fixture declaration
references. It is intentionally specific to this fixture and is not a
complete validator for the export format. The staged Sorts are concrete,
which no current checker pass accepts, so the checker examines the same
export separately, staged with symbolic levels, in
`tests/core/test_export_definitions.py`; a deliberately altered composition
fails there.

## Retired prototypes

The first plain-term prototypes of the checking passes (`scope.fs`,
`shift.fs`, `instantiate.fs`, `beta.fs`, `compare.fs`, `infer.fs` and
`declaration-probe.fs`, with the `arena.fs` pair store) and their later
`tagged-*` variants were retired on 2026-11-02 together with their tests,
once the current code had at least the same test coverage
([decisions record](../project/DECISIONS.md), "Legacy retired — 2026-11-02").
They worked on concrete Sorts (`Sort n` with a number). Each operation now
has one current module, tested by `make test-core` and compared with pinned
Lean by `make check` on the cases the prototypes were compared on, with every
Sort symbolic (a concrete universe n is the level succ^n zero):

| Operation | Current module | Pinned-Lean comparison (cases) |
| --- | --- | --- |
| Binder scope | `src/core/constant-term-scope.fs` | `test-constant-term-scope-differential`, Lean's `hasLooseBVars` (64) |
| De Bruijn shift | `src/kernel/mixed-shift.fs` | `test-mixed-shift-plain-differential`, `liftLooseBVars` (80) |
| Single-binder instantiation | `src/kernel/mixed-instantiate.fs` | `test-mixed-instantiate-plain-differential`, `instantiate1` (25) |
| Weak-head beta | `src/kernel/mixed-beta.fs` | `test-mixed-beta-plain-differential`, `Kernel.whnf` (15) |
| Conservative conversion | `src/kernel/mixed-convert.fs` | `test-mixed-convert-plain-differential`, `isDefEq` (15) |
| Type inference | `src/kernel/mixed-infer.fs` | `test-mixed-infer-plain-differential`, `Kernel.check` (52) |
| Definition probe | `src/kernel/mixed-definition-probe.fs` | `test-mixed-definition-differential` (9) |
| Node storage | `src/lib/store.fs`, `src/lib/node.fs` | unit tests in `tests/lib/` |

Two differences are intended: conversion now reduces binder domains instead
of requiring them to match exactly, and the definition probe accepts a claim
in any Sort, where the old declaration probe required a proposition (theorem
mode is to be rebuilt in phase 2). Everything in this table is untrusted:
results are diagnostics, not checked theorem handles, and the kernel review
gate in `AGENTS.md` still applies.
