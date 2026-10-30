# Decisions and proposed work

## Bootstrap boundary

The first Forth module is a host smoke test, not a proof kernel, a verified
program, or a specification of mathematical integers. Gforth cell arithmetic
and execution are host assumptions. The CI distribution Gforth is a separate
compatibility check; it does not establish Gforth 1.0 coverage.

## Kernel and execution design — proposed, human review required

Compare indexed expression DAGs with pointer-linked trees before choosing a
representation; indexed arenas support portable serialization but require
explicit bounds and lifetime management. Compare per-check arenas against
reference counting with respect to reclamation and auditability. FFI belongs
outside the kernel, behind a separate host adapter; no ABI or allocator choice
is approved by this note. Define typing rules, axioms, serialization, resource
limits and negative tests in an ADR before any kernel semantics are implemented.

## First meaningful examples — proposed

- Theorem track: construct a polymorphic composition proof, given `A → B` and
  `B → C` derive `A → C`; reject a composition with incompatible intermediate
  types. Compare both with pinned Lean when the supported fragment exists.
- Program track: specify and verify a bounded integer clamp, including its
  range and behavior inside the bounds; reject a faulty implementation or
  contract. See `docs/PROGRAM_EXAMPLE.md` for the proposed contract and runtime
  assumptions to resolve before implementing.

Neither example is implemented or verified. A smaller identity proof may be
needed first to validate the core typing rules.

## Bootstrap backlog

1. Make installation repeatable on a clean Ubuntu/WSL machine; authenticate
   release hashes and eliminate unnecessary optional dependencies.
2. Establish CI on the pinned Gforth release; record actual remote CI status.
3. Review the first kernel ADR and Lean oracle cases, including invalid terms.
4. Specify the executable example and separate source proof from runtime trust.
5. Design versioned API schemas and explicit proof-step provenance.
6. Evaluate the bundled Forth tester with deliberate failures and establish the
   unit, interface, functional and regression layers in `docs/TESTING_STRATEGY.md`.
