# Forth library inventory

What reusable Forth facilities exist, how mature they are, and what the
product will need that does not exist yet. Everything listed is untrusted
experimental code unless stated otherwise; none is a reviewed kernel
component. Measured 2026-11-02 at commit `4779924`. Modules are in
`src/core/` (data model) or `src/kernel/` (checker passes) unless named
with another folder; superseded variants are in
`src/legacy/` ([source layout](../../src/README.md)).

## What exists

| Facility | Module(s) | What it is | State |
| --- | --- | --- | --- |
| Expression store | `src/core/terms.fs` | Index-based nodes for sorts, bound variables, application, λ, Π and constants; nodes refer to earlier indices, so a term is a DAG with sharing | 64 nodes; global; constructors check ranges only |
| Universe-level store | `src/core/levels.fs` | Level DAGs: zero, succ, max, imax, parameters | 64 levels; global |
| Name interning | `src/core/names.fs` | Lean structured names (string and numeric components) stored once and referred to by index | 64 names, 2,048 bytes; lookup is a linear scan, no hashing |
| Stale-handle detection | `src/core/generation-handles.fs`, `symbolic-session.fs` | Handles carry a generation number so a handle from before a reset is rejected | Works; tests found one unguarded path |
| Constant references | `src/core/constant-references.fs`, `constant-term-*.fs` | A constant's name plus universe arguments, with syntax and scope audits | Global, 32 references |
| DAG walkers | `shift`, `instantiate`, `beta`, `compare`/`convert`, `infer` in three variants: current `mixed-` in `src/kernel/`; plain and `tagged-` in `src/legacy/` | Bounded traversals with explicit work stacks and fuel, rolling back on failure | `mixed-*` is current; the other two variants are superseded (roadmap Q9) |
| Level algorithms | `level-scope`, `level-value`, `level-compare`, `level-substitute`, `mixed-level-substitute` | Scope checks, evaluation, conservative equality and simultaneous substitution of levels | Current |
| Signature index | `mixed-signature-probe.fs`, `mixed-signature-audit.fs` (older, in `src/legacy/`: `raw-declaration-index`, `raw-signature-specialize`) | Candidate signatures of constants, specialised to universe arguments | 32 entries; unchecked assumptions |
| Record staging | `src/import/load.fs` | Copies already-decoded expression records into the term store | Not a parser |
| Generic pair arena | `src/legacy/arena.fs` | Early atom/pair storage experiment | No dependants; retirement candidate |
| Program examples | `src/program/clamp.fs`, `examples.fs` | Six executable words (clamp, checked add, abs, factorial, gcd, in-range) | Runtime tested against Lean models, not verified |
| Depth analyzer | `src/program/program-depth.fs` | Stack-depth diagnostic for a tiny opcode list | Not connected to real Forth words |
| Test support | `tests/support/tester.fs`, `checks.fs`, `term-cases.fs`, `composition.fs` | Adapter for Gforth's bundled tester that fails the run on the first error; shared checks and fixtures | Test-only |

## JSON and NDJSON

There is **no JSON or NDJSON reader in Forth**. Lean exports are decoded by
the Python preview (`tests/support/ndjson_preview.py`), which turns a fixture
into a compact byte stream; about eleven hand-written Forth stream readers
(`tests/core/*-stream.fs`) each load one fixture's stream. They duplicate
the same framing code. The implementation plan allows an untrusted decoder in
another language but requires the semantics to be checked in Forth; a
production importer will need a streaming Forth NDJSON reader, or a reviewed
decision to keep decoding outside Forth with a validated binary interchange.

## Missing for a usable checker at Mathlib scale

- **Capacity and memory.** Every store holds 64 entries in fixed global
  arrays. Mathlib's export has millions of expression nodes. Needed: growable
  or file-backed arenas, explicit memory budgets and measured limits.
- **Hashing and hash-consing.** Names are found by linear search and terms are
  not shared by content. Needed: hash tables for names and structural sharing
  of identical terms and levels.
- **Records and defining words.** No `BEGIN-STRUCTURE`/`FIELD:` layouts and no
  `CREATE ... DOES>` defining words; each module re-implements array-plus-count
  storage with raw offsets. One `arena:`-style defining word would replace many.
- **One outcome vocabulary.** 34 words translate one module's status codes
  into another's. A shared set of outcomes (ok, rejected, unknown, invalid,
  exhausted) would remove them.
- **Dispatch tables.** Walkers branch on node tags with long `IF` chains; no
  execution-token tables are used.
- **Namespaces.** No wordlists; the `LF.CORE`, `LF.KERNEL` modules planned in
  the handoff do not exist.
- **Re-entrancy.** All state is global, so only one check can run per Forth
  image (roadmap C1–C4).
- **Serialization.** No deterministic, architecture-independent format for
  checked terms or receipts.
- **Pretty-printing and explanation.** No printer for terms, levels or proof
  steps.
- **A shared stream reader**, replacing the eleven test readers.

How the existing code should be written and refactored is in
[the Forth style guide](FORTH_STYLE.md).
