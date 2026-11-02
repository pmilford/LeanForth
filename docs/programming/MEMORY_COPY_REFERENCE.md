# Memory copy program reference

`tests/reference/memory-copy-reference.lean` imports the existing independent
Lean memory-program model. `copyProgram destination` is the composed sequence
`load`, `push destination`, `store`. Given a source address on top of an
arbitrary stack tail, it loads the source before storing the value to the
destination, consuming the source and preserving the entire tail. Addresses
are natural numbers, values are mathematical integers, and the destination is
an instruction parameter. The memory and instruction definitions are those
of `program-contracts.lean` and `memory-program-reference.lean`.

`copy_execution` proves that executing this sequence equals mapping the
abstract `copyCell` result to a state with the original stack tail. Thus the
connection includes success and failure, rather than assuming the sequence
implements copy. For any two in-bounds addresses, `copy_success` proves the
destination reads the original source value, memory size is unchanged, and
every other backing cell is unchanged. The addresses may coincide;
`copy_same_address` additionally proves all backing cells are unchanged in
that case. Both bounds failures yield `none`, including when both addresses
are invalid. No resulting state is exposed on failure, so this does not assert
rollback in a runtime. The frame includes inaccessible backing cells, a
property of this function-backed model.

These are Lean-checked mathematical theorems about handwritten abstract
semantics, with no new axioms or `sorry`. They are not LeanForth certificates
or proofs about a Forth implementation, compiler, executable, or runtime. The
model omits byte layout, alignment, finite-width addresses, permissions,
concurrency and real memory effects. No correspondence to Forth-2012 or Gforth
is established. Human review remains necessary for any future integration
across a trusted boundary.

`tests/reference/memory-copy-properties.lean` also proves that the copy
succeeds exactly when both addresses are in bounds, that operand/tag errors
and bounds failures persist through a following instruction sequence, and
that a successful copy passes the unchanged stack tail to that continuation.
These results have the same abstract-model limitations described above.

`tests/reference/memory-copy-twice.lean` proves that two copies have the same
modeled state as one, including aliased addresses, and covers bounds and
failure through continuations. Lean's axiom audit for these reference results
includes `propext` and `Quot.sound`; the exact-success theorem also uses
`Classical.choice`. These are reported assumptions of the Lean reference,
not an approved LeanForth axiom policy. `make reference` checks the file.

`tests/reference/memory-copy-frame-composition.lean` proves that a copied value
is preserved by a successful continuation whose stated write footprint excludes
the destination, and that cells outside both footprints retain their original
values. It also proves the footprint contract for a modeled store. The footprint
is an assumption about the continuation, not an automatic analysis or a proof
about the Forth runtime. Lean reports `propext` and `Quot.sound` for these
reference theorems; `make reference` checks them.

`tests/reference/memory-copy-commute.lean` shows two modeled copies commute
when each destination differs from the other destination and the other source.
It also gives a concrete counterexample when one copy reads the other's
destination. The proof applies to the abstract memory and instruction model,
not to the Forth runtime; `make reference` checks it.

## Reproduction

From the repository root, the following commands passed on 2026-11-01 using
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Linux x86-64:

```sh
mkdir -p /tmp/leanforth-memory-copy-reference
.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -o /tmp/leanforth-memory-copy-reference/program-contracts.olean tests/reference/program-contracts.lean
LEAN_PATH=/tmp/leanforth-memory-copy-reference .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -o /tmp/leanforth-memory-copy-reference/memory-program-reference.olean tests/reference/memory-program-reference.lean
LEAN_PATH=/tmp/leanforth-memory-copy-reference .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean tests/reference/memory-copy-reference.lean
```

Lean imports compiled modules; rebuild both imports when their sources change.
`make reference` also checks this file through `memory-program-check.sh`.
CI was not run for this change.
SHA-256 hashes at verification:

```text
3cb499863916d2c5ccaa44eba24ece852b59f81ad25843a5336212f93f646d27  tests/reference/program-contracts.lean
fee5e49425ed17e7d3777684dcb8fcc3ccbbdbcb4ac59f552bcd5bc87aee9e46  tests/reference/memory-program-reference.lean
768b51026da7b1b5410ca327badbf4503af01eefc15645247550b516024616f0  tests/reference/memory-copy-reference.lean
bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38  .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
```

This advances the abstract verified-program path. The theorem path, shared
kernel and NDJSON importer are unchanged; their approximately ten-milestone
tracks and current code inventory are recorded in `docs/project/PROJECT_PROGRESS.md`.
Full Mathlib compatibility and verified executable Forth remain open.
