# Stack and memory program reference

`tests/reference/memory-program-reference.lean` is an **untrusted Lean
reference**, not a LeanForth proof certificate or a proof of any Forth program,
interpreter, compiler, or runtime. It imports the actual `Memory`, `load`,
`store`, `store_read_frame`, and `out_of_bounds_access` definitions and
theorems from `tests/reference/program-contracts.lean`.

The state pairs that bounded memory with a stack of tagged mathematical
integer values and natural-number addresses. The list head is the stack top.
The modeled instructions have these effects (Forth notation, top at right):

| Instruction | Stack effect | Failure |
| --- | --- | --- |
| `push x` | `( -- x )` | None |
| `load` | `( addr -- value )` | Underflow, wrong tag, or address outside memory |
| `store` | `( value addr -- )` | Underflow, wrong tags, or address outside memory |

Every untouched stack item remains in order. Loads leave memory unchanged;
stores use the imported update. Execution stops at the first failure and
returns `none`, with no resulting state; the model does not expose the
intermediate state or claim rollback of effects in a real runtime.

`write_then_read` proves that pushing a value and address, storing, pushing the
same address, and loading succeeds for any in-bounds address, returning the
value above the original arbitrary stack tail. Memory retains its size, the
address reads back the value, and all other backing cells are unchanged, even
outside the accessible range. `load_out_of_bounds` and
`store_out_of_bounds` prove failure for all addresses at or beyond the bound,
including with arbitrary following instructions. The reference also checks
representative underflow and wrong-tag failures. These are general Lean
theorems, not a finite runtime comparison.

The model has no byte layout, finite-width cell arithmetic, address conversion,
alignment, allocation, permissions, aliasing or concurrency effects. Its
function-backed memory has inaccessible cells, whose preservation is a model
property. It assumes the handwritten semantics describe the intended abstract
operations; it establishes no correspondence with Forth-2012, Gforth, a
LeanForth implementation, or machine execution. No LeanForth kernel checks
these results, and no new axioms or `sorry` are introduced.

## Reproducing the check

On 2026-11-01, Linux x86-64 WSL2, the local toolchain reported Lean 4.35.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. These commands passed
with exit status zero from the repository root:

```sh
mkdir -p /tmp/leanforth-memory-reference
.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -o /tmp/leanforth-memory-reference/program-contracts.olean tests/reference/program-contracts.lean
LEAN_PATH=/tmp/leanforth-memory-reference .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean tests/reference/memory-program-reference.lean
```

The temporary compiled import is needed because Lean imports compiled modules;
the escaped module name preserves the existing hyphenated source filename.
Rebuild the import when the source changes. `make reference` now builds the
dependency in an isolated temporary directory and checks this file. CI was not
run for this change.

SHA-256 at verification time:

```text
3cb499863916d2c5ccaa44eba24ece852b59f81ad25843a5336212f93f646d27  tests/reference/program-contracts.lean
fee5e49425ed17e7d3777684dcb8fcc3ccbbdbcb4ac59f552bcd5bc87aee9e46  tests/reference/memory-program-reference.lean
bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38  .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
```

This advances the program track's abstract representation and execution
model; it does not change the theorem track, shared proof kernel, or NDJSON
import status. The approximately ten milestones on each track and their
remaining work are recorded in `docs/PROJECT_PROGRESS.md`; full Mathlib
compatibility, independent proof checking, and verified Forth execution remain
open. See the progress report for the current status.
