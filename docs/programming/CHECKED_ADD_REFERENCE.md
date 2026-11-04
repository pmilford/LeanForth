# Checked addition: Lean reference

`tests/reference/checked-add.lean` defines a mathematical model of the branch
structure of `lf-checked-add` in `src/program/examples.fs`. `some (a + b)`
represents success and `none` represents failure. It is an independent Lean
reference, not a formal semantics of Forth and not a verified Forth program.

## Contract and proved properties

The inputs `a` and `b` are mathematical integers in the inclusive interval
`[min, max]`. The explicit signed bounds satisfy `0 ≤ max` and
`min = -max - 1`, matching the range of two's-complement signed cells. No
particular cell width is assumed. The model uses exact integer arithmetic and
strict signed comparisons; it does not define wraparound arithmetic.

For positive `b`, the model rejects when `a > max - b`; for negative `b`, it
rejects when `a < min - b`; for zero, it succeeds. Lean checks:

- `thresholds_safe`: the subtraction used in the applicable guard is itself
  representable, under the stated bounds and input assumption.
- `success_iff`: the model returns the exact mathematical sum precisely when
  that sum lies within the inclusive bounds.
- `failure_iff`: the model fails precisely when the sum lies below `min` or
  above `max`. The result specification applies to all representable inputs;
  the `b`-in-range and nonnegative-maximum assumptions are retained in the
  theorem signature as part of the common contract even where not needed by
  Lean's proof.

Concrete examples cover both endpoints, overflow in both directions, zero and
opposite-sign additions. These examples supplement the general proofs. Lean's
`omega` tactic constructs proof terms checked by Lean; no new axioms or
`sorry` are introduced in this file.

`CheckedAddContract` is the word's contract, in the style of `ClampContract`
(plan task 1.5.3): for signed-cell bounds and inputs in the cell,
`CheckedAddSpec` requires the exact sum when it fits the cell and no result
when it does not. `checkedAdd_contract` proves that the model meets it.
Three deliberately wrong variants are proved to violate it: `upperOffByOne`
(rejects when `max - b ≤ a`) wrongly rejects `6 + 1 = 7` in a four-bit
cell, `lowerOffByOne` (rejects when `a ≤ min - b`) wrongly rejects
`0 + (-8) = -8`, and `wrappingAdd`, which adds without a check and wraps as
Forth's `+` does, returns `-8` for `7 + 1`. `wrappingAdd_exact_when_fits`
shows that the last one returns every sum that fits, so only the contract's
failure clause rejects it. The contract replaces the earlier
`SuccessContract` (a restatement of `success_iff`), which that variant
would have met, since it never returns the exact sum on overflow.
[`program-ir.lean`](../../tests/reference/program-ir.lean) copies the
contract and proves that the IR of `lf-checked-add` meets the same clauses
(`checkedAdd_meets_contract`; see
[program IR](PROGRAM_IR.md#contracts-of-the-five-other-words)). On
2026-11-03 the file passed with `lean -DwarningAsError=true`; `#print
axioms` reports `propext`, `Classical.choice` and `Quot.sound` for the
contract and its three refutations. The SHA-256 below is from the earlier
2026-11-01 check.

## Forth and trust boundary

Relating these results to execution requires a separate proof of the word's
stack operations, branches, constants, signed comparisons, subtraction and
addition against this model. In particular, it assumes the host has the stated
two's-complement range, its operations agree with the modeled integer operations
when representable, and sufficient data and return stack space is available.
Those are assumptions, not conclusions of this reference. Forth-2012 portability
across host representations, a specific Gforth runtime, compilation and machine
execution are not established. The proofs were checked by Lean's kernel, not a
LeanForth kernel; no proof certificate import or runtime correspondence has
been implemented here.

## Reproduction and status

From the repository root, with the existing local toolchain installed:

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --version
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --githash
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean tests/reference/checked-add.lean
sha256sum tests/reference/checked-add.lean .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
```

On 2026-11-01 in Linux WSL2 x86-64, Lean reported 4.35.0, revision
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; the proof command exited 0 without
output. SHA-256: reference file
`5f318a5ad996c48b8c57c6fda6f9ffa5933000bcce6eb2a67f8c07e81b04ea96`, Lean binary
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
`bash scripts/check-env.sh` found Lean and Gforth absent from PATH; the local
Lean path above was used. The file is now included in `make reference`.
No CI run was made for this change; the previous
recorded GitHub Actions Smoke run 41120284014 passed for commit `44ca571`,
which does not include it.

See [project progress](../project/PROJECT_PROGRESS.md) for current milestone status,
import limitations, and the shared proof-kernel dependency.
