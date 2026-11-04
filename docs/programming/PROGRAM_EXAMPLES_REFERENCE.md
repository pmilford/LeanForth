# Independent Lean references for program examples

`tests/reference/program-examples.lean` gives two mathematical models inspired
by `src/program/examples.fs`. They use Lean integers, `Option` for failure or
success, and `Bool` for interval membership. They do not import LeanForth or
translate or execute the Forth source.

- `checkedAbs_correct` assumes integer bounds `min = -max - 1`, `0 ≤ max`,
  and `min ≤ n ≤ max`. It proves that the model rejects exactly the minimum
  input; otherwise it returns the integer absolute value, which lies between
  zero and `max`. The bounds describe the range of a two's-complement signed
  cell, without fixing a cell width.
- `inRange_reversed` proves that reversed bounds are rejected.
  `inRange_ordered` and `inRange_ordered_false` prove that, for ordered
  bounds, success is respectively true exactly for inclusive membership and
  false exactly when the value is outside. These statements use arbitrary
  integers; applying them to cells requires representable inputs.

The two words' contracts, in the style of `ClampContract` (plan task
1.5.3), are predicates on candidate functions:

- `CheckedAbsContract`: for signed-cell bounds and an input in the cell,
  `CheckedAbsSpec` requires no result for the smallest cell and otherwise
  the magnitude `n.natAbs`, which lies between 0 and `max`.
  `checkedAbs_contract` proves that the model meets it; `absAcceptsMin`,
  Forth's `ABS` without the test, is refuted: it returns 8 for the
  smallest four-bit cell.
- `InRangeContract`: `InRangeSpec` requires no result for reversed bounds
  and, for ordered bounds, true exactly inside the closed interval and
  false exactly outside it. `inRange_contract` proves that the model meets
  it; `inRangeExclusiveUpper` (reports `10` outside `[0, 10]`) and
  `inRangeRejectsEqual` (rejects the one-point interval `[3, 3]` as if it
  were reversed) are refuted.

`InRangeContract` replaces the earlier `OrderedContract`, a restatement of
`inRange_ordered`, which said nothing about reversed bounds or values
outside the interval. [`program-ir.lean`](../../tests/reference/program-ir.lean)
copies both contracts and proves that the IR of `lf-checked-abs` and
`lf-in-range` meets the same clauses (`checkedAbs_meets_contract`,
`inRange_meets_contract`; see
[program IR](PROGRAM_IR.md#contracts-of-the-five-other-words)). On
2026-11-03 the file passed with `lean -DwarningAsError=true`; `#print
axioms` reports `propext`, `Classical.choice` and `Quot.sound` for the two
contracts and the two in-range refutations, and `propext` for
`absAcceptsMin_violates`. The SHA-256 under "Reproduction and trust"
predates them.

The `Option` values abstract the different stack results on failure and
success. Nothing in this file connects these definitions to Forth words,
stack effects, flag encodings, signed comparisons, `ABS`, cell
representation, stack capacity, execution, a compiler, or a runtime; the
IR theorems of `program-ir.lean` connect them to the words' IR, not to
Gforth. These proofs do not establish correctness or safety of the
executable examples on a host, nor do they show that LeanForth checks
them. The file is included in `make reference`; CI status has not been
established by the local check.

## Reproduction and trust

From the repository root, run:

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --version
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean tests/reference/program-examples.lean
sha256sum tests/reference/program-examples.lean
```

On 2026-11-01 the commands reported Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux; the proof
command exited 0 without diagnostics. The file SHA-256 was
`df5fb9d9945a22d2a12cc55cedd4a0997ec397ba18674bdf44f2369ee0a56409`.
A separate `#print axioms` audit reported `propext` and `Quot.sound` for
`checkedAbs_correct`; `propext` for each of `inRange_reversed` and
`inRange_ordered`; and `propext`, `Classical.choice`, and `Quot.sound` for
`inRange_ordered_false`. These are Lean dependencies, not a claim about the
LeanForth kernel's axiom allowlist. Lean and its toolchain remain trusted for
this independent check. CI status was not checked or changed.
