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

The `Option` values abstract the different stack results on failure and
success. No theorem connects these definitions to Forth words, stack effects,
flag encodings, signed comparisons, `NEGATE`, cell representation, stack
capacity, execution, a compiler, or a runtime. No machine arithmetic or
source-to-model correspondence is verified. In particular, these proofs do
not establish correctness or safety of the executable examples, nor do they
show that LeanForth checks these proofs. The other example words are not
covered. The file is included in `make reference`; CI status has not been
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
