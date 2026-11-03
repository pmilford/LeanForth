# Program receipts, schema version 0.1

**Status: implemented as a schema with examples and a validator
(2026-11-02, task 2.5.1 of the [plan draft](../project/PLAN_DRAFT.md)).
Nothing writes receipts yet;** the first generated one is the clamp receipt
of task 2.5.6. The format falls under the *[format]* review gate of
`AGENTS.md`: it is a proposal until the owner approves it.

A program receipt records what is known about one Forth word, and on what
it rests. It answers three separate questions and never merges them into
one verdict:

| Part | Question | Statuses |
| --- | --- | --- |
| `check` | Was a proof about the word checked, and by which checker? | `not-checked`, `checked-by-lean-reference`, `accepted-by-leanforth`, `rejected`, `unsupported`, `failed` |
| `verify` | Are the proof obligations of the word's contract all discharged? | `not-generated`, `open`, `discharged`, `refuted`, `unsupported` |
| `run` | What did runtime tests on a named host show? | `not-run`, `passed`, `failed` |

A receipt has no `verified`, `ok` or `status` field, and the schema rejects
any field it does not define. A reader who wants a one-word answer must
look at all three parts and at the assumptions; that is deliberate
(`AGENTS.md`: compiled code and runtimes are trusted boundaries to report,
and a source proof does not verify them).

- **Schema:** [`schemas/program-receipt-0.1.schema.json`](../../schemas/program-receipt-0.1.schema.json)
  (JSON Schema draft 2020-12, subset below).
- **Examples:** [`tests/program/receipts/`](../../tests/program/receipts/):
  three valid receipts (clamp checked by the Lean reference; gcd with
  nothing checked or run yet; the shape a phase 5 receipt checked by
  LeanForth will have) and four invalid ones, each rejected for one pinned
  reason.
- **Validator:** [`tests/support/schema_subset.py`](../../tests/support/schema_subset.py),
  Python standard library only.
- **Tests:** [`tests/program/test_receipts.py`](../../tests/program/test_receipts.py),
  part of `make test` (target `test-program-ir`).

## The three statuses in plain words

Take `lf-clamp ( value lower upper -- result true | false )`.

- Mathematics: for integers v, l, u with l ≤ u the word returns
  min(max(v, l), u) and true, so l ≤ result ≤ u; for l > u it returns
  false.
- Forth: `: lf-clamp 2dup > if 2drop drop false exit then >r max r> min true ;`
- Lean: `ProgramIR.clamp_correct` in `tests/reference/program-ir.lean`
  states that the word's IR returns exactly that, for every cell width and
  every stack below the inputs ([program IR](PROGRAM_IR.md)).

Its receipt today says:

- **check: `checked-by-lean-reference`.** Lean 4.35.0 checked
  `clamp_correct`. The label must read *checked by the Lean reference, not
  by LeanForth*: LeanForth's own checker cannot check programs before data
  types arrive (phase 5, owner answer OQ-5).
- **verify: `not-generated`.** Proof obligations will be generated from the
  IR and a contract by task 2.5.5; until then there are none.
- **run: `passed`.** `make test-program-differential` ran 686 cases on
  Gforth 1.0.0, x86-64, 64-bit cells. The label must read *runtime-tested;
  testing is not proof*.

and lists its assumptions: one signed host cell per value, two's
complement, the reader translated the source faithfully, Gforth executes
the words as the IR semantics says, the stacks have room, Lean checked the
theorems correctly.

When LeanForth's checker accepts the obligations (phase 5), `check` becomes
`accepted-by-leanforth` with the label *experimental — not independently
audited*, and `verify` becomes `discharged`, listing each obligation and the
theorem that proves it. `run` stays separate: a source proof says nothing
about the compiler or the runtime.

## Rules the schema enforces

Besides types, required fields and closed objects:

| Rule | Why |
| --- | --- |
| `check.status` `checked-by-lean-reference` needs checker `lean`, at least one theorem and one evidence file, and the label *checked by the Lean reference, not by LeanForth* | A Lean check can never be passed off as LeanForth's |
| `accepted-by-leanforth` needs checker `leanforth`, theorems, evidence and the label *experimental — not independently audited* | Owner decision 1: every accepted result is labelled until an outside audit |
| For both, `check.axioms` may name only `propext`, `Classical.choice` and `Quot.sound` | The owner's axiom policy; `sorryAx` and `Lean.ofReduceBool` can never appear in a checked receipt |
| `not-checked` has the label *not checked* and no axioms | |
| `verify.status` `discharged` needs `check.status` `checked-by-lean-reference` or `accepted-by-leanforth`, a generator, and every obligation `discharged` with its theorem | Obligations are discharged only by checked proofs |
| `not-generated` has no obligations; `open` has an open one; `refuted` a refuted one | |
| `run.status` `passed` needs a host, at least one case, zero failures and the label *runtime-tested; testing is not proof*; `failed` needs a failure; `not-run` has zero cases | |
| `assumptions` always include a `trusted-runtime` and a `host-cells` entry | The runtime and cell width are always trusted boundaries |
| A Lean check needs a `trusted-lean` assumption; an IR needs `trusted-reader`; `floatingPoint: true` needs `floating-point` | Each trusted component is named |
| Hashes are 64 lowercase hex digits (SHA-256); paths are relative to the repository root; `provenance.kind` `generated` needs its generator | Receipts must be reproducible |

`provenance.kind` is `example` for hand-written receipts such as those in
`tests/program/receipts/`: they illustrate the schema and are **not
evidence**. Generated receipts will say `generated` and name the tool.

A receipt that validates is well formed, not true: the validator checks the
shape and the consistency of the three parts, never the claims themselves.
Replaying a receipt (phase 5, task 5.5.2) is what checks the claims.

## The validator and its JSON Schema subset

The owner's default is to install nothing new (question OQ-12 of the plan
draft), so receipts are validated by a small standard-library validator
instead of the `jsonschema` package. It implements exactly these keywords:
`type`, `properties`, `required`, `additionalProperties` (boolean only),
`const`, `enum`, `pattern`, `minLength`, `minimum`, `maximum`, `items`,
`minItems`, `maxItems`, `contains`, `allOf`, `anyOf`, `if`/`then`/`else`,
`not`, local `$ref` into `$defs`, and the annotations `$schema`, `$id`,
`$comment`, `title`, `description`.

It fails closed: a schema that uses any other keyword, a `$ref` that is not
local or does not resolve, or a keyword value of the wrong shape is refused
before anything is validated, so the schema cannot appear to enforce a rule
the validator does not implement. Documents are parsed strictly: duplicate
keys, `NaN` and `Infinity` are errors, `true` is not the number 1, and a
pattern's final `$` does not match before a trailing newline.

```sh
python3 tests/support/schema_subset.py schemas/program-receipt-0.1.schema.json RECEIPT.json
python3 tests/program/test_receipts.py
```

`test_receipts.py` validates every example, checks that each invalid
example and each of 30 small mutations of the clamp receipt fails for its
stated reason, checks the validator's own rules, and plants a fault in
the validator (it stops checking `contains`) to show that the mutation
suite catches it. It also validates the JSON example below.

## A complete receipt

The valid clamp example (`tests/program/receipts/valid-clamp-lean-reference.json`):

```json
{
  "schema": "leanforth-program-receipt",
  "schemaVersion": "0.1",
  "provenance": {
    "kind": "example",
    "createdAt": "2026-11-02",
    "note": "Written by hand to illustrate schema 0.1; not evidence. What it states held at the commit that added it: tests/reference/program-ir.lean proves clamp_correct and make test-program-differential passed 686 cases."
  },
  "program": {
    "word": "lf-clamp",
    "stackEffect": "( value lower upper -- result true | false )",
    "source": {
      "path": "src/program/clamp.fs",
      "line": 12,
      "sha256": "e4444161f4a3436b1a4509338e15fe2aeb47cab1f4327069e31b401bf1dc6a30"
    },
    "ir": {
      "version": "0.1",
      "sha256": "651875025cec88f7ae5b6669b227df28ebd3bbcbc29f11af08370024bf5cfb50"
    },
    "floatingPoint": false
  },
  "contract": {
    "id": "lf-clamp/0",
    "statement": "For integers v, l, u: if l ≤ u the word returns min(max(v, l), u) and true; if l > u it consumes its three inputs and returns false. Cells below are kept.",
    "lean": "ProgramIR.clamp_correct",
    "file": {
      "path": "tests/reference/program-ir.lean",
      "sha256": "c2cd91dec1b7f9fb6c45abaec64225d64f9c62ef7bed8317565de9f6359fca97"
    }
  },
  "check": {
    "status": "checked-by-lean-reference",
    "checker": {
      "name": "lean",
      "version": "4.35.0",
      "commit": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
    },
    "theorems": [
      "ProgramIR.clamp_correct",
      "ProgramIR.clamp_matches_stack_model"
    ],
    "label": "checked by the Lean reference, not by LeanForth",
    "axioms": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "evidence": [
      {
        "path": "tests/reference/program-ir.lean",
        "sha256": "c2cd91dec1b7f9fb6c45abaec64225d64f9c62ef7bed8317565de9f6359fca97"
      }
    ],
    "note": "The theorems are about the IR's semantics, not about Gforth running the source."
  },
  "verify": {
    "status": "not-generated",
    "obligations": [],
    "note": "Verification conditions are generated from 2.5.5 on."
  },
  "run": {
    "status": "passed",
    "host": {
      "forth": "gforth",
      "version": "1.0.0",
      "os": "linux",
      "arch": "x86-64",
      "cellBits": 64
    },
    "cases": 686,
    "failures": 0,
    "label": "runtime-tested; testing is not proof",
    "evidence": [
      {
        "path": "tests/program/differential.sh",
        "sha256": "1019ee9ea260254b5555696c3c7557cad97ceba65dee0e1acec12f69ec640a1c"
      }
    ]
  },
  "assumptions": [
    {
      "id": "A1",
      "kind": "host-cells",
      "text": "Every value is one signed host cell; the Lean theorems hold for every cell width of at least two bits, the runtime tests ran on 64-bit cells."
    },
    {
      "id": "A2",
      "kind": "twos-complement",
      "text": "Cells use two's complement, so arithmetic wraps as the IR semantics says; the clamp itself does no arithmetic."
    },
    {
      "id": "A3",
      "kind": "trusted-reader",
      "text": "The reader translated the colon definition into the IR faithfully; nothing checks the translation itself."
    },
    {
      "id": "A4",
      "kind": "trusted-runtime",
      "text": "Gforth and its compiler execute 2DUP, >, IF, 2DROP, DROP, >R, MAX, R>, MIN, TRUE, FALSE and EXIT as the IR semantics says."
    },
    {
      "id": "A5",
      "kind": "stack-capacity",
      "text": "The data and return stacks have room for the word's items; underflow and overflow are not proved absent on the host."
    },
    {
      "id": "A6",
      "kind": "trusted-lean",
      "text": "Lean 4.35.0 (the pinned toolchain) checked the theorems correctly."
    }
  ],
  "tools": [
    {
      "name": "lean",
      "version": "4.35.0",
      "commit": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
    },
    {
      "name": "gforth",
      "version": "1.0.0"
    }
  ]
}
```

## Versioning

`schemaVersion` is `0.1`, the first version of the v0 series. Any change to
the fields or rules gives a new version and a new schema file next to this
one; old receipts keep validating against the schema they name. The plan
extends the schema to theorem receipts (task 3.4.3) and wraps it in the
versioned JSON-RPC interface (task 3.5.1, [interface contracts](INTERFACE_CONTRACTS.md)).
