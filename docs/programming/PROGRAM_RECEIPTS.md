# Program receipts, schema version 0.2

**Status: version 0.2 approved by the owner on 2026-11-03 ([format] gate;
schema SHA-256 `bb76793e1cba339d…`, pinned by a test; any change is a new
version). Implemented as a schema with examples, a validator and a strict
reader (version 0.2, 2026-11-03; the draft 0.1 of 2026-11-02, task 2.5.1
of the [plan draft](../project/PLAN_DRAFT.md), is superseded and refused).
The clamp
receipt of task 2.5.6 is generated** by `scripts/program_receipt.py` from
the actual checks ([verification conditions and the clamp
receipt](PROGRAM_VC.md)). The format falls under the *[format]* review gate
of `AGENTS.md`: it is a proposal until the owner approves it.

A program receipt records what is known about one Forth word, and on what
it rests. It answers three separate questions and never merges them into
one verdict:

| Part | Question | Statuses |
| --- | --- | --- |
| `check` | Was a proof about the word checked, and by which checker? | `not-checked`, `checked-by-lean-reference`, `accepted-by-leanforth`, `rejected`, `unsupported`, `failed` |
| `verify` | Are the proof obligations of the word's contract all discharged, and by which check? | `not-generated`, `open`, `discharged`, `refuted`, `unsupported` |
| `run` | What did runtime tests on a named host show? | `not-run`, `passed`, `failed` |

A receipt has no `verified`, `ok` or `status` field, and the schema rejects
any field it does not define. A reader who wants a one-word answer must
look at all three parts and at the assumptions; that is deliberate
(`AGENTS.md`: compiled code and runtimes are trusted boundaries to report,
and a source proof does not verify them).

- **Schema:** [`schemas/program-receipt-0.2.schema.json`](../../schemas/program-receipt-0.2.schema.json)
  (JSON Schema draft 2020-12, subset below; its patterns are also valid
  ECMA-262 expressions for the `u` flag). The superseded draft 0.1,
  [`schemas/program-receipt-0.1.schema.json`](../../schemas/program-receipt-0.1.schema.json),
  is kept unchanged as a record only: the reader refuses every receipt
  that names it ([versioning](#versioning)).
- **The generated receipt:** [`tests/program/receipts/generated/lf-clamp.json`](../../tests/program/receipts/generated/lf-clamp.json)
  and its [printed form](../../tests/program/receipts/generated/lf-clamp.md).
- **Examples:** [`tests/program/receipts/`](../../tests/program/receipts/):
  three valid hand-written receipts (clamp checked by the Lean reference
  without obligations; gcd with nothing checked or run yet; the shape a
  phase 5 receipt checked by LeanForth will have) and four invalid ones,
  each rejected for one pinned reason. The 0.1 examples and the 0.1 clamp
  receipt are kept in [`tests/program/receipts/0.1/`](../../tests/program/receipts/0.1/)
  as a record, and the reader refuses them. Hand-written examples are never
  evidence.
- **Validator:** [`tests/support/schema_subset.py`](../../tests/support/schema_subset.py),
  Python standard library only.
- **Reader:** `scripts/program_receipt.py validate` reads a receipt
  strictly and checks its schema and the [rules beyond JSON
  Schema](#rules-beyond-json-schema); `verify` also replays it.
- **Tests:** [`tests/program/test_receipts.py`](../../tests/program/test_receipts.py)
  and [`tests/program/receipt_check.py`](../../tests/program/receipt_check.py),
  part of `make test`.

## The three statuses in plain words

Take `lf-clamp ( value lower upper -- result true | false )`.

- Mathematics: for integers v, l, u in the cell range with l ≤ u the word
  returns r = min(max(v, l), u) and true, so l ≤ r ≤ u; for l > u it
  consumes its three inputs and returns false. Cells below are kept.
- Forth: `: lf-clamp 2dup > if 2drop drop false exit then >r max r> min true ;`
  in `src/program/clamp.fs`, with its contract in
  `tests/program/contracts/lf-clamp.contract`.
- Lean: `ProgramVC.LfClamp0.contract` in `tests/program/vc/obligations.lean`
  states the contract against the IR's semantics for every cell width,
  input and stack below, and is proved from the path obligations
  `ProgramVC.LfClamp0.O1` and `O2` ([verification conditions](PROGRAM_VC.md)).

Its generated receipt says:

- **check: `checked-by-lean-reference`.** Lean 4.35.0 checked
  `ProgramVC.LfClamp0.contract`, `ProgramVC.LfClamp0.O1` and
  `ProgramVC.LfClamp0.O2`. Each theorem lists its own axioms (`O1`:
  propext and Quot.sound; the other two also Classical.choice), and
  `check.axioms` lists their union. The label must read *checked by the
  Lean reference, not by LeanForth*: LeanForth's own checker cannot check
  programs before data types arrive (phase 5, owner answer OQ-5).
- **verify: `discharged`, settled by `checked-by-lean-reference`.** The
  untrusted generator `scripts/program_vc.py` produced two obligations from
  the IR and the contract, one per path through the word; Lean discharged
  each with the theorem named with it. `verify.settledBy` says which check
  did that: the Lean reference, not LeanForth.
- **run: `passed`.** The three-way runtime comparison ran 986 cases on
  Gforth 1.0.0, Linux x86-64, 64-bit cells, with 0 failures; Lean's model
  agreed on all 991 clamp cases. The label must read *runtime-tested;
  testing is not proof*.

and lists seven assumptions: one signed host cell per value, two's
complement, the reader translated the source faithfully
(`trusted-reader`), Gforth executes the words as the IR semantics says
(`trusted-runtime`), the stacks have room, Lean checked the theorems
correctly (`trusted-lean`), and the obligations come from an untrusted
generator, safe only because the contract theorem is stated against the IR
semantics (`untrusted-generator`).

When LeanForth's checker accepts the obligations (phase 5), `check` becomes
`accepted-by-leanforth` with the label *experimental — not independently
audited* and the assumption that LeanForth's checker accepted the proofs
correctly (`trusted-leanforth`), and `verify.settledBy` becomes
`accepted-by-leanforth`; `valid-clamp-future-leanforth.json` shows the
shape. `run` stays separate: a source proof says nothing about the compiler
or the runtime.

## Rules the schema enforces

Besides types, required fields and closed objects. A *positive* check is
`checked-by-lean-reference` or `accepted-by-leanforth`; every other check
status has accepted nothing. A *settled* obligation is `discharged` or
`refuted`.

| Rule | Why |
| --- | --- |
| Each `check.status` has exactly one label: `not-checked` *not checked*; `checked-by-lean-reference` *checked by the Lean reference, not by LeanForth*; `accepted-by-leanforth` *experimental — not independently audited*; `rejected` *rejected by the checker*; `unsupported` *not supported by the checker*; `failed` *check did not complete* | A failure can never carry a success's label; owner decision 1 labels every accepted result until an outside audit |
| Each `run.status` has exactly one label: `not-run` *not run*; `passed` *runtime-tested; testing is not proof*; `failed` *runtime tests failed* | A failed or missing run can never carry a pass's label |
| `checked-by-lean-reference` needs checker `lean`, at least one theorem and one evidence file; `accepted-by-leanforth` the same with checker `leanforth`; any checker is `lean` or `leanforth` | A Lean check can never be passed off as LeanForth's, and a script is not a checker |
| Each theorem in `check.theorems` lists its own `axioms`, and `check.axioms` their union; axioms may be only `propext`, `Classical.choice` and `Quot.sound`, whatever the status, and only a positive check may name any | The owner's axiom policy, reported per theorem (`AGENTS.md`); `sorryAx` and `Lean.ofReduceBool` can never appear in a receipt |
| Every status but `not-checked` names its checker; `not-checked` names no checker, no theorems and no evidence | Who rejected or failed is part of the result; nothing checked has nothing to show |
| A positive check needs `program.ir` (not `null`), and so does every `verify.status` but `not-generated`; an IR needs a `trusted-reader` assumption | The theorems and the obligations are about the IR; only the IR ties them to the source |
| A settled obligation names its theorem, an `open` one names none; any settled obligation, whatever `verify.status` says, needs a positive check | Obligations are settled only by checked proofs |
| `verify.settledBy` is present exactly when an obligation is settled, and equals `check.status` | Says who discharged the obligations: the Lean reference or LeanForth |
| `verify.status` `discharged` needs every obligation `discharged` and the contract's Lean theorem and file (`contract.lean`, `contract.file`); every status but `not-generated` names its generator; `not-generated` has no generator and no obligations; `open` has an open one and none refuted; `refuted` a refuted one; `unsupported` lists none | Obligations from an untrusted generator prove the contract only through the contract theorem proved from them; a partial list could be read as the whole |
| `run.status` `passed` needs a host, at least one case, zero failures and evidence; `failed` a host, a failure and evidence; `not-run` zero cases, no host and no evidence | |
| `assumptions` always include `trusted-runtime`, `host-cells`, `twos-complement` and `stack-capacity` entries | The runtime, the cell width, its arithmetic and the stacks are always trusted boundaries |
| `checked-by-lean-reference` needs a `trusted-lean` assumption and the tool `lean`; `accepted-by-leanforth` a `trusted-leanforth` assumption and the tool `leanforth`, and no other receipt may have a `trusted-leanforth` assumption; a verify that names a generator needs `untrusted-generator`; `floatingPoint: true` needs `floating-point` | Each trusted component is named, and LeanForth's checker only where it checked |
| `program.word` is printable ASCII with letters in lower case, the spelling the IR uses | The reader folds A–Z as Gforth does, so one word has one name |
| Hashes are 64 lowercase hex digits (SHA-256); paths are relative and stay inside the repository (segments separated by single slashes, none starting with a dot, so no `..` and no `.git`); dates are real calendar dates; `provenance.kind` `generated` needs its generator | Receipts must be reproducible and must not point outside the repository |
| Every text and note has at least one printable ASCII character other than a space, and no control character, no format character (bidirectional controls, zero-width characters, tags: Unicode Cf), no line or paragraph separator and no surrogate | A text cannot be blank or invisible, cannot start a new line, and shows what it says |

`provenance.kind` is `example` for hand-written receipts such as those in
`tests/program/receipts/`: they illustrate the schema and are **not
evidence**. Generated receipts say `generated` and name the tool.

## Rules beyond JSON Schema

JSON Schema cannot compare one field with another, so the reader checks
these rules of schema 0.2 after the schema (`rule_problems` in
`scripts/program_receipt.py`):

- assumption ids, obligation ids and theorem names are distinct, and no
  axiom list repeats an axiom;
- `check.axioms` is exactly the union of the theorems' axioms;
- each settled obligation's theorem is among `check.theorems`, and for a
  `discharged` verify so is `contract.lean`;
- `run.failures` is at most `run.cases`;
- `check.checker` and `verify.generator` are among `tools`.

**Left to replay.** A receipt that passes the schema and the rules is well
formed, not true: nothing here looks inside the files it names or reruns
a check. That the theorems use no axiom left unlisted, that the checker is
the pinned toolchain, that the generator named in `provenance` wrote the
receipt and that the hashes match the files are checked by replaying the
receipt: `scripts/program_receipt.py verify` does it for the clamp receipt
today, and task 5.5.2 (phase 5) for receipts in general.

**Notes and texts are unchecked prose.** The schema checks that a note, a
statement or an assumption's text is visible text on one line, never what
it says. A note reading *verified by LeanForth* is still only a note: only
the status fields, the fixed labels and the rules above carry meaning.
Read the parts, not the prose.

## Reading a receipt

```sh
python3 -I scripts/program_receipt.py validate RECEIPT.json...    # strict JSON, schema, rules
python3 -I scripts/program_receipt.py verify tests/program/receipts/generated/lf-clamp.json
python3 -I tests/support/schema_subset.py schemas/program-receipt-0.2.schema.json RECEIPT.json
```

`validate` reads each receipt with the strict loader, requires
`schemaVersion` 0.2, and checks schema 0.2 and the rules beyond JSON
Schema; `verify` does the same for one receipt and then replays it. A
receipt that names the superseded draft 0.1 is refused with its own code:
0.1 lacks the rules 0.2 added, so reading it would let a receipt escape
them by naming the older version. Both print nothing and exit 0 when there
is no problem; otherwise they print one line per problem on standard error
and exit 1 (2 for a usage error). Each line is `FILE: CODE: PATH: MESSAGE`:

| Code | Meaning |
| --- | --- |
| `unreadable` | The file cannot be opened or is not UTF-8; nothing else is checked |
| `not-strict-json` | The file is not strict JSON (see below); nothing else is checked |
| `superseded-version` | `schemaVersion` is `0.1`, a draft that was never approved; nothing else is checked |
| `unknown-version` | `schemaVersion` is missing or is not `0.2` |
| `schema` | The schema refuses the receipt; PATH is the JSON path, such as `$.run.label` |
| `rule` | A rule beyond JSON Schema fails |
| `replay` (`verify` only) | The field differs from the receipt rebuilt from the repository and the recorded evidence |

`schema_subset.py` checks only the schema, one line `FILE: PATH: MESSAGE`
per problem.

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
local or does not point at a schema (a `$ref` into a `properties` map or a
`required` list is refused), or a keyword value of the wrong shape is
refused before anything is validated, so the schema cannot appear to
enforce a rule the validator does not implement. A pattern's `^`, `$` and
`.` mean what they mean in ECMA-262, as JSON Schema says: `^...$` must match
the whole string (Python's `$` would also match before a final newline),
and `.` matches no line terminator (Python's would match a carriage return
or U+2028); inline flags are refused. The schema's patterns use only
syntax both engines share, so a standard validator (ECMA-262 with the `u`
flag, as ajv uses) compiles them too: characters outside the Basic
Multilingual Plane are written as JSON escapes, never as Python's
`\UXXXXXXXX`. When node is installed, `make test` compiles every pattern
with the `u` flag and checks that it accepts the same sample strings as
the Python reading.

Documents are parsed strictly, and every reader of receipts uses this
loader: duplicate keys are errors (Python's `json` would keep the last),
and so are `NaN` and `Infinity`; any number with a fraction or an exponent
(no receipt field is fractional, and `1e-400` or `12.0000000000000001`
would be read lossily); integers outside I-JSON's exact range
±(2^53 − 1); lone surrogates; nesting deeper than 64 levels (a receipt
needs 5); text after the document and a byte-order mark. `true` is not the
number 1. No size limit is enforced yet: a receipt with a 5 MB note is
read.

`test_receipts.py` validates every example, checks that each invalid
example, each small mutation of the receipts (at least one for every rule
above, and one for every finding of the review of 2026-11-03) and each
mutation that breaks a rule beyond JSON Schema fails for its stated reason,
checks the validator's own rules, plants a fault in the validator (it stops
checking `contains`) and in the rules (they stop finding duplicates) to
show that the suites catch them, pins schemas 0.1 and 0.2 by their hashes,
checks that every 0.1 receipt, and each hole 0.2 closed written into a 0.1
receipt, is refused as `superseded-version`, and checks that the JSON
receipt below is the generated one. `receipt_check.py`
checks the generated receipt and that tampered receipts and texts are
refused by the layer named with each.

## A complete receipt

The generated clamp receipt (`tests/program/receipts/generated/lf-clamp.json`):

```json
{
  "schema": "leanforth-program-receipt",
  "schemaVersion": "0.2",
  "provenance": {
    "kind": "generated",
    "generator": {
      "name": "python",
      "version": "program_receipt.py 0.2"
    },
    "createdAt": "2026-11-02",
    "note": "Written by scripts/program_receipt.py from the repository files named below, at the hashes given, and the evidence recorded on 2026-11-02 by make check. A receipt is a statement of evidence, not an approval; it passes no review gate."
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
    "statement": "For integers v, l, u in the cell range: if l ≤ u the word returns r = min(max(v, l), u) and true, so l ≤ r ≤ u, r = v when l ≤ v ≤ u, r = l when v < l and r = u when v > u; if l > u it consumes its three inputs and returns false. Cells below are kept.",
    "lean": "ProgramVC.LfClamp0.contract",
    "file": {
      "path": "tests/program/contracts/lf-clamp.contract",
      "sha256": "841a7163bb05f9f7519606cf49c2cd33b228ea2ce7c50c70dcd512f4a5783af2"
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
      {
        "name": "ProgramVC.LfClamp0.contract",
        "axioms": [
          "propext",
          "Classical.choice",
          "Quot.sound"
        ]
      },
      {
        "name": "ProgramVC.LfClamp0.O1",
        "axioms": [
          "propext",
          "Quot.sound"
        ]
      },
      {
        "name": "ProgramVC.LfClamp0.O2",
        "axioms": [
          "propext",
          "Classical.choice",
          "Quot.sound"
        ]
      }
    ],
    "label": "checked by the Lean reference, not by LeanForth",
    "axioms": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "evidence": [
      {
        "path": "tests/program/vc/obligations.lean",
        "sha256": "8eca805030d431fcca39d5503435433ddf6ccf5dc4143955ae6a81ed88b92df2"
      },
      {
        "path": "scripts/program_vc.py",
        "sha256": "2be3fb1a81593e2c34699681597246472417b1763e7de8893bfbace540efbd18"
      }
    ],
    "note": "Lean proved ProgramVC.LfClamp0.contract, the contract stated against the IR semantics for every cell width, input and stack below, from the path obligations listed under verify. Checked by Lean 4.35.0, not by LeanForth, whose checker cannot check programs yet."
  },
  "verify": {
    "status": "discharged",
    "settledBy": "checked-by-lean-reference",
    "generator": {
      "name": "python",
      "version": "program_vc.py 0.1"
    },
    "obligations": [
      {
        "id": "O1",
        "statement": "If lower > upper: the word leaves false (bottom first), and the postcondition holds.",
        "status": "discharged",
        "theorem": "ProgramVC.LfClamp0.O1"
      },
      {
        "id": "O2",
        "statement": "If lower ≤ upper: the word leaves min(max(value, lower), upper), true (bottom first), and the postcondition holds.",
        "status": "discharged",
        "theorem": "ProgramVC.LfClamp0.O2"
      }
    ],
    "note": "One obligation per path through the word's IR (IF splits a path), generated by an untrusted generator from the IR and the contract; each is discharged by the Lean theorem named with it, checked by the Lean reference, not by LeanForth."
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
    "cases": 986,
    "failures": 0,
    "label": "runtime-tested; testing is not proof",
    "evidence": [
      {
        "path": "tests/program/ir-run-table.fs",
        "sha256": "dad809a3718e09f7b2aa05036fad14de27527e1ceaa105a2b7bf39c52b40d0f9"
      },
      {
        "path": "src/program/ir-run.fs",
        "sha256": "32f12815f6fbe902467d1c8858a993f8e3e5179f6fc51cc85f8053471f2c25b6"
      },
      {
        "path": "tests/program/ir_run_differential.py",
        "sha256": "be6ae1f4b269b74e4a4ddec292f42a9def395daa14fa5cc7e7737de10422b705"
      },
      {
        "path": "tests/reference/program-ir-run.lean",
        "sha256": "e1dc7a719b655a13224777cc0cc292cbc301ee7583e4009f0db7e175381bc95b"
      }
    ],
    "note": "On 986 inputs (the existing clamp tables and seeded random cells) the host word and the IR interpreter left the same stack; Lean's evaluation of the model agreed on all 991 clamp cases, including failures the host cannot run (too few inputs, no fuel)."
  },
  "assumptions": [
    {
      "id": "A1",
      "kind": "host-cells",
      "text": "Every value is one signed host cell. The Lean theorems hold for every cell width of at least two bits; the runtime comparison ran on 64-bit cells."
    },
    {
      "id": "A2",
      "kind": "twos-complement",
      "text": "Cells are two's complement, so the host's arithmetic wraps as the IR semantics says (src/lib/portability.fs)."
    },
    {
      "id": "A3",
      "kind": "trusted-reader",
      "text": "The reader (src/program/ir-reader.fs) translated the colon definition into the IR faithfully, and nothing else in the source file changes what its words mean on the host. The reader splits the file into lines at LF itself and finds names ignoring letter case as Gforth does; it refuses a redefinition, under any spelling, of a word it knows (the IR's words, some other standard words and the file's own), any byte outside printable ASCII other than a space, a tab, an LF and a CR just before an LF, and a division before CONSTANT; it never runs the source. Gforth is assumed to load the file with its default settings (decimal BASE, standard words), and the file to define no name that code compiled after it in the same session uses, other than the words under test: the reader accepts definitions of other host words, such as . or DEPTH, which would change what such code, a test harness for example, means. Nothing proves the translation; make test compares the reader's output with the IR named here."
    },
    {
      "id": "A4",
      "kind": "trusted-runtime",
      "text": "Gforth and its compiler execute 2DUP, >, IF, 2DROP, DROP, FALSE, EXIT, THEN, >R, MAX, R>, MIN and TRUE as the IR semantics says. The runtime comparison tested this on 986 cases; it does not prove it."
    },
    {
      "id": "A5",
      "kind": "stack-capacity",
      "text": "The data and return stacks have room for the word's items; stack overflow is not modeled."
    },
    {
      "id": "A6",
      "kind": "trusted-lean",
      "text": "Lean 4.35.0, the pinned toolchain, checked the theorems correctly."
    },
    {
      "id": "A7",
      "kind": "untrusted-generator",
      "text": "The obligations come from an untrusted generator (scripts/program_vc.py). This is safe only because the contract theorem Lean proved is stated against the IR semantics copied verbatim from tests/reference/program-ir.lean, and Lean prints the generated program back equal to the IR file; lf-clamp's proof is not checked by LeanForth."
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
    },
    {
      "name": "python",
      "version": "program_vc.py 0.1"
    }
  ]
}
```

## Versioning

`schemaVersion` names the schema a receipt follows. A schema, once a
receipt names it, keeps its meaning: any change to the fields or rules
gives a new version and a new schema file next to the old one. Until the
owner approves the format (the *[format]* gate), every version is a draft,
and a draft that a later version supersedes is not read at all: it lacks
rules the later version added, so the reader refuses a receipt that names
it (`superseded-version`) rather than let the receipt choose the weaker
rules. What happens to receipts of an approved version when a later
version comes is for the owner to decide at the gate.

- **0.1** (2026-11-02): the first draft, never approved. It was tightened in
  place after an independent review, before any receipt had been
  generated; then the clamp receipt was generated as 0.1. Superseded by
  0.2: the reader refuses every 0.1 receipt. The file is kept byte for byte
  as a record (a test pins its hash), with its examples and the 0.1 clamp
  receipt in `tests/program/receipts/0.1/`.
- **0.2** (2026-11-03), after the independent review of 0.1, and what the
  generator now writes; the clamp receipt was regenerated. Changes:
  `run.label` required with one label per run status, and `not-run` with no
  host and no evidence; `verify.settledBy`, equal to `check.status`, when
  an obligation is settled; the assumption kind `untrusted-generator`,
  required when verify names a generator; a generator for every verify
  status but `not-generated`, the IR for every one but `not-generated`, no
  obligations for `unsupported`, and the contract's theorem and file for
  `discharged`; `twos-complement` and `stack-capacity` always required;
  `trusted-leanforth` only on receipts checked by LeanForth; a checker is
  `lean` or `leanforth`; `check.theorems` items are objects with a `name`
  and their own `axioms`; text rules for every text and note (notes must
  not be empty); and the rules beyond JSON Schema, checked by the reader.
  Later the same day, after the re-review, the text pattern was re-encoded
  (characters outside the Basic Multilingual Plane as JSON escapes instead
  of Python's `\UXXXXXXXX`, which ECMA-262 engines cannot compile). On
  every Unicode code point it accepts exactly what it accepted before, so
  no receipt's validity changed; a test pins the file's hash from then on.

The plan extends the schema to theorem receipts (task 3.4.3) and wraps it
in the versioned JSON-RPC interface (task 3.5.1, [interface
contracts](INTERFACE_CONTRACTS.md)).
