# Program receipts, schema version 0.3

**Status: version 0.3 (2026-11-12) is version 0.2 without `check.label`,
a [format] change the owner decided on 2026-11-12, when results stopped
carrying a label (check reports 0.4 and 0.5 and run records 0.3 dropped it
the same day). Version 0.2, approved by the owner on 2026-11-03 ([format]
gate; schema SHA-256 `bb76793e1cba339d…`), stays unchanged and readable;
the draft 0.1 of 2026-11-02 is superseded and refused. Implemented as
schemas with examples, a validator and a strict reader. The clamp receipt
is generated** by `scripts/program_receipt.py` from the actual checks
([verification conditions and the clamp receipt](PROGRAM_VC.md)). Since
plan task 5.5.1 (2026-11-12) its CHECK part is LeanForth's verdict: Lean
wrote the proofs, its exporter wrote them with every declaration they use,
and LeanForth's checker (`bin/leanforth check`) re-checked that export.
Receipts for IR 0.2 programs (the SHA-256 helper words) will take version
0.4 at the owner's [format] gate ([below](#schema-04-what-ir-02-receipts-need)).

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

- **Schema:** [`schemas/program-receipt-0.3.schema.json`](../../schemas/program-receipt-0.3.schema.json)
  (JSON Schema draft 2020-12, subset below; its patterns are also valid
  ECMA-262 expressions for the `u` flag). Version 0.2,
  [`schemas/program-receipt-0.2.schema.json`](../../schemas/program-receipt-0.2.schema.json),
  is kept unchanged and still read; the superseded draft 0.1,
  [`schemas/program-receipt-0.1.schema.json`](../../schemas/program-receipt-0.1.schema.json),
  is kept unchanged as a record only: the reader refuses every receipt
  that names it ([versioning](#versioning)).
- **The generated receipt:** [`tests/program/receipts/generated/lf-clamp.json`](../../tests/program/receipts/generated/lf-clamp.json)
  and its [printed form](../../tests/program/receipts/generated/lf-clamp.md),
  from the evidence [`lf-clamp-evidence.json`](../../tests/program/receipts/generated/lf-clamp-evidence.json)
  and the pinned export's manifest
  [`tests/program/vc/lf-clamp.ndjson.manifest.json`](../../tests/program/vc/lf-clamp.ndjson.manifest.json).
- **Examples:** [`tests/program/receipts/`](../../tests/program/receipts/):
  three valid hand-written receipts (clamp checked by the Lean reference
  without obligations; gcd with nothing checked or run yet; the shape of a
  receipt checked by LeanForth) and four invalid ones, each rejected for
  one pinned reason, one of them a 0.3 receipt with the withdrawn label put
  back. The 0.2 examples and the 0.2 clamp receipt (checked by the Lean
  reference, before 5.5.1) are kept in [`tests/program/receipts/0.2/`](../../tests/program/receipts/0.2/),
  read but not rebuilt; the 0.1 ones in [`tests/program/receipts/0.1/`](../../tests/program/receipts/0.1/)
  as a record, and the reader refuses them. Hand-written examples are
  never evidence.
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

- **check: `accepted-by-leanforth`.** Lean 4.35.0 wrote the proofs of
  `ProgramVC.LfClamp0.contract`, `ProgramVC.LfClamp0.O1` and
  `ProgramVC.LfClamp0.O2`, from the tactic scripts the untrusted generator
  wrote, and its exporter (`scripts/export.sh`) wrote them with every
  declaration they use, 4,277 in all, to an export of 23.6 MB that the
  committed manifest `tests/program/vc/lf-clamp.ndjson.manifest.json` pins
  (SHA-256 `b53290b4…`; `make check` makes it again, byte for byte).
  LeanForth's checker (`bin/leanforth check --jobs 2`, LeanForth
  0.1.0-dev, verdict version 9) re-checked that export and accepted all
  4,277 declarations: the status is LeanForth's verdict. Each theorem
  lists its axioms as LeanForth reports them (`O1`: propext and
  Quot.sound; the other two also Classical.choice), and `make check`
  requires them to equal Lean's own `#print axioms`; `check.axioms` lists
  their union. LeanForth has no tactics yet: it wrote no proof.
- **verify: `discharged`, settled by `accepted-by-leanforth`.** The
  untrusted generator `scripts/program_vc.py` produced two obligations from
  the IR and the contract, one per path through the word; each is
  discharged by the theorem named with it, which Lean proved and
  LeanForth's checker accepted.
- **run: `passed`.** The three-way runtime comparison ran 986 cases on
  Gforth 1.0.0, Linux x86-64, 64-bit cells, with 0 failures; Lean's model
  agreed on all 991 clamp cases. The run label reads *runtime-tested;
  testing is not proof*.

and lists eight assumptions: one signed host cell per value, two's
complement, the program words (`src/program/verify.fs`, ADR 0019's mode
shift) wrote the IR from the source faithfully (`trusted-reader`), Gforth
executes the words as the IR semantics says (`trusted-runtime`), the
stacks have room, Lean elaborated the Lean source and its exporter wrote
the export faithfully, so that the statement, the IR semantics and the
program LeanForth checked mean what the source says (`trusted-lean`; Lean's
own check of the proofs is not relied on), the obligations come from an
untrusted generator, safe only because the contract theorem is stated
against the IR semantics (`untrusted-generator`), and LeanForth's checker
checked every declaration of the export correctly (`trusted-leanforth`).

A receipt never says more than LeanForth's verdict. When LeanForth rejects
one of the theorems, `check` is `rejected` (`unsupported` for unknown or
unsupported, `failed` when it did not finish), `verify` is `open` with no
obligation discharged, and there is no `trusted-leanforth` assumption.
Evidence in which a theorem depends on an axiom outside the allowlist
(NOT PROVED), in which LeanForth's axioms differ from Lean's, or which is
about another export than the pinned one gives no receipt at all.
`tests/program/receipt_check.py` builds each of these cases. `run` stays
separate: a source proof says nothing about the compiler or the runtime.

## Rules the schema enforces

Besides types, required fields and closed objects. A *positive* check is
`checked-by-lean-reference` or `accepted-by-leanforth`; every other check
status has accepted nothing. A *settled* obligation is `discharged` or
`refuted`.

| Rule | Why |
| --- | --- |
| `check` has no `label` (0.3): a receipt with one is refused, the withdrawn result label included | The owner withdrew result labels on 2026-11-12; `check.status` alone says who checked what, and a failure's status can never be a success's |
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
these rules of schemas 0.2 and 0.3 (they are the same) after the schema (`rule_problems` in
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
python3 -I tests/support/schema_subset.py schemas/program-receipt-0.3.schema.json RECEIPT.json
```

`validate` reads each receipt with the strict loader, requires
`schemaVersion` 0.3 or 0.2, and checks that version's schema and the rules
beyond JSON Schema; `verify` does the same for one receipt and then
replays it, which only a 0.3 receipt can pass (the generator writes 0.3). A
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
| `unknown-version` | `schemaVersion` is missing or is neither `0.2` nor `0.3` |
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
show that the suites catch them, pins schemas 0.1, 0.2 and 0.3 by their
hashes, checks that every 0.3 receipt validates under 0.2 with its label
put back and every 0.2 one under 0.3 with it taken out (so 0.3 removed the
label and nothing else),
checks that every 0.1 receipt, and each hole 0.2 closed written into a 0.1
receipt, is refused as `superseded-version`, and checks that the JSON
receipt below is the generated one. `receipt_check.py`
checks the generated receipt, that tampered receipts and texts are
refused by the layer named with each, and the receipts that LeanForth's
other verdicts give.

## A complete receipt

The generated clamp receipt (`tests/program/receipts/generated/lf-clamp.json`):

```json
{
  "schema": "leanforth-program-receipt",
  "schemaVersion": "0.3",
  "provenance": {
    "kind": "generated",
    "generator": {
      "name": "python",
      "version": "program_receipt.py 0.3"
    },
    "createdAt": "2026-11-12",
    "note": "Written by scripts/program_receipt.py from the repository files named below, at the hashes given, and the evidence recorded on 2026-11-12 by make check. A receipt is a statement of evidence, not an approval; it passes no review gate."
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
    "status": "accepted-by-leanforth",
    "checker": {
      "name": "leanforth",
      "version": "0.1.0-dev, verdict version 9"
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
    "axioms": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "evidence": [
      {
        "path": "tests/program/vc/obligations.lean",
        "sha256": "2abd460a52f8a413b5fd9f9e6cffcb3f7ee5affca1346ed3082f913bb8141631"
      },
      {
        "path": "scripts/program_vc.py",
        "sha256": "04012f147279ee03b4fc689dfa104025b830bc2f65233d6e96226cae958301f0"
      },
      {
        "path": "scripts/export.sh",
        "sha256": "3ad758381ff3a6312940e696dae2bc423884aeef34c402c43851ccd53f78d855"
      },
      {
        "path": "tests/program/vc/lf-clamp.ndjson.manifest.json",
        "sha256": "eae3f015023667f0fa8d12e84cd5d2df0c1cb4e0aaf73306790759fd4e026d8d"
      }
    ],
    "note": "Lean 4.35.0 wrote the proofs of ProgramVC.LfClamp0.contract and its path obligations, from the tactic scripts of the untrusted generator, and its exporter wrote them with every declaration they use, 4,277 in all, to the export with SHA-256 b53290b494bc90b41646531f05b46adca6ee49d497b934021e011c29ed7df6eb that tests/program/vc/lf-clamp.ndjson.manifest.json pins. LeanForth's checker re-checked that export and accepted all 4,277 of them, these theorems among them: the status is LeanForth's verdict. LeanForth has no tactics yet and wrote no proof."
  },
  "verify": {
    "status": "discharged",
    "settledBy": "accepted-by-leanforth",
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
    "note": "One obligation per path through the word's IR (IF splits a path), generated by an untrusted generator from the IR and the contract; each is discharged by the theorem named with it, which Lean proved and LeanForth's checker accepted."
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
        "sha256": "c2be05f55f5c50f2f6e336537a70a9957e74d4b067423a3c9ccc242d0d611726"
      },
      {
        "path": "tests/program/ir_run_differential.py",
        "sha256": "be074390110925e9b32f83a223be300b6e4f9e1a881dc261ca1c7f29010b2a26"
      },
      {
        "path": "tests/reference/program-ir-run.lean",
        "sha256": "5d716b4ecc30cce00d36bc02257c43a47eb2317892c0f9c28aab849c313f2ff1"
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
      "text": "The program words (src/program/verify.fs, the mode shift of ADR 0019) wrote the IR faithfully: each Forth word the file uses means in the IR what the host's word of that name does, and nothing else in the source file changes what its words mean on the host. They run the file through Forth's own text interpreter, one line at a time, with only their entry word visible; each token must be a word of the file (a call, bound when Forth finds it, to the version visible there), a word of FORTH-WORDLIST with verification semantics and the identity it had when they loaded, or a number in a Forth-2012 form (decimal, # $ % prefixes or 'c'), which they read themselves; no word of the file or of the host runs. A standard word redefined after they loaded and before the run is refused, except, on Gforth 0.7.3, a compile-only word, since all of those share one token there; one redefined before they loaded is not noticed, so the verifying Forth too is assumed to have its own standard words. A file may define its own words again, as Forth allows; each version has its own IR name (x, x'1, ...), and program.word names one. They refuse a redefinition, under any spelling, of a word with verification semantics or of a Forth-2012 Core or Core Ext word, a name the IR gives another version, a name that reads as a number, any byte outside printable ASCII other than a space, a tab, an LF and a CR just before an LF, and a division before CONSTANT. Gforth is assumed to load the file with its default settings (decimal BASE, standard words), and the file to define no name that code compiled after it in the same session uses, other than the words under test: definitions of host words outside those word sets, such as Gforth's own, are accepted and would change what such code, a test harness for example, means. Nothing proves the translation; recording the evidence wrote this IR again with the program words, and make test compares them with the IR named here and with the earlier reader (src/program/ir-reader.fs)."
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
      "text": "Lean 4.35.0, the pinned toolchain, elaborated tests/program/vc/obligations.lean and its exporter (lean4export 3.1.0, through scripts/export.sh) wrote the export faithfully: the contract statement, the IR semantics and the program that LeanForth checked mean what that Lean source says. Lean also wrote the proofs, from the generator's tactic scripts, and checked them itself; that check is not relied on here, since LeanForth's checker checked the export again."
    },
    {
      "id": "A7",
      "kind": "untrusted-generator",
      "text": "The obligations come from an untrusted generator (scripts/program_vc.py). This is safe only because the contract theorem is stated against the IR semantics copied verbatim from tests/reference/program-ir.lean, and Lean prints the generated program back equal to the IR file."
    },
    {
      "id": "A8",
      "kind": "trusted-leanforth",
      "text": "LeanForth's checker (bin/leanforth check, 0.1.0-dev, verdict version 9) checked every declaration of the export correctly: it accepted all 4,277 of them, the contract theorem, its obligations and every definition, inductive type and lemma they use, directly or not, each with its axioms. It follows Lean 4.35.0's kernel rules; it has no tactics and wrote no proof."
    }
  ],
  "tools": [
    {
      "name": "lean",
      "version": "4.35.0",
      "commit": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
    },
    {
      "name": "leanforth",
      "version": "0.1.0-dev, verdict version 9"
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
version comes is for the owner to decide at the gate; for 0.2, approved,
the reader keeps reading it.

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
  On 2026-11-04, with IR 0.2 implemented, the clamp receipt was
  regenerated, still 0.2, its IR byte for byte the same: only the
  `trusted-reader` assumption's text changed (redefinitions of the file's
  own words are now accepted as versions, numbers may carry Forth-2012's
  prefixes), and the evidence's date.
- **0.3** (2026-11-12), a [format] change the owner decided on 2026-11-12:
  results carry no "experimental", "not independently audited" or
  "pre-alpha" label, so `check.label` and its one-label-per-status rules
  are gone; nothing else changed (a test puts the label back into every
  0.3 receipt and validates it under 0.2). `run.label` stays: it says that
  testing is not proof, a trust boundary `AGENTS.md` requires receipts to
  state, not a label on a result. The clamp receipt became 0.3 with plan
  task 5.5.1, when its CHECK part became LeanForth's verdict; the 0.2
  receipt, checked by the Lean reference, is kept in
  `tests/program/receipts/0.2/`.

### Schema 0.4: what IR 0.2 receipts need

[IR 0.2](PROGRAM_IR.md#ir-02) is implemented, but no receipt can describe
an IR 0.2 program yet: schema 0.3's `program.ir.version` is the constant
`"0.1"`, and nothing in it says that a word prints. So
`scripts/program_receipt.py` refuses to write a receipt for an IR whose
first line is not `lf-ir 0.1` ("needs receipt schema 0.4 … awaits the
owner's [format] gate; no receipt written"), and `tests/program/receipt_check.py`
checks that refusal. Receipts of IR 0.1 programs, version names such as
`lf-clamp'1` included, stay schema 0.3 (`program.word` admits `'`; the
`trusted-reader` assumption then says which later version the name means
after loading). Schema 0.4 (proposed by ADR 0019 Amendment 1, A4, as 0.3;
renumbered on 2026-11-12, when the owner's label decision took 0.3) is to
be decided at the [format] gate with the first IR 0.2 receipt (a SHA-2
helper word); it would change exactly two things:

1. `program.ir.version`: `"0.1"` or `"0.2"`.
2. `program.output` (boolean, required): true when the word or any word it
   calls has an `out` line; then an assumption of the new kind `output` is
   required (as `floatingPoint` requires `floating-point`), saying whether
   the contract describes the output or only the stacks, that output is
   assumed to succeed (a closed pipe stops Gforth with THROW −2049, which
   the model does not have), and the `BASE` assumed. The `run` part would
   compare stacks as today and, for a contract that describes output, the
   captured standard output with the events Lean's `Event.render` gives.

The pending renaming of `trusted-reader` could ride along. Nothing of
this is implemented; the newest schema file is 0.3.

The plan extends the schema to theorem receipts (task 3.4.3) and wraps it
in the versioned JSON-RPC interface (task 3.5.1, [interface
contracts](INTERFACE_CONTRACTS.md)).
