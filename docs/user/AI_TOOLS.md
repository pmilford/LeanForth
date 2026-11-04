# For AI tools

How an AI agent or a script can use LeanForth today, what it may and may
not conclude, and where the planned machine interface will come. Status
2026-11-03. There is **no LeanForth API yet**: the interfaces below are
command lines, among them `bin/leanforth` with fixed exit statuses, Forth
words and one JSON format, all untrusted. The planned JSON-RPC interface
is a [design](../programming/INTERFACE_CONTRACTS.md), not code.

## Rules for any tool

These follow `AGENTS.md` and the [owner's decisions](../project/OWNER_DECISIONS.md);
they hold whatever a tool is asked to do.

1. **Only the checker decides *accepted*.** The first checker is
   experimental and has not passed its review gate: report a declaration
   as accepted by LeanForth only from its own verdict line, with the label
   *experimental, not independently audited* and its axioms, and never as
   proved. A passing test, a decoded record, Lean's acceptance of a
   reference model or a model's own reasoning is not a LeanForth proof.
2. **Use the outcome words exactly.** *unknown* is not *rejected*, and
   neither is a disproof; *exhausted* (out of fuel) and *full* (out of room)
   are resource limits; *invalid* is malformed input. Only *ok* is ever
   accepted ([outcomes](CONCEPTS.md#outcomes)).
3. **Keep a program's three answers apart.** A receipt's `check`, `verify`
   and `run` parts are never merged into one "verified"
   ([program receipts](../programming/PROGRAM_RECEIPTS.md)). `check.status`
   and `verify.settledBy` say who checked: `checked-by-lean-reference` means
   Lean, not LeanForth. A receipt's notes and texts are unchecked prose;
   only its statuses, fixed labels and assumptions carry meaning.
4. **Label every explanation** by where it came from: a fixed template, a
   reconstruction from the proof term, or AI-written. Explanations are never
   part of what is checked.
5. **Never make a check pass by changing what is checked.** No new axiom,
   no `sorry`, no weakened specification, no failure reported as success.
   Allowed axioms are decided by the owner only.
6. **Every accepted result will carry the label** *experimental — not
   independently audited* and its axiom list; keep both when quoting it.
7. **Stop at a review gate.** Checker rules, import, certificate formats,
   axioms and runtime assumptions need the owner's approval; ask in plain
   language with a recommendation.

## Interfaces that exist

| Interface | Call | Result | On failure |
| --- | --- | --- | --- |
| Test suites | `make test`, `make check`, or one target ([running the checks](RUNNING_THE_CHECKS.md)) | Exit status 0 | Nonzero exit status; the failing command's output on standard error |
| Command line | `bin/leanforth check [--no-manifest] [--fuel N] [--resources] [--json] EXPORT`, any size, also `count`, `reexport`, `version`, `capabilities` ([the command line](COMMAND_LINE.md)) | One line `NAME: VERDICT` per declaration, an accepted one `NAME: accepted (experimental, not independently audited); axioms: …`, then `N declarations: …` and `accepted: N (…); axioms: …`; with `--json` one JSON report (`schemas/check-report-0.1.schema.json`; deterministic but for its `measured` member); names as Lean shows them, with `\u{X}` escapes for control and format characters, so one line is one declaration; exit status 0 when every declaration is accepted and proved | Exit status 1 rejected, 2 unsupported or unknown, 3 a resource limit, 4 malformed input or command line, 5 an internal fault, 6 all accepted but some NOT PROVED (proposed) (the most severe wins, in the order 5, 4, 1, 3, 2, 6); a refused declaration's reason on the indented line after it; a file that cannot be read gives one line `error: OUTCOME: REASON (field F, line N)` |
| Export counter | `.tools/gforth/bin/gforth-fast src/import/ndjson-count.fs -e 's" FILE" count-export bye'`; checks `FILE.manifest.json` ([manifests](../development/NDJSON_READER.md#manifests)) unless `count-export-unchecked` is used | A text report of record counts by kind; exit status 0 | One line `error: OUTCOME: REASON (field F, line N)` or `(line N, byte B)` (line 0 for a missing or wrong manifest) and exit status 1 |
| Export manifest writer | `scripts/export.sh OUT.ndjson MODULE...` (export and manifest) or `python3 scripts/export_manifest.py EXPORT [--mathlib-commit SHA]` | `EXPORT.manifest.json`, valid under `schemas/export-manifest-1.schema.json`; exit status 0 | One line on standard error, no manifest written, exit status 1 |
| Forth words | `.tools/gforth/bin/gforth src/main.fs`, then the words of `src/` (each module's header gives stack effects, state and error cases) | Values on the data stack; an outcome number 0–6 | An outcome other than 0; refused constructions give `false` |
| IR reader | `lf-ir-read-file ( xt c-addr u -- outcome )`; `xt ( c-addr u -- )` receives each line | IR 0.1 text ([program IR](../programming/PROGRAM_IR.md)) | One line such as `unsupported @1:7: not a known word or 32-bit decimal: foo` and *unsupported*, *invalid* or *full*; lines written before it must not be used |
| Receipt reader | `python3 -I scripts/program_receipt.py validate FILE...` (strict JSON, schema 0.2 and the rules beyond JSON Schema; a receipt naming the superseded draft 0.1 is refused); `verify FILE` also replays the clamp receipt | Exit status 0 and no output | One line per problem on standard error, `FILE: CODE: PATH: MESSAGE` with CODE `unreadable`, `not-strict-json`, `superseded-version`, `unknown-version`, `schema`, `rule` or `replay`, such as `FILE: schema: $: additional property 'verified' is not allowed`; exit status 1 (2 for a usage error) |
| Receipt schema only | `python3 -I tests/support/schema_subset.py schemas/program-receipt-0.2.schema.json FILE...` | Exit status 0 and no output | One line per problem, such as `FILE: $: additional property 'verified' is not allowed`, and exit status 1 |

The outcome numbers are fixed by [ADR 0008](../adr/0008-outcome-vocabulary.md):
0 ok, 1 invalid, 2 exhausted, 3 unknown, 4 rejected, 5 unsupported,
6 full. In Forth an outcome is a status, not a flag: test it with `ok?`
or compare it with a named outcome, never with `IF`, because 0 means
success.

## Determinism

- **Results are deterministic.** The same input gives the same outcome and
  the same output bytes: no result depends on randomness, a clock or the
  network. Randomized tests use pinned seeds (for example 20261102 for the
  NDJSON mutation sweep). The reader's field-by-field output equals Python's
  `json` module byte for byte on every fixture (in `make test`) and on all
  of Mathlib (run once, 2026-11-02).
- **Parallel runs must equal serial runs.** The job pool's tests compare
  jobs on 1, 2 and all workers with serial runs; the planned checker is
  required to give the same verdicts and library whatever the number of
  workers ([ADR 0012](../adr/0012-checked-environment.md)).
- **Times and memory are not deterministic**; measurements in the
  documentation name the machine, tools and date.
- **Fuel is part of the input.** A check given less fuel can end
  *exhausted* where more fuel decides it; report the fuel used.

## Where JSON will come

| Piece | State |
| --- | --- |
| Program receipt, schema 0.2 (`schemas/program-receipt-0.2.schema.json`; the superseded draft 0.1 is kept as a record and refused by the reader) | Exists, with valid and invalid examples, a standard-library validator and a strict reader; the clamp receipt is generated (task 2.5.6, [`lf-clamp.json`](../../tests/program/receipts/generated/lf-clamp.json)): checked and discharged by the Lean reference, not by LeanForth, and runtime-tested; a proposal under the *[format]* gate until the owner approves it |
| JSON reader in Forth (`src/lib/json.fs`) | Exists; reads Lean's exports, and will read API requests |
| Run records with input hashes and verdicts, replay | Exist, task 2.2.5 ([run records](../programming/RUN_RECORDS.md)): `bin/leanforth check --record RECORD EXPORT` and `bin/leanforth replay EXPORT RECORD`, whose report is JSON (exit 0 confirmed, 1 refused, 4 not comparable); the format awaits the *[format]* gate |
| `leanforth` command with fixed exit codes (0 all accepted, 1 something rejected, 2 unsupported or unknown, 3 resource limit, 4 malformed input, 5 internal fault, 6 all accepted but some NOT PROVED) | Version 0 exists (tasks 3.4.1–3.4.3, [the command line](COMMAND_LINE.md)), with `check --json` and its schema `schemas/check-report-0.1.schema.json`; code 6 and the report format await the owner's confirmation at the *[format]* gate |
| JSON-RPC 2.0 over standard input and output: `system.capabilities`, `proof.check`, `proof.pretty`, `program.receipt`, with schemas and golden examples | Planned, tasks 3.5.1–3.5.3 ([design](../programming/INTERFACE_CONTRACTS.md)) |
| Error-code catalogue and an LLM guide | Planned, task 3.5.4 |
| The same schemas as MCP tools | Planned, task 8.5.1; needs the owner's approval of the dependency |

Until then, a tool that needs structured results should run the `make`
targets and Forth words above and treat every result as an untrusted
diagnostic.
