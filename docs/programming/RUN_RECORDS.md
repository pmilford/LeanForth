# Run records and replay, schema version 0.1

**Status: implemented 2026-11-03 (plan task 2.2.5 of the
[plan draft](../project/PLAN_DRAFT.md)); format 0.1 approved by the owner
[format] on 2026-11-04 after three independent review rounds
([decisions](../project/OWNER_DECISIONS.md#program-words-and-run-records-approved-2026-11-04)).** A
*run record* is the evidence of one check of a Lean export by LeanForth's
first checker: which file was checked, by which tools, with which settings,
and the verdict of every declaration. *Replay* checks the same file again
and compares the new record with the old one, field by field. Both are
written in Forth, with the project's JSON writer and SHA-256: no Python is
on the path that makes or replays a record.

A record is evidence, not an approval. It passes no review gate, and it is
never a source of saved results: replay re-checks everything, as the final
run mode of [ADR 0012, E8](../adr/0012-checked-environment.md#e8-saved-results-and-the-two-run-modes)
requires. Until the checker passes its review gate, every accepted verdict
in a record carries the label *experimental, not independently audited*.

- **Schemas:** [`schemas/run-record-0.1.schema.json`](../../schemas/run-record-0.1.schema.json)
  and [`schemas/replay-report-0.1.schema.json`](../../schemas/replay-report-0.1.schema.json),
  JSON Schema draft 2020-12 within the subset that
  [`tests/support/schema_subset.py`](../../tests/support/schema_subset.py)
  implements ([program receipts](PROGRAM_RECEIPTS.md#the-validator-and-its-json-schema-subset)).
- **Code:** `src/import/run-record.fs` writes records, `src/import/run-replay.fs`
  compares them; the command line drives both
  (`bin/leanforth check --record RECORD EXPORT` and
  `bin/leanforth replay EXPORT RECORD`, [the command line](../user/COMMAND_LINE.md#run-records-and-replay)),
  and so does `tests/support/run-records.fs`, without the manifest check;
  both read the export into the checker's input with
  `src/import/checker-input.fs`.
- **Golden records:** `tests/core/run-records/`, one per pinned export and
  per broken copy of the composition export, written with Gforth 1.0.0.

## Making and replaying a record

```sh
make run-record EXPORT=tests/reference/composition.ndjson RECORD=composition.json
make replay EXPORT=tests/reference/composition.ndjson RECORD=composition.json
```

`FUEL=n` sets the fuel of each check (default 100000, as `bin/leanforth check` uses).
`make run-record` names the LeanForth commit (`git rev-parse HEAD`) and
whether tracked files differ from it (`git diff --quiet HEAD`); outside a
git checkout both are null. Both targets exit with status 0 only for a
record written, or a record confirmed; replay prints its report on
standard output. The same in Forth, from the repository root:

```forth
require ~+/tests/support/run-records.fs
s" COMMIT" false ni-source    \ optional: 40 lowercase hexadecimal digits
s" tests/reference/composition.ndjson" 100000 s" composition.json" ni-record .
s" tests/reference/composition.ndjson" 100000 s" composition.json" ni-replay .
```

`ni-record ( c-addr1 u1 fuel c-addr2 u2 -- outcome )` checks the export
c-addr1 u1 and writes its record to c-addr2 u2; `ni-replay` with the same
arguments checks it again, compares and prints the report. The lower
level, `ni-run ( c-addr u fuel -- outcome )`, leaves the record in memory
(`rr-text`), and `rp-replay-text ( c-addr u -- outcome )` compares a record
given as text. Underneath, a run is `rr-start ( c-addr u -- outcome )`
(which keeps the file's name), `rr-settings!`, `rr-import ( flag --
outcome )` (the manifest enforced when flag is true), `rr-check` after a
read that was ok, `rr-finish ( -- outcome )`, `rr-write` and `rr-release`
(`src/import/run-record.fs` documents each).

## What a record holds

The record of the broken copy `composition-wrong-argument.ndjson`, as
written on one line and shown here indented:

```json
{
  "schema": "leanforth-run-record",
  "schemaVersion": "0.1",
  "input": {
    "sha256": "25de2e97121f116649630694fdfa25dd50d74ac20c648e01f68f45781ea193e4",
    "bytes": 1787,
    "lines": 35,
    "manifest": {"outcome": "invalid", "field": "",
                 "reason": "manifest missing, unreadable or too large", "enforced": false}
  },
  "export": {"exporter": "lean4export", "exporterVersion": "3.1.0", "format": "3.1.0",
             "lean": "4.35.0", "leanGithash": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"},
  "leanforth": {"commit": null, "modified": null},
  "host": {"forth": "gforth", "version": "1.0.0", "engine": "gforth", "cellBits": 64},
  "settings": {"fuel": 100000, "dependencyPool": 64, "terms": 64, "levels": 64,
               "names": 64, "declarations": 32, "dependenciesPerCheck": 16,
               "parameters": 64, "referenceLevels": 64},
  "check": {"read": "ok", "run": "ok", "mode": "final", "allowlistVersion": 0},
  "declarations": [
    {"index": 0, "name": "composition", "verdict": "rejected",
     "diagnostic": {"code": 59, "reason": "rejected: argument type mismatch (D1-D5)",
                    "site": "mixed-infer lf-mixed-infer", "numbers": [4, 0], "step": 7}}
  ]
}
```

| Field | Contents | Where it comes from |
| --- | --- | --- |
| `input.sha256`, `bytes`, `lines` | SHA-256 of the file's bytes (as `sha256sum` prints it), its size, and its line feeds plus one for a last line without one | the file, read by `rr-hash` before the check and again after it; a change in between fails the run (`rr-finish`) |
| `input.manifest` | the outcome of checking the file against `FILE.manifest.json` ([NDJSON reader, manifests](../development/NDJSON_READER.md#manifests)), recorded whatever it is; `field` and `reason` are `export-error`'s, empty for ok; `enforced` true only when the importer refused to load the input unless it matched that manifest | `src/import/manifest.fs`; `enforced` from `rr-import` (below) |
| `export` | the exporter, export format and Lean versions the metadata record names; null when no metadata record was read | the NDJSON reader, which accepts only the pinned versions |
| `leanforth` | the commit and whether tracked files differed from it, or null for both | the caller (`ni-source`; `make run-record` asks git) |
| `host` | the Forth system, its version, its engine (the program's file name, such as `gforth` or `gforth-fast`) and cell width | Gforth's `version-string` and argument 0, else `unknown` |
| `settings` | fuel per check, the dependency pool, and the checker's capacities (since plan task 6.2.0, `parameters` and `referenceLevels` record 64, the old limits, though universe lists have none; the next version of the record will say so) | the run, and the constants of `src/core/` and `src/kernel/` |
| `check` | the importer's outcome, the run's (`not-run` when the input was not read), and the environment's run mode and allowlist version | the transport, `rr-check`, the environment's header |
| `declarations` | every declaration in input order: `index`, `name` and `verdict`, and for an accepted one `label` and `axioms`, for any other but `not-checked` its `diagnostic` | the slots of the checked environment, after the run |

## What a verdict claims

Verdicts are read from the checked environment after the run, never from
what a check said about itself:

- **accepted** only for a slot made final with outcome ok, which only the
  publisher's full success can make ([ADR 0012, E4](../adr/0012-checked-environment.md#e4-staging-then-publishing-only-after-full-success)).
  It always has the label *experimental, not independently audited* and the
  axiom set read from the slot (`lf-env-axioms`). The first checker's
  allowlist (version 0) names no axiom, so the set must be empty; a slot
  with any axiom bit fails the record (`rr-write` gives invalid) rather
  than be written.
- **rejected, unknown, unsupported, invalid, exhausted, full**: the slot's
  outcome ([ADR 0008](../adr/0008-outcome-vocabulary.md)), with the
  diagnostic the check left: its code and catalogue name
  ([diagnostics](DIAGNOSTICS.md)), site, two numbers and the step of
  `check-declaration` it reached (null when it recorded none).
- **invalid** also for a slot that is not final although its check began:
  the check or its publication threw and the run stopped there (E4).
- **not-checked** for a slot the run never reached.

**Was the manifest enforced?** `manifest.outcome` says whether the file
matches the manifest beside it; `manifest.enforced` says whether that
mattered to the check. The record says enforced only when the run record
module loaded the input itself with the manifest checked
(`rr-import ( flag -- outcome )`, flag true: `cin-read-checked` of
`src/import/checker-input.fs`), as `bin/leanforth check` does by default.
`rr-import` takes no file name: it reads the file `rr-start` kept and
hashed, as `rr-finish` does, so no run can hash one file and check another
(review rvRP3, M1); it is the only way a recorded run reads its input
(`rr-read!` and `rr-file!` are internal to the module, rvRP3 R2-3).

What every record guarantees, exactly. The importer reads the file twice:
a first pass that builds the names table and the universe parameters, and
a second that builds the terms and declarations. Each pass computes the
SHA-256 of the bytes it reads: the manifest check computes it when the
manifest is checked, and the reader's tap otherwise (`cin-read`, the same
hash over every line and its line feed). Then, checked or not:

1. the second pass's SHA-256 must equal the first's, else the read is
   invalid ("the export changed between the two passes", line 0; rvRP3
   R2-1 and round 3), so both halves of what is checked come from bytes
   with one SHA-256;
2. that SHA-256 must equal the one `rr-start` recorded (`cin-digest`),
   else the read is invalid and `rr-moved?` is true.

So the verdicts of every record, enforced or not, are the checker's
verdicts on bytes whose SHA-256 is `input.sha256`, whatever happened to
the file between the reads: swapped for another export and swapped back
between `rr-start` and `rr-finish` (A, then B, then A; a test does
exactly that), or swapped during the first pass only (a test serves the
file through a FIFO to do exactly that, with and without the manifest
check). **Enforced adds only** that each pass also matched the manifest
beside the file, as it stood when that pass read it, in its SHA-256,
lines, bytes and record counts: an input that does not match its manifest
is not read at all, and a record that says enforced with a read that
succeeded and a manifest that did not match is refused (by the writer and
by the schema). What no record guarantees: that the file still holds
those bytes after the run (`rr-finish` reads it once more, and a change
caught there fails the run), or anything about a file other than the one
named.
With `--no-manifest` and from `tests/support/run-records.fs` (and so the
golden records and `make run-record`), the record says not enforced, also
when the manifest is missing or does not match: the record never claims a
check it did not see done.

**Only the run's own environment.** Verdicts are read only from the
checked environment that the run's own `rr-check` made, never from another
one that happens to be current, even over the same input (review F1).
Environments are compared by identity, which never repeats, not by
address: when the run's environment is freed and a new one is made at the
same address, the new one is another environment (round 2 of the review;
its probe is a test), so no record is written. `rr-release` frees the
run's environment only while it is the current one with the run's
identity, through the current environment and never through the address
it kept: an environment the caller made another one current over, or
freed, is never read or freed again (it stays allocated unless the caller
frees it; rvRP3 L2). So the caller must not free the run's environment
itself, and if it displaces it, it frees it. If
the run could not make its environment (no memory, a pool out of range),
the record lists no declaration and its `check.run` says why, with `mode`
and `allowlistVersion` null. If the run's environment was freed, or another
is current when the record is written, no record is written (`rr-write`
gives invalid). Each kept outcome starts invalid, never ok, so a slot is
never matched with a step that did not run. And checks that ran although
the read was not ok checked whatever input an earlier read left: such a
record is refused too (rvRP3 L1).

**A run that stops.** When a check or its publication throws, the run stops
there (ADR 0012, E4): `check.run` is invalid, that declaration is invalid
with the publisher's fault as its diagnostic, and those after it are
not-checked. The declarations accepted before the stop still count and
are listed as accepted: their slots were made final, with their records,
before the fault, and nothing changes a final slot.

`rr-write` also refuses (invalid) a record in which a final slot's outcome
is not the one its step published, so a diagnostic always belongs to its
verdict. The schema refuses an accepted verdict without its label or with
a diagnostic or an axiom, a label on any other verdict, a missing
diagnostic, declarations when no environment was made (`mode` null), a
not-checked declaration in a run that ended ok, a mode other than final
and an allowlist version other than 0.

**Texts and numbers.** Every text follows the text rule the owner approved
for [program receipts 0.2](PROGRAM_RECEIPTS.md#rules-the-schema-enforces):
no control character (C0 or C1), no format character (bidirectional
controls, zero-width characters, tags), no line or paragraph separator, no
surrogate. Names, host texts, metadata texts, a failed manifest's reason
and a diagnostic's reason and site must also be *shown*: at least one
character that is seen, that is not a space, not a blank-looking filler
(U+115F, U+1160, U+2800 BRAILLE BLANK, U+3164 HANGUL FILLER, U+FFA0), not
a combining mark (Unicode general category M) and not a default-ignorable
code point, all as of Unicode 15.1. So a name that is empty, blank, a
filler, or made only of combining marks or of ignorable characters is
refused, by the same check as a blank one; `a` followed by a combining
accent is shown. Unlike the receipts' rule this does not ask for an ASCII
character, because a Lean name may be written in any script. Characters
of private use (such as U+E000) and code points not yet assigned (such as
U+FFFF) count as seen, though many fonts draw them blank: which code
points are assigned changes with every Unicode version, so banning them
would make the rule move with it. The rule is the library
`src/lib/text-rule.fs` ([Forth libraries](../development/FORTH_LIBRARY.md));
its two tables are generated by `scripts/text_rule_tables.py` from Python's
Unicode data, and the tests check both tables, and the schema's two
patterns, against it (Unicode 15.0 and 15.1 give the same; on CI another
version fails the test instead of skipping it).
Limits: names 1024 bytes, other texts 128 bytes, a site 255. The writer
checks every text it writes against the same rule and limits, character by
character, and refuses the record (invalid, or full for a length) rather
than write what the schema refuses; the tests compare its rule with the
schema's pattern at both ends of every range. JSON Schema counts length
in characters, so the schema allows the same number of characters, which
every text within the byte limit meets. Numbers are integers within
I-JSON's exact range, ±(2^53 − 1). JSON Schema sees a number only after it
is parsed, so no schema can tell `100000.0` or `1e5` from `100000`: the
strict loader (`load_strict` in `tests/support/schema_subset.py`) refuses
those spellings, and replay compares a number's text, so a record with
them is refused (`settings-differ` for `"fuel":100000.0`).

## Replay

Replay reads the old record (at most 128 KiB, whitespace allowed), checks
the input again with the same transport and the replayer's settings, and
compares. The new record leads: each of its members must be in the old
record exactly once, with an equal value; a member the old record has and
the new one lacks is a finding too. Values compare as follows:

- strings by their decoded text, so `"a"` equals `"a"`;
- numbers by their text, so `100000.0`, `1e5` and `100000` all differ;
- objects by key, whatever the order of their members;
- arrays element by element, in order, after their lengths;
- whitespace between tokens is no difference.

A declaration's verdict is compared first, and nothing else of it when the
verdicts differ. Nothing differs silently: a different input, manifest,
export, commit, host or setting is a finding as much as a different
verdict, and only a report without findings confirms the record. The
report is written whole or not at all.

```json
{"schema":"leanforth-replay-report","schemaVersion":"0.1","result":"refused",
 "findings":[{"code":"settings-differ","path":"$.settings.fuel"},
             {"code":"accepted-not-established","path":"$.declarations[0].verdict"}],
 "findingsTotal":2}
```

(the composition record replayed with fuel 50, which exhausts the check).
The first 32 findings are listed, all are counted. Codes:

| Code | Meaning |
| --- | --- |
| `unreadable` | the old record cannot be read, or is larger than 128 KiB; nothing is compared |
| `not-json` | the old record is not one JSON text within the reader's limits (nesting at most 8) |
| `unknown-schema` | not a `leanforth-run-record` of schema version 0.1 |
| `rerun-failed` | the input could not be checked again (missing, unreadable, changed during the run) |
| `missing-field` | the old record lacks a field the new one has |
| `unknown-field` | the old record has a field the new one lacks |
| `duplicate-key` | the old record repeats a key; its values are not compared |
| `input-differs` | the input's hash, size, lines, manifest outcome or whether the manifest was enforced |
| `export-differs` | the Lean or exporter versions in the metadata |
| `tool-differs` | the LeanForth commit, or the host Forth's name, version, engine or cell width |
| `settings-differ` | fuel, the dependency pool or a capacity |
| `run-differs` | the importer's or the run's outcome, the mode or the allowlist version |
| `declarations-differ` | the number of declarations, or a declaration's index or name |
| `verdict-differs` | a verdict, or an accepted declaration's label or axioms |
| `accepted-not-established` | the old record says accepted where the new run did not accept |
| `reason-differs` | a diagnostic |

A path names the field: `$.input.sha256`, `$.declarations[0].verdict`. A
key taken from the old record is cut at 128 bytes in a path, between two
characters, never inside one (review F2).

## Determinism and hosts

Two runs of the same input on the same host write the same bytes (tested
in one process and in two). Records written by Gforth 1.0.0 and by Gforth
0.7.3 (CI's portability host) differ only in `host.version` and, where the
two programs have different names, `host.engine`: on 2026-11-03 all nine
records agreed otherwise, and each Gforth replayed the other's records
with findings only there (`tests/core/test_run_records.py --other-gforth`,
run with the local Gforth 0.7.3; `make test` on CI's Gforth 0.7.3 replays
the golden records written by 1.0.0 the same way).

## Trust boundaries and limits

- Untrusted code: a record says what the checker's environment held after
  the run. That the checker is right is the [kernel] gate's question, not
  the record's. The transport from the file is test-only; it could hand
  the checker a different claim than the file holds, which no record can
  show.
- The record is read from the file, the importer and the environment at
  different times: the file is read up to six times (hash, metadata,
  manifest, the importer's two passes, hash again; `bin/leanforth` also
  opens it once first, without reading, to report a missing file). A file
  whose digest, size or lines differ at the last read from the first
  fails the run. A file changed and changed back between any two of them
  (A, then B, then A), the importer's two passes included, is caught by
  every recorded read, enforced or not: its two passes must read bytes of
  one SHA-256, and that must be the first read's (above). `rr-start`'s own
  metadata read is hashed the same way, and so is its manifest check when
  it passes: either one that read other bytes fails the start (invalid,
  `rr-moved?` true). A manifest check that failed (a missing manifest, or
  a difference found before the digest) has no digest of the whole file:
  `input.manifest` then says it failed as that read saw it, which an
  enforced read checks again on each pass. A plain `bin/leanforth check`
  (no record) has the same check of its two passes, with or without
  `--no-manifest`. Phase 3's importer will read once.
- The commit is what the caller says, checked only for its form; the host
  fields are what Gforth reports.
- Diagnostic numbers are those the check recorded. For the internal faults
  that record environment identities (codes 25 and 27) they differ between
  two runs in one process; they never arise from a well-formed input.
- Limits: a record text of 64 KiB, names of 1 KiB, host, metadata,
  manifest and commit texts of 128 bytes (a longer metadata text is
  written null), the checker's own limits (32 declarations). A record that
  does not fit is not written (`rr-write` gives full); that includes an
  input of more declarations than a record keeps (`lf-input-default`, 32,
  the schema's limit), which a larger input store (`lf-input-capacity!`)
  would let the importer read (rvRP3 R2-2). An export whose
  declaration name breaks the text rule (a Lean name may hold almost any
  character) cannot be recorded: `rr-write` gives invalid, and the check
  itself is unaffected.
- State: one shared record per module (`run-record`, `run-replay`); one
  run or replay at a time.

## Tests and planted faults

`make test-run-records` (part of `make test`):
`tests/core/run-record.fs` checks each fixture's verdicts and diagnostics,
that the verdicts are the slots' (equal to `lf-check-input`'s), the record
of a run that stops part way (a THROW in the publisher), determinism, the
commit's form, each failure of `rr-write` and `rr-finish`, a foreign
environment (the review's reproducer: none of its verdicts is written),
the run's environment freed and a new one made at the same address (the
second review's `aba.fs`, with its fuel and with equal fuel: no record,
the new environment left alive, and the address's reuse asserted, or a
note printed when the allocator did not reuse it), a displaced environment
left alone by `rr-release`, whether the manifest was enforced (checked
read, unchecked read, the driver, the internal `rr-read!`, a checked read
of a copy without a manifest, and a contradiction refused), a checked read
of other bytes than `rr-start` hashed, that `rr-read!` and `rr-file!` are
not found outside the module, `rr-import` with no started file, checks run
after a read that failed (the third review's `p8`), the text rule,
blank-looking texts (the fillers, combining marks or ignorable characters
alone) and the number range, hashing, cuts between characters, and replay
findings; `tests/lib/text-rule.fs` tests the text rule on its own,
malformed UTF-8 and the private helpers on bytes that are not UTF-8
included; `tests/core/test_run_records.py` swaps the export and its
manifest for another export and back between `rr-start` and `rr-finish`
(the third review's `p3`: the checked read fails, and the record lists no
verdict); serves the export through a FIFO so that only the importer's
first pass reads another file, with its own manifest (the third review's
round 2, `p9` and `p11`: other names, and a declaration the file at rest
rejects but the other file accepts), recorded and read once, with the
manifest checked and without, and each read fails as invalid with the
reason "the export changed between the two passes" at line 0; serves
another file to `rr-start`'s metadata read, and to its manifest check
with that file's manifest, and `rr-start` fails (each reader runs under
`timeout`, so none can hang; skipped, with a note, where there are no
FIFOs or no `timeout`); records an input
of 32 declarations (all 32 listed) and refuses, full, one of 33 with a
larger input store; writes the nine records
to files and checks them against the schema, Python's SHA-256, the golden
records and each other, and replays them. It refuses 15 tampered records,
each with its code and path (a changed verdict, hash, host version, reason
or manifest outcome; a missing field; a duplicate key; an unknown field; a
claim of acceptance for a rejected declaration; a dropped declaration; a
number written as a string, with a fraction or with an exponent; text that
is not JSON; another schema version), and two replays with another fuel or
another commit; it confirms a pretty-printed record and one whose verdict
is spelled with an escape, and replays a record with a 201-byte multibyte
key into a valid report whose path is cut between characters. It shows
that the schema refuses 43 records, those that claim more than a checker
could (among them an enforced manifest that does not match) and those that
break the text rule, a limit or the real values of `mode` and
`allowlistVersion`, or whose name looks blank; that each schema pattern
means the same in ECMA-262 (node, `u` flag) and in Python; that the
writer's text rule equals the schema's on 1,623 code points (every range's
ends and their neighbours); and that both tables of `src/lib/text-rule.fs`
and the schema's two patterns are exactly what `scripts/text_rule_tables.py`
computes from Unicode 15.0 or 15.1. Fifty faults planted in the modules
and in the importer's comparison of its passes
(`tests/mutants/faults.toml`, section "run records and replay") are each
caught by these tests; `tests/cli/test_leanforth.py` checks that the
command line's records say enforced, and say not enforced with
`--no-manifest`.

## Versioning

`schemaVersion` names the schema a record or report follows; any change to
fields or rules gives a new version and a new schema file next to the old
one, as for [program receipts](PROGRAM_RECEIPTS.md#versioning). Replay
refuses a record of any other version (`unknown-schema`).

- **0.1** (2026-11-03): the first draft, under the [format] gate. Tightened
  in place the same day after the independent review (the text rule and
  limits of receipts 0.2, numbers within I-JSON's range, the real values
  of `mode` and `allowlistVersion`, no not-checked declaration in a run
  that ended ok, no declarations without an environment). No run record
  had been published outside the tests, and every record the tests had
  written still validates, so the version stays 0.1. After the review's
  second round, still the same day and still with no record published
  outside the tests: the field `input.manifest.enforced` (required), and
  blank-looking texts refused. The golden records were written again; the
  version stays 0.1. The third round changed no field or schema rule: it
  tied `enforced` to the recorded bytes and the run to rr-start's file
  (records only got stricter to write), so the version stays 0.1.

## Rejected alternatives

- **Writing records with a Python script.** It would put Python on the
  user's path for every check; the JSON writer and SHA-256 are in Forth.
- **Comparing whole files byte for byte.** A record from another host or a
  pretty-printed copy would be refused without saying which field differs;
  field-by-field findings name the field and keep a duplicate key or an
  extra field from passing unseen.
- **Loading records as saved results to skip checks.** ADR 0012 E8 allows
  that only in a development mode, which phase 2 does not have; replay
  re-checks everything.
- **The diagnostic from inside the check.** The publisher can change an
  outcome after the check (a failed re-check, a full pool, a THROW); the
  record reads each declaration's diagnostic after its step instead, and
  refuses a slot whose outcome is not the one the step published.
