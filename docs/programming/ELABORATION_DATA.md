# Elaboration data: Lean's attributes for LeanForth's front end

Plan row FE1d ([plan](../project/PLAN_DRAFT.md#phase-8-front-end-fe1fe12-2026-11-12-replaces-831-and-832);
[ADR 0021](../adr/0021-front-end.md) D10; [front-end design](../design/FRONT_END.md#49-elaboration-data)).
Status (2026-11-12): **integrated** in the stages of
[DONE_CHECKER.md](../development/DONE_CHECKER.md#stages): the exporter,
the reader and `leanforth check --elab-data` exist and are tested, against
pinned Lean on all of `Init`; the implementer ran `check --snapshot
INIT.lfsnap --elab-data init.elab.ndjson tests/author/19-add-zero.lf` on
a snapshot of all of `Init` (the data read whole, 13.7 s and 0.6 GB in
all; the slice's data refused there as another export's); the done
checker has not run it. Nothing uses the data yet (the elaborator, FE1e
and FE1g, is not built).

## What it is and why

A Lean export (lean4export, [NDJSON_READER.md](../development/NDJSON_READER.md))
holds the declarations of a library: their types and values, which is all
the kernel needs. Lean's *elaborator*, which turns what a user writes into
those terms, needs more: which declarations are **instances** of which
**classes** and with what priority (so that `0 + n` finds `Nat`'s
addition), which instances are **default instances** (so that the numeral
`0` is a `Nat` when nothing else says so), how readily each declaration
unfolds (its **reducibility**), and which **eliminator** the `induction`
and `cases` tactics use for a type (`Nat.recAux` rather than `Nat.rec`).
Lean keeps these as attributes in its `.olean` files, not in the export.

The elaboration data is a second file, written beside the export by a
small Lean program run with pinned Lean when the library is exported (the
owner approved it as a development tool on 2026-11-12, "Front-end syntax",
answer 8), and read by LeanForth, which checks it against the export. A
user who only checks LeanForth text needs no Lean.

The same fact in three forms: in mathematics, *addition on ℕ is a
binary operation*; in Lean, `instance instAddNat : Add Nat := ⟨Nat.add⟩`,
so that `#synth Add Nat` answers `instAddNat`; in the elaboration data,
the line

```json
{"instance":{"class":["Add"],"name":["instAddNat"],"priority":1000,"synth_order":[]}}
```

and, once FE1e is built, in LeanForth text `0 n +` finds it the way Lean's
`0 + n` does.

**Trust.** The data is untrusted and never reaches the kernel: nothing in
it can make a declaration accepted, since every term the front end builds
is checked by the kernel ([ADR 0021](../adr/0021-front-end.md) D1). It can
change what a statement *means* (a wrong instance would make `+` mean
something else), which is why it is checked record by record against the
export, refused whole on any mismatch, and why every statement will be
printed back in three forms ([parser] gate).

## Making it: `scripts/export-elab.sh`

```text
$ scripts/export.sh init.ndjson Init                     # the export and its manifest
$ scripts/export-elab.sh init.elab.ndjson init.ndjson Init
init.elab.ndjson: 2938 instance, 34 default_instance, 7609 reducibility, 6 eliminator; left out (not declarations of the export): 31 instance, 0 default_instance, 114 reducibility, 0 eliminator
```

(Shown, not run by `make check-doc-examples`, which runs the console
examples below: it needs pinned Lean; `make reference-elab-data` runs
it.) `scripts/export-elab.sh OUTPUT EXPORT MODULE...` checks the Lean version
and revision as `scripts/export.sh` does, runs
`scripts/export_elab.lean` (`lean --run`) on the modules, then
`scripts/export_elab.py`, which

- keeps the records whose every name is a declaration of EXPORT, so that
  a slice of a library (`scripts/export.sh OUT Init -- NAMES`) gets the
  data of its own declarations; for a whole module the records left out
  are those of declarations leanexport does not write: internal names
  (a part starting with `_`, such as private declarations) and unsafe
  ones, unless an exported declaration uses them (145 for `Init`);
- refuses (exit status 1, nothing written) a record whose names are all
  there but of the wrong kind (the export and the modules do not belong
  together), anything not as the Lean program writes it, another Lean, and
  an export whose SHA-256 differs from its manifest's;
- sorts the records and writes the header, so the same input always gives
  the same bytes.

Measured on 2026-11-12 (development machine): `Init` in about 6 s (1.5 s
Lean, 4 s reading the 346 MB export); the file is 1.0 MB. The init slice
of the tests (`tests/author/init-slice.ndjson`, 59 declarations) gives
`tests/front/init-slice.elab.ndjson`: 3 instances (`instAddNat`,
`instHAdd`, `instOfNatNat`), 2 default instances (`instHAdd` for `HAdd`,
priority 1000; `instOfNatNat` for `OfNat`, priority 100), 18 reducibility
statuses and no eliminator (`Nat.recAux` is not in the slice).

What the Lean program reads, after `importModules` with the extensions
loaded (global entries only: nothing scoped is active after an import):

| Record | Lean 4.35.0 source | Count in `Init` |
| --- | --- | --- |
| `instance` | `Meta.instanceExtension`: every instance not erased, its priority and `synthOrder`; its class found as `Meta.addInstance` checks it (`forallTelescopeReducing`, `isClass?`) | 2,969 |
| `default_instance` | `Meta.defaultInstanceExtension`: class, instance, priority | 34 |
| `reducibility` | every constant whose `getReducibilityStatusCore` is not `semireducible`: `reducible`, `irreducible`, `implicit_reducible` or `instance_reducible` (Lean 4.35.0's five statuses) | 7,723 (4,491 reducible, 2,782 instance_reducible, 343 implicit_reducible, 107 irreducible) |
| `eliminator` | `Meta.customEliminatorExt`: `@[induction_eliminator]` and `@[cases_eliminator]`, keyed as Lean keys them by the head constants of the explicit targets' types | 6 (`Nat.recAux`, `Nat.casesAuxOn`, `BitVec.cons_induction`, `Decidable.falseTrueCases` twice, `Std.PlausibleIterStep.casesOn`) |

## The format, version 1

One JSON object per line ([schema](../../schemas/elab-data-1.schema.json),
which every line satisfies). A name is the JSON array of its parts, root
first, each a string or a natural number (`Nat.add` is `["Nat","add"]`;
a private name keeps its numeric part).

Line 1, the header:

```json
{"elab_data":{"export_sha256":"5f906a8e...","format":"leanforth-elab-data","format_version":1,"lean_githash":"eb6cafb7290e8bd5f2937522d8d804f58f02bafc","lean_version":"4.35.0","modules":["Init"],"records":{"default_instance":2,"eliminator":0,"instance":3,"reducibility":18},"records_sha256":"..."}}
```

`export_sha256` is the export's SHA-256 as its manifest records it;
`records` the number of each kind of record that follows;
`records_sha256` the SHA-256 of every later line with its line feed, so
that a file cut off between two lines, or changed, is refused.

Then the records, sorted by kind and then by text:

| Kind | Members |
| --- | --- |
| `instance` | `name` (the instance), `class`, `priority` (natural, below 2^32), `synth_order` (naturals: the order in which its instance arguments are synthesized) |
| `default_instance` | `class`, `name` (the instance), `priority` |
| `reducibility` | `name`, `status`: one of `reducible`, `irreducible`, `implicit_reducible`, `instance_reducible` |
| `eliminator` | `kind` (`induction` or `cases`), `name` (the eliminator), `types` (the names of the explicit targets' types) |

## Reading it: `leanforth check --elab-data`

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson --elab-data tests/front/init-slice.elab.ndjson tests/author/19-add-zero.lf | head -1
elaboration data: 3 instances, 2 default instances, 18 reducibility statuses, 0 eliminators
```

`--elab-data DATA` goes with a LeanForth text and its library (`--env
EXPORT` or `--snapshot FILE`). After the library is read and before the
text runs, `src/front/elab-data.fs` reads DATA against the library's
names and the SHA-256 of its export: the manifest check's, the
snapshot's, or with `--no-manifest` the file's, hashed then. The verdicts
are those of the same run without `--elab-data`: nothing uses the data
yet. A refusal stops the run before the text runs, with the line and the
reason, and the outcome's exit status (4 invalid, 2 unsupported, 3 full);
here the test file `tests/front/cut-off.elab.ndjson`, the eliminators
fixture with its last record cut off:

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson --elab-data tests/front/cut-off.elab.ndjson tests/author/19-add-zero.lf
error: invalid: the elaboration data was refused at line 27 (error 20): records differ in number from the header; the LeanForth text was not checked
```

What the reader checks, each failure refused with its reason:

| Check | Reason printed | Outcome |
| --- | --- | --- |
| line 1 is a header of this format | `no header`, `not elaboration data` | invalid |
| its format version, Lean version and revision | `another format version`, `another Lean version` | unsupported |
| its members, each well typed | `malformed line` | invalid |
| its export SHA-256 is the library's | `elaboration data of another export` | invalid |
| every line is one JSON object of a known kind with exactly its members | `not one JSON value within the limits`, `unknown record kind`, `malformed line` | invalid |
| every name is exactly one declaration of the library | `unknown name`, `a name several declarations have` | invalid |
| of the right kind: a class an inductive type, an instance or eliminator not one | `a declaration of the wrong kind` | invalid |
| no declaration named twice (instance, default instance, reducibility); one eliminator per kind and types | `an instance named twice`, `a default instance named twice`, `a reducibility named twice`, `two eliminators for the same types` | invalid |
| priorities and synthesis-order entries fit 32 bits | `a number beyond 2^32 - 1` | unsupported (no Lean library has one; the field widens if one appears) |
| after the last line: the records of each kind and their SHA-256 are the header's | `records differ in number from the header`, `records differ from their SHA-256` | invalid |
| every line ends with a line feed and is at most 1 MB | `no line, or a line without its line feed`, `a line longer than the limit` | invalid, full |
| the file opens | `file missing or unreadable` | invalid |

A refused read keeps nothing. Each refusal has a stable error code,
printed with its text (`at line 2 (error 12): unknown name`):

## Errors

| Code | Text | Outcome | When |
| --- | --- | --- | --- |
| 1 | `file missing or unreadable` | invalid | the file cannot be opened |
| 2 | `no line, or a line without its line feed` | invalid | an empty file, or a last line cut off |
| 3 | `a line longer than the limit` | full | a line of more than 1 MB |
| 4 | `not one JSON value within the limits` | invalid (full past 65,536 tokens or 8 levels) | a line that is not JSON |
| 5 | `no header` | invalid | line 1 is not `{"elab_data": {...}}` |
| 6 | `not elaboration data` | invalid | the header's format is another |
| 7 | `another format version` | unsupported | `format_version` is not 1 |
| 8 | `another Lean version` | unsupported | written by another Lean version or revision |
| 9 | `elaboration data of another export` | invalid | `export_sha256` is not the library's |
| 10 | `malformed line` | invalid | a member missing, added or of the wrong type; a malformed name |
| 11 | `unknown record kind` | invalid | a record of a kind this format does not have |
| 12 | `unknown name` | invalid | no declaration of the library has the name |
| 13 | `a name several declarations have` | invalid | the library has more than one declaration of the name |
| 14 | `a declaration of the wrong kind` | invalid | a class that is no inductive type, an instance or eliminator that is one |
| 15 | `an instance named twice` | invalid | two instance records of one declaration |
| 16 | `a default instance named twice` | invalid | two default-instance records of one declaration |
| 17 | `a reducibility named twice` | invalid | two reducibility records of one declaration |
| 18 | `two eliminators for the same types` | invalid | two eliminators of one kind with the same target types |
| 19 | `a number beyond 2^32 - 1` | unsupported | a priority or synthesis-order entry that large |
| 20 | `records differ in number from the header` | invalid | records missing or added |
| 21 | `records differ from their SHA-256` | invalid | a record changed |
| 22 | `no room` | full | the heap has no room for the tables |
| 23 | `name lookup failed` | as the lookup's | the stage's name lookup failed |
| 24 | `the library's stage is sealed: its names cannot be looked up` | invalid | called with a sealed stage (a Forth caller's mistake) |
| 25 | `a read in progress` | invalid | called during a read (a Forth caller's mistake) |

Misuse is refused before anything runs:
`--elab-data` without `--env` or `--snapshot` ("needs --env or
--snapshot, the library it describes") or with an export instead of a
text ("goes only with a LeanForth text").

## The Forth interface (`src/front/elab-data.fs`)

Untrusted, fail-closed; its state is in the checker context (ADR 0009).
Declarations are the stage's declaration numbers (`src/import/stage.fs`).

| Word | Stack effect | What it does |
| --- | --- | --- |
| `elab-read` | `( c-addr u stage sha -- outcome )` | read the file against a stage read and not sealed, and the export's 32-byte SHA-256 at `sha` |
| `elab-error`, `elab-error-line`, `elab-error-code`, `elab-error-why` | `( -- line c-addr u )` | where and why the last read failed: its line, its [code](#errors) and text |
| `elab-loaded?` | `( -- flag )` | the last read was ok |
| `elab-reset` | `( -- )` | forget everything |
| `elab-count` | `( kind -- n )` | records of a kind: `elab-instance`, `elab-default`, `elab-reducibility`, `elab-eliminator` |
| `elab-instance@` | `( i -- d class priority )` | instance `i` |
| `elab-instance-order` | `( i -- addr n )` | its synthesis order, `n` cells |
| `elab-instance-of` | `( d -- i true \| false )` | the instance record of a declaration |
| `elab-default@` | `( i -- class d priority )` | default instance `i` |
| `elab-status` | `( d -- status )` | `elab-semireducible` (no record), `elab-reducible`, `elab-irreducible`, `elab-implicit-reducible`, `elab-instance-reducible` |
| `elab-eliminator@` | `( i -- kind d )` | eliminator `i`, kind `elab-induction` or `elab-cases` |
| `elab-eliminator-types` | `( i -- addr n )` | its target types, `n` cells |
| `elab-eliminator-for` | `( d kind -- i true \| false )` | the eliminator of a kind whose one target type is `d` |

## Tests and evidence

- `make test-elab-data` (in `make test`): `tests/front/elab-data.fs`, the
  reader's words (every kind read back, eliminators found by kind and
  type, a refused read keeps nothing, a later read replaces an earlier
  one, a missing file, a read during a read and a sealed stage refused,
  each of the 10 allocations of a read in a new context refused in turn:
  full, never another outcome, no block kept; error codes and texts, BASE
  kept); `tests/front/test_elab_data.py`, the finisher (kept and left
  out, deterministic, 8 refusals), the schema (52 good lines, 11 wrong
  ones), the [error catalogue](#errors) against the reader's, and the command
  line: the good data with an export, a snapshot and `--no-manifest`, 16
  eliminators (the table grows), the verdicts unchanged, 3 misuses and 63
  damaged files, each refused with its line, code, text and exit status.
  Both run on Gforth 0.7.3 too. Block coverage of `src/front/elab-data.fs`
  over `make test`: 526 of 531 blocks (the 5 left are listed in
  `tests/coverage-baseline.json`).
- `make reference-elab-data` (in `make check`, pinned Lean):
  `tests/front/elab-init.sh`, about 60 s. `scripts/export-elab.sh`
  reproduces `tests/front/init-slice.elab.ndjson` byte for byte; for all
  of `Init` (its export checked by SHA-256), the records written plus
  those left out equal pinned Lean's own counts, found through Lean's
  public queries one constant at a time
  (`tests/reference/elab-data-counts.lean`: `getInstancePriority?`,
  `getDefaultInstances`, `getReducibilityStatus`,
  `getCustomEliminator?`); LeanForth reads all 10,587 records against the
  staged `Init` export and finds the same counts, statuses and samples as
  Lean (`synthInstance` for `Add Nat` and `OfNat Nat 0`, the default
  instances of `OfNat` and `HAdd`, Nat's eliminators `Nat.recAux` and
  `Nat.casesAuxOn`); every line is valid under the schema.
- Planted faults (`tests/mutants/faults.toml`, `fe-elab-*` and
  `fe-priority-ignored`), each caught: an unknown name, a wrong kind,
  another export, a changed record count or SHA-256, a reducibility or an
  eliminator given twice, a refused read that keeps records, a priority
  kept as 0, names looked up part by part at the root, and
  `--elab-data` ignored.

## Limits and what is left

- Nothing uses the data yet: FE1e (instances, default instances) and FE1g
  (eliminators) will.
- Only `--elab-data FILE`; naming the data in the export's manifest (the
  plan row's alternative) is not done, and a snapshot does not keep the
  data (both later steps).
- The first slice only: simp lemmas, `elab_as_elim`, class out-parameters,
  structure fields and parents, matchers and equations, `protected` and
  `export` aliases come with later rows (design §4.9).
- Scoped entries (active only after `open`) are not exported.
- A name several declarations of the library have is refused; a single
  export has none, but a snapshot with layers could.
