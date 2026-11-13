# Elaboration data: Lean's attributes for LeanForth's front end

Plan rows FE1d and FE1e1 ([plan](../project/PLAN_DRAFT.md#phase-8-front-end-fe1fe12-2026-11-12-replaces-831-and-832);
[ADR 0021](../adr/0021-front-end.md) D10; [front-end design](../design/FRONT_END.md#49-elaboration-data);
[FE1e design](../design/FE1E_APPLICATIONS.md#31-elaboration-data-format-2) §3.1).
Status (2026-11-12), in the stages of
[DONE_CHECKER.md](../development/DONE_CHECKER.md#stages):

- Format 1 (FE1d) was **integrated**: the implementer ran
  `check --snapshot INIT.lfsnap --elab-data init.elab.ndjson tests/author/19-add-zero.lf`
  on a snapshot of all of `Init`. The data was read whole, in 13.7 s and
  0.6 GB in all; the slice's data was refused there as another export's.
  The done checker has not run it.
- Format 2 (FE1e1) is **tested alone**. The exporter, the reader and
  `leanforth check --elab-data` read and check it, and the reference test
  compares it with pinned Lean on all of `Init`. The format-2 sections
  below are the current ones; format 1 is now refused.
- Nothing uses the data yet. The elaborator (FE1e3 and later), the
  tactics (FE1g) and Meta's whnf (FE1d2) are not built.

## What it is and why

A Lean export (lean4export, [NDJSON_READER.md](../development/NDJSON_READER.md))
holds the declarations of a library: their types and values, which is all
the kernel needs. Lean's *elaborator*, which turns what a user writes into
those terms, needs more:

- which declarations are **instances** of which **classes**, with what
  priority, and in which order Lean's instance search tries them (so that
  `0 + n` finds `Nat`'s addition exactly as Lean does);
- which instances are **default instances** (so that the numeral `0` is a
  `Nat` when nothing else says so);
- how readily each declaration unfolds (its **reducibility**);
- which **eliminator** the `induction` and `cases` tactics use for a type
  (`Nat.recAux` rather than `Nat.rec`);
- which definitions are **matchers**, **auxiliary recursors** or
  **projection functions**, which Lean's own weak-head normal form
  (Meta's whnf) unfolds in special ways.

Lean keeps these as attributes and environment extensions in its
`.olean` files, not in the export.

The elaboration data is a second file, written beside the export. A
small Lean program writes it, run with pinned Lean when the library is
exported (the owner approved it as a development tool on 2026-11-12,
"Front-end syntax", answer 8). LeanForth reads it and checks it against
the export. A user who only checks LeanForth text needs no Lean.

The same fact in three forms:

- In mathematics: *addition on ℕ is a binary operation*.
- In Lean: `instance instAddNat : Add Nat := ⟨Nat.add⟩`, so that
  `#synth Add Nat` answers `instAddNat`.
- In the elaboration data, the line

```json
{"instance":{"class":["Add"],"keys":[{"arity":1,"const":["Add"]},{"arity":0,"const":["Nat"]}],"name":["instAddNat"],"priority":1000,"rank":17,"synth_order":[]}}
```

The line says three things:

- `instAddNat` is an `Add` instance of priority 1000.
- Lean's instance tree files it under the path `Add Nat`.
- It is the 18th value (rank 17) of the tree under `Add`.

Once FE1e is built, the LeanForth text `0 n +` finds it the way Lean's
`0 + n` does.

**Trust.** The data is untrusted and never reaches the kernel: nothing in
it can make a declaration accepted, since every term the front end builds
is checked by the kernel ([ADR 0021](../adr/0021-front-end.md) D1). It can
change what a statement *means* (a wrong instance would make `+` mean
something else). What LeanForth checks and what it takes on trust:

- **Checked against the export, when it is read:**
  - the file's form: every line, member, key and number, and the records
    of each kind and their SHA-256 as the header states them;
  - that the header names the library's export by its SHA-256;
  - that every name is exactly one declaration of the library, of the
    right *kind*:
    - a class is an inductive type;
    - an instance, eliminator, tagged declaration or projection function
      is not one;
    - a matcher is a definition;
    - a projection's constructor is a constructor;
    - a projection key names an inductive type;
  - that no declaration is named twice;
  - that an instance's or default instance's class has a class record;
  - that an instance's keys make one term, as Lean's paths do;
  - that the ranks under each root key of Lean's instance tree run 0, 1,
    2, ... without a gap or a repeat, so that every value of the tree is
    an instance or an instance left out;
  - that a left-out instance the export is said to lack is no declaration
    of the library;
  - that a matcher's and a projection's numbers fit the declaration's
    type: as many leading Pi binders as their arity needs, an elimination
    universe among the universe parameters, the field among the
    constructor's.
- **Taken on trust from pinned Lean:** everything the export cannot
  confirm by names, kinds and types alone. These are pinned Lean's
  output, bound to the export only by its SHA-256, which is not a key:
  anyone can write a file with the right hash and other values.
  - that an instance belongs to the class its record names and has those
    keys (Lean computes both from the instance's type);
  - the ranks themselves (the order of Lean's tree depends on 64-bit name
    hashes and on import order, which the export does not hold);
  - priorities and synthesis orders;
  - which default instance a class has, and its rank;
  - out-parameter positions, reducibility statuses and tags;
  - the matchers' alternatives and discriminant names;
  - whether a projection's structure is a class;
  - which eliminator Lean's `induction` and `cases` use.
- **Still to come:**
  - Plan row FE1e3 checks, at the first instance problem, each
    instance's and default instance's class against its type's
    conclusion, each instance's keys (recomputed by FE1e2's `mkPath`) and
    each class's out-parameters ([FE1e design](../design/FE1E_APPLICATIONS.md#4-the-instance-class-check-fe1d-review-m1) §4).
  - For the rest, the guard is that every statement is printed back in
    three forms and compared with Lean's ([parser] gate).

## Making it: `scripts/export-elab.sh`

```text
$ scripts/export.sh init.ndjson Init                     # the export and its manifest
$ scripts/export-elab.sh init.elab.ndjson init.ndjson Init
init.elab.ndjson: 290 class, 2938 instance, 31 instance_left_out, 34 default_instance, 7609 reducibility, 6 eliminator, 3790 tag, 2553 matcher, 975 projection, 0 sunfold; left out (not declarations of the export): 0 class, 0 instance, 0 default_instance, 114 reducibility, 0 eliminator, 45 tag, 78 matcher, 12 projection
```

The example above is shown, not run by `make check-doc-examples`, because
it needs pinned Lean; `make reference-elab-data` runs it. The console
examples further down are run.

`scripts/export-elab.sh OUTPUT EXPORT MODULE...` works in three steps:

1. It checks the Lean version and revision as `scripts/export.sh` does.
2. It runs `scripts/export_elab.lean` (`lean --run`) on the modules.
3. It runs `scripts/export_elab.py`, which does the following:

- It keeps the records whose every name is a declaration of EXPORT, so
  that a slice of a library (`scripts/export.sh OUT Init -- NAMES`) gets
  the data of its own declarations. For a whole module, the records left
  out are those of declarations leanexport does not write: internal names
  (a part starting with `_`, such as private declarations) and unsafe
  ones, unless an exported declaration uses them (249 for `Init`).
- It keeps Lean's instance tree whole under every root key the export can
  reach. A value of the tree whose declaration the export lacks, or which
  Lean has erased, becomes an `instance_left_out` record with its keys,
  rank, priority and the reason. A root key whose own names the export
  lacks is left out with all its values: no query of the export can
  reach it.
- It refuses, with exit status 1 and nothing written:
  - a record whose names are all there but of the wrong kind, or an
    instance of the export whose class or keys name what the export
    lacks: the export and the modules do not belong together;
  - anything not as the Lean program writes it, such as a key that is not
    one of Lean's, keys that are not one term, or ranks under a root that
    are not 0, 1, 2, ...;
  - another Lean;
  - an export whose SHA-256 differs from its manifest's.
- It sorts the records and writes the header, so the same input always
  gives the same bytes.

Measured on 2026-11-12 (development machine), `Init` takes about 12 s:
about 6 s for Lean and 6 s for reading the 346 MB export; the file is
2.6 MB. The init slice of the tests (`tests/author/init-slice.ndjson`, 59
declarations) gives `tests/front/init-slice.elab.ndjson`:

- 3 classes (`Add`, `HAdd` with out-parameter 2, `OfNat`);
- 3 instances (`instAddNat`, `instHAdd`, `instOfNatNat`);
- 54 instances left out: the rest of `Add`'s, `HAdd`'s and `OfNat`'s
  trees, such as `Zero.toOfNat0`;
- 2 default instances (`instHAdd` for `HAdd`, priority 1000;
  `instOfNatNat` for `OfNat`, priority 100);
- 18 reducibility statuses;
- 5 tags (of `Nat.casesOn`, `Nat.brecOn`, `Nat.below`);
- 4 matchers (`Nat.add.match_1` and three private ones);
- 3 projection functions (`Add.add`, `HAdd.hAdd`, `OfNat.ofNat`);
- no eliminator (`Nat.recAux` is not in the slice).

What the Lean program reads, after `importModules` with the extensions
loaded (global entries only: nothing scoped is active after an import):

| Record | Lean 4.35.0 source | Count in `Init` |
| --- | --- | --- |
| `class` | `classExtension` (Class.lean:14): the classes and the positions of their out-parameters and out-level parameters | 290 |
| `instance`, `instance_left_out` | `Meta.instanceExtension`'s discrimination tree (Instances.lean:95), walked depth first per root key, children and values in their stored order: each value's name, class (as `Meta.addInstance` finds it: `forallTelescopeReducing`, `isClass?`), priority, `synthOrder`, keys (`InstanceEntry.keys`) and rank; the program stops if the tree and Lean's table of instance names disagree | 2,969 (0 erased) |
| `default_instance` | `Meta.defaultInstanceExtension`: class, instance, priority, and the rank in `getDefaultInstances` (most recent first) | 34 |
| `reducibility` | every constant whose `getReducibilityStatusCore` is not `semireducible`: `reducible`, `irreducible`, `implicit_reducible` or `instance_reducible` (Lean 4.35.0's five statuses) | 7,723 (4,491 reducible, 2,782 instance_reducible, 343 implicit_reducible, 107 irreducible) |
| `eliminator` | `Meta.customEliminatorExt`: `@[induction_eliminator]` and `@[cases_eliminator]`, keyed as Lean keys them by the head constants of the explicit targets' types | 6 (`Nat.recAux`, `Nat.casesAuxOn`, `BitVec.cons_induction`, `Decidable.falseTrueCases` twice, `Std.PlausibleIterStep.casesOn`) |
| `tag` | per constant: the tag attributes `elab_as_elim` and `elab_without_expected_type` (Elab/App.lean:28, 1123); `aux_recursor` (`isAuxRecursor`, AuxRecursor.lean:31, which also holds for `Eq.ndrec` and `Eq.ndrecOn`); `no_confusion` (`isNoConfusion`); `cases_on`, `rec_on`, `brec_on` (`isCasesOnRecursor` and its siblings: an auxiliary recursor named `casesOn`, `recOn`, `brecOn`) | 3,835 (1,496 aux_recursor, 886 no_confusion, 604 cases_on, 584 rec_on, 244 elab_as_elim, 21 brec_on) |
| `matcher` | per constant, `Meta.getMatcherInfoCore?` (Meta/Match/MatcherInfo.lean:141) | 2,631 |
| `projection` | per constant, `getProjectionFnInfo?` (ProjFns.lean:37) | 987 |

The order of the instance tree cannot be recovered from the export: Lean
orders a node's children by `Key.lt` (DiscrTree/Basic.lean:40), which
compares constants by `Name.quickLt`, a comparison of 64-bit name
hashes. Lean orders the values of a leaf by insertion, which follows the
import order of modules and the order of declarations in each. So the
data carries each value's rank: its place in the depth-first walk of its
root key's tree. Lean's `DiscrTree.getUnify` returns the matching values
in exactly that order, filtered to the matches (probe p6 of the FE1e
design). `getInstances` then sorts them stably by priority, and Lean
tries them from the last.

## The format, version 2

One JSON object per line ([schema](../../schemas/elab-data-2.schema.json),
which every line satisfies). Names and keys are written as follows:

- A name is the JSON array of its parts, root first, each a string or a
  natural number (`Nat.add` is `["Nat","add"]`; a private name keeps its
  numeric part).
- A key is one of Lean's discrimination-tree keys (`DiscrTree.Key`):

| Key | JSON | Lean's `Key.arity` (the terms that follow it in a path) |
| --- | --- | --- |
| star (any term) | `"star"` | 0 |
| other | `"other"` | 0 |
| arrow (a Pi type) | `"arrow"` | 1 (its domain) |
| constant `c` applied to `n` arguments | `{"const":NAME,"arity":n}` | n |
| natural-number literal | `{"lit":"DIGITS"}`, the decimal digits as a text (as lean4export writes `natVal`; `Init` has 2^64) | 0 |
| string literal | `{"lit_str":S}` | 0 |
| projection of field `i` of structure `s`, applied to `n` arguments | `{"proj":NAME,"idx":i,"arity":n}` | n + 1 |

An fvar key is not one: no global instance has it, so the exporter stops
and the reader refuses it as malformed.

Line 1 is the header:

```json
{"elab_data":{"export_sha256":"5f906a8e...","format":"leanforth-elab-data","format_version":2,"lean_githash":"eb6cafb7290e8bd5f2937522d8d804f58f02bafc","lean_version":"4.35.0","modules":["Init"],"records":{"class":3,"default_instance":2,"eliminator":0,"instance":3,"instance_left_out":54,"matcher":4,"projection":3,"reducibility":18,"sunfold":0,"tag":5},"records_sha256":"..."}}
```

- `export_sha256` is the export's SHA-256 as its manifest records it.
- `records` gives the number of each kind of record that follows.
- `records_sha256` is the SHA-256 of every later line with its line feed,
  so that a file cut off between two lines, or changed, is refused.

Then the records, sorted by kind in the order of this table, and within a
kind by text:

| Kind | Members |
| --- | --- |
| `class` | `name` (the class), `out_params` (the positions of its out-parameters), `out_level_params` (the positions of its universe parameters that occur only in out-parameters) |
| `instance` | `name` (the instance), `class`, `priority` (natural, below 2^32), `synth_order` (naturals: the order in which its instance arguments are synthesized), `keys`, `rank` (its place under its root key, the first of its keys) |
| `instance_left_out` | a value of Lean's instance tree that is no `instance` record: `name`, `keys`, `priority`, `rank`, and `reason`, either `erased` (in Lean's tree but never a candidate) or `not_exported` (the export lacks its declaration; Lean would try it, so FE1e answers *unsupported* when it is a candidate, design §2.7). Its keys may name a constant the export lacks: the reader keeps such a name as a *foreign* key, which no query of the library can equal |
| `default_instance` | `class`, `name` (the instance), `priority`, `rank` (its place in Lean's `getDefaultInstances` of the class, the most recent first) |
| `reducibility` | `name`, `status`: one of `reducible`, `irreducible`, `implicit_reducible`, `instance_reducible` |
| `eliminator` | `kind` (`induction` or `cases`), `name` (the eliminator), `types` (the names of the explicit targets' types) |
| `tag` | `name`, `tag`: one of `elab_as_elim`, `elab_without_expected_type`, `aux_recursor`, `no_confusion`, `cases_on`, `rec_on`, `brec_on` |
| `matcher` | `name` (the matcher), `num_params`, `num_discrs`, `u_elim_pos` (the place of the universe parameter it eliminates into, or `null` when it eliminates only into `Prop`), `alt_infos` (each alternative's `num_fields`, `num_overlaps` and `has_unit_thunk`), `discr_names` (each discriminant's `h :` name, or `null`). Lean's `overlaps` map, which only the splitter reads, is not written |
| `projection` | `name` (the projection function), `ctor` (the structure's constructor), `num_params` (the structure's parameters), `idx` (the field), `from_class` (whether the structure is a class) |
| `sunfold` | smart-unfolding bodies (plan row FE1d2): a kind of format 2 that no exporter writes yet; the reader refuses such a record as *unsupported* (error 38). The [design](#smart-unfolding-bodies-designed-not-built) is below |

A default instance the export lacks leaves a gap in its class's ranks;
format 2 has no record for it (none in `Init`). Plan row FE1e3 answers
*unsupported* when a gap is reached.

Format version 1 ([schema](../../schemas/elab-data-1.schema.json): the
`instance` record without `keys` and `rank`, the `default_instance`
record without `rank`, and only the four kinds `instance`,
`default_instance`, `reducibility` and `eliminator`) is refused as
"another format version" (unsupported, error 7). Export the data again
with `scripts/export-elab.sh`.

## Reading it: `leanforth check --elab-data`

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson --elab-data tests/front/init-slice.elab.ndjson tests/author/19-add-zero.lf | head -1
elaboration data: 3 instances, 2 default instances, 18 reducibility statuses, 0 eliminators, 54 instances left out, 3 classes, 5 tags, 4 matchers, 3 projections
```

`--elab-data DATA` goes with a LeanForth text and its library (`--env
EXPORT` or `--snapshot FILE`). After the library is read and before the
text runs, `src/front/elab-data.fs` reads DATA. It checks DATA against the
library's names and against the SHA-256 of its export: the manifest
check's, the snapshot's, or, with `--no-manifest`, the file's, hashed
then. The verdicts are those of the same run without `--elab-data`:
nothing uses the data yet. A refusal stops the run before the text runs.
It prints the line and the reason, and exits with the outcome's status (4
invalid, 2 unsupported, 3 full). Here the test file
`tests/front/cut-off.elab.ndjson`, the eliminators fixture with its last
record cut off, is refused:

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson --elab-data tests/front/cut-off.elab.ndjson tests/author/19-add-zero.lf
error: invalid: the elaboration data was refused at line 96 (error 20): records differ in number from the header; the LeanForth text was not checked
```

What the reader checks, each failure refused with its reason:

| Check | Reason printed | Outcome |
| --- | --- | --- |
| line 1 is a header of this format | `no header`, `not elaboration data` | invalid |
| its format version, Lean version and revision | `another format version`, `another Lean version` | unsupported |
| its members, each well typed | `malformed line` | invalid |
| its export SHA-256 is the library's | `elaboration data of another export` | invalid |
| every line is one JSON object of a known kind with exactly its members | `not one JSON value within the limits`, `unknown record kind`, `malformed line` | invalid |
| the kind is one this reader reads | `a record kind this reader does not read yet` (`sunfold`) | unsupported |
| every name is exactly one declaration of the library (a left-out instance's key constants: or none, kept as foreign keys) | `unknown name`, `a name several declarations have` | invalid |
| of the right kind: a class an inductive type; an instance, eliminator, tagged declaration or projection function not one; a matcher a definition; a projection's constructor a constructor; a projection key's structure an inductive type | `a declaration of the wrong kind` | invalid |
| an instance's and a default instance's class has a class record before it | `a class without its class record before it` | invalid |
| every key one of Lean's forms (a literal's digits canonical), and an instance's or left-out instance's keys one term | `malformed line`, `keys that are not one term` | invalid |
| no declaration named twice as one kind; no tag twice; one eliminator per kind and types | `an instance named twice`, `a default instance named twice`, `a reducibility named twice`, `a class named twice`, `a tag named twice`, `a matcher named twice`, `a projection named twice`, `two eliminators for the same types` | invalid |
| no two values under one root key with one rank, no two default instances of one class with one rank | `two values of one root key with one rank`, `two default instances of one class with one rank` | invalid |
| a left-out instance whose reason is `not_exported` is no declaration of the library | `a left-out instance the library has` | invalid |
| a matcher's type has a leading Pi binder for each parameter, the motive, each discriminant and each alternative, and its elimination universe is one of its universe parameters; a projection function's type has one for each parameter and the structure, and its constructor's type one for each parameter and field up to `idx` (written out, without unfolding) | `numbers that do not fit the declaration's type` | invalid |
| as many discriminant names as discriminants | `malformed line` | invalid |
| priorities, ranks, arities, positions and other numbers fit 32 bits | `a number beyond 2^32 - 1` | unsupported (no Lean library has one; the field widens if one appears) |
| after the last line: the records of each kind and their SHA-256 are the header's | `records differ in number from the header`, `records differ from their SHA-256` | invalid |
| after the last line: the ranks under each root key have no gap (every value of rank r > 0 has a value of rank r - 1 beside it) | `ranks of a root key with a gap` | invalid |
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
| 7 | `another format version` | unsupported | `format_version` is not 2 (format 1 among them) |
| 8 | `another Lean version` | unsupported | written by another Lean version or revision |
| 9 | `elaboration data of another export` | invalid | `export_sha256` is not the library's |
| 10 | `malformed line` | invalid | a member missing, added or of the wrong type; a malformed name or key; discriminant names that are not one per discriminant |
| 11 | `unknown record kind` | invalid | a record of a kind this format does not have |
| 12 | `unknown name` | invalid | no declaration of the library has the name |
| 13 | `a name several declarations have` | invalid | the library has more than one declaration of the name |
| 14 | `a declaration of the wrong kind` | invalid | a class that is no inductive type, an instance or eliminator that is one, and the other kinds above |
| 15 | `an instance named twice` | invalid | two instance records of one declaration |
| 16 | `a default instance named twice` | invalid | two default-instance records of one declaration |
| 17 | `a reducibility named twice` | invalid | two reducibility records of one declaration |
| 18 | `two eliminators for the same types` | invalid | two eliminators of one kind with the same target types |
| 19 | `a number beyond 2^32 - 1` | unsupported | a priority, rank, arity, position or other number that large |
| 20 | `records differ in number from the header` | invalid | records missing or added |
| 21 | `records differ from their SHA-256` | invalid | a record changed |
| 22 | `no room` | full | the heap has no room for the tables |
| 23 | `name lookup failed` | as the lookup's | the stage's name lookup failed |
| 24 | `the library's stage is sealed: its names cannot be looked up` | invalid | called with a sealed stage (a Forth caller's mistake) |
| 25 | `a read in progress` | invalid | called during a read (a Forth caller's mistake) |
| 26 | `the library's export could not be hashed` | as the hash's (full: no room for its buffer) | with `--no-manifest`, the library file could not be hashed again |
| 27 | `a class without its class record before it` | invalid | an instance's or default instance's class has no class record before it |
| 28 | `a class named twice` | invalid | two class records of one declaration |
| 29 | `a tag named twice` | invalid | one tag of one declaration given twice |
| 30 | `keys that are not one term` | invalid | a key list that is empty, ends before its term does or goes on after it |
| 31 | `two values of one root key with one rank` | invalid | two instances or left-out instances under one root key with the same rank |
| 32 | `ranks of a root key with a gap` | invalid | after the last line: a rank r > 0 under a root key with no rank r - 1 |
| 33 | `two default instances of one class with one rank` | invalid | two default instances of a class with the same rank |
| 34 | `a left-out instance the library has` | invalid | a `not_exported` left-out instance whose name is a declaration of the library |
| 35 | `a matcher named twice` | invalid | two matcher records of one declaration |
| 36 | `a projection named twice` | invalid | two projection records of one declaration |
| 37 | `numbers that do not fit the declaration's type` | invalid | a matcher's or projection's numbers that its type, or its constructor's, cannot have |
| 38 | `a record kind this reader does not read yet` | unsupported | a `sunfold` record (plan row FE1d2) |

Misuse is refused before anything runs:

- `--elab-data` without `--env` or `--snapshot`: "needs --env or
  --snapshot, the library it describes".
- with an export instead of a text: "goes only with a LeanForth text".
- with a layered snapshot (`--snapshot BASE --snapshot LAYER`): "does
  not go with a layered snapshot yet". The hash checked would be the base's
  export's, while the names would also be the layers', so a record naming a
  layer's declaration would pass as the base's.

## The Forth interface (`src/front/elab-data.fs`, `src/front/elab-keys.fs`)

Both files are untrusted and fail closed; their state is in the checker
context (ADR 0009). Declarations are the stage's declaration numbers
(`src/import/stage.fs`). Some words take a record number `i` (or `j`, `k`,
`m`, `p`, an alternative `a`, a key `k`) and do not check it: it must be
below `elab-count` of its kind. Only the `elab-*` words below are the
interface; each module's helpers and fields are named `ed-*` and `ek-*`.
Example, in three forms, of what the words give for the slice's data:

- mathematics: the class of additions on a type, and the instance for ℕ;
- Lean: `#synth Add Nat` gives `instAddNat`, and
  `DiscrTree` files it under `Add Nat`;
- LeanForth (Forth): `s" instAddNat" top elab-instance-of` gives `0 true`;
  `0 elab-instance-keys` gives the key list `k 2`; `k elab-key-tag` is
  `elab-key-const`; `k elab-key-decl` is `Add`'s declaration;
  `0 elab-instance-rank` is 17.

| Word | Stack effect | What it does |
| --- | --- | --- |
| `elab-read` | `( c-addr u stage sha -- outcome )` | read the file against a stage read and not sealed, and the export's 32-byte SHA-256 at `sha` |
| `elab-error`, `elab-error-line`, `elab-error-code`, `elab-error-why` | `( -- line c-addr u )` | where and why the last read failed: its line, its [code](#errors) and text |
| `elab-unhashed` | `( outcome -- outcome )` | for a caller that could not hash the export: refuse with error 26 at line 0, nothing loaded |
| `elab-loaded?` | `( -- flag )` | the last read was ok |
| `elab-reset` | `( -- )` | forget everything |
| `elab-count` | `( kind -- n )` | records of a kind: `elab-instance`, `elab-default`, `elab-reducibility`, `elab-eliminator`, `elab-left-out`, `elab-class`, `elab-tag`, `elab-matcher`, `elab-projection` (`elab-sunfold`: always 0) |
| `elab-instance@` | `( i -- d class priority )` | instance `i` |
| `elab-instance-order` | `( i -- addr n )` | its synthesis order, `n` cells |
| `elab-instance-keys` | `( i -- k n )` | its keys, `k` .. `k+n-1` |
| `elab-instance-rank` | `( i -- rank )` | its rank under its root key (its first key) |
| `elab-instance-of` | `( d -- i true \| false )` | the instance record of a declaration |
| `elab-left-out@` | `( j -- priority rank reason )` | left-out instance `j`; reason `elab-erased` or `elab-not-exported` |
| `elab-left-out-keys` | `( j -- k n )` | its keys |
| `elab-default@` | `( i -- class d priority )` | default instance `i` |
| `elab-default-rank` | `( i -- rank )` | its rank among its class's |
| `elab-class-of` | `( d -- k true \| false )` | the class record of a declaration |
| `elab-class@` | `( k -- d )` | class `k`'s declaration |
| `elab-class-out-params`, `elab-class-out-levels` | `( k -- addr n )` | its out-parameter and out-level positions, `n` cells |
| `elab-status` | `( d -- status )` | `elab-semireducible` (no record), `elab-reducible`, `elab-irreducible`, `elab-implicit-reducible`, `elab-instance-reducible` |
| `elab-tagged?` | `( d tag -- flag )` | whether `d` has the tag: `elab-tag-as-elim`, `elab-tag-no-expected`, `elab-tag-aux-recursor`, `elab-tag-no-confusion`, `elab-tag-cases-on`, `elab-tag-rec-on`, `elab-tag-brec-on` |
| `elab-eliminator@` | `( i -- kind d )` | eliminator `i`, kind `elab-induction` or `elab-cases` |
| `elab-eliminator-types` | `( i -- addr n )` | its target types, `n` cells |
| `elab-eliminator-for` | `( d kind -- i true \| false )` | the eliminator of a kind whose one target type is `d` |
| `elab-matcher-of` | `( d -- m true \| false )` | the matcher record of a declaration |
| `elab-matcher@` | `( m -- d params discrs )` | matcher `m` |
| `elab-matcher-elim` | `( m -- pos true \| false )` | its elimination universe's place; false: into `Prop` only |
| `elab-matcher-alts`, `elab-alt@` | `( m -- a n )`, `( a -- fields overlaps thunk? )` | its alternatives |
| `elab-projection-of` | `( d -- p true \| false )` | the projection record of a declaration |
| `elab-projection@`, `elab-projection-decl`, `elab-projection-class?` | `( p -- ctor params idx )`, `( p -- d )`, `( p -- flag )` | projection `p` |
| `elab-key-tag` | `( k -- tag )` | `elab-key-star`, `-other`, `-lit`, `-str`, `-const`, `-arrow`, `-proj`, `-foreign` |
| `elab-key-decl`, `elab-key-idx` | `( k -- d )`, `( k -- i )` | a constant's or projection's declaration; a projection's field |
| `elab-key-arity` | `( k -- n )` | Lean's `Key.arity` (the table above; a foreign constant's arguments) |
| `elab-key-text` | `( k -- c-addr u )` | a literal's digits, a string literal's bytes, a foreign constant's name (each part as 32-bit fields: 0, the length and the bytes of a string, or 1 and the number) |
| `elab-key=`, `elab-key-hash` | `( k1 k2 -- flag )`, `( k -- h )` | Lean's equality of keys, texts compared byte for byte; a 32-bit hash equal for equal keys |
| `elab-one-term?` | `( k n -- flag )` | keys `k` .. `k+n-1` make one term in Lean's path order |
| `elab-keys#` | `( -- n )` | the keys kept |

`elab-keys.fs` also has the words `elab-data.fs` builds keys with
(`elab-key-new`, `elab-key-ref!`, `elab-key-arity!`, `elab-key-idx!`,
`elab-key-text-start`, `elab-key-text-end`, `elab-text-room`,
`elab-keys-clear`); its header documents them.

## Smart-unfolding bodies: designed, not built

Plan row FE1d2 (on the branch that adds it) needs one more fact for Meta's
whnf. When the option `smartUnfolding` is on (the default) and `f._sunfold`
exists, `unfoldDefinition?` unfolds `f` by `f._sunfold`'s value and runs
`smartUnfoldingReduce?` (Meta/WHNF.lean:720, 853, 918). That value is `f`
written with direct recursion instead of `brecOn`. Annotations mark where a
match must reduce (`sunfoldMatch`) and where an alternative was reached
(`sunfoldMatchAlt`). lean4export writes neither `_sunfold` definitions
(an internal name) nor annotations (mdata). Measured with pinned Lean
(scratch probe, 2026-11-12):

- `Init` has 389 `_sunfold` definitions.
- Their annotations have three keys: `sunfoldMatch` (389),
  `sunfoldMatchAlt` (1,014) and `borrowed` (8, the compiler's
  borrow mark).
- `Nat.add._sunfold` is
  `fun x y => [sunfoldMatch] Nat.add.match_1 (fun _ _ => Nat) x y (fun a => [sunfoldMatchAlt] a) (fun a b => [sunfoldMatchAlt] Nat.succ (Nat.add a b))`.

The design, for format 2's reserved kind `sunfold` (the header already
counts it, so the data needs no new format version):

- **Record:** `{"sunfold":{"name":F,"level_params":[NAME...],"nodes":[NODE...],"value":I}}`.
  - `F` is the definition `f` of the library.
  - `level_params` are `f._sunfold`'s universe parameters (Lean gives
    `f`'s).
  - `nodes` is a hash-consed table of the value's subterms, each node
    referring only to earlier nodes by their index, so that shared
    subterms are written once.
  - `value` is the index of the root.
- **Nodes:**
  - `{"bvar":i}`
  - `{"sort":L}`
  - `{"const":NAME,"levels":[L...]}`
  - `{"app":[f,a]}`
  - `{"lam":{"name":NAME,"info":"default|implicit|strict|inst","type":i,"body":j}}`
    and `{"forall":...}` alike
  - `{"let":{"name":NAME,"type":i,"value":j,"body":k,"non_dep":bool}}`
  - `{"lit":"DIGITS"}`, `{"str":S}`
  - `{"proj":{"struct":NAME,"idx":i,"expr":j}}`
  - `{"mdata":{"entries":[[KEY,VALUE]...],"expr":i}}`, with `KEY` a name
    and `VALUE` one of `{"bool":b}`, `{"nat":"DIGITS"}`, `{"string":S}`,
    `{"name":NAME}` (Lean's `DataValue`; the exporter stops at any other)
  - no free variables or metavariables.
  - Binder names keep their macro scopes as name parts (hygienic names
    such as `x._@.Init.Prelude.2314059840._hygCtx._hyg.13`).
- **Levels**, as JSON trees: `"zero"`, `{"succ":L}`, `{"max":[L,L]}`,
  `{"imax":[L,L]}`, `{"param":NAME}`.
- **Checked when read:** the forms; every constant is one declaration of
  the library; `F` is a definition of the library and has one record; the
  universe parameters are `F`'s, and every `param` is among them; nodes
  refer only to earlier nodes; no bound variable is loose at the root; an
  mdata key is one of the three seen (others unsupported until seen).
- **Checked at first use** (FE1d2's whnf): the value, its annotations
  erased, is type-checked by the kernel against `F`'s type, which is the
  type of `f._sunfold`; *unsupported* if the kernel cannot.
- **Taken on trust:** that it is Lean's `_sunfold` body (any well-typed
  term passes the kernel). Lean's whnf uses it only to decide how far to
  unfold, and every term the front end builds is still kernel-checked;
  the guard is FE1d2's node-for-node comparisons with pinned Lean.
- **Size:** 389 records for `Init`; the node tables keep each record's
  sharing.

## Tests and evidence

- `make test-elab-data` (in `make test`):
  - `tests/front/elab-data.fs` tests the key store's words on keys made
    by hand: each form, equality and hash, one term, and full when the
    heap has no room. It tests the reader's words:
    - every kind read back: instances with keys and ranks, left-out
      instances with foreign keys and literals, classes, tags, matchers,
      projections;
    - eliminators found by kind and type;
    - a refused read keeps nothing, and a later read replaces an earlier
      one;
    - a missing file, a read during a read, a sealed stage and a name
      two declarations of the stage have (error 13) are refused;
    - each allocation of a read in a new context refused in turn: full,
      never another outcome, no block kept;
    - error codes and texts; BASE kept.
  - `tests/front/elab-check-lf.fs` tests the check step: `--no-manifest`
    hashes the library again, and refusing the hash's buffer gives error
    26, full.
  - `tests/front/test_elab_data.py` tests:
    - the finisher: kept and left out, the tree kept whole, deterministic,
      21 refusals;
    - the schema: 190 good lines and 22 wrong ones;
    - the [error catalogue](#errors) against the reader's;
    - the command line: the good data with an export, a snapshot and
      `--no-manifest`, 16 eliminators (the table grows), 3 accepted
      variants, the verdicts unchanged, and 4 misuses (a layered snapshot
      among them);
    - 110 damaged files, each refused with its line, code, text and exit
      status and never "accepted": format 1's checks, format 2's (codes
      27-38, the key forms, ranks, matchers, projections), and a format-1
      file.
  - Never run by `make test` (listed in `tests/coverage-baseline.json`):
    - a name lookup that fails in an open tier (error 23);
    - a tier name beyond the stage's name-to-declaration array;
    - no room while the eliminators' or the ranks' table grows;
    - a THROW inside a read.
- `make reference-elab-data` (in `make check`, pinned Lean):
  `tests/front/elab-init.sh`, about 4 minutes on a busy machine (2026-11-12).
  - `scripts/export-elab.sh` reproduces
    `tests/front/init-slice.elab.ndjson` byte for byte.
  - For all of `Init` (its export checked by SHA-256), the data's
    `records_sha256` is the pinned one. The records written plus those
    left out equal pinned Lean's own counts, found through Lean's public
    queries one constant at a time
    (`tests/reference/elab-data-counts.lean`): `getInstancePriority?`,
    `getErasedInstances`, `getDefaultInstances`, `isClass`,
    `getReducibilityStatus`, `getCustomEliminator?`, the tag predicates,
    `getMatcherInfo?`, `getProjectionFnInfo?`.
  - LeanForth reads all of the records against the staged `Init` export
    and finds the same counts, statuses and samples as Lean (instances
    with their priorities and keys, among them a 2^64 literal, a string
    literal, a projection key and arrow keys; default instances; a
    class's out-parameters; tags; a matcher; a projection; Nat's
    eliminators).
  - For 19 instance problems, the data's ranks give Lean's own
    `DiscrTree.getUnify` order, and its priorities give `getInstances`'
    order (`tests/reference/elab-instance-order.lean`). Among them are
    `OfNat ?α 0`, `HAdd Nat Nat ?γ`, `Add ?α`, `DecidableEq Nat` and
    `HPow Nat Nat Nat`, where the priority sort, not the tree, puts
    `instHPow` before `Lean.Grind.Semiring.npow`.
  - Every line is valid under the schema.
- Planted faults (`tests/mutants/faults.toml`, `fe-elab-*`,
  `fe-priority-ignored` and, for format 2, `fe-ed2-*`), each caught:
  - format 1's checks: an unknown name, a wrong kind (of an instance, of
    a class), another export, a changed record count or SHA-256, an
    instance, default instance, reducibility or eliminator given twice, a
    refused read that keeps records, a priority kept as 0, names looked
    up part by part at the root, another Lean or format version, the
    32-bit bound, a sealed stage, the header's and a record's shape, the
    status mapping, the eliminator's kind ignored in a lookup,
    `--no-manifest` using the manifest's digest, and `--elab-data`
    ignored;
  - format 2's checks (21 faults): each of codes 27-38 skipped, a foreign
    constant allowed in an instance's keys, foreign constants refused in
    a left-out instance's keys, an arrow key's arity read as 0, equal
    texts compared by their offsets, a literal's digits not checked,
    ranks compared without their root keys, a class's out-levels stored
    as its out-parameters, and the finisher's rank check skipped.

## Limits and what is left

- Nothing uses the data yet: FE1e3 and later (instances, default
  instances), FE1g (eliminators) and FE1d2 (matchers, projections,
  auxiliary recursors, smart unfolding) will.
- The class of each instance and default instance, each instance's keys
  and each class's out-parameters are checked against their types only by
  plan row FE1e3; until then they rest on pinned Lean (above, "Trust").
- Smart-unfolding bodies are designed (above), not written or read.
- Only `--elab-data FILE`. Naming the data in the export's manifest (the
  plan row's alternative) is not done, and a snapshot does not keep the
  data; both are later steps.
- Simp lemmas, structure fields and parents, equations, `protected` and
  `export` aliases, `NoConfusionInfo` and the matchers' overlap maps come
  with later rows (design §4.9).
- Scoped entries (active only after `open`) are not exported.
- A name several declarations of the library have is refused; a single
  export has none.
- Not with a layered snapshot (refused): that needs data for each layer
  and a hash of each.
- The tables of keys, facts and records take about 40 bytes per
  declaration and 32 per key: a few MB for `Init`, tens of MB for Mathlib
  (not measured).
