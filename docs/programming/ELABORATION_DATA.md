# Elaboration data: Lean's attributes for LeanForth's front end

Plan rows FE1d, FE1e1 and slice S2 ([plan](../project/PLAN_DRAFT.md#phase-8-front-end-fe1fe12-2026-11-12-replaces-831-and-832);
[ADR 0021](../adr/0021-front-end.md) D10; [front-end design](../design/FRONT_END.md#49-elaboration-data);
[FE1e design](../design/FE1E_APPLICATIONS.md#31-elaboration-data-format-2) §3.1;
[S2 design](../design/S2_INTERFACE.md#3-the-smart-unfolding-records-and-their-markers) §3).
Status (2026-11-13), in the stages of
[DONE_CHECKER.md](../development/DONE_CHECKER.md#stages):

- Format 1 (FE1d) was **integrated**: the implementer ran
  `check --snapshot INIT.lfsnap --elab-data init.elab.ndjson tests/author/19-add-zero.lf`
  on a snapshot of all of `Init`. The data was read whole, in 13.7 s and
  0.6 GB in all; the slice's data was refused there as another export's.
  The done checker has not run it.
- Format 2 (FE1e1) was **tested alone**; it is now refused, as format 1
  is (a format-2 file says `"sunfold":0`, which would read as "no
  definition has a smart-unfolding body").
- Format 3 (S2 merge A, branch `s2-unfold`) is **tested alone**: format 2
  plus every smart-unfolding body (`sunfold`) and the `match_pattern`
  tag. The exporter, the reader and `leanforth check --elab-data` write,
  read and check it; Meta's whnf (`lf-menv-smart?`) answers from it. The
  sections below are format 3's.
- Format 3.1 (slice MF1 of [MATHLIB_FRONT.md](../design/MATHLIB_FRONT.md),
  2026-11-18, the owner's [format] approval of that day) is format 3 with
  [inert nodes](#format-31-inert-metadata); the same reader also takes a
  default instance named twice and, from the exporter, an anonymous
  binder, so that the data of all of Mathlib is written and read whole.
  Works end to end on all of Mathlib (run by the implementer on
  2026-11-18, under [Format 3.1](#format-31-inert-metadata)); the done
  checker has not run it.
- `leanforth check` reads the data but no verdict uses it yet: the
  instance table (FE1e3) and Meta's whnf are tested alone; the
  elaborator (s1-elab) is not merged.

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
    - a projection key names an inductive type (in a left-out instance,
      a constant or structure the library lacks is kept as a foreign
      key instead);
  - that no declaration is named twice;
  - that an instance's or default instance's class has a class record;
  - that an instance's keys make one term, as Lean's paths do;
  - that the ranks under each root key of Lean's instance tree run 0, 1,
    2, ... without a gap or a repeat, so that every value of the tree is
    an instance or an instance left out;
  - that a left-out instance the export is said to lack is no declaration
    of the library;
  - that a matcher's and a projection's numbers fit the declaration's
    type: a matcher's type has exactly as many leading Pi binders as its
    arity, a projection's at least its parameters and the structure; an
    elimination universe is among the universe parameters, the field among
    the constructor's;
  - that a class's out-parameters are among its parameters and its
    out-levels among its universe parameters.
- **Taken on trust from pinned Lean:** everything the export cannot
  confirm by names, kinds and types alone. These are pinned Lean's
  output, bound to the export only by its SHA-256, which is not a key:
  anyone can write a file with the right hash and other values.
  - that an instance belongs to the class its record names and has those
    keys (Lean computes both from the instance's type), until the first
    instance problem checks them (below; an instance whose check cannot
    finish stays on trust, unverified);
  - the ranks themselves (the order of Lean's tree depends on 64-bit name
    hashes and on import order, which the export does not hold);
  - priorities and synthesis orders;
  - which default instance a class has, and its rank (its class is
    checked at the first instance problem, below);
  - which of a class's parameters are out-parameters (within range, as
    above); the synthesis orders' positions (they count the binders
    after unfolding, which the reader does not do: FE1e3 does);
  - reducibility statuses and tags;
  - the matchers' alternatives and discriminant names;
  - whether a projection's structure is a class;
  - which eliminator Lean's `induction` and `cases` use.
- **Checked at the first instance problem** (FE1e3, branch `s1-synth`,
  tested alone; [FE1e design](../design/FE1E_APPLICATIONS.md#4-the-instance-class-check-fe1d-review-m1) §4):
  each instance's root key is its recorded class's constant (error
  115) and its class is its type's conclusion's (error 112); each
  default instance's type ends in its recorded class (error 116); each
  instance's keys, recomputed by FE1e2's `mkPath`, equal the record's
  when its root is first queried (error 113). A difference refuses the
  data at that query and every later one. A record whose check cannot
  finish is unverified: kept on trust, and a search that tries it
  answers unsupported (S1 note §9).
- **Still to come:**
  - Plan row FE1e3b recomputes each class's out-parameters.
  - For the rest, the guard is that every statement is printed back in
    three forms and compared with Lean's ([parser] gate).

## Making it: `scripts/export-elab.sh`

```text
$ scripts/export.sh init.ndjson Init                     # the export and its manifest
$ scripts/export-elab.sh init.elab.ndjson init.ndjson Init
init.elab.ndjson: 290 class, 2938 instance, 31 instance_left_out, 34 default_instance, 7609 reducibility, 6 eliminator, 3813 tag, 2553 matcher, 975 projection, 387 sunfold; left out (not declarations of the export): 0 class, 0 instance, 0 default_instance, 114 reducibility, 0 eliminator, 45 tag, 78 matcher, 12 projection, 2 sunfold; 25 sunfold bodies naming what the export lacks
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
- It keeps a smart-unfolding body when its definition is in the export,
  whatever the body names, and counts the bodies that name a constant the
  export lacks (25 of `Init`'s 387 kept: each names a `f._proof_N` lemma
  that lean4export does not write); LeanForth answers *unsupported* where
  it would use one (S2 merge B).
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
- 10 tags (of `Nat.casesOn`, `Nat.brecOn`, `Nat.below`, and
  `match_pattern` of `Add.add`, `HAdd.hAdd`, `Nat.add`, `Unit.unit`, `rfl`);
- 4 matchers (`Nat.add.match_1` and three private ones);
- 3 projection functions (`Add.add`, `HAdd.hAdd`, `OfNat.ofNat`);
- 1 smart-unfolding body (`Nat.add`'s);
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
| `tag` | per constant: the tag attributes `elab_as_elim` and `elab_without_expected_type` (Elab/App.lean:28, 1123); `aux_recursor` (`isAuxRecursor`, AuxRecursor.lean:31, which also holds for `Eq.ndrec` and `Eq.ndrecOn`); `no_confusion` (`isNoConfusion`); `cases_on`, `rec_on`, `brec_on` (`isCasesOnRecursor` and its siblings: an auxiliary recursor named `casesOn`, `recOn`, `brecOn`); `match_pattern` (`hasMatchPatternAttribute`, Meta/Match/MatchPatternAttr.lean:41) | 3,858 (1,496 aux_recursor, 886 no_confusion, 604 cases_on, 584 rec_on, 244 elab_as_elim, 23 match_pattern, 21 brec_on) |
| `matcher` | per constant, `Meta.getMatcherInfoCore?` (Meta/Match/MatcherInfo.lean:141) | 2,631 |
| `projection` | per constant, `getProjectionFnInfo?` (ProjFns.lean:37) | 987 |
| `sunfold` | every constant `f._sunfold` (`mkSmartUnfoldingNameFor`, Meta/WHNF.lean:50), a definition: `f`, its universe parameters, its value as tables of levels and nodes, and `getStructuralRecArgPos? f` (WHNF.lean:46, which is `getStructuralRecArgPosImp?`, Elab/PreDefinition/Structural/Eqns.lean:191) | 389 |

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

## The format, versions 3 and 3.1

One JSON object per line ([schema](../../schemas/elab-data-3.schema.json),
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
{"elab_data":{"export_sha256":"5f906a8e...","format":"leanforth-elab-data","format_version":3,"lean_githash":"eb6cafb7290e8bd5f2937522d8d804f58f02bafc","lean_version":"4.35.0","modules":["Init"],"records":{"class":3,"default_instance":2,"eliminator":0,"instance":3,"instance_left_out":54,"matcher":4,"projection":3,"reducibility":18,"sunfold":1,"tag":10},"records_sha256":"..."}}
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
| `instance_left_out` | a value of Lean's instance tree that is no `instance` record: `name`, `keys`, `priority`, `rank`, and `reason`, either `erased` (in Lean's tree but never a candidate) or `not_exported` (the export lacks its declaration; Lean would try it, so FE1e answers *unsupported* when it is a candidate, design §2.7). Its keys may name a constant, or project a structure, that the export lacks: the reader keeps such a key as a *foreign* key, which no query of the library can equal |
| `default_instance` | `class`, `name` (the instance), `priority`, `rank` (its place in Lean's `getDefaultInstances` of the class, the most recent first; at most 65,535, error 40). An instance may have two records, of one class at two ranks: Lean conses each `default_instance` attribute onto its class's list (`addDefaultInstanceEntry`, Meta/Instances.lean:390-394) and `synthesizeUsingDefaultPrio` tries both (Mathlib makes `instHSMul` one in `Init/Prelude.lean` and again in `Mathlib/Algebra/Notation/Defs.lean`); both are kept and `lf-default-instances` gives both cells. Two of one class may not share a rank, but the ranks may have gaps: a default instance whose declaration the export lacks has no record of its own (format 2 has no `default_instance_left_out`), so its rank is missing, and refusing gaps would refuse every slice that lacks one. FE1e3's `lf-default-instances` gives a gap there (`lf-default-gap?`), and a caller that reaches it answers *unsupported* |
| `reducibility` | `name`, `status`: one of `reducible`, `irreducible`, `implicit_reducible`, `instance_reducible` |
| `eliminator` | `kind` (`induction` or `cases`), `name` (the eliminator), `types` (the names of the explicit targets' types) |
| `tag` | `name`, `tag`: one of `elab_as_elim`, `elab_without_expected_type`, `aux_recursor`, `no_confusion`, `cases_on`, `rec_on`, `brec_on`, `match_pattern` |
| `matcher` | `name` (the matcher), `num_params`, `num_discrs`, `u_elim_pos` (the place of the universe parameter it eliminates into, or `null` when it eliminates only into `Prop`), `alt_infos` (each alternative's `num_fields`, `num_overlaps` and `has_unit_thunk`), `discr_names` (each discriminant's `h :` name, or `null`). Lean's `overlaps` map, which only the splitter reads, is not written |
| `projection` | `name` (the projection function), `ctor` (the structure's constructor), `num_params` (the structure's parameters), `idx` (the field), `from_class` (whether the structure is a class) |
| `sunfold` | a [smart-unfolding body](#smart-unfolding-bodies-format-3): `name` (the definition `f`), `level_params` (the universe parameters of `f._sunfold`, which are `f`'s), `levels` and `nodes` (its value, as tables), `value` (the root, a node's place), `rec_arg` (`f`'s structural recursion argument, or `null`). Every `f._sunfold` of the modules has one, so a definition with no record has none |

A default instance the export lacks leaves a gap in its class's ranks
(none does in `Init`); the instance tree's ranks have none, since every
value of the tree has a record.

Format versions 1 ([schema](../../schemas/elab-data-1.schema.json): the
`instance` record without `keys` and `rank`, the `default_instance`
record without `rank`, and only the four kinds `instance`,
`default_instance`, `reducibility` and `eliminator`) and 2
([schema](../../schemas/elab-data-2.schema.json): no smart-unfolding
body and no `match_pattern` tag, its header saying `"sunfold":0`) are
refused as "another format version" (unsupported, error 7): a format-2
file read as format 3 would say that no definition has a smart-unfolding
body, and `Nat.add` would unfold by its `brecOn` value, unlike Lean.
Export the data again with `scripts/export-elab.sh`.

Format 3.1 (`"format_version":"3.1"`, a text: LeanForth's JSON formats
hold no fractions) is format 3 with one more node form, the
[inert node](#format-31-inert-metadata). The exporter writes 3.1 only
when a body holds one, so the data of `Init` and of every slice made so
far is format 3, byte for byte as before. The reader takes both: in a
format-3 file an inert node is malformed (error 10), as it is to the
readers of format 3 before 3.1, which refuse a 3.1 file as another format
version (error 7, unsupported) and read format 3 alike.

## Reading it: `leanforth check --elab-data`

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson --elab-data tests/front/init-slice.elab.ndjson tests/author/19-add-zero.lf | head -1
elaboration data: 3 instances, 2 default instances, 18 reducibility statuses, 0 eliminators, 54 instances left out, 3 classes, 10 tags, 4 matchers, 3 projections, 1 smart-unfolding bodies
```

`--elab-data DATA` goes with a LeanForth text and its library (`--env
EXPORT` or `--snapshot FILE`). After the library is read and before the
text runs, `src/front/elab-data.fs` reads DATA. It checks DATA against the
library's names and against the SHA-256 of its export: the manifest
check's, the snapshot's, or, with `--no-manifest`, the file's, hashed
then. When the export's manifest names the data's records SHA-256
(`elab_records_sha256`, which `scripts/export-elab.sh` adds after writing
the data: S1 note M6), DATA's header must have that `records_sha256`
(error 39), so an edited or other data file is refused even when its own
header was rewritten to match its records. With `--no-manifest` or a
snapshot the binding is the header's export SHA-256 alone. The verdicts are those of the same run without `--elab-data`:
nothing uses the data yet. A refusal stops the run before the text runs.
It prints the line and the reason, and exits with the outcome's status (4
invalid, 2 unsupported, 3 full). Here the test file
`tests/front/cut-off.elab.ndjson`, the eliminators fixture with its last
record cut off, is refused:

```console
$ bin/leanforth check --env tests/author/init-slice.ndjson --elab-data tests/front/cut-off.elab.ndjson tests/author/19-add-zero.lf
error: invalid: the elaboration data was refused at line 102 (error 20): records differ in number from the header; the LeanForth text was not checked
```

What the reader checks, each failure refused with its reason:

| Check | Reason printed | Outcome |
| --- | --- | --- |
| line 1 is a header of this format | `no header`, `not elaboration data` | invalid |
| its format version, Lean version and revision | `another format version`, `another Lean version` | unsupported |
| its members, each well typed | `malformed line` | invalid |
| its export SHA-256 is the library's | `elaboration data of another export` | invalid |
| every line is one JSON object of a known kind with exactly its members | `not one JSON value within the limits`, `unknown record kind`, `malformed line` | invalid |
| a smart-unfolding body: its definition a definition, once; its universe parameters the definition's, in order, and every `param` level one of them; every table entry naming only earlier ones, the root a node; a constant with as many universe arguments as its declaration has parameters; no loose bound variable at the root; an annotation one entry `sunfoldMatch`, `sunfoldMatchAlt` or `borrowed` with the value true; an inert node (format 3.1 only) of one of its three keys; a projection's structure an inductive type. A constant, or a projection's structure, that no declaration has makes the body foreign, and an inert node makes it inert: kept, and *unsupported* where it would be used | `a smart-unfolding body named twice`, `universe parameters other than the definition's`, `an index to no earlier entry`, `numbers that do not fit the declaration's type`, `a loose bound variable`, `an annotation this reader does not know`, `a declaration of the wrong kind` | invalid; unsupported for an annotation |
| every name is exactly one declaration of the library (a left-out instance's key constants and projected structures: or none, kept as foreign keys) | `unknown name`, `a name several declarations have` | invalid |
| of the right kind: a class an inductive type; an instance, eliminator, tagged declaration or projection function not one; a matcher a definition; a projection's constructor a constructor; a projection key's structure an inductive type | `a declaration of the wrong kind` | invalid |
| an instance's and a default instance's class has a class record before it | `a class without its class record before it` | invalid |
| every key one of Lean's forms (a literal's digits canonical), and an instance's or left-out instance's keys one term | `malformed line`, `keys that are not one term` | invalid |
| no declaration named twice as one kind (a default instance may be, of one class at two ranks, as Lean keeps it); no tag twice; one eliminator per kind and types | `an instance named twice`, `a default instance of two classes`, `a reducibility named twice`, `a class named twice`, `a tag named twice`, `a matcher named twice`, `a projection named twice`, `two eliminators for the same types` | invalid |
| no two values under one root key with one rank, no two default instances of one class with one rank | `two values of one root key with one rank`, `two default instances of one class with one rank` | invalid |
| a default instance's rank is at most 65,535 (`elab-default-rank-most`): FE1e3's `lf-default-instances` answers one cell per rank, so a larger rank (no Lean library has a class with that many default instances) would ask for gigabytes | `a default instance's rank beyond 65535` | invalid |
| a left-out instance whose reason is `not_exported` is no declaration of the library | `a left-out instance the library has` | invalid |
| a matcher's type has exactly a leading Pi binder for each parameter, the motive, each discriminant and each alternative (lets among them not counted), and its elimination universe is one of its universe parameters; a projection function's type has one for each parameter and the structure, and its constructor's type one for each parameter and field up to `idx` (written out, without unfolding); a class's out-parameters are among its type's Pi binders and its out-levels among its universe parameters | `numbers that do not fit the declaration's type` | invalid |
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
| 7 | `another format version` | unsupported | `format_version` is neither the number 3 nor the text `"3.1"` (formats 1 and 2 among them) |
| 8 | `another Lean version` | unsupported | written by another Lean version or revision |
| 9 | `elaboration data of another export` | invalid | `export_sha256` is not the library's |
| 10 | `malformed line` | invalid | a member missing, added or of the wrong type; a malformed name or key; discriminant names that are not one per discriminant; an inert node in a format-3 file |
| 11 | `unknown record kind` | invalid | a record of a kind this format does not have |
| 12 | `unknown name` | invalid | no declaration of the library has the name |
| 13 | `a name several declarations have` | invalid | the library has more than one declaration of the name |
| 14 | `a declaration of the wrong kind` | invalid | a class that is no inductive type, an instance or eliminator that is one, and the other kinds above |
| 15 | `an instance named twice` | invalid | two instance records of one declaration |
| 16 | `a default instance of two classes` | invalid | two default-instance records of one declaration with two classes (of one class at two ranks they are read, as Lean keeps them; at one rank, error 33) |
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
| 37 | `numbers that do not fit the declaration's type` | invalid | a matcher's, projection's or class's numbers that its type, its constructor's or its universe parameters cannot have; a smart-unfolding body's constant with other than its declaration's number of universe arguments (a constant the library lacks: any number) |
| 38 | `a record kind this reader does not read yet` | unsupported | not given since format 3, which reads every kind (format 2's readers gave it for a `sunfold` record) |
| 39 | `other records than the export's manifest names` | invalid | the library's manifest has `elab_records_sha256` (M6) and the header's `records_sha256` differs |
| 40 | `a default instance's rank beyond 65535` | invalid | a `default_instance` record's `rank` above 65,535 (`elab-default-rank-most`) |
| 41 | `a smart-unfolding body named twice` | invalid | two `sunfold` records of one definition |
| 42 | `an index to no earlier entry` | invalid | a level or node that names itself or a later entry of its table, a node's level beyond the table, or a root that is no node |
| 43 | `a loose bound variable` | invalid | the root of a smart-unfolding body has a loose bound variable |
| 44 | `universe parameters other than the definition's` | invalid | `level_params` that are not the definition's, in order, or a `param` level that is none of them |
| 45 | `an annotation this reader does not know` | unsupported | an `mdata` node other than one entry `sunfoldMatch`, `sunfoldMatchAlt` or `borrowed` with the value true (no other is in `Init`), or an inert node whose `key` is not `save_info`, `noImplicitLambda` or `congrHole` |

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
| `elab-count` | `( kind -- n )` | records of a kind: `elab-instance`, `elab-default`, `elab-reducibility`, `elab-eliminator`, `elab-left-out`, `elab-class`, `elab-tag`, `elab-matcher`, `elab-projection`, `elab-sunfold` |
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
| `elab-tagged?` | `( d tag -- flag )` | whether `d` has the tag: `elab-tag-as-elim`, `elab-tag-no-expected`, `elab-tag-aux-recursor`, `elab-tag-no-confusion`, `elab-tag-cases-on`, `elab-tag-rec-on`, `elab-tag-brec-on`, `elab-tag-match-pattern` |
| `elab-eliminator@` | `( i -- kind d )` | eliminator `i`, kind `elab-induction` or `elab-cases` |
| `elab-eliminator-types` | `( i -- addr n )` | its target types, `n` cells |
| `elab-eliminator-for` | `( d kind -- i true \| false )` | the eliminator of a kind whose one target type is `d` |
| `elab-matcher-of` | `( d -- m true \| false )` | the matcher record of a declaration |
| `elab-matcher@` | `( m -- d params discrs )` | matcher `m` |
| `elab-matcher-elim` | `( m -- pos true \| false )` | its elimination universe's place; false: into `Prop` only |
| `elab-matcher-alts`, `elab-alt@` | `( m -- a n )`, `( a -- fields overlaps thunk? )` | its alternatives |
| `elab-projection-of` | `( d -- p true \| false )` | the projection record of a declaration |
| `elab-projection@`, `elab-projection-decl`, `elab-projection-class?` | `( p -- ctor params idx )`, `( p -- d )`, `( p -- flag )` | projection `p` |
| `elab-sunfold-of` | `( d -- s true \| false )` | the smart-unfolding body of a definition |
| `elab-sunfold-decl`, `elab-sunfold-value`, `elab-sunfold-rec-arg`, `elab-sunfold-foreign?` | `( s -- d )`, `( s -- n )`, `( s -- k true \| false )`, `( s -- flag )` | body `s`: its definition, its root node, the recursion argument (false: null), whether a node names a constant the library lacks |
| `elab-sunfold-inert?`, `elab-sunfold-usable?` | `( s -- flag )` | body `s` holds an [inert node](#format-31-inert-metadata) (format 3.1); it is neither foreign nor inert, the only bodies `lf-libdec-sunfold` decodes (any other answers *unsupported*) |
| `elab-node-kind`, `elab-node-a` .. `elab-node-d`, `elab-node-levels` | `( n -- kind )`, `( n -- x )`, `( n -- addr k )` | node `n` (numbered across bodies): `elab-node-bvar`, `-sort`, `-app`, `-lam`, `-forall`, `-let`, `-have`, `-lit`, `-str`, `-proj`, `-mdata`, `-const`, and its fields as `src/front/elab-data.fs` tabulates them (a binder's name, a literal's digits and a string's bytes are keys, read with `elab-key-text`; a constant's or structure's declaration is -1 when the library has none; an inert node is an `-mdata` whose annotation is `elab-inert`); a constant's levels, `k` cells |
| `elab-level-kind`, `elab-level-a`, `elab-level-b` | `( l -- kind )`, `( l -- x )` | level `l`: `elab-level-zero`, `-succ`, `-max`, `-imax` (earlier levels in `a`, `b`), `-param` (its place among the definition's universe parameters in `a`) |
| `elab-key-tag` | `( k -- tag )` | `elab-key-star`, `-other`, `-lit`, `-str`, `-const`, `-arrow`, `-proj`, `-foreign` |
| `elab-key-decl`, `elab-key-idx` | `( k -- d )`, `( k -- i )` | a constant's or projection's declaration; a projection's field |
| `elab-key-arity` | `( k -- n )` | Lean's `Key.arity` (the table above; for a foreign key, its own, as Lean's key had it) |
| `elab-key-text` | `( k -- c-addr u )` | a literal's digits, a string literal's bytes, a foreign key's text: a constant's name, each part as 32-bit fields (0, the length and the bytes of a string, or 1 and the number); a projection's field 2, its index, then its structure's name |
| `elab-key=`, `elab-key-hash` | `( k1 k2 -- flag )`, `( k -- h )` | Lean's equality of keys, texts compared byte for byte; a 32-bit hash equal for equal keys |
| `elab-one-term?` | `( k n -- flag )` | keys `k` .. `k+n-1` make one term in Lean's path order |
| `elab-keys#` | `( -- n )` | the keys kept |
| `elab-decl-of`, `elab-decl-name` | `( name -- d true \| false )`, `( d -- name )` | a name's declaration in the stage the data was read against, and back |
| `elab-bind!` | `( c-addr u -- )` | the records SHA-256 (64 hexadecimal digits) the next `elab-read` must find in the header, or `0 0`: the export manifest's `elab_records_sha256` (error 39) |

`elab-keys.fs` also has the words `elab-data.fs` builds keys with
(`elab-key-new`, `elab-key-ref!`, `elab-key-arity!`, `elab-key-idx!`,
`elab-key-text-start`, `elab-key-text-end`, `elab-text-room`,
`elab-keys-clear`), and those `front/discr-keys.fs` makes a query's keys
with (`elab-keys-mark`, `elab-keys-drop`, the tag `elab-key-fvar`, which
no data key has); its header documents them.

**Using the instance records (FE1e2, FE1e3; branch `s1-synth`, tested
alone).** `src/front/discr-keys.fs` recomputes Lean's keys (`lf-dt-path`,
mkPath; `lf-dt-key`, getUnifyKeyArgs) and `src/front/instances.fs`
rebuilds Lean's instance tree from the ranks and answers getInstances
(`lf-inst-candidates`) and getDefaultInstances (`lf-default-instances`).
The first query checks every record's class and root key (the class's
constant, with the type's number of arguments) and every default
instance's class (`lf-inst-classes`); a root's first query checks its
instances' keys. A difference refuses the data (errors 112, 113, 115,
116) at that query and every later one, whatever its root, until the
data is read again (`elab-generation` changes) or `lf-inst-reset`; a record whose star
covers a term the type gives, as a `no_index` annotation the export
drops leaves it, makes that instance unverified (error 114). `make
reference-synth` recomputes every Init instance and compares getInstances
with pinned Lean's `#synth` traces.

## Smart-unfolding bodies (format 3)

Meta's whnf needs one more fact (plan S2). When the option
`smartUnfolding` is on (the default) and `f._sunfold` exists,
`unfoldDefinition?` unfolds `f` by `f._sunfold`'s value and runs
`smartUnfoldingReduce?` (Meta/WHNF.lean:720, 853, 918). That value is `f`
written with direct recursion instead of `brecOn`. Annotations mark where a
match must reduce (`sunfoldMatch`) and where an alternative was reached
(`sunfoldMatchAlt`). lean4export writes neither `_sunfold` definitions
(an internal name) nor annotations (mdata). Measured with pinned Lean
(`scripts/export_elab.lean` on `Init`, 2026-11-13):

- `Init` has 389 `_sunfold` definitions, every one a definition with a
  structural recursion argument; 387 are of definitions the export has.
- In the node tables (shared subterms written once) the annotations are
  389 `sunfoldMatch`, 983 `sunfoldMatchAlt` and 7 `borrowed` (the
  compiler's borrow mark), each one entry with the value true.
- 25 of the 387 name a constant the export lacks, each a `f._proof_N`
  lemma: such a body is kept and *unsupported* where it is used.
- `Nat.add._sunfold` is
  `fun x y => [sunfoldMatch] Nat.add.match_1 (fun _ _ => Nat) x y (fun a => [sunfoldMatchAlt] a) (fun a b => [sunfoldMatchAlt] Nat.succ (Nat.add a b))`.

The same fact in three forms: in mathematics, `0 + (k + 1) = (0 + k) + 1`
by the second equation of `+`; in Lean, `Nat.add` has the smart-unfolding
body above, so `Nat.add 0 (k + 1)` unfolds to `Nat.succ (Nat.add 0 k)`;
in the data, one `sunfold` record:

```json
{"sunfold":{"level_params":[],"levels":["zero",{"succ":0}],"name":["Nat","add"],"nodes":[{"const":["Nat"],"levels":[]},...],"rec_arg":1,"value":23}}
```

- **Record:** `{"sunfold":{"name":F,"level_params":[NAME...],"levels":[LEVEL...],"nodes":[NODE...],"value":I,"rec_arg":K}}`.
  - `F` is the definition `f` of the library.
  - `level_params` are `f._sunfold`'s universe parameters, which are
    `f`'s, in order.
  - `levels` and `nodes` are tables of the value's levels and subterms,
    each entry naming only earlier ones by their place, so that shared
    parts are written once; `value` is the root's place among the nodes.
    Two subterms share a node only when they are equal with their binder
    names and binder information (`Expr.equal`, not Lean's `==`, which
    ignores both and gave 18 of Init's 389 bodies another binder's name).
  - `rec_arg` is `f`'s structural recursion argument (Lean checks that it
    reduces to a constructor before the smart path's answer stands,
    WHNF.lean:898-905), or `null`. It is a place among an application's
    arguments, which Lean compares with their number where it uses it:
    it may lie beyond the binders `f`'s type shows, as
    `Nat.decidableExistsLT`'s does (its type ends in `DecidablePred`, a
    definition of a Pi type), so the reader checks no bound.
- **Levels:** `"zero"`, `{"succ":L}`, `{"max":[L,L]}`,
  `{"imax":[L,L]}`, `{"param":NAME}`, each `L` an earlier level's place.
  A table rather than JSON trees, so that a record nests at most 8 deep,
  the reader's limit.
- **Nodes:**
  - `{"bvar":i}`, `{"sort":L}`, `{"const":NAME,"levels":[L...]}`
  - `{"app":[f,a]}`
  - `{"lam":{"name":NAME,"info":"default|implicit|strict|inst","type":i,"body":j}}`
    and `{"forall":...}` alike (a binder's name may be anonymous, `[]`)
  - `{"let":{"name":NAME,"type":i,"value":j,"body":k,"non_dep":bool}}`
  - `{"lit":"DIGITS"}`, `{"str":S}`
  - `{"proj":{"struct":NAME,"idx":i,"expr":j}}`
  - `{"mdata":{"entries":[[KEY,{"bool":true}]],"expr":i}}`, `KEY` one of
    `["sunfoldMatch"]`, `["sunfoldMatchAlt"]`, `["borrowed"]`
  - format 3.1 only: `{"inert":{"expr":i,"key":KEY}}`, `KEY` one of
    `"save_info"`, `"noImplicitLambda"`, `"congrHole"`
    ([below](#format-31-inert-metadata))
  - no free variables or metavariables (the exporter stops).
  - Binder names keep their macro scopes as name parts (hygienic names
    such as `x._@.Init.Prelude.2314059840._hygCtx._hyg.13`).
- **Checked when read:** the forms; `F` is a definition of the library
  with one record; the universe parameters are `F`'s and every `param`
  is among them; every entry names only earlier ones; no bound variable
  is loose at the root; every constant
  and projected structure is one declaration of the library (a
  structure an inductive type) or none, which makes the body foreign; an
  annotation is one of the three.
- **Not checked at first use.** The design of 2026-11-12 had the kernel
  type-check each body at its first use; it is withdrawn (S2 design
  review M4, 2026-11-13): it would need a new kernel entry point on a
  scratch term ([kernel], [bypass] gates), and the trust argument below
  makes it unnecessary.
- **Taken on trust ([import] gate, S2 merge A):** that it is Lean's
  `_sunfold` body. The bodies are untrusted data, bound to the export by
  the manifest's `elab_records_sha256` (M6). A wrong body can only change
  an elaborated term, which the kernel checks against the declarations it
  reads itself; Lean's whnf uses it only to decide how far to unfold, and
  the guard is the node-for-node comparisons of S2's elaborated terms
  with pinned Lean's.
- **Kept:** each record's universe parameters, levels and nodes in the
  reader's tables (`elab-sunfold-of`, `elab-node-kind`, ...); a node's
  literal, string and binder name as keys of `src/front/elab-keys.fs`.
  Merge B decodes a body into the term store at its first use and
  `lf-menv-smart?` already answers from the records (merge A).
- **Size:** 387 records, 31,829 nodes and 1,088 levels for `Init`'s
  export; the longest line is 11 KB, the largest table 355 nodes.

## Format 3.1: inert metadata

Lean leaves metadata (`mdata`) in a few smart-unfolding bodies that
LeanForth's front end does not carry. On Mathlib (pinned Mathlib
`56a0058`, `scripts/export_elab.lean`, 2026-11-17;
[MATHLIB_FRONT.md](../design/MATHLIB_FRONT.md) O1) format 3 could not say
11 of its 1,844 bodies:

| Kind | Lean | Bodies | Example |
| --- | --- | ---: | --- |
| `save_info` | `mkSaveInfoAnnotation` (Elab/Term/TermElabM.lean:1495): a postponed metavariable's mark, so that the editor keeps its information | 8 | `Lean.stateStackModify` |
| `noImplicitLambda` | `mkNoImplicitLambdaAnnotation` (TermElabM.lean:1735-1741): "add no `fun` here" | 1 | `Batteries.BinomialHeap.Imp.Heap.WF.findMin` |
| `congrHole` | Mathlib's `TermCongr` hole: two private keys, `congrHoleForLhsKey` (a boolean) and `congrHoleIndex` (a number) | 1 | `GradedMonoid.GMonoid.gnpowRec` |
| (an anonymous binder) | `Name.anonymous` as a binder's name: not metadata, and already format 3 (`[]`); only the exporter refused it | 1 | `Mathlib.Tactic.Ring.ExProd.evalIntCast` |

The exporter writes each of the three kinds, and only these, as an inert
node: the entries' keys and values give way to the kind's name, and the
header says `"3.1"`. Any other metadata (`noindex`, `inaccessible`,
`patternWithRef`, `let_fun`, ...) still stops it. For example the node
`{"mdata":{"entries":[[["save_info"],{"bool":true}]],"expr":47}}` of
`Mathlib.Tactic.GuessName.applyNameDict`'s RAW record is written
`{"inert":{"expr":47,"key":"save_info"}}`.

The reader keeps an inert node as an `mdata` node of `elab-inert` around
its term and marks its body inert (`elab-sunfold-inert?`). An inert body
is never decoded: `lf-libdec-sunfold` answers *unsupported*, so the smart
path of its definition answers unsupported, as for a foreign body. Lean
steps through such metadata in `whnfEasyCases` (Meta/WHNF.lean:396) but
keeps it in `isDefEqQuick` (ExprDefEq.lean:1993-2023), in smart
unfolding's `go` (WHNF.lean:729-733) and in type inference
(InferType.lean:248), so carrying it faithfully touches many walkers; it
waits for a theorem that needs one of these definitions (none is on the
path of the Mathlib front end's targets). A body holding one is unusable,
never wrong. (The design planned the node as an annotation that every
walker answers unsupported on; refusing the whole body when it is
decoded gives the same answers, at most sooner, and changes no walker.)

**On all of Mathlib** (2026-11-18, branch `mf1`, by the implementer; the
done checker has not run it), with no step-around (the design's
measurement runs had left the 11 bodies out and deleted the second
`instHSMul` default instance from a copy):

```console
$ LEAN_PATH=… scripts/export-elab.sh mathlib.elab.ndjson mathlib.ndjson Mathlib
mathlib.elab.ndjson: 2450 class, 43808 instance, 470 instance_left_out, 52 default_instance, 85147 reducibility, 152 eliminator, 44264 tag, 25047 matcher, 15463 projection, 1785 sunfold; left out (not declarations of the export): … 59 sunfold; 86 sunfold bodies naming what the export lacks; 12 inert markers (format 3.1)
$ bin/leanforth check --snapshot mathlib-d789e45f.lfsnap --elab-data mathlib.elab.ndjson tests/author/01-identity.lf
elaboration data: 43808 instances, 52 default instances, 85147 reducibility statuses, 152 eliminators, 470 instances left out, 2450 classes, 44264 tags, 25047 matchers, 15463 projections, 1785 smart-unfolding bodies
…
729264 declarations: 729264 accepted; 729263 from the snapshot, 1 checked in this run
```

The exporter took 144 s and 9.1 GB (pinned Lean's part most of it), exit
0; it bound the data in a copy of the export's manifest
(`elab_records_sha256` `a4892a53…b18c`). The check exited 0 in 254 s and
9.61 GB (`gforth-fast`; the measurement's run 3, with the step-arounds:
294 s, 9.61 GB). Seven bodies hold the 12 inert nodes
(`GradedMonoid.GMonoid.gnpowRec`, `Batteries.BinomialHeap.Imp.Heap.WF.findMin`,
`Lean.stateStackModify`, `Mathlib.Tactic.GuessName.applyNameDict` and three
private ones) and one, `Mathlib.Tactic.Ring.ExProd.evalIntCast`, the
anonymous binder; the other three of the 11 are bodies of definitions the
export lacks, left out as before. The data has both `instHSMul` default
instances of `HSMul`.

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
    - error codes and texts; BASE kept;
    - format 3.1 (`tests/front/format31.elab.ndjson`, which
      `test_elab_data.py` writes): an inert node of each kind read back,
      its body inert and not usable, a lambda with an anonymous binder, a
      default instance of one class at ranks 0 and 1, both kept; a
      format-3 read after it.
  - `tests/front/whnf.fs`: an inert body is neither decoded nor unfolded
    by (*unsupported*), and unfolds again once the mark is cleared.
  - `tests/front/elab-check-lf.fs` tests the check step: `--no-manifest`
    hashes the library again, and refusing the hash's buffer gives error
    26, full.
  - `tests/front/test_elab_data.py` tests:
    - the finisher: kept and left out, the tree kept whole, deterministic,
      format 3 when no body holds inert metadata, 35 refusals (a
      smart-unfolding body of a theorem, naming a later node or level,
      with an unknown annotation, Lean's `noindex`, `save_info` false, a
      `TermCongr` hole with its keys swapped, without its index or with an
      index or flag of the wrong form, a root beyond its nodes or an
      unknown binder info among them), a body naming what the export
      lacks kept and counted; a RAW body with the three kinds of inert
      metadata and an anonymous binder written as format 3.1, exactly the
      format-3.1 fixture's body, and read by `leanforth check`;
    - the schema: 302 good lines and 39 wrong ones;
    - the [error catalogue](#errors) against the reader's;
    - the command line: the good data with an export, a snapshot and
      `--no-manifest`, 16 eliminators (the table grows), 12 accepted
      variants (an erased left-out instance the library has, a
      discriminant's name, a matcher into `Prop` only, a projection key of
      the slice's structure and of one it lacks, a string literal key, a
      default rank at the limit, a body naming a constant the slice lacks,
      a body with a node of every form, a body with no recursion
      argument and one beyond its type's binders, a body of a
      universe-polymorphic definition), the format-3.1 fixture and a 3.1
      file without an inert node, the verdicts
      unchanged, and 4 misuses (a layered snapshot among them);
    - 196 damaged files, each refused with its line, code, text and exit
      status and never "accepted": format 1's checks, format 2's (codes
      27-37, the key forms, ranks, matchers, projections, every record
      kind with a member added), format 3's (codes 41-45, 12 and 14,
      malformed nodes, levels, references and annotations of a body,
      max and imax levels, and a polymorphic body with no or other
      universe parameters), format 3.1's (an inert node in a format-3
      file, of another key, malformed or naming itself, `save_info` as an
      annotation, a default instance of two classes or twice at one rank,
      and six other versions: 3.1 as a number, "3", "3.2", "3.10", "3.1 "
      and 31), and a format-1 and a format-2 file.
  - Never run by `make test` (9 blocks, listed with their reasons in
    `tests/coverage-baseline.json`):
    - a name lookup that fails in an open tier (error 23), also after a
      left-out instance's name had a valid form;
    - a tier name beyond the stage's name-to-declaration array;
    - no room while the eliminators' table grows;
    - no room for a foreign key, a texted key or its text (the
      allocation-refusal test refuses each allocation in turn, but none
      falls on these claims);
    - a let among a matcher's parameters (13 of `Init`'s matchers, read
      by `make reference-elab-data`; no slice has one);
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
  - format 2's checks (25 faults): each of codes 27-38 skipped, a foreign
    constant allowed in an instance's keys, foreign constants refused in
    a left-out instance's keys, an arrow key's arity read as 0, equal
    texts compared by their offsets, a literal's digits not checked,
    ranks compared without their root keys, a class's out-levels stored
    as its out-parameters, the finisher's rank check skipped, and the
    review's: a matcher's arity checked as at most, the foreign mode left
    on after a left-out instance, a foreign projection without its mark,
    and a class's ranges unchecked.

## Limits and what is left

- No verdict uses the data yet: FE1e3 and later (instances, default
  instances), FE1g (eliminators) and S2 (matchers, projections,
  auxiliary recursors, smart unfolding) use it in the front end, which
  `leanforth check` does not run on the data yet (s1-elab).
- The class of each instance and default instance and each instance's
  keys are checked against their types at the first instance problem
  (FE1e3, not yet run by `leanforth check`, which uses no data yet); each
  class's out-parameters only by plan row FE1e3b; until then they rest
  on pinned Lean (above, "Trust").
- Smart-unfolding bodies are written and read (format 3); their decoding
  into terms, and the smart path that uses them, is S2's merge B.
- Only `--elab-data FILE`. The export's manifest names the data's records
  SHA-256 (M6) but not its file, so the data is not found from the
  manifest alone, and a snapshot does not keep the data or the binding;
  both are later steps.
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
