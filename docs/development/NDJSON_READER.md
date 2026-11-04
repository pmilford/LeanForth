# Forth reader for Lean NDJSON exports

LeanForth reads Lean's kernel exports in Forth. Lean's exporter
(`leanexport`, lean4export 3.1.0, pinned with Lean 4.35.0) writes a
declaration library as NDJSON: one JSON object per line, first a metadata
record, then names, universe levels, expressions and declarations, each
referring to earlier records by index. The reader decodes those records and
hands each one, checked for shape and references, to a word the caller
chooses. It is the first step of `leanforth check FILE.ndjson`
([the command line](../user/COMMAND_LINE.md), version 0, plan phase 3):
under the owner's product rule, end users need only a Forth system and
an NDJSON file, so nothing on the user's path is Python
([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md), "Product dependencies"
and OQ-4).

**Status: [import] gate approved by the owner on 2026-11-03** ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)); the checksum manifest it asked for is implemented and checked by default ([Manifests](#manifests), 2026-11-03, plan task 3.2.6, awaiting its [import] review); next: an upgrade test for new Lean and Mathlib versions. **Implemented 2026-11-02, untrusted, fail-closed.** The reader
decides nothing about types or proofs; a decoded record is input for the
checker, never a checked declaration. Since 2026-11-03 the importer stage
stages every record of an export into the compact store, all of Mathlib
included ([Staging into the compact store](#staging-into-the-compact-store),
plan items 3.2.1 and 3.3.1 in part); the checker does not read it yet, and
its term, level and name stores still hold 64 entries each:
`src/import/checker-input.fs` fills those for today's checker (plan task
3.2.2, version 0; `bin/leanforth check`), so only exports the size of the
test fixtures can be checked. The Python preview
([NDJSON_PREVIEW.md](NDJSON_PREVIEW.md)) stays as an independent second
reader for tests.

## Using it

Count the records of an export by kind, with the same report as the
measurement script `docs/development/measurements/scale-2026-11-02/count.py`:

```sh
.tools/gforth/bin/gforth-fast src/import/ndjson-count.fs \
  -e 's" .tools/mathlib/mathlib.ndjson" count-export bye'
```

`gforth-fast` is about three times faster than `gforth` and gives the same
results. `bin/leanforth count FILE` runs the same report from the shell,
with the command line's exit statuses ([the command line](../user/COMMAND_LINE.md)).
The file is checked against its manifest,
`mathlib.ndjson.manifest.json` beside it, by default ([Manifests](#manifests));
`s" OTHER.json" count-manifest` before `count-export` names another
manifest file, and `count-export-unchecked` reads without one, a choice
the caller makes explicitly. On failure the tool prints one line instead of the report and
Gforth exits at once with status 1; after the report, `bye` exits with
status 0. Forth-2012 has no `bye` with a status, so the tool uses Gforth's
`(bye)`, present in both CI hosts, Gforth 0.7.3 and 1.0 (another host
would end with an uncaught `THROW`). Inside a Forth session, or for many
files in one process as the tests do, `count-report` (and
`count-report-unchecked`) prints the same and never exits. For a copy of
`tests/reference/composition.ndjson` with an application referring to
itself, with a closing quote removed on line 2, and with the Lean version
changed (with the fixture's manifest beside each, or unchecked: the
reader's own failure comes first):

```text
error: invalid: bad reference (field fn, line 27)
error: invalid: unterminated string (line 2, byte 43)
error: unsupported: unsupported exporter, format or Lean version (line 1)
```

The manifest catches what the reader cannot: `constant-fixture.ndjson`
cut cleanly after its 21st line, a shorter but valid library that
`count-export-unchecked` counts without complaint; a copy of the
composition with one letter of a name changed; and a file without
`FILE.manifest.json`:

```text
error: invalid: export differs from its manifest (field lines, line 0)
error: invalid: export differs from its manifest (field sha256, line 0)
error: invalid: manifest missing, unreadable or too large (line 0)
```

From Forth, `manifest-read ( c-addr u m -- outcome )` of
`src/import/manifest.fs` reads with the manifest and `export-read` alone
without; the [Manifests](#manifests) section shows the words.

From Forth, give each record kind a handler `( record -- outcome )` and read
the file. A handler reads the decoded fields by name and returns an outcome;
anything but ok stops the reading with that outcome.

```forth
require src/import/ndjson.fs
export: library
variable applications
: on-app ( record -- outcome ) drop 1 applications +! outcome-ok ;
library export-init drop
' on-app kind-app library export-handler !
s" file.ndjson" library export-read   \ ( -- outcome )
```

A kind without a handler stops the reading as **unsupported**, so a
consumer never skips records silently; `ndjson-count.fs` and
`tests/core/ndjson-dump.fs` set a handler for every kind.

### Threat model

The reader defends against **hostile input**: whatever an export file, or
a line given to `export-line`, holds, the reader refuses it or hands over
exactly the records format 3.1.0 gives it, each checked whole before any
handler sees it ([what is checked](#what-is-checked-and-the-outcomes)).

**Handlers and the caller are trusted code**, relied on to keep the
handler contract below and to use only the words this document describes.
Even so, the reader fails closed on the breaches it can detect cheaply,
and this is the whole list; each is refused as it says, with *invalid*, an
exception or no result, never taken as *ok*:

- a handler leaves no outcome, or extra items (invalid);
- a handler's outcome is a number outside the outcome vocabulary (invalid);
- a handler takes more than its record and leaves fewer items than it was
  given, or changes either of the two cells under its record (`THROW` -4);
- a handler calls `export-read` or `export-line` on its own export (that
  call reads nothing and gives invalid);
- a handler calls `export-init`, `export-free` or `export-restart` on its
  own export (`ABORT"`, -2);
- a handler changes the line's JSON view so that one of a block's three
  lists is lost (invalid);
- `list-count`, `list-item` or `recursor-rule` is given a copy of a
  record of an earlier line, that is, a record copied by its handler and
  kept once the export has counted a later line, even one that failed,
  and also after `export-restart` or `export-init` (no list and no rule:
  0, -1 and 0);
- `list-count`, `list-item` or `recursor-rule` is given a field that holds
  no list, an index outside the list, a list of objects (`list-item`) or a
  record that is not a recursor (`recursor-rule`) (0, -1 and 0);
- `export-handler` is given a number that is not a record kind (`ABORT"`,
  -2).

A `THROW` from a handler, -4 and -2 included, passes on to the caller of
`export-line` or `export-read` with the export idle; `export-read` closes
the file first.

**Not detected**, and outside what the reader defends against:

- a handler that changes data-stack cells below the two canaries and puts
  the canaries back. Those cells hold only the data of whoever called
  `export-line` or `export-read`: while a handler runs, nothing of the
  reader's lies on the data stack, so such a handler changes its caller's
  data, never what the reader does;
- a handler that changes or unbalances the return stack, where the reader
  keeps what it needs after the handler;
- a handler that writes its record; this misleads only the handler, since
  the reader never reads a record back after its handler;
- a handler that writes the export (its counters, flags, handler table,
  decoded records, or position in a block's list) or the line's JSON view
  or bytes, other than so that a block's list is lost. Such a write can
  make later records be checked against wrong counts, let the handler read
  its export again, or make a block's elements be skipped, repeated or
  decoded from changed tokens (each still checked);
- a handler or caller that keeps a record's address instead of a copy.
  The reader reuses its records: one for each record of a line, one for
  each element of a block and one for the rule `recursor-rule` gives. A
  kept address therefore reads as a later record, of the current line and
  with that record's lists, and a kept rule as the rule of the next call;
- a handler or caller that gives `list-count` or `list-item` a list field
  of one record with another record. The list is read in the line of the
  record it is given with, so a field of an earlier record given with a
  record of the current line reads whatever the current line holds at
  that token index;
- a handler or caller that keeps a record's texts, digits or `mdata-data`
  past its handler: they point into the line and its JSON view, which the
  next line overwrites. `mdata-data` is the token index of a JSON object
  in that view, and no reader word takes it or checks its line;
- a caller that uses an export before `export-init` gave ok or after
  `export-free`, uses one export from two tasks at once, or stores
  anything but the execution token of a handler with `export-handler`;
- a caller that gives `list-count`, `list-item` or `recursor-rule`
  anything but a record the reader handed over or a copy of one, or gives
  `export-line` an address and length that are not one readable line
  without its line feed (JSON reads a line feed inside as white space;
  `export-read` never gives one);
- a handler or caller that uses words of `ndjson.fs` this document does
  not describe, such as `export-next` or `export-lines`;
- a tap (`export-tap!`, [below](#manifests)) that changes the bytes it is
  shown or uses the export: a tap is trusted caller code, like a handler,
  and a `THROW` from it passes on as from a handler.

A review judges the reader against this model: input that gets malformed
data accepted, decoded wrongly or handed over stale is a soundness bug;
misuse by a handler or the caller is a bug only where the first list says
the reader detects it.

### The handler contract

A handler must keep this contract:

- It takes its record and leaves exactly one outcome, nothing else. The
  reader checks the stack depth: a handler that leaves no outcome or extra
  items stops the reading as invalid ("handler left no outcome or extra
  items"). While a handler runs, the two cells under its record hold the
  export as canaries. A handler that takes more than its record throws -4
  (stack underflow), since its caller's data is gone, when it leaves fewer
  items than it was given or changes either canary. Deeper cells are not
  checked: Forth cannot isolate a handler's stack. They hold only the data
  of whoever called `export-line` or `export-read`, nothing of the
  reader's: the export being read, the counter it adds the record to, the
  tally of the record's kind (`export-kind-count`), a declaration's kind
  and the table of a block's list wait on the return stack, and the
  position in a block's list in the export.
- It does not call `export-read` or `export-line` on the same export; the
  reader refuses that as invalid ("export read again by its own handler").
  Nor does it call `export-init`, `export-free` or `export-restart` on it:
  they throw (`ABORT"`, -2, "ndjson: export in use by its handler"), since
  they would free or reset buffers and counts in use.
- It writes neither its record nor the export. Neither is checked, but a
  write to the record misleads only the handler itself: the reader never
  reads a record back after its handler. Whether a declaration is an
  inductive block is read before its handler; the block's three lists are
  found again in the line's checked JSON view, and every element is
  decoded and checked again from the line; the export, not the record,
  numbers the elements. A handler that writes the JSON view so that a list
  is lost stops the reading as invalid ("handler changed the export");
  other writes to the export are not detected.
- It keeps only a copy of a record, never its address: the reader decodes
  the next record into the same memory, and `recursor-rule` the next rule.
  A kept address is not detected; it reads as the later record.
- It copies any text, digits or list it wants to keep: they point into the
  current line and its JSON tape, valid only until the handler returns.
  The lists and rules of a copy kept past its line read as none
  (`list-count` gives 0, `list-item` -1, `recursor-rule` 0); texts,
  digits and `mdata-data` are not checked.
- It gives `list-count` and `list-item` a list field together with its
  own record, the record the field was read from. This is not checked.
- A `THROW` from a handler, including the two above, passes on to the
  caller of `export-line` or `export-read` with the export idle again;
  `export-read` closes the file first.
- `export-handler ( kind export -- addr )` takes only a record kind
  (`kind-meta` to `kind-recursor`); another number aborts ("ndjson: no
  such record kind").
- Nothing depends on `BASE`: numbers are read in decimal by hand, so a
  handler may change `BASE` freely; and `lib/bytes.fs`, `lib/json.fs` and
  `import/ndjson.fs` load in decimal whatever `BASE` is, then restore it
  at the end of a successful load. A `THROW` while one of them loads
  leaves `BASE` decimal: Forth-2012 gives a file no way to restore it
  then.

## Layers

| File | Knows | Does |
| --- | --- | --- |
| `src/lib/bytes.fs` | bytes, lines, UTF-8 | `reader:` records: whole lines of a file in one heap buffer that grows for long lines up to a limit; every line must end with a line feed; line numbers and file offsets. `text-framed` refuses carriage returns and a byte-order mark. UTF-8 length, validity and encoding. |
| `src/lib/json.fs` | JSON (RFC 8259) | `json:` views: one JSON text parsed, without recursion, into a tape of tokens; escapes decoded in place; numbers kept as digit text; limits on nesting, tokens, string and number length. |
| `src/import/ndjson.fs` | lean4export 3.1.0 | `export:` records: the reader, the JSON view, the decoded records, the handler table and the counters. Tables describe every record shape; each record is checked whole before its handler sees it. |
| `src/import/ndjson.fs` (continued) | | The tap (`export-tap!`): a word shown every line `export-read` reads, before decoding. The tally (`export-kind-count`): records handed over and accepted, by kind. |
| `src/lib/sha256.fs` | FIPS 180-4 | SHA-256, incremental; a standalone library ([FORTH_LIBRARY.md](FORTH_LIBRARY.md#sha-256)). |
| `src/import/manifest.fs` | manifest format 1 | `manifest:` records: the export's manifest checked whole, the export hashed through the tap during its one read, then compared ([Manifests](#manifests)). |
| `src/import/ndjson-count.fs` | count.py's report | The counting tool above, with the manifest checked by default. |
| `src/import/ndjson-emit.fs` | lean4export 3.1.0's bytes | The re-exporter: every record handed over, written back as the exporter writes it ([Re-export](#re-export)). |

Each layer keeps its state in records passed on the stack, so separate
readers are independent ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md));
one reader is single-threaded. `lib/bytes.fs` and `lib/json.fs` are among
the few text modules allowed byte access, which `scripts/check-portable-forth.py`
lists with their reasons.

## Record kinds and their fields

Each record is handed over in a decoded record. Every decoded record starts
with `record-kind`, `record-index` (its own index; declarations and the
elements of an inductive block count from 0), `record-line`,
`record-export` and `record-generation`. The line is the line of the file
for `export-read`; for `export-line`, which may be given lines from
memory, it is the number of lines given to the export since
`export-restart` or `export-init`. The generation is the export's count
of lines since `export:` made it, which nothing resets; the list and rule
readers compare it with the export's to tell whether the export's JSON
view still holds the record's line.
References are indices of earlier records. Lists are read
with `list-count ( list record -- n )` and `list-item ( i list record -- u )`;
a list field holds its JSON array's token index inverted (below -1), so a
reference, which is at least 0, or an unset field, -1, never reads as a
list, not even a reference that happens to equal an array's token index.
Texts are an address and a length (`2@`), valid only inside the handler.

Before each decode every field after the header is set to -1, so nothing
survives from an earlier record. A record's own fields are always all
written. The layouts of different kinds overlap, so a field the kind does
not have reads -1 (as a flag: true) or one of the record's own fields: a
handler reads only the fields of its record's kind. The readers check
their arguments: `list-count` gives 0 for a field that holds no list;
`list-item` is for lists of references and gives -1 for an index outside
the list or for a list of objects (a block's lists, a recursor's rules);
`recursor-rule` gives 0 for a record that is not a recursor or an index
outside its rules. All three give no list and no rule (0, -1 and 0) for a
record of an earlier line, kept past its handler: once the export has
counted a later line, even one that failed, whatever that line holds at
the same token index, and also after `export-restart`, when line numbers
start again. A rule record has a header of its own: kind `kind-rule` (a
kind no handler takes), the rule's index, and the line, export and
generation of its recursor; reading it leaves `export-error` as it was.

| Kind | JSON | Fields |
| --- | --- | --- |
| `kind-meta` | `{"meta":{...}}` | `meta-exporter`, `meta-exporter-version`, `meta-lean-githash`, `meta-lean-version`, `meta-format-version` (texts) |
| `kind-name-str`, `kind-name-num` | `{"in":n,"str":{"pre","str"}}`, `{"in":n,"num":{"pre","i"}}` | `name-prefix`; `name-part` (the string, or the number's decimal digits, of any size) |
| `kind-succ`, `kind-max`, `kind-imax`, `kind-param` | `{"il":n,...}` | `succ-of`; `max-left`, `max-right`; `param-name` |
| `kind-bvar`, `kind-sort` | `{"ie":n,"bvar":k}`, `{"ie":n,"sort":l}` | `bvar-index`; `sort-level` |
| `kind-const` | `{"ie":n,"const":{"name","us"}}` | `const-name`, `const-levels` (list) |
| `kind-app` | `{"ie":n,"app":{"fn","arg"}}` | `app-fn`, `app-arg` |
| `kind-lam`, `kind-forall` | `lam`, `forallE` | `binder-name`, `binder-type`, `binder-body`, `binder-info` (0 default, 1 implicit, 2 strictImplicit, 3 instImplicit) |
| `kind-let` | `letE` | `let-name`, `let-type`, `let-value`, `let-body`, `let-nondep` (flag) |
| `kind-proj` | `proj` | `proj-type-name`, `proj-idx`, `proj-struct` |
| `kind-natval`, `kind-strval` | `natVal`, `strVal` | `literal-text` (decimal digits of any size; UTF-8 text) |
| `kind-mdata` | `mdata` | `mdata-expr`, `mdata-data` (index of the JSON object) |
| `kind-axiom`, `kind-def`, `kind-thm`, `kind-opaque`, `kind-quot` | `{"axiom":{...}}` etc. | `decl-name`, `decl-params` (list), `decl-type`, `decl-value`, `decl-all` (list), `decl-unsafe`, `decl-hints` (0 opaque, 1 abbrev, 2 regular), `decl-height`, `decl-safety` (0 safe, 1 unsafe, 2 partial), `decl-quot-kind` (0 type, 1 ctor, 2 lift, 3 ind), as the kind has them |
| `kind-inductive` | `{"inductive":{"types","ctors","recs"}}` | `block-types`, `block-ctors`, `block-recursors` (lists of objects); then each element as its own record: |
| `kind-type` | an element of `types` | the declaration fields, `type-num-params`, `type-num-indices`, `type-all`, `type-ctors`, `type-num-nested`, `type-rec`, `type-unsafe`, `type-reflexive` |
| `kind-ctor` | an element of `ctors` | the declaration fields, `ctor-induct`, `ctor-cidx`, `ctor-num-params`, `ctor-num-fields`, `ctor-unsafe` |
| `kind-recursor` | an element of `recs` | the declaration fields, `recursor-all`, `recursor-num-params`, `recursor-num-indices`, `recursor-num-motives`, `recursor-num-minors`, `recursor-k`, `recursor-unsafe`, `recursor-rules`; `recursor-rule ( i record -- rule )` gives `rule-ctor`, `rule-fields`, `rule-rhs` |

## What is checked, and the outcomes

Every line ends in exactly one outcome, and reading stops at the first that
is not ok. No failure is ever reported as ok, and no record reaches a
handler before it has been checked whole, so an inductive block's types,
constructors and recursors are handed over only after the whole block
passed.

| Outcome | When |
| --- | --- |
| ok | A complete, well-formed record, accepted by its handler |
| invalid (malformed) | Bad framing (no final line feed, carriage return, byte-order mark, blank line); not JSON (syntax, bad escape, lone surrogate, invalid UTF-8, a control byte in a string); not a record of format 3.1.0: unknown kind, a field missing, unknown or repeated, a value of the wrong JSON type or outside its enumeration, an index that is not the next one, a reference that is not to an earlier record, an anonymous name where one is not allowed, a natural literal not in canonical decimal, a height beyond UInt32, metadata not first or repeated, an inductive block without types, no metadata or no declaration in the file |
| unsupported | Metadata naming another exporter, format or Lean version than lean4export 3.1.0, format 3.1.0 and Lean 4.35.0 (`eb6cafb7…`); a record kind without a handler |
| full (a limit) | A line longer than the limit (64 MiB), JSON nested deeper than 64, more than 65,536 JSON tokens on one line, a natural number field (such as `bvar` or `idx`) that does not fit in a cell, no heap memory |

A handler's own outcome (rejected, for example) also stops the reading, as
does a broken handler contract (invalid or a `THROW`, see above).

`export-error ( export -- line key-addr key-u why-addr why-u )` gives the
line, numbered as `record-line` is, the field being decoded and the
reason, both cleared at the start of every line; for a JSON error,
`json-offset` of the export's JSON view gives the byte within the line.
When a handler stops the reading, the field is empty and the reason is "no
handler for this record kind" or "handler refused the record"; a file that
cannot be opened gives "cannot open the file" at line 0.

**Left to the consumer** (the checker or the staging step): distinct names
in `levelParams`, `all` and `ctors`; a declaration's presence in its own
`all` list; universe parameter scope; unique declaration names; anything
about types.

### Differences from the Python preview

The preview ([NDJSON_PREVIEW.md](NDJSON_PREVIEW.md)) is a bounded prototype
with semantic checks of a few declaration kinds. The reader differs on
purpose:

- No prototype bounds: the preview stops at 4,096-byte lines, a 1 MiB
  stream, 256 names and 64 expressions; the reader's limits are above.
- Every kind of format 3.1.0 is decoded, including `letE`, `proj`,
  literals, `mdata`, axioms, opaques, quotients and inductive blocks, which
  the preview reports as unsupported; whether a kind is supported is the
  consumer's choice of handlers.
- Nested values of inductive blocks are reference-checked (the preview does
  not); the preview's declaration-level checks (listed above) are not done.
- JSON nested past the limit is a limit here and malformed in the preview.
  Both read `-0` as 0 and refuse lone surrogate escapes.

## Manifests

Lean's export carries no checksum or signature: its first line names only
the exporter, format and Lean versions, which the reader requires to be
the pinned ones. A file cut off cleanly between two lines would therefore
read as a shorter, valid library. Under the owner's decision of
2026-11-03 ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03),
plan task 3.2.6), LeanForth's export step writes a manifest beside each
export, and the reader checks it by default, in Forth, computing SHA-256
during its single read. A missing or wrong manifest is *invalid* unless
the caller explicitly skips the check. **Implemented 2026-11-03,
untrusted, fail-closed; awaiting its [import] review.**

**Writing a manifest** (on the developer's machine, at export time):

```sh
scripts/export.sh OUT.ndjson MODULE... [-- DECLARATION...]
```

runs the pinned toolchain's `leanexport` (`LEAN` names the pinned `lean`
binary; never an elan proxy; `LEAN_PATH` finds the modules), writes the
export through `OUT.ndjson.partial` so that a failed export never looks
complete, then runs `python3 scripts/export_manifest.py OUT.ndjson`
(with `--mathlib-commit SHA` when `MATHLIB_COMMIT` is set), which writes
`OUT.ndjson.manifest.json`. The writer reads the export once with
Python's `hashlib` and `json`, an implementation independent of the Forth
reader, and refuses a file without a final line feed, a line that is not
a JSON object, an unknown record kind, or metadata that is not the first
line. Its output is deterministic: sorted keys, two-space indentation, a
final line feed.

**Format version 1** (`schemas/export-manifest-1.schema.json`), one JSON
object with exactly these members:

| Member | Holds |
| --- | --- |
| `format`, `format_version` | `"leanforth-export-manifest"` and `1` |
| `sha256` | SHA-256 of the whole file, 64 lowercase hexadecimal digits, as `sha256sum` prints it |
| `bytes`, `lines` | the file's size and its lines, each ended by a line feed |
| `records` | an object with one member per record kind, all present: `meta`, `name.str`, `name.num`, `level.succ`, `level.max`, `level.imax`, `level.param`, `expr.bvar`, `expr.sort`, `expr.const`, `expr.app`, `expr.lam`, `expr.forallE`, `expr.letE`, `expr.proj`, `expr.natVal`, `expr.strVal`, `expr.mdata`, `decl.axiom`, `decl.def`, `decl.thm`, `decl.opaque`, `decl.quot`, `decl.inductive`, and the elements of inductive blocks, `inductive.type`, `inductive.ctor`, `inductive.recursor` |
| `exporter`, `exporter_version`, `export_format`, `lean_version`, `lean_githash` | as the export's metadata line states them |
| `mathlib_commit` | the Mathlib commit exported (40 lowercase hexadecimal digits), or `null` |

Numbers are canonical decimal: no sign, no leading zero, no fraction or
exponent. Each reference export has its manifest committed beside it
(`tests/reference/*.ndjson.manifest.json`).

**Checking.** `src/import/manifest.fs`, from Forth:

```forth
require src/import/manifest.fs
export: library
manifest: checks
library export-init drop  library checks manifest-init drop
' on-app kind-app library export-handler !      \ and a handler for every kind
s" file.ndjson" checks manifest-read             \ ( -- outcome ): file.ndjson.manifest.json
checks manifest-free  library export-free
```

`manifest-use ( c-addr u m -- )` names another manifest file for the next
`manifest-read` only. `manifest-read` checks the manifest whole before it
reads the export (so a malformed manifest fails at once, not after a
two-minute read): one JSON object of at most 64 KiB, exactly the members
above, each of its type, format version 1, and the five version members
equal to the pinned ones. It then reads the export with `export-read`, so
with the export's handlers, while the export's tap gives every line and
its line feed to SHA-256 (`src/lib/sha256.fs`), once, as it is read and
before decoding changes it. After an ok read it compares the lines, the
bytes, the records handed over by kind (`export-kind-count`) and the
SHA-256 with the manifest's, and reports the first difference. The tap is
removed and the manifest's text freed on every path, including a `THROW`
from a handler, which passes on with the file closed.

| Case | Outcome | Reason (field), line 0 |
| --- | --- | --- |
| No manifest file, unreadable, or larger than 64 KiB | invalid | manifest missing, unreadable or too large |
| Not JSON | invalid | manifest is not valid JSON |
| Not an object; a member missing, unknown or repeated; a value of the wrong type; a number not canonical; a digest not lowercase hexadecimal of its length | invalid | manifest malformed (the member, or none) |
| `format_version` other than `1` | invalid | unsupported manifest format version (`format_version`) |
| A version member other than the pinned one | invalid | manifest names another exporter or Lean version (the member) |
| A failure of the reader itself | the reader's | the reader's reason, field and line |
| Lines, bytes, a kind's records or SHA-256 differ | invalid | export differs from its manifest (`lines`, `bytes`, the kind, or `sha256`) |
| The export's name with `.manifest.json` longer than 4,096 characters | invalid | manifest file name too long |

**Skipping the check** is the caller's explicit choice: `export-read`
alone, or `count-export-unchecked` and `count-report-unchecked` in the
counting tool.

**What it protects against.** A truncated, corrupted or mixed-up export:
a file cut at any line, a changed byte, a manifest of another file. It
is not a signature: whoever can rewrite the export can rewrite its
manifest, so it does not protect against forgery. Records reach the
handlers before the totals can be compared, so a consumer keeps what it
built only when the outcome is ok, as after any failure part-way through
a file.

**Measured** (2026-11-03, this machine, `gforth-fast` 1.0, one thread,
the file in the page cache; `count-export` against `count-export-unchecked`,
alternating; `.claude/work/CK/measure.sh` in the agent's notes):

| Export | Size | Read, unchecked | Read with manifest (SHA-256 during the read) | Manifest written by `export_manifest.py` |
| --- | --- | --- | --- | --- |
| `Init` (`scripts/export.sh … Init`: 29 s; SHA-256 `c1b2071a…a59a179`, as before) | 345,690,182 B, 6,452,982 lines | 6.1–6.4 s | 11.6–12.1 s | 14 s |
| all of Mathlib (`18448e5d…59c6`, equal to `sha256sum`'s) | 6,258,342,501 B, 110,895,826 lines | 1 min 58.6 s (117.2 s user) | 3 min 35.8 s (214.8 s user) | 4 min 14 s |

The hash costs about 5.6 s on `Init` and 97 s on Mathlib, 62–65 MB/s of
the file, a little under the library's 69–73 MB/s in memory because each
line is a separate update (one more for its line feed); the reports were
byte-identical with and without it, and the checked Mathlib read passing
shows the Forth SHA-256 equal to `sha256sum`'s, `18448e5d…59c6`. Memory
stays that of the reader (13,960 against 13,956 KiB resident on `Init`;
17,032 against 17,124 on Mathlib). Other agents' jobs ran on the machine
during the Mathlib runs, one run each. Counted in user-mode instructions
(`perf stat`, `Init`, two runs each, the same to 0.01%): main's reader
took 109.68 billion, this one unchecked 110.49 billion (+0.74%: the tap's
test and the tally of each record's kind), and checked 205.29 billion.

**Tests** (`make test-manifest`; the export step with pinned Lean in
`make check`):

- `tests/core/manifest.fs`: a checked read of a fixture, the tap removed
  and the text freed after every read and after a handler's `THROW` (file
  closed), a handler that calls `manifest-read` on its own export
  (invalid, as `export-read` gives, the outer read's tap and text left
  alone), `manifest-use` for one read only, a missing manifest, a file
  name too long, the error fields at line 0, and the heap blocks given
  back by `manifest-free`.
- `tests/core/test_export_manifest.py`: the writer gives exactly the five
  committed manifests, each valid under the schema, and refuses six kinds
  of bad input writing nothing; the five reference exports with their
  manifests give count.py's report; 48 failure cases each give invalid
  with the expected reason and field at line 0: `constant-fixture.ndjson`
  truncated at a line boundary (which the unchecked reader accepts), one
  changed byte, a missing manifest, format version 2, other Lean,
  exporter and format versions, another file's manifest, each number and
  digest changed, and a corpus of malformed manifests (not JSON, empty,
  an array, a repeated member, an extra member, a missing kind, `-0`,
  `1787.0`, `1787e0`, capitals in a digest, larger than 64 KiB; exactly
  64 KiB is read), each also refused by the schema where JSON Schema can
  say so; a manifest named with `count-manifest`; the reader's own
  failure reported as before.
- `tests/core/ndjson.fs`: the tap sees every line of two files once, with
  its cell, and nothing given to `export-line`; a `THROW` from the tap
  closes the file; `export-init` removes the tap; the tally counts every
  kind, a block's elements included, starts again with each reading,
  leaves out a refused record and takes only record kinds.
- `tests/reference/manifest-check.sh` (`make reference-manifest`, in
  `make check`): `scripts/export.sh` with pinned Lean reproduces the
  composition fixture and its manifest byte for byte; the check accepts
  it and refuses a copy with one letter changed, which the unchecked
  reader accepts.
- 15 planted faults, kept in `tests/mutants/faults.toml` (`make mutants`;
  ids `manifest-…`, `ndjson-tap-skipped`, `ndjson-tally-refused`), each
  caught: line feeds not
  hashed, the SHA-256 or the bytes not compared, extra members allowed,
  any format version, a digest's length unchecked, the 64 KiB limit one
  byte short, non-canonical numbers, the tap left set after a read, the
  failure's line not reset, a handler's `manifest-read` on its own export
  not refused, an entry missing from the table of type checks or of
  version checks, the tap never called, refused records counted; the tree
  without a fault passes.

## Staging into the compact store

The importer stage (`src/import/stage.fs`, with the records and handlers
in `stage-records.fs`; ADR 0016 C9 step 2, plan items 3.2.1 and 3.3.1 in
part; 2026-11-03) reads an export through this reader, checked against
its manifest by default, into a compact input tier
([ADR 0016](../adr/0016-compact-store.md),
[FORTH_LIBRARY.md](FORTH_LIBRARY.md#the-compact-store)), ready for every
worker to read without locks. **Untrusted [import] code, fail-closed.**
The feed (`src/import/feed.fs`, plan task 3.2.2, ADR 0016 C9 step 3;
below) gives a sealed stage to the checker. Loaded by `src/main.fs`; it
declares no context member and allocates nothing while loading.

```forth
require src/import/stage.fs
create lib /stage allot
16 lib stage-init drop                         \ expression table: 2^16 slots
s" tests/reference/constant-fixture.ndjson" lib stage-load .   \ 0: ok
lib stage-decls .                              \ 3
lib stage-free
```

**What a stage holds** after `stage-load`:

- every name, level, expression and literal, hash-consed in the input
  tier (C1–C4), and the export-index maps that give each export index's
  store number (`export>name`, `export>level`, `export>expr`; loading aids,
  4 bytes per record, freed by `stage-unmap`);
- every declaration as a 32-byte record (C2), numbered in file order (an
  inductive block, then its types, constructors and recursors): the kind,
  flags (unsafe, a definition's safety and hints, a quotient's kind, a
  recursor's `k`, a type's `isRec` and `isReflexive`, and a mark), the
  name, the universe parameters (a tuple of names), the type, the value of
  a definition, theorem or opaque, a regular definition's height, a tuple
  of the kind's other data (`all`; a block's numbers of types,
  constructors and recursors; a type's `numParams`, `numIndices`, `all`,
  `ctors`, `numNested`; a constructor's `induct`, `cidx`, `numParams`,
  `numFields`; a recursor's `all`, `numParams`, `numIndices`,
  `numMotives`, `numMinors` and its rules, `[ctor nfields rhs]` each),
  and the declaration staged before it with the same name; read with
  `staged-kind@`, `staged-name@`, … `staged-item` (the header of
  `stage-records.fs` lists them all);
- the name-to-declaration array (C4): `stage-find ( name stage -- d true |
  false )` gives the newest declaration of a name, `stage-previous` the
  one before it, so ADR 0012 E5 sees every declaration of a name;
- constants resolved when sealed (C4): `stage-resolved ( e stage -- d true
  | false )` gives a constant's declaration when exactly one declaration
  has its name; with several, false, and the array and chain decide.

**Life cycle.** `stage-init ( log2 stage -- outcome )` makes an empty
stage whose expression table starts at 2^log2 slots (about 59 bytes of
export per expression: 2^24 for `Init`, 2^28 for Mathlib), the others at
2^12. `stage-read ( c-addr u stage -- outcome )` reads the file with its
manifest, `FILE.manifest.json` or the file `stage-manifest-use` names;
`stage-read-unchecked` reads it without one, the caller's explicit
choice. `stage-seal` resolves the constants, sets the marks and makes the
tier read-only (its tables spread to at most half full, its stores
trimmed); `stage-load` and `stage-load-unchecked` read, then seal.
`stage-free` frees everything. Each step out of order is *invalid*. A
read that fails, for any reason or by a `THROW` (which then passes on),
rolls the stage back to empty, so nothing of a partial, malformed or
mismatched file stays, and the stage can read again; a stage whose
rollback or sealing failed is broken, and only `stage-free` applies.

| Case | Outcome | Reason (`stage-error`) |
| --- | --- | --- |
| Any failure of the reader or of the manifest check | the reader's or the manifest's | theirs, as above |
| An export index no map holds (a bad reference), a name, level, list or expression that is not a record of the tier, a declaration field missing or present against its kind | invalid | handler refused the record, at its line |
| A constant whose name no declaration has | invalid, at sealing | unknown constant, line 0; `stage-culprit@` gives the name |
| A number beyond 32 bits where a field holds it (a numeric name component, a projection's index, a count of an inductive type, constructor or recursor, a rule's field count) | full | number beyond 32 bits |
| The stage's heap blocks past `stage-limit!` | full | memory limit of the stage reached |
| The limits of C1 (2^27 names, a bound variable's range 2^20 − 1, 2^32 − 1 records per family), more than 2^27 − 1 declarations, no heap | full | handler refused the record |
| An `mdata` expression | ok: staged but marked | — |

**Staged but marked.** The compact store has no record for an `mdata`
expression's key-value data, which Lean's exporter writes only when asked
(`--export-mdata`). Instead of refusing the whole export, the stage keeps
the expression it wraps under its own tag (`tag-mdata`), counts it
(`stage-mdata`), and at sealing marks every declaration whose type, value
or recursor rule holds one (`staged-marked?`, `stage-marks`), found in
one walk over the expressions in number order with a bitset of one bit
per expression (13 MB for an export of Mathlib's size), made only when an
`mdata` record was staged. The stored term is then not
the term exported, so no check may accept a marked declaration; the
checker can refuse it as unsupported without walking it.

**Memory limit** (plan 3.3.1 in part). `stage-limit! ( bytes stage -- )`
bounds the heap blocks the stage holds (`stage-allocated`: the tier, the
maps, the declarations and the array; not the reader's line buffer); the
read stops as *full* at the first record after which they exceed it.
Blocks grow by doubling, so the peak may pass the limit by the last
block's growth. Sealing counts the marks' bitset against the limit
(*full*, the stage broken), but not the tier's rebuild of each table at
most half full, which for a moment holds a table's old and new slots
(Mathlib's expression table, pre-sized to 2^28, is not rebuilt). 0, the
default, is no limit but the heap's.

**Tests** (`make test-stage`, in `make test`; the round trips also in
`make test-compact`):

- `tests/core/stage.fs`: the life cycle and its refusals; the
  declarations of `constant-fixture.ndjson` and of `ndjson-block.ndjson`
  (a block, two types, two constructors, a recursor with two rules, a
  theorem) read back field by field; finding by name; each constant's
  resolution; three failed reads (another file's manifest, the memory
  limit, a handler's `THROW`), each rolled back to empty, after which the
  stage loads exactly as a fresh one; bad references refused by the
  stage's own checks, through forged records; the `mdata` of
  `reexport/kinds.ndjson` staged and `Nat.add`, the one declaration that
  holds it (through its type), marked (a Python walk of the file finds the
  same one); the marks through a letE's body, a recursor rule and a
  projection (`stage-cases/marks.ndjson`), none when no declaration holds
  the `mdata` (`stage-cases/unref.ndjson`), and the bitset over the limit;
  `stage-unmap` before sealing doing nothing; a
  scratch tier over the sealed input as a checker-context member, freed by
  its teardown word, also after a `THROW`; every heap block given back.
  Loaded under `HEX`.
- `tests/core/test_stage.py`: twelve changed exports — an unknown
  constant (invalid at sealing, its name given), two declarations of one
  name (both found; the constant naming them resolved to neither), a file
  cut between two lines and one with a changed byte (the manifest
  differs), no manifest, a reference to a later expression, three numbers
  beyond 32 bits (full), another Lean version (unsupported), and two
  unchanged files.
- The round trip, `tests/core/compact-verify.sh`: every fixture export of
  `tests/` (the five reference exports with their manifests, the four
  check-declaration cases, `ndjson-block.ndjson` and
  `reexport/kinds.ndjson`, which has every record kind, and the two
  `stage-cases`, unchecked) staged and re-emitted from the store,
  metadata, names, levels, expressions and declarations, equal family by
  family to this reader's dump, with every named declaration found through
  the array and by its text and every constant's resolution checked; and
  `Init` in `make check` (`reference-compact-init`).
- Planted faults in `tests/mutants/faults.toml` (`stage-…`), each caught:
  a named declaration dropped, a constant no declaration has taken as
  resolved, a name with two declarations resolved to the newest, the
  chain to the earlier declaration lost, a failed read not rolled back, a
  bad reference read as record 0, `mdata` left unmarked, or unmarked when
  reached only through a recursor rule, a letE's body or a projection, a
  declaration's value not checked.

**Measured** (2026-11-03, `gforth-fast` of Gforth 1.0, one thread, this
machine shared with other agents; `tests/support/compact-load.fs`'s
`compact-measure` under `/usr/bin/time -v`; the ADR 0016 column is its
prototype's, without declarations or manifest):

| | `Init` | all of Mathlib | ADR 0016 (prototype) |
| --- | ---: | ---: | --- |
| Export | 345,690,182 B, SHA-256 `c1b2071a…a59a179` | 6,258,342,501 B, `18448e5d…59c6` | |
| Load, manifest check and seal (expression table pre-sized) | 16.4 s (2²⁴) | 325.7 s, 5 min 26 s (2²⁸) | 12.1 s; 256 s |
| The same without the manifest | 11.7 s | not run (the manifest's SHA-256 costs about 97 s on Mathlib, measured above) | |
| Peak resident memory | 218 MB | 3.41 GB | 0.23 GB; 3.32 GB pre-sized |
| Input tier in use | 176.4 MB | 2.949 GB | 0.14 GB; 2.94 GB with declarations |
| Declaration records (blocks included); bytes | 59,953; 1.9 MB | 736,276; 23.6 MB | 729 k × 32 B |
| Name-to-declaration array | 1.2 MB | 17.0 MB | 17 MB |
| Export-index maps (freed by `stage-unmap`) | 35.7 MB | 570.7 MB | 0.44 GB |
| Every named declaration found through the array (newest, then the chain) | 59,349 of 59,349, 1 ms | 729,263 of 729,263, 12 ms | 6.7 ms |
| The same by its text, component by component through a scratch tier | 59,349, 77 ms | 729,263, 1.06 s | 0.61–0.69 s |
| Constants resolved, checked against the array | 56,957, none wrong | 1,426,722, none wrong | |
| Declarations marked (`mdata`) | 0 | 0 | |

Unchecked, the stage loads `Init` in 11.7 s against the library's 11.1 s
for names, levels and expressions alone
([FORTH_LIBRARY.md](FORTH_LIBRARY.md#measured)), within the ±20% between
runs: the declarations, the array, the resolution and the seal cost
little; the manifest's SHA-256 is the rest. Sealing found no unknown
constant in Mathlib, and every resolution agrees with the array.
`Init`'s round trip gives the
name, level and expression digests of ADR 0016 (`062a404d…`, `a37233ac…`,
`83d1d3ca…`) and 59,953 declaration lines equal to the reader's
(`ffb3ba16…`), in 33 s with both dumps; Mathlib's full round trip was not
run.

### Feeding the checker

`lf-feed ( stage feed -- outcome )` (`src/import/feed.fs`; a `/feed`
record the caller provides holds the loading aids, freed at the end)
makes a sealed stage the current context's checker input, in file order:

```forth
create lib /stage allot   create feeding /feed allot
24 lib stage-init drop
s" init.ndjson" lib stage-load drop      \ checked against its manifest
lib feeding lf-feed .                    \ 0, ok
100000 65536 lf-check-input              \ ( env outcome ), as for any input
```

The stage's names stay in its input tier, shared and read-only: the
context attaches the tier as its names (`lf-name-attach`), so a name's ID
is its number in the stage, and the environment finds a name's
declarations through the input's name index (ADR 0012 E5, ADR 0016 C4;
`tests/core/check-declaration-ndjson.fs` checks every lookup of the
fixtures against the scan). Levels, expressions and declarations are
copied into the context's stores, whose capacity settings the feed raises
to fit (never lowers): the checker reads terms through handles and
identities, which the input tier does not keep. An inductive block gives
no declaration; its types, constructors and recursors do (refused by the
audit, U1). Universe parameters join the session's level context first
(at most 64: `Init` uses 62). Outcomes: ok; invalid for a stage that is
not sealed, a level or expression of a kind the checker's stores do not
hold (a free or meta variable), or a declaration of a kind it does not
know; full for a store that refuses a record (its capacity, no heap),
the level context, or a list longer than the checker takes; `feed-at`
names the expression or declaration where it stopped.

The stage must outlive the view: the context's scratch tier points into
the stage's input tier, so free the stage only after `lf-name-detach` (or
after the context is freed).

The pinned exports and the broken copies give the same verdicts fed as
through the test transport, and so do the first-checker, binder-domain
and universe-scope tables against pinned Lean: `make
test-first-checker-fed-differential` and the two like it write each case
as an export (`tests/support/case_export.py`), stage and feed it
(`tests/support/fed-checker-driver.fs`) and compare the verdict with
Lean's. Three first-checker cases name a constant their export does not
declare; a real export always does, so the stage refuses those exports as
invalid, and the tables allow that for them alone. All of `Init` (59,953 staged records, 59,349
declarations, 6,099,054 terms, 56,957 references) fed and checked with
`gforth-fast`: see [ADR 0016's progress](../adr/0016-compact-store.md#c9-migration-and-the-plan-tasks-it-covers)
for the outcome counts, time and memory.

## Evidence

All run on 2026-11-02 with the pinned Gforth 1.0 (`gforth` and
`gforth-fast`); the unit and file tests also with Gforth 0.7.3, CI's
portability host.

- **Unit tests** (in `make test`). Each file loads its module under `HEX`
  and checks that `BASE` is restored; `tests/support/heap-watch.fs` counts
  the heap blocks held. `tests/lib/bytes.fs` (UTF-8 against an
  independent model over every first and second byte, encoding round
  trips, scanning, framing, the reader with tiny buffers, limits at and one
  past their bound, positions, the first buffer freed by a second
  `reader-init` and none left after `reader-free`),
  `tests/lib/json.fs` (valid texts and their tokens, a malformed corpus of
  69 texts that must all be invalid, escapes, numbers in binary and
  hexadecimal `BASE`, every limit at and past its bound, failure
  positions, kind-checked readers, no heap block left by a second
  `json-init` and `json-free`), `tests/core/ndjson.fs` (every record
  kind field by field, and for each kind the malformed, unsupported and
  limit cases; nothing handed over from a bad block; decoding under other
  `BASE`s; no field surviving from an earlier record; the token limit at
  and one past its bound, and the depth limit through the reader, 64
  accepted and 65 full; checked list and rule readers, including a
  reference equal to an array's token index, a list of objects, a rule's
  header and a recursor kept past its line, also after a failed line,
  which keeps its field and reason, with an array or objects shaped like
  rules at the token index of its lists, a line later and at the same
  line number after `export-restart`; no field or reason carried over to
  the next line; the line numbers of `export-line`; handler outcomes and
  their reasons, a broken stack contract (taking more than the record,
  also when one item is left, the item under the record is replaced or
  the handler reaches two cells down; one that reaches three cells down,
  also under `export-read`, or three or four cells down in a block's
  walk, changes only its caller's data, and every record is still handed
  over; a `THROW` from one still closes the file), re-entry,
  `export-init`, `export-free` and `export-restart` from a handler, block
  lists redirected to an empty array of the line or spoilt (every element
  still handed over) or lost from the JSON view (invalid), a changed kind
  or element number, a `THROW` that closes the file and leaves the export
  idle; `export-handler` refusing a non-kind; the three heap blocks of an
  export freed by `export-init` again and by `export-free`; the five
  reference fixtures; and, on `tests/core/ndjson-block.ndjson`, a
  handler that zeroes every cell of its caller's under the canaries while
  `export-read` reads an inductive block of two types, two constructors
  and a recursor, with all 19 records handed over and the reading ok).
  `scripts/check-portable-forth.py` tests its load
  check on a scratch tree it writes itself before it checks the
  repository: fourteen modules, of which the nine that use an adapted word
  with no load, a load after the use, a load in a multi-line comment, in
  a `0 [IF]` branch or in the `[ELSE]` of `TRUE [IF]`, a use after
  `[CHAR] \` or `CHAR (` on the same line, or a load in a comment after
  `'` or `CHAR` inside a definition must be reported, and the five
  that load it first (directly, through another module, under a guard,
  or in the middle of a line) or only mention a word in strings, comments
  or after `[UNDEFINED]` must not; and four lines that its line checks
  must read with the comments and strings, but not the `\` of `[CHAR] \`
  or the `(` of `CHAR (` outside a definition, taken out.
- **File tests** (`tests/core/test_ndjson_reader.py`, in `make test`):
  counts equal to `count.py` and field-by-field dumps equal to
  `tests/support/ndjson_dump.py` (Python's `json` module) and to the strict
  oracle on every reference fixture; thirteen broken files (no final line
  feed, CRLF, byte-order mark, blank line, invalid UTF-8, swapped lines, an
  unsupported exporter, ...) each failing at the expected line with no
  partial output; a line of exactly 64 MiB read through `export-read`,
  and one byte more full at its line; a seeded mutation sweep (seed
  20261102, 300 files in `make test`, with ASCII and non-ASCII bytes and
  multibyte sequences) checked against the strict oracle
  `tests/support/ndjson_oracle.py`: same outcome, same failing line, and
  the same records handed over before it, or the same whole dump. The
  oracle is written from this document, not from the Forth code; unlike
  Python's `json` module it refuses `NaN`, lone surrogates and duplicate
  keys and reads integers of any length.
- **Planted faults** were caught: swapping `app`'s `fn` and `arg` (by the
  fixture dumps), a wrong `\n` escape and a wrong UTF-8 class (by the unit
  tests), a reference check off by one (by the unit tests and by the
  mutation sweep), and an accepted malformed text (by the corpus test).
  After the review's fixes, fourteen more were each caught, one at a time
  on a copy of the tree: numbers read with `>NUMBER` in `digits>u` or in
  heights (by the `BASE` tests), records or block elements not unset, no
  token limit, list indices unchecked, the handler's stack depth
  unchecked, re-entry allowed, the file left open after a `THROW`, the
  line limit one byte short (by the 64 MiB test), a reference check off by
  one, a lone low surrogate accepted, a line taken without its line feed
  and `json-items-of` ignoring the kind; the tree without a fault passed.
  After the second review's fixes, 21 more, each undoing one fix, were
  each caught by the unit tests on Gforth 1.0 and 0.7.3: no canary check;
  the busy mark kept after a `THROW`; resetting or freeing allowed from a
  handler; block lists not checked after the handler; a declaration's kind
  or an element's number read back from the record; lists not inverted;
  `list-item` taking a list of objects; a rule without its header, handed
  out when it failed, or leaving its reason; a field kept from an earlier
  line; each of the three modules loading in the caller's `BASE`, or
  `ndjson.fs` not restoring it; `export-handler` taking any number; the
  reader's depth limit one more or one less; `reader-init` or `json-init`
  keeping the old memory. After the third review's fixes, 17 more, each
  undoing one fix, were each caught on Gforth 1.0 and 0.7.3, by the unit
  tests or the load check's own test: a block's lists read back from the
  record (with or without the check that they are still lists); a list
  lost from the JSON view taken as empty; only the cell under the record
  checked; the counter's address, or a declaration's kind, kept on the
  data stack under the handler; the kind read after the handler;
  `recursor-rule` clearing the failed field and reason; `export-line` not
  counting its line, or `record-line` taken from the file reader; and in
  the load check, `( )` comments, literal `[IF]` conditions, loads under
  other `[IF]` conditions, the order of load and use, `[UNDEFINED]`
  names, strings, or the escapes of `s\"` not handled. After the fourth
  review's fixes, ten more, each undoing one fix, were each caught on
  Gforth 1.0 and 0.7.3, by the unit tests or the script's own tests:
  `export-lines`, `export-caught` or the walk of a block's three lists
  keeping the export on the data stack; a block's list walked with its
  visit and export on the data stack; the list readers not checking the
  generation, or comparing line numbers instead; a line not advancing the
  generation; records not stamped with it; and a word after `[CHAR]` read
  as a comment or a string, by the load check or by the line checks.
- **Independent AI review** (2026-11-02; not a substitute for the human
  review that `AGENTS.md` requires for declaration import): its fuzzer
  found no malformed input reaching a handler in 19,000 files, and it
  reported eight issues, all fixed the same day: decoding depended on
  `BASE`; a decoded record kept fields of earlier records; one long line
  could take about 0.8 GB (there was no token limit); the list and rule
  readers did not check their index; a handler's refusal and a file that
  cannot be opened gave misleading reasons; a second `init` did not free
  the first's buffers and a `THROW` from a handler left the file open; the
  handler contract was not written down; and the gaps in the tests listed
  above. After the fixes the reviewer's own fuzzer and oracle, run with
  `python3 -I`, found 0 discrepancies in 12,000 files: 6,000 with `gforth`
  (seed 20261103: 433 accepted, 5,567 rejected), 3,000 with `gforth-fast`
  (seed 20261104: 207 and 2,793) and 3,000 with Gforth 0.7.3 (seed
  20261105: 224 and 2,776). The repository's oracle agrees with the
  reviewer's on all of 10,000 generated files.
- **Second independent AI review** (2026-11-02, of the fixes above; also
  not a substitute for the human review): no input on its own got
  malformed data accepted, decoded wrongly or handed over stale. It
  reported findings that need a contract-breaking handler, misuse of a
  reader word or a non-decimal `BASE` while loading, all fixed the same
  day with a test that reproduces the reviewer's probe: a handler that
  took more than its record but left one item, or replaced the item under
  it, was not caught (it could make the reader count through the wrong
  address); a handler could reset, re-initialise or free its own export;
  the contract did not forbid writing the record; `list-count` read a
  reference equal to an array's token index as a list, and `list-item` read
  inside a list of objects; rule records had no header, and a recursor
  kept past its line gave a rule of -1 fields and a stale reason; a
  failure's field carried over to the next `export-line`; loading under
  `HEX` decoded `10` as 16 and accepted wrong records; `export-handler`
  wrote past its table for a kind out of range. `cell`, used by
  `ndjson.fs` but not a Forth-2012 word, is now defined by
  `src/lib/portability.fs` where missing, and
  `scripts/check-portable-forth.py` refuses a module under `src/` that uses
  an adapted word without loading that file.
- **Third independent AI review** (2026-11-02, of the second review's
  fixes; also not a substitute for the human review): no defect with input
  alone or with a handler that keeps its contract. It reported one medium
  finding, fixed the same day with a test that reproduces its probe: the
  reader still read a block's lists back from the record after the
  block's handler, so a handler could point `block-ctors` at another, empty
  array of the same line and no constructor was handed over, the line
  ok; the lists are now found again in the line's checked JSON view. Of
  its four low findings, three were fixed with tests: the canary covered
  only the cell under the record, so a handler reaching two cells down
  could make the reader count a record through another address (now two
  canaries, the counter and a declaration's kind on the return stack, and
  the limits stated in the contract above); the load check of
  `scripts/check-portable-forth.py` counted a `require` inside a
  multi-line comment or a `0 [IF]` branch, accepted a use before the
  `require`, and missed one in the middle of a line (fixed, with the
  self-test above); `recursor-rule` erased a failure's field and reason
  (now kept). The fourth is documented: a `THROW` while a module loads
  leaves `BASE` decimal. It also noted that `export-line` alone never
  numbered its lines, so `record-line` and `export-error`'s line were
  stale for lines given from memory (now counted, with a test), and five
  points of style, all applied. The `cell` fallback of
  `src/lib/portability.fs` stays untested: both CI hosts define `cell`.
- **Fourth independent AI review** (2026-11-02, of the third review's
  fixes; also not a substitute for the human review): no defect with
  input alone or with a handler that keeps its contract, and no high or
  medium finding. Its three low findings were fixed the same day, each
  with a test that fails before the fix and reproduces its probe. The
  reader's own data still lay under the canaries: during `export-read`
  two copies of the export being read, and during a block's walk the
  list's visit and export (and, deeper, the block's export), so a handler
  that reached three or four cells down and put the canaries back could
  end the reading ok after two of 35 records, or skip a constructor with
  the line ok. The reader now keeps nothing of its own on the data stack
  while a handler runs: the export waits on the return stack and a block
  list's position in the export. The review suggested keeping the walk
  and checking afterwards that every element was handed over; that left
  the block's export five cells down, and a changed export under the walk
  could make it read another export's tape. `recursor-rule` on a kept
  recursor could decode objects of a later line at the token index of its
  rules; records now carry the export's generation, which nothing
  resets, and the list and rule readers give nothing for a record of an
  earlier line (the review suggested comparing line numbers, which repeat
  after `export-restart`). The load check read the `\` of `[CHAR] \` as a
  comment; a word after `CHAR`, `[CHAR]`, `'`, `[']`, `POSTPONE`,
  `[COMPILE]`, `[DEFINED]` or `[UNDEFINED]` is now taken as it is, in the
  load check and in the line checks. Three points of style were applied.
  At the coordinator's request the threat model above is now written
  down, here and in the header of `ndjson.fs`, for later reviews to judge
  the reader against.
- **Fifth independent AI review** (2026-11-02, of the fourth review's
  fixes, against the threat model; also not a substitute for the human
  review): no defect with input alone or with a handler that keeps its
  contract, and nothing that blocks the declaration-import gate. Its two
  low findings were resolved the same day. The fourth review's change to
  the load check took the word after `CHAR` or `'` inside a definition
  too, where both are compiled and the `\` or `(` after them starts a
  comment: a `require` in that comment counted as a load, so a module
  that used `cell` without loading `portability.fs` was no longer
  reported, although both Gforths load such a file without reading the
  `require`. `CHAR` and `'` now take a word only outside a definition,
  and the line checks read the source through the same reader as the
  load check, with the reviewer's two modules and one line added to the
  script's self-tests. That reader also reads stack comments that hold a
  quote, `s\"` strings and a `\` inside a string correctly, which the
  line checks once read in part as code; 334 lines of 194 files now read
  differently, none with a new finding. The threat model did not list
  three breaches the reader does not detect: keeping a record's address
  instead of a copy, giving the list readers a list field of another
  record, and keeping `mdata-data` past its line; the contract and the
  lists above now name them. Its suggested test, a handler that zeroes
  every cell under the canaries while `export-read` reads an inductive
  block, passes; with the export kept on the data stack under the
  handler, as before the fourth review's fixes, it fails. Its point of
  style on `record-stamp` was applied.
- **Differentials on real exports**: the counting reports equal `count.py`
  byte for byte on `Init`, `Std` and all of Mathlib (and the recorded
  `count.out` of [the Mathlib measurements](measurements/mathlib-2026-11-02/README.md));
  the field-by-field dumps of the Forth reader and of Python's `json`
  module are identical on `Init` (6,455,017 lines) and on all of Mathlib
  (110,919,898 lines: 110,895,826 records, 24,071 inductive elements and
  the final line; SHA-256 `3cf988e8b53bc3c1…f831ddd674` for both). After
  the review's fixes the `Init` dump is unchanged, field by field (SHA-256
  `2ca3a7a21eed4785…f6c38e65` before and after, equal to Python's), and the
  Mathlib count still equals `count.out` byte for byte. After the second
  review's fixes the `Init` dump is again the same (6,455,017 lines, the
  same SHA-256), and the `Init` count report is byte-identical; so are
  both after the third and the fourth review's fixes.

## Measured speed and memory

Counting every record (`ndjson-count.fs`, which decodes and checks every
field) against `count.py`, which only parses each line with Python's
`json` module and counts keys. Measured 2026-11-02 on the machine of
[the Mathlib measurements](measurements/mathlib-2026-11-02/README.md) (WSL2,
Ryzen 5 7600X), one thread, the file in the page cache, with
`/usr/bin/time -v`: wall time and peak resident memory. Every Forth report
was byte-identical to `count.py`'s.

| Export (pinned Lean 4.35.0) | Size | `count.py`, Python 3.13 | Forth, `gforth-fast` 1.0 | Forth, `gforth` 1.0 |
| --- | --- | --- | --- | --- |
| `Init` | 345,690,182 B, 6,452,982 lines | 11.8 s, 10,248 KiB | **6.0 s**, 13,516 KiB | 19.5 s, 10,428 KiB |
| `Std` | 562,170,995 B, 10,193,568 lines | 18.6 s, 10,356 KiB | **9.6 s**, 13,472 KiB | 31.3 s, 10,452 KiB |
| all of Mathlib | 6,258,342,501 B, 110,895,826 lines | 3 min 32.5 s, 36.6 MB (recorded) | **1 min 42.9 s**, 16,588 KiB | 5 min 35.2 s, 13,524 KiB |

The review's fixes (unset records, the handler checks, checked readers)
cost about 4%: measured again later the same day, one after the other,
all of Mathlib took 1 min 44.0 s (102.9 s user, 16,640 KiB) before them
and 1 min 49.2 s (107.7 s user, 16,708 KiB) after, both reports equal to
`count.out`; `Init`, three runs each, 5.95 s and 6.18 s of user time on
average. The second review's fixes add 1.2% of instructions: counting
`Init` with `gforth-fast` took 107.58 billion user-mode instructions
before them and 108.88 billion after (`perf stat -e instructions:u`), of
which the checks made by a defining word account for 0.3% and the `CATCH`
around each handler for 0.5%. Wall times, measured while other jobs ran
on the machine, moved by less than their run-to-run spread (five
alternating runs each: 6.18 s and 6.27 s of user time on average). The
third review's fixes add 0.37% of instructions (109.13 billion before
them, 109.53 billion after); in three alternating runs each the task
time was 6.46 s both before and after. The fourth review's fixes add
0.15% (109.53 billion before them, 109.69 billion after); in three
alternating runs each the task time was 6.78 s before and 6.84 s after,
within the runs' spread (6.70 to 6.83 s, and 6.72 to 7.01 s).

So the Forth reader decodes about 60 MB/s with `gforth-fast`, twice
Python's line-parsing rate, in constant memory (the resident size is
Gforth's own image plus the line buffer). On `Init`, about two thirds of
the time is JSON tokenizing and one third decoding and checking records;
splitting lines and the framing checks take under a tenth. The default
`gforth` engine is about 3.3 times slower; the command line (`bin/leanforth
count` and `reexport`) uses `gforth-fast`. Exports were made with
`leanexport Init` and `leanexport Std` from the pinned toolchain (SHA-256
`c1b2071a…a59a179` and `bae74d69…a9afcbeb`); the Mathlib export is the one
recorded in the Mathlib measurements (`18448e5d…59c6`).

Commands (from the repository root):

```sh
/usr/bin/time -v .tools/gforth/bin/gforth-fast src/import/ndjson-count.fs \
  -e 's" .tools/mathlib/mathlib.ndjson" count-export bye'
python3 -I docs/development/measurements/scale-2026-11-02/count.py .tools/mathlib/mathlib.ndjson
```

## Re-export

*Have we re-exported Mathlib from LeanForth, imported it again and
compared it byte for byte with Lean's NDJSON?* Yes, since 2026-11-03 (plan
task 3.2.4): the Forth re-exporter `src/import/ndjson-emit.fs` takes every
record the reader hands over and writes it back in lean4export 3.1.0's
exact bytes. The pinned `Init`, `Std` and all of Mathlib come back
**byte-identical** (same SHA-256), and the reader reads each copy back into
the same field-by-field dump as the original
([measurements](measurements/reexport-2026-11-03/README.md)). So the
reader loses nothing the exporter writes: the decoded fields of every
record determine its line exactly. Like the reader, the re-exporter is
untrusted and decides nothing about types or proofs.

```sh
scripts/ndjson-reexport.sh --reimport EXPORT COPY   # or: make reexport EXPORT=... COPY=...
scripts/ndjson-reexport.sh EXPORT -                 # stream: no copy is kept
```

The script re-exports with the pinned `gforth-fast`, prints both SHA-256
sums and `identical`, or the first differing line, the byte within it
and both lines around it, and exits 0 only for identical files (and, with
`--reimport`, equal dumps). For `tests/reference/composition.ndjson` with
line 27 written `{"ie":13, "app":{"fn":1,"arg":12}}`, the same record in
another spelling:

```text
export 662f5c769e5876d6958b767cb6589679e9aba82e2b430295a53114dfca4ee161
reexported 35 lines
copy   7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec
different: first at line 27, byte 3 of the line (byte 1235 of the file)
export: {"ie":13, "app":{"fn":1,"arg":12}}
copy:   {"app":{"arg":12,"fn":1},"ie":13}
dump of export e821bfc2499000904579f49cf53106636c75fa67bbce1c811069594e2df90fad
dump of copy   e821bfc2499000904579f49cf53106636c75fa67bbce1c811069594e2df90fad
reimport: equal dumps
```

The Forth word alone is
`gforth-fast src/import/ndjson-emit.fs -e 's" IN" s" OUT" reexport bye'`;
it prints `reexported N lines`, or an error line as the counting tool
does and exits with status 1. On a failure the copy holds at most the
lines before the failing one.

### The exporter's format

Taken from the exporter's source in the pinned toolchain
(`src/lean/LeanExport/Basic.lean`: each record is `Json.compress` of a
`Json.mkObj`, printed with `IO.println`) and from Lean's JSON printer
(`src/lean/Lean/Data/Json/Printer.lean` and `Basic.lean`), then checked
against the exporter's output:

- **One line per record**: compact JSON, no white space, then one line
  feed, the last line too.
- **Key order**: a Lean `Json` object is a tree map of its keys, so every
  object's keys come in increasing order, whatever order the exporter's
  source lists them in: `{"cidx":…,"induct":…,"isUnsafe":…,"levelParams":…,"name":…,"numFields":…,"numParams":…,"type":…}`.
  The index key of a name, level or expression (`in`, `il`, `ie`) is one of
  them, so it comes first or last by the keys alone:
  `{"app":{"arg":12,"fn":1},"ie":13}` but `{"ie":15,"lam":{…}}`.
- **Numbers**: natural numbers (a `JsonNumber` with exponent 0) in decimal
  without sign or leading zeros, of any size (`"i"` of a numeric name);
  `natVal` as a string of such digits.
- **Strings**: Lean's `Json.escape` writes `"`, `\`, line feed and carriage
  return as `\"`, `\\`, `\n` and `\r`, every other byte below 32 as `\u00xx`
  in lowercase hexadecimal, and every other character as its UTF-8 bytes:
  DEL, `/` and all of Unicode are not escaped. So tab, backspace and form
  feed are `\u0009`, `\u0008` and `\u000c`, where Python's `json.dumps` and
  the JSON writer's default write `\t`, `\b` and `\f`. The writer
  (`src/lib/json-write.fs`) gained the setting `jw-lean` for Lean's
  escapes; the re-exporter sets it.
- **Enumerations** as the exporter spells them: `binderInfo` (`default`,
  `implicit`, `strictImplicit`, `instImplicit`), `safety` (`safe`,
  `unsafe`, `partial`), a quotient's `kind` (`type`, `ctor`, `lift`,
  `ind`) and `hints` (`"opaque"`, `"abbrev"` or `{"regular":height}`).
- **Inductive blocks**: `{"inductive":{"ctors":[…],"recs":[…],"types":[…]}}`.
  The reader hands the types over first, so the re-exporter keeps them in
  a buffer until the block's last element.
- **mdata's data** is one object of strings (`KVMap.toJson`, written only
  with the exporter's `--export-mdata`), so in key order too: the
  re-exporter writes its members sorted. Lean never writes an object
  inside one of its values, real numbers or two equal keys; the
  re-exporter refuses those as invalid (an unsorted inner object) or
  unsupported (a real number), and more than 256 members as full.

The JSON writer checks every object's key order (`jw-sorted`), so a key
written out of order fails the line instead of reaching the copy.

Nothing of the format is impossible to reproduce: the exporter writes one
form for each record, and every field of that form is in the decoded
record. A file in another spelling of the same records (white space, key
order, other escapes such as `\t` or `é`) is read the same and comes
back in the exporter's form, so its copy differs from it while the two
dumps are equal, as above.

### Tests and evidence

- `tests/core/ndjson-emit.fs` (in `make test`, loaded under `HEX` with
  the heap watched): every record kind and every enumeration word, lines
  in the exporter's bytes coming back unchanged; other spellings (white
  space, key order, `\t`, `\/`, `\u` escapes and surrogate pairs, `-0`)
  in the exporter's form; mdata's members sorted; every failure, which
  never gives ok and leaves no byte of its line: an enumeration code out
  of range (binder information, safety, quotient kind and hints, given by
  a handler that changes its record), mdata's data with equal keys, an
  unsorted inner object, a real number or 257 members, a key past the
  writer's key pool,
  a line inside an unfinished block, a block element outside a block, an
  input that cannot be read and an output that cannot be written; buffer
  growth and its limit; all 11 NDJSON exports under `tests/` re-exported
  in memory byte for byte, also with `BASE` hexadecimal; and no heap block
  left.
- `tests/core/test_ndjson_emit.py` (in `make test`): every `*.ndjson` under
  `tests/` that starts with the exporter's metadata (all but
  `tests/lib/json-write-corpus.ndjson`, record lines for the JSON writer
  without metadata) re-exported through files with the command-line word,
  byte for byte, and read back into the same dump; a seeded sweep (seed
  20261103, two spellings of each export) with random white space,
  shuffled members and random escapes, each of which must come back as
  the original bytes; a seeded fuzz sweep (seed 20261104, 200 exports
  each changed by one of the reader's mutations, above): every mutant the
  reader refuses is refused with an error line, and every one it accepts
  comes back as a copy the reader reads into the same dump and that
  re-exports to itself byte for byte (in `make test` 40 accepted, 18 of
  them already in the exporter's form, since the three exports of
  `tests/reference/inductive/` joined the files the sweep draws from
  (ADR 0015; before, 42 and 22); a run of 3,000 accepted 614, all
  passing, 292 unchanged); and the script in both modes, on a file in
  another spelling, on a file the reader refuses and with bad usage.
  Plan task 3.2.4 asked for identity on all fixtures and accepted fuzz
  cases: byte identity where the input is in the exporter's form, and
  otherwise the same records and a fixed point.
- `tests/core/reexport/kinds.ndjson` is pinned Lean's own export (with
  `--export-mdata --export-unsafe`) of `tests/core/reexport/kinds.lean`:
  1,390 lines with every record kind, levels `max` and `imax`, a 129-bit
  `natVal`, a `letE` with `nondep` true, `proj`, `mdata`, every quotient
  kind, an opaque and an unsafe definition, an axiom (`propext`), mutual,
  nested and reflexive inductive types and names with spaces, quotes,
  backslashes and Greek letters. `make check` (`reference-reexport`,
  `tests/core/reexport/lean-check.sh`) exports it again and compares, and
  exports `tests/core/reexport/strings.lean`, a string literal with every
  class of byte the printer escapes apart (11,158 lines with what string
  literals depend on, not kept): it checks that pinned Lean writes
  `"tab\u0009 nl\n cr\r bs\u0008 ff\u000c nul\u0000 us\u001f esc\u001b del…"`
  and that the copy is identical, with equal dumps.
- **Planted faults**, each caught: in the unit test, an application's
  arguments swapped (the bytes differ, first at the composition's line
  27) and its keys written in the wrong order (the writer refuses the
  line as invalid); and in a copy of the source, one at a time: the
  application's two fields swapped (both test files), Python's escapes
  instead of Lean's (the unit test; `make check`'s string export), the
  recursors' list opened one element late (both test files) and mdata's
  members not sorted (the unit test).
- **Measured** on `Init`, `Std` and all of Mathlib: below.

### Measured

Re-exported with `gforth-fast` 1.0 into a file, one run at a time, the
input in the page cache; `/usr/bin/time -v` wall time and peak resident
memory of the re-export alone; then SHA-256 and `cmp` of both files and
the reader's field-by-field dump of each
([commands and logs](measurements/reexport-2026-11-03/README.md)).

| Export (pinned Lean 4.35.0) | Lines, bytes | Re-export | Identical | SHA-256 of both | Dump of both |
| --- | --- | --- | --- | --- | --- |
| `Init` | 6,452,982, 345,690,182 B | 17.8 s, 14,856 KiB | yes | `c1b2071a…a59a179` | `2ca3a7a2…f6c38e65` |
| `Std` | 10,193,568, 562,170,995 B | 29.2 s, 14,884 KiB | yes | `bae74d69…a9afcbeb` | `76750d5c…cce14a` |
| all of Mathlib | 110,895,826, 6,258,342,501 B | 5 min 29 s, 20,104 KiB | yes | `18448e5d…59c6` | `3cf988e8…f831ddd674` |

The dumps of `Init` and Mathlib equal those recorded under
[Evidence](#evidence). Re-exporting takes about three times as long as
reading alone (1 min 43 s for Mathlib): the JSON writer checks every call
and every key's order, and has not been tuned. Memory stays flat; the
peak grows with the longest line (Mathlib's 2.7 MB string), held as read
and as written.

## Is a binary quick-import worth building?

**Not now.** Reading and checking all of Mathlib's 6.26 GB export takes
under two minutes on one core in 17 MB. That is small next to the other
steps of a full run: producing the export took 6.5 minutes and 13.8 GB, the
official checker needs about 32 minutes, and LeanForth's own checking is
estimated at hours of CPU ([SCALE_ASSESSMENT.md](../project/SCALE_ASSESSMENT.md)).
A binary format might cut the reading to seconds, but it would be a second
input format to specify, version, test and keep in step with lean4export.
It would also be made from the NDJSON file, so it is a cache of unchecked
data: under the owner's saved-results decision (OQ-3) a final run reads the
NDJSON file anyway. Better targets, when reading does become a large share
of a run: caching *checked* results (OQ-3's development mode), reading
several parts of the file in parallel (lines can be tokenized
independently), and tuning the JSON layer, which has headroom (a bare
line-scanning loop in `gforth-fast` reaches about 1 GB/s). Revisit once the
checker itself is fast enough for reading to be more than a few percent of
a full check.

## Limits and memory

The reader holds one line at a time: a 1 MiB buffer that doubles for longer
lines (Mathlib's longest line is 2,713,224 bytes, line 64,253,241, a
`strVal` holding a JavaScript widget bundle), a token tape that starts at
256 tokens and doubles, and a container stack of 64 cells. Memory does not
grow with the file. Natural numbers in names (`num`) and literals
(`natVal`) are kept as digit text of any size, for the planned big-number
module; counts and references must fit in a cell.

The token limit bounds the tape. Mathlib's line with the most JSON tokens
has 3,051 (line 17,297,817, an inductive block of 20,471 bytes; `Std`'s
most is 1,658 and `Init`'s 533, measured 2026-11-02 with a handler that
reads the JSON view's token count). The limit, `export-token-limit`, is
65,536, 21 times that; a token takes three cells (24 bytes with 64-bit
cells), so the tape never exceeds 1.5 MiB. The worst case for one line is
therefore the 64 MiB line buffer (64 MiB and one byte, plus a moment of
twice that while `RESIZE` copies it) and 1.5 MiB of tape: about 66 MiB.
Before the limit, a valid 63 MB line of small values needed one 24-byte
token per two bytes of text, about 0.8 GB ([measured below](#measured-memory-for-one-long-line)).
`lib/json.fs` itself still sets no token limit (`json-init` allows as many
tokens as memory holds); a caller that reads untrusted text sets
`json-token-limit`, as `export-init` does.

### Measured memory for one long line

A valid export whose line 4 is a 63,000,043-byte `mdata` record with
31.5 million small values (`{"k":[0,0,…]}`) as its data, counted with
`gforth-fast` and `/usr/bin/time -v` (2026-11-02):

| Reader | Outcome | Peak resident memory |
| --- | --- | --- |
| before the token limit | ok, counted | 812,416 KiB |
| with the token limit | full: too many tokens (line 4, byte 131,085) | 75,468 KiB |

The 75 MB are Gforth's image, the line buffer grown to hold the 63 MB
line, and the 1.5 MiB tape.
