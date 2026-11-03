# Forth reader for Lean NDJSON exports

LeanForth reads Lean's kernel exports in Forth. Lean's exporter
(`leanexport`, lean4export 3.1.0, pinned with Lean 4.35.0) writes a
declaration library as NDJSON: one JSON object per line, first a metadata
record, then names, universe levels, expressions and declarations, each
referring to earlier records by index. The reader decodes those records and
hands each one, checked for shape and references, to a word the caller
chooses. It is the first step of `leanforth check FILE.ndjson` (plan phase
3): under the owner's product rule, end users need only a Forth system and
an NDJSON file, so nothing on the user's path is Python
([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md), "Product dependencies"
and OQ-4).

**Status (2026-11-02): implemented, untrusted, fail-closed.** The reader
decides nothing about types or proofs; a decoded record is input for the
checker, never a checked declaration. It does not yet stage records into
the term, level and name stores, which hold only 64 entries each; that is
the next step (plan items 3.2.1 and 3.3.1). The Python preview
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
results. On failure the tool prints one line instead of the report and
Gforth exits at once with status 1; after the report, `bye` exits with
status 0. Forth-2012 has no `bye` with a status, so the tool uses Gforth's
`(bye)`, present in both CI hosts, Gforth 0.7.3 and 1.0 (another host
would end with an uncaught `THROW`). Inside a Forth session, or for many
files in one process as the tests do, `count-report` prints the same and
never exits. For a
copy of `tests/reference/composition.ndjson` with an application referring
to itself, with a closing quote removed on line 2, and with the Lean
version changed:

```text
error: invalid: bad reference (field fn, line 27)
error: invalid: unterminated string (line 2, byte 43)
error: unsupported: unsupported exporter, format or Lean version (line 1)
```

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

A handler must keep this contract:

- It takes its record and leaves exactly one outcome, nothing else. The
  reader checks the stack depth: a handler that leaves no outcome or extra
  items stops the reading as invalid ("handler left no outcome or extra
  items"); one that takes more than its record throws -4 (stack
  underflow), since its caller's data is gone.
- It does not call `export-read` or `export-line` on the same export; the
  reader refuses that as invalid ("export read again by its own handler").
- It copies any text, digits or list it wants to keep: they point into the
  current line and its JSON tape, valid only until the handler returns.
- A `THROW` from a handler passes on to the caller of `export-read`, after
  the reader has closed the file and marked the export idle. After a
  `THROW` out of `export-line` itself, `export-restart` clears the mark.
- Decoding never depends on `BASE`: numbers are read in decimal by hand, so
  a handler may change `BASE` freely.

## Layers

| File | Knows | Does |
| --- | --- | --- |
| `src/lib/bytes.fs` | bytes, lines, UTF-8 | `reader:` records: whole lines of a file in one heap buffer that grows for long lines up to a limit; every line must end with a line feed; line numbers and file offsets. `text-framed` refuses carriage returns and a byte-order mark. UTF-8 length, validity and encoding. |
| `src/lib/json.fs` | JSON (RFC 8259) | `json:` views: one JSON text parsed, without recursion, into a tape of tokens; escapes decoded in place; numbers kept as digit text; limits on nesting, tokens, string and number length. |
| `src/import/ndjson.fs` | lean4export 3.1.0 | `export:` records: the reader, the JSON view, the decoded records, the handler table and the counters. Tables describe every record shape; each record is checked whole before its handler sees it. |
| `src/import/ndjson-count.fs` | count.py's report | The counting tool above. |

Each layer keeps its state in records passed on the stack, so separate
readers are independent ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md));
one reader is single-threaded. `lib/bytes.fs` and `lib/json.fs` are the only
modules allowed byte access (`scripts/check-portable-forth.py`).

## Record kinds and their fields

Each record is handed over in a decoded record. Every decoded record starts
with `record-kind`, `record-index` (its own index; declarations and the
elements of an inductive block count from 0), `record-line` and
`record-export`. References are indices of earlier records. Lists are read
with `list-count ( list record -- n )` and `list-item ( i list record -- u )`.
Texts are an address and a length (`2@`), valid only inside the handler.

Before each decode every field after the header is set to -1, so nothing
survives from an earlier record. A record's own fields are always all
written. The layouts of different kinds overlap, so a field the kind does
not have reads -1 (as a flag: true) or one of the record's own fields: a
handler reads only the fields of its record's kind. The readers check
their arguments: `list-count` gives 0 for a field that holds no list,
`list-item` gives -1 for an index outside the list, and `recursor-rule`
gives 0 for a record that is not a recursor or an index outside its rules.

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
does a broken handler contract (invalid, see above).

`export-error ( export -- line key-addr key-u why-addr why-u )` gives the
line, the field being decoded and the reason; for a JSON error,
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

## Evidence

All run on 2026-11-02 with the pinned Gforth 1.0 (`gforth` and
`gforth-fast`); the unit and file tests also with Gforth 0.7.3, CI's
portability host.

- **Unit tests** (in `make test`): `tests/lib/bytes.fs` (UTF-8 against an
  independent model over every first and second byte, encoding round
  trips, scanning, framing, the reader with tiny buffers, limits at and one
  past their bound, positions, buffers freed by a second `reader-init`),
  `tests/lib/json.fs` (valid texts and their tokens, a malformed corpus of
  69 texts that must all be invalid, escapes, numbers in binary and
  hexadecimal `BASE`, every limit at and past its bound, failure
  positions, kind-checked readers), `tests/core/ndjson.fs` (every record
  kind field by field, and for each kind the malformed, unsupported and
  limit cases; nothing handed over from a bad block; decoding under other
  `BASE`s; no field surviving from an earlier record; the token limit at
  and one past its bound; checked list and rule readers; handler outcomes
  and their reasons, a broken stack contract, re-entry, a `THROW` that
  closes the file; the five reference fixtures).
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
- **Differentials on real exports**: the counting reports equal `count.py`
  byte for byte on `Init`, `Std` and all of Mathlib (and the recorded
  `count.out` of [the Mathlib measurements](measurements/mathlib-2026-11-02/README.md));
  the field-by-field dumps of the Forth reader and of Python's `json`
  module are identical on `Init` (6,455,017 lines) and on all of Mathlib
  (110,919,898 lines: 110,895,826 records, 24,071 inductive elements and
  the final line; SHA-256 `3cf988e8b53bc3c1…f831ddd674` for both). After
  the review's fixes the `Init` dump is unchanged, field by field (SHA-256
  `2ca3a7a21eed4785…f6c38e65` before and after, equal to Python's), and the
  Mathlib count still equals `count.out` byte for byte.

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
average.

So the Forth reader decodes about 60 MB/s with `gforth-fast`, twice
Python's line-parsing rate, in constant memory (the resident size is
Gforth's own image plus the line buffer). On `Init`, about two thirds of
the time is JSON tokenizing and one third decoding and checking records;
splitting lines and the framing checks take under a tenth. The default
`gforth` engine is about 3.3 times slower; the command-line tool should use
`gforth-fast`. Exports were made with
`leanexport Init` and `leanexport Std` from the pinned toolchain (SHA-256
`c1b2071a…a59a179` and `bae74d69…a9afcbeb`); the Mathlib export is the one
recorded in the Mathlib measurements (`18448e5d…59c6`).

Commands (from the repository root):

```sh
/usr/bin/time -v .tools/gforth/bin/gforth-fast src/import/ndjson-count.fs \
  -e 's" .tools/mathlib/mathlib.ndjson" count-export bye'
python3 -I docs/development/measurements/scale-2026-11-02/count.py .tools/mathlib/mathlib.ndjson
```

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
