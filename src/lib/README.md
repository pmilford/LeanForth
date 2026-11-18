# The LeanForth Forth library

A set of general-purpose Forth libraries: hashing, JSON, big numbers,
sorting, hash tables, growable memory, a job pool and more. They were
written for the LeanForth checker, but nothing in this directory knows
about Lean or about LeanForth. They are meant to be used in other Forth
programs.

- **Standard:** Forth-2012. Tested on Gforth 1.0.0 and Gforth 0.7.3, on
  64-bit Linux. Words a host may lack (`-rot`, `>=`, the structure words)
  come from `portability.fs`.
- **Licence:** MIT, as for the whole project (`LICENSE` at the root).
- **Full documentation:** [FORTH_LIBRARY.md](../../docs/development/FORTH_LIBRARY.md)
  describes each library's algorithm, cost and measured speed.
  [LIBRARY_WORDS.md](../../docs/development/LIBRARY_WORDS.md) is a generated
  index of every public word.

## Using a library in your own program

1. Copy this directory into your project. Each file `require`s the other
   files it needs, by relative path, so keep them together.
2. Load the file you want:

   ```forth
   require lib/sha256.fs
   ```

3. Use its public words. Each file's header comment lists them, says what
   the library assumes, and gives an example.

A complete example, from the header of `sha256.fs`:

```forth
require lib/sha256.fs

sha256: hasher                \ a record holding one hash in progress
create digest 32 allot  create text 64 allot
hasher sha256-init
s" ab" hasher sha256-update  s" c" hasher sha256-update
digest hasher sha256-final  digest text sha256-hex  text 64 type
```

This prints `ba7816bf...f20015ad`, the SHA-256 of "abc".

## The most useful libraries for other projects

| File | What it gives you |
| --- | --- |
| `sha256.fs` | SHA-256 (FIPS 180-4). Feed the message in pieces of any size; get the 32-byte digest or its hex text. |
| `json.fs` | A strict JSON reader (RFC 8259). Parses one JSON text without recursion, with limits on depth and size; malformed input is refused, never guessed at. |
| `json-write.fs` | A JSON writer (RFC 8259) with deterministic output: the same data always gives the same bytes. |
| `bignum.fs` | Natural numbers of any size: add, subtract, multiply, divide, compare, and conversion to and from decimal text. |
| `bigint.fs` | Signed integers of any size, built on `bignum.fs`, with Euclidean division and remainder. |
| `sort.fs` | Stable in-place sorting of records of any size, by your own comparison word or by key: insertion sort for short inputs, merge sort above that. |
| `htab.fs` | Open-addressing hash tables that grow as they fill, with your own hashing and comparison. |
| `memo.fs` | A ready-made map from fixed-size keys to fixed-size values, built on `htab.fs` and `slab.fs`. Use it as a cache or a dictionary. |
| `pqueue.fs` | A priority queue (binary min-heap) of cells, ordered by your own comparison word. |
| `slab.fs` | A growable array in one heap block: it doubles as needed up to a limit you set, and can be cut back to an earlier size. |
| `bytes.fs` | A line reader for files with long lines, plus UTF-8 validation and decoding. |
| `decimal.fs` | Numbers to decimal or hex text and back, correct whatever `BASE` is set to. |
| `task.fs` | A job pool: run words in parallel on a fixed set of worker threads (POSIX threads on Gforth 1.0; cooperative tasks on Gforth 0.7). |
| `sections.fs` | A binary file format with named sections, each protected by a SHA-256 checksum, for saving and reloading large tables. |

## Every file

**Numbers and text**

| File | One line |
| --- | --- |
| `bignum.fs` | Arbitrary-size natural numbers. |
| `bigint.fs` | Arbitrary-size signed integers. |
| `decimal.fs` | Decimal and hex text conversion, independent of `BASE`. |
| `bits.fs` | Bit sets, the width of a cell, base-2 logarithm, and binary search. |
| `find.fs` | The first index of a linear search by a caller's test (`find-index`). |
| `texts.fs` | Tables of short texts in the dictionary and their search by a caller's test (`texts-find`). |
| `u32.fs` | Reading and writing packed unsigned 32-bit fields on any cell size. |
| `bytes.fs` | Bounded line reader and UTF-8 checks. |
| `name-table.fs` | Small read-only tables of names laid down while loading, each entry some data cells and a counted name, found by exact bytes. |
| `text-rule.fs` | Tests whether UTF-8 text is "visible": no control, format or separator characters, and not blank-looking. |
| `text-run.fs` | Tools for interpreting text in a vocabulary of your own: saving and restoring the interpreter's settings, reading a whole file, scanning lines. |

**Hashing and files**

| File | One line |
| --- | --- |
| `sha256.fs` | SHA-256, incremental. |
| `hash32.fs` | Fast 32-bit hashing (not cryptographic) that gives the same values on 32-bit and 64-bit systems. |
| `json.fs` | Strict JSON reader. |
| `json-write.fs` | Deterministic JSON writer. |
| `sections.fs` | Sectioned binary files with checksums. |

**Containers and algorithms**

| File | One line |
| --- | --- |
| `sort.fs` | Stable sorting of records in place. |
| `htab.fs` | Open-addressing hash tables. |
| `memo.fs` | Keyed tables: fixed-size keys to fixed-size values. |
| `pqueue.fs` | Priority queues. |
| `cons.fs` | Sets that store each distinct record once and name it by a number (hash-consing), in a shared read-only tier and a scratch tier. |
| `pools.fs` | Interned lists of 32-bit numbers and interned texts: each distinct one stored once. |
| `runs.fs` | Sequences of cells that are only ever appended to, so that sequences share storage and a saved sequence is one handle. |
| `xt-table.fs` | Tables of execution tokens with a default entry, for dispatching on a small number. |

**Memory**

| File | One line |
| --- | --- |
| `blocks.fs` | Heap blocks held in a cell: allocate zeroed, resize, release. |
| `slab.fs` | Growable arrays of fixed-size units in one heap block. |
| `store.fs` | Bounded stores of fixed-size records that detect stale handles after a reset. |
| `store-columns.fs` | Extra per-record columns that grow together with a store. |
| `node.fs` | A record of a tag and two fields, kept in a store. |
| `bounds.fs` | Range and index checks that never wrap around. |

**Walking data structures**

| File | One line |
| --- | --- |
| `walk.fs` | Depth-first walks over a graph of nodes with a fuel limit and a bounded work stack, in place of recursion. |
| `frame.fs` | Multi-step passes over a graph on an explicit stack that grows on the heap, in place of deep recursion. |

**Program structure**

| File | One line |
| --- | --- |
| `outcome.fs` | One shared set of result codes (ok, invalid, exhausted, unknown, rejected, unsupported, full) that every library returns. |
| `module.fs` | Public and private wordlists for the library, so helper words do not clutter your dictionary. |
| `context.fs` | One heap record per worker thread holding all of a computation's mutable state, so that code can run in parallel. |
| `task.fs` | The job pool. |
| `portability.fs` | Forth-2012 definitions of a few common words, compiled only where the host lacks them. |
| `lib.fs` | Loads the core group in one line: portability, bounds, store, node, outcome, walk, frame, context. |

## Conventions shared by all the libraries

- **Results are outcomes, not exceptions.** A word that can fail leaves an
  outcome code on the stack (`outcome.fs`). `ok?` tests it. Running out of
  room is the outcome "full", never a crash or silent truncation.
- **Everything is bounded.** Readers, tables and walks take limits and
  stop cleanly at them. Malformed input is refused.
- **The caller owns the memory.** Most libraries work in a record or an
  arena that you provide, so there is no hidden global state.
- **Helpers are private.** Public words are in the wordlist `lf-lib`;
  helpers are in `lf-lib-private` and stay out of your way.

## What to know before relying on them

- They are tested (`tests/lib/`, run by `make test`), and several are
  compared against an independent implementation: the big numbers and the
  JSON writer against Python's. They have not had an outside security or
  correctness audit.
- Every file loads on its own: `make test-lib-standalone` copies each one
  with exactly the files it requires into a folder outside the project,
  loads it on Gforth and gforth-fast with `BASE` set to 7, and checks that
  `BASE` and the search order are as before; every number in the source is
  read in decimal, and each file requires directly every file whose words it
  uses (`tests/lib/test_requires.py`), not only through another file. Every header has an example ending in the text it
  prints, and that test runs each one as written there, on both engines
  (and on Gforth 0.7.3), so an example cannot go stale.
- `make lib-bench` measures each library at a small and a large size on
  gforth-fast and gforth; the figures, with what each library costs as
  inputs grow and the sizes LeanForth really passes it on `Init`, are in
  [FORTH_LIBRARY.md](../../docs/development/FORTH_LIBRARY.md#measured-profiles-2026-11-18).
- `bytes.fs`'s reader reads ordinary text by default (a last line without
  a line feed, CRLF line ends, a leading byte-order mark); `reader-strict`
  gives the strict framing LeanForth uses for Lean's exports.
- `context.fs` and `task.fs` were designed around the checker's needs.
  They are general, but less polished as stand-alone tools than the rest.
- `task.fs`'s public words are the job pool's interface, listed in its
  header; its records, queue and workers are private. `blocks.fs`,
  `outcome.fs` and `node.fs` have no helpers: every word they define is
  public, in `lf-lib` as every library's.
