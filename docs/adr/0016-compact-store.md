# ADR 0016: the compact store for Mathlib-scale input

Status: the checker on the large store, with no depth limit, **approved [kernel]** by the owner on 2026-11-04 ([decisions](../project/OWNER_DECISIONS.md#checker-on-the-large-store-approved-resource-settings-2026-11-04-late)). **Accepted** by the owner on 2026-11-03, with the three recommendations of
[Decisions for the owner](#decisions-for-the-owner) ([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md)).
Previously: **proposed**, 2026-11-02 (plan tasks 6.0.1 and 6.2.0–6.2.3; also
1.1.5, 3.2.1 and 3.3.1). The owner approved writing this design and asked
the questions answered below. It changes how terms are stored, not what
the checker decides, so it is a [kernel] no-behaviour-change design: the
code that implements it needs the review gate in `AGENTS.md`. The 32-bit
access words of `src/lib/u32.fs`, which the owner approved separately, and
since 2026-11-03 the library code of C9 step 1 implement it (see
[C9's progress](#c9-migration-and-the-plan-tasks-it-covers)); since step 3, in part, the checker's
stores grow on the heap and it reads a staged export's names from the input tier. The
measurements come from a scratch prototype ([measurements](../development/measurements/compact-store-2026-11-02/README.md)).
It builds on [ADR 0009](0009-reentrant-state-and-parallel-checking.md)
(accepted: per-task contexts, a shared read-only environment) and
[ADR 0012](0012-checked-environment.md) (design accepted: input,
environment and context storage, E1; finding a constant, E5), and on the
estimates of [SCALE_ASSESSMENT.md](../project/SCALE_ASSESSMENT.md).

## Summary in plain words

To check all of Mathlib, LeanForth must hold about 106 million term nodes
in memory. Today each node takes 32 bytes plus per-module side arrays, and
every table holds 64 entries. This design stores each node in **16 bytes**:
four 32-bit numbers (a tag with a small payload, two children, and a word
of facts about the node, modelled on Lean's own). Equal terms are stored
once (*hash-consing*), found through hash tables. The terms read from the
input file form one **shared, read-only tier** that every worker reads
without locks; each check builds its new terms in its own **scratch tier**,
thrown away when the check ends. A scratch prototype loaded every name,
level, expression and declaration of all of Mathlib this way, gave every
name, level and expression back exactly as the file has it, and needs
**about 2.9 GB** for the whole input (4.2 GB peak with the loading aids).
That is a little under the assessment's estimate of 3.1 GB. Theorem proofs
are 71% of Mathlib's nodes; dropping them after their check could save
most of that, but needs a decision about theorem unfolding and is not
needed to fit.

## The owner's questions, answered

**Are all the node fields used?** Not today. A node now has three cells
(tag, first, second) plus an identity cell, 32 bytes on this machine. A
`Sort` or a bound variable uses only the first field; an application uses
both. The identity cell is used for handles, but not by name entries. In
the compact layout every kind uses at least its tag, one child or payload
and its data word; the unused parts are listed per kind in C1. They are a
few percent of the space.

**Are they all 64-bit addresses, or should some be bytes or bit fields?**
They are not addresses even today: children are *indices* (numbers of
records), which is why they can shrink. Mathlib has 106 million nodes, so a
32-bit index (up to 4.29 billion) has 40 times headroom. The compact node
has four 32-bit fields; two of them are bit fields: the tag word (5 bits of
tag, 27 bits of payload) and the data word (20 + 1 + 1 + 10 bits). Bytes
would save little more and cost alignment.

**Is the storage a tree or a B-tree?** Neither. Nodes sit in arrays,
numbered in the order they are made, and a node names its children by
number, so the terms form a *shared graph* (a DAG): a sub-term used a
thousand times is stored once. Lookups by content go through hash tables.
B-trees are built for ordered keys on disk pages; the checker never needs
order (see Rejected alternatives).

**How is it searched?** Following a child is arithmetic: node *i* lives at
byte 16·*i* of its tier. Finding "is this term already stored?" uses the
expression hash table: one hash computation, then on average 2.6 slots
compared during the Mathlib load. Finding a declaration by name is an array
index: names are interned when read, so a name is a number, and the
declaration of name *n* is entry *n* of a name-to-declaration array. A name
typed by a user is looked up component by component through the name hash
table (under 1 µs per Mathlib name, measured).

**How can it be optimised and hashed?** The hash of a node is computed
from its tag, payload and child indices with a portable 32-bit mixing
function (C4). Because equal children already have equal indices, this is
enough to recognise equal terms, so the node does not need to store a
hash. Speed comes from not repeating work: hash-consing makes equal terms
one node, the data word lets passes skip closed sub-terms, and per-check
caches keyed by node number remember inferred types, normal forms and
pairs already compared (plan §6.4). A walk of every declaration that
remembers visited nodes made 226.7 million visits on Mathlib in 21–22 s; the
same walk without that memory would make 1.3×10¹⁴ visits. Profiling Lean's
own checker the same day showed where the time goes: substitution about
40%, managing memory about a fifth, hash tables about a quarter, the logical
rules under 6% (facts P1–P5). The design aims at exactly those: one
reusable substitution memo, memory released per check in one step, one
table probe per new node, and constants resolved when the input is loaded.

**Would hashing the top levels into 64-way tables speed it up?** A hash
table *is* that idea taken to its end. A 64-way table uses 6 bits of the
hash to pick one of 64 sub-tables, then the next 6 bits, and so on; a flat
hash table uses all 28 bits at once to pick one of 268 million slots, so a
lookup reads one or two neighbouring slots instead of four or five levels
of sub-tables (64⁴ is only 16.8 million). Multi-level tables pay off when
many *versions* of a map must share structure: Lean uses 32-way ones
(`PersistentHashMap`, 5 bits per level) only for the constants of the file
being elaborated, and a flat hash table for all imported constants
(`SMap`, facts L5–L6). LeanForth's input never changes and its
environment's slots are written once (ADR 0012), so it needs no versions,
and flat tables are simpler and faster.

**Why do some fields in Lean's layout seem unused — identity, outer-variable
range, depth? Do they move into a bit-field word?**

- *Identity* is not a Lean field. It is LeanForth's own stale-reference
  guard: `store:` gives every record a serial number that never repeats,
  so a handle to a record that was rolled back and whose index was reused
  is detected. Lean needs none: a Lean term is an unchangeable value that
  stays in memory as long as anything refers to it.
  The input tier needs none either, because it is filled once and never
  rolled back or reset, so an index into it can never become stale. The
  scratch tier is reset after every check, and its indices never leave the
  check (handles given to callers name environment slots, ADR 0012 E3), so
  it does not need per-record identities either.
- *Outer-variable range and depth* are real Lean fields, and yes, Lean keeps
  them in one bit-field word. Every Lean expression carries a 64-bit
  `Expr.Data` word: 32 bits of hash, 8 bits of approximate depth (capped
  at 255), four flags (has free variables, has expression metavariables,
  has universe metavariables, has universe parameters) and 20 bits of
  loose-bound-variable range (fact L1). The range says how many enclosing
  binders a term refers to; zero means the term is closed, so substituting
  for a bound variable can skip it. The depth is there to spread hash
  values; Lean's elaborator also uses it as a cheap size limit. The compact
  node keeps the range and the universe-parameter flag, keeps a depth
  (wider, capped at 1023, for sizing the walkers' explicit stacks), and
  drops the hash and the two metavariable flags (C1).

## Facts

### From LeanForth today

- F1. `src/lib/store.fs`: a store is a header, one identity cell per record
  and the records; `src/lib/node.fs` records are three cells (`node-tag`,
  `node-first`, `node-second`). Terms, levels and names hold 64 records
  each, names 2,048 bytes of text. Children are indices that must point to
  earlier records, so every term is acyclic.
- F2. Leaves leave the second field 0 (`lf-term-leaf`, `lf-level-succ`,
  `lf-level-param`); name entries are four cells whose identities "are
  issued but unused" (`src/core/names.fs`).
- F3. Names are found by a linear scan of all entries (`lf-name-find-str`),
  and the first checker finds a constant by scanning the input names below
  its slot (ADR 0012 E5). Constant references hold at most 8 universe
  arguments; Mathlib needs 30.
- F4. `src/import/ndjson.fs` decodes every record of an export and hands it
  to a handler per kind; it holds one line at a time.

### From Lean 4.35.0

Read from the pinned toolchain's sources (`src/lean/` of
`leanprover--lean4---v4.35.0`, identical to tag `v4.35.0`, commit
`eb6cafb7…`) and, for the C++ kernel, from
`raw.githubusercontent.com/leanprover/lean4/v4.35.0/` on 2026-11-02;
hashes under Reproduction.

- L1. `src/Lean/Expr.lean` lines 119–131 document `Expr.Data`, a `UInt64`
  (line 132), as a 32-bit hash, an 8-bit `approxDepth` ("used to minimize
  the number of hash collisions"), four 1-bit flags (`hasFVar`,
  `hasExprMVar`, `hasLevelMVar`, `hasLevelParam`) and a 20-bit
  `looseBVarRange`; the accessors (lines 137–159) read the hash from bits
  0–31, the depth from bits 32–39, the four flags from bits 40–43 and the
  range from bits 44–63. Outside `Expr.lean` the depth is used only by the
  elaborator, tactics and printer as a cheap size threshold (for example
  `src/Lean/Meta/PPGoal.lean` line 64).
- L2. `Expr.mkData` (lines 170–172) is implemented by `lean_expr_mk_data`
  in `src/kernel/expr.cpp` lines 105–115: the depth is capped at 255
  (line 106); a range above 1,048,575 = 2²⁰ − 1 stops Lean with "too many
  bound variables" (lines 107–109); the fields are packed by shifts
  (lines 112–114). `lean_expr_mk_app_data` (lines 120–126) builds an
  application's word from its children's: depth + 1 capped at 255, the
  larger range, the flags or-ed.
- L3. The word is a computed field of every `Expr` (`Expr.lean` lines
  471–513): a bound variable `#i` has range *i* + 1; a binder's range is
  the larger of its type's and its body's minus one (never below zero),
  since the binder itself binds one variable; constants and sorts
  set "has level parameters" from their universe levels; the hash of a
  binder covers its type and body, not its name or binder information.
- L4. Every Lean object starts with an 8-byte header (`include/lean/lean.h`
  lines 161–166). An application is therefore about 32 bytes: header, two
  8-byte pointers and the data word (from the layout, not measured; Lean's
  allocator adds its own overhead).
- L5. Lean's environment stores imported constants in a flat hash map and
  only the current file's in a persistent one ("HashMap is faster than
  PersistentHashMap", `src/Lean/Data/SMap.lean` lines 20–41).
- L6. `PersistentHashMap` is a 32-way hashed trie: `shift := 5`,
  `branching := 2 ^ shift`, `maxDepth := 7`
  (`src/Lean/Data/PersistentHashMap.lean` lines 44–46).

### Where Lean's kernel spends its time (measured the same day)

From [the kernel profile](../development/measurements/lean-kernel-profile-2026-11-02/README.md)
and [SCALE_ASSESSMENT.md, last section](../project/SCALE_ASSESSMENT.md#where-leans-kernel-spends-its-time-and-what-leanforth-should-do-about-it)
(perf on `leanchecker --fresh` for `Init`, `Std` and a 224,291-constant
Mathlib slice):

- P1. Instantiation and abstraction take 39–42% of the time; Lean builds a
  fresh hash map for every `instantiate` call, keyed by node and binder
  offset, and that memo alone is 14–16%.
- P2. Allocation, reference counting and freeing take 21–23%; destroying
  each declaration's caches 5.5–6.7%; re-sharing each theorem before
  checking it 5–6%; structural comparison and hashing of terms 7–8%.
- P3. Looking constants up by name takes 5–8%; substituting universe levels
  into a constant's type, body or recursor rule 12–14% (nanoda: 17%).
- P4. The typing rules themselves take under 6%. Time follows the number
  of distinct sub-terms, at about 2–7 µs per node (3.0 µs on average for
  `Init`).
- P5. nanoda spends 38% of its time building nodes, with two hash lookups
  per new node (the export's table, then the declaration's).

### Measured with the prototype (2026-11-02)

Full tables in [the measurements](../development/measurements/compact-store-2026-11-02/README.md).
`gforth-fast` (Gforth 1.0) unless stated; the machine also ran other jobs,
so times vary by about ±20%.

| | `Init` | `Std` | all of Mathlib |
| --- | ---: | ---: | ---: |
| Expression nodes (export) | 6,099,054 | 9,539,642 | 105,894,257 |
| Duplicates found by hash-consing | 0 | 0 | 0 |
| Bytes per node: record / hash-table slot | 16 / 5.5 | 16 / 7.0 | 16 / 10.1 |
| Input tier, all parts, bytes in use | 0.14 GB | 0.24 GB | 2.94 GB |
| Load, `gforth-fast`: table growing / pre-sized | 14.4 s / 12.1 s | 22.7 s / — | 328–383 s / 256 s |
| Load, `gforth` | 32.0 s | 61.4 s | not run |
| The reader alone, `gforth-fast` | 6.3–6.9 s | 9.6–10.0 s | 103 s |
| Peak resident memory of the whole run | 0.23 GB | 0.37 GB | 4.16 GB |
| Expression table: load factor; slots compared per insertion | 0.73; 2.6 | 0.57; 2.2 | 0.39; 2.6 |
| Name lookups by text (every declaration) | 0.032 s | 0.10 s | 0.61–0.69 s (729,263) |
| Walk with a visited cache: visits, time | 12.1 M, 1.0 s | 20.0 M, 2.0 s | 226.7 M, 21–22 s |
| Walk without a cache | 764.5 M, 25 s | over 1.3×10⁹ (2 capped at 10⁸) | 1.3×10¹⁴; capped at 10⁶ per declaration, 11.4×10⁹ in 364 s |
| Nodes reachable only from theorem proofs | 82% | 78% | 71% |

The load was verified. For all three exports the prototype re-emitted
every name, level and expression record from the packed store, and the
result equals the reader's own field dump (`tests/core/ndjson-dump.fs`),
line for line (6.4 M, 10.1 M and 110.2 M lines; SHA-256 per family in the
measurements). The data words agree with an independent Python
computation for `Init` and `Std`. A planted fault (the hash-consing
comparison ignoring one child) was caught by the re-emission. The
Forth-2012 fallback of `u32.fs`, forced, gave the same `Init` digests.

**Gforth's cost of building a node and of a substitution step** (the
kernel profile's open question; `bench.fs` on `Init`, `gforth-fast`, with
a scratch tier as in C3 and the memo of C4):

| Operation | Input table 73% full | Input table 36% full |
| --- | ---: | ---: |
| Build a new application node with input children (input probe misses, scratch insert) | 1,740 ns | 646 ns |
| Build a new application node with a scratch child (scratch probe only) | 264 ns | 245 ns |
| Build an application node that exists in the input (input probe hits) | 612 ns | 351 ns |
| One instantiate step (a visited node with loose variables, its memo lookup and its build) | 508 ns | 404 ns |

Instantiating the body of each of `Init`'s 535,415 lambdas with a closed
term made 93.1 M steps and 52.3 M new nodes. Plain `gforth` is about 2
times slower (869 ns per step). For comparison, Lean's kernel spends about
3 µs per distinct node on all of its work (P4), of which substitution is
about 40%; a Forth step of 0.4–0.5 µs is the right order of magnitude but
not yet fast. These are prototype figures: the words are untuned and each
field access goes through several small words. A miss against a full input
table is the dearest operation, hence C4's rule to seal it at most half
full.

## Decision (proposed)

### C1 The node record: 16 bytes, four packed 32-bit fields

```text
field 0  head   bits 0-4 tag            bits 5-31 payload (27 bits)
field 1  a      first operand (an index, or a small number)
field 2  b      second operand
field 3  data   bits 0-19 loose bound-variable range (exact, as Lean's)
                bit 20 has universe parameters
                bit 21 has free variables (scratch only; 0 in the input)
                bits 22-31 approximate depth, capped at 1023
```

A field is an unsigned number 0 … 2³²−1 read and written only through
`u32@` and `u32!` (C7); bit fields are shifts and masks of that number, so
the layout is defined by arithmetic, not by byte order. Records are 16
bytes, so four fit a 64-byte cache line and, on an arena that starts on a
16-byte boundary, none straddles two.

| Kind (share of Mathlib's nodes) | Tag | Payload | a | b | Data used |
| --- | --- | --- | --- | --- | --- |
| application (85.5%) | 1 tag | unused | function | argument | all |
| lambda (7.8%) | 4 tags, one per binder information | binder name | binder type | body | all |
| Pi, `forallE` (5.1%) | 4 tags, as lambda | binder name | domain | body | all |
| constant (1.35%) | 1 tag | its declaration, resolved when the input is sealed (C4; not yet read by the checker, whose feed builds references by name: C9 steps 4-6) | name | universe-argument list | parameters flag |
| `letE` (0.23%) | 2 tags (dependent or not) | name | type | value | all; a second record holds the body |
| projection (0.04%) | 1 tag | structure's type name | the structure | field index | all |
| `natVal`, `strVal` (0.02%) | 1 tag each | unused | literal number | unused | none |
| `Sort` (0.002%) | 1 tag | unused | level | unused | parameters flag |
| bound variable (0.0003%) | 1 tag | unused | de Bruijn index | unused | range = index + 1 |
| `mdata` (none in exports) | — | — | — | — | refused as unsupported |
| free variable (scratch only, if chosen) | 1 tag | unused | variable number | unused | free-variable flag |

Unused parts: the payload of applications (27 bits on 85% of nodes,
reserved, for example for an application's argument count), `b` of leaves
and literals, and the second record of each `letE` (3.9 MB in Mathlib).
**Not stored:** Lean's 32-bit hash, because the hash of a hash-consed node
is recomputed in a few instructions from its tag, payload and child indices
whenever needed (C4); Lean's two metavariable flags, because kernel input
has no metavariables; and an identity cell (see the owner's questions).
Lean needs a stored hash because it does not store each term once: its
tables and its structural comparison (P2) must recognise equal terms that
are different objects. Once equal terms are one node, a node's number is
its identity, and a hash of (tag, payload, child numbers) finds it; the
kernel profile's recommendation to store a hash computed from the
children's hashes is met this way without the 4 bytes per node (0.42 GB
for Mathlib).
Binder names, binder information and `letE`'s non-dependence flag do not
affect typing in Lean's kernel, but are kept so that the stored term is
exactly the term read (ADR 0012 E1: the checked claim is the stored claim)
and can be printed and re-emitted. Limits, each reported as *full* when
reached: 2³² − 1 node numbers for the input and one scratch tier together
(C3), 2²⁷ names (Mathlib has 4.24 M), range 2²⁰ − 1 (Lean's own limit,
L2).

**Levels** use the same 16-byte record (tags zero, successor, `max`, `imax`,
parameter; payload: the parameter's name; `a`, `b`: children; data: the
"has parameters" bit). Mathlib has 47,805.

### C2 Names, universe lists and literals

- **Names**: 16-byte records — tag (string or number) and byte length;
  prefix name; byte offset of the string (or the number, which fits 32
  bits in all of Mathlib); a stored 32-bit hash of (prefix, component),
  since recomputing it would read the bytes. String bytes live once in a
  byte pool, copied with `MOVE` and compared with `COMPARE`. Interned: equal
  names are one number.
- **Universe-argument and parameter lists**: a list arena of 32-bit fields,
  `[n] [item 1] … [item n]`, interned like nodes, so a constant node stores
  one list number. No fixed limit (Mathlib's longest is 30; plan 6.2.0).
  Mathlib has 152,089 distinct lists in 2.9 MB.
- **Literals**: `natVal` digits and `strVal` UTF-8 bytes in a byte pool,
  interned by content (24,845 in Mathlib, 3.2 MB); big numbers become limbs
  when the big-number module exists (plan §6.8).
- **Declarations** of the input: 32-byte records (kind, name, parameter
  list, type, value, hint data, recursor rules, next declaration of the
  same name); the environment's slots stay as ADR 0012 E2 defines them.

### C3 Two tiers

- **Input tier**: everything decoded from the export — names, levels,
  lists, literals, nodes, input declarations and the expression hash index.
  The importer fills it before checking starts, then seals it: no record or
  table entry changes afterwards, so every worker reads it without locks
  (ADR 0009 decision 3; ADR 0012 E1 and E7; plan 7.2.1). It has no
  identities and no marks.
- **Scratch tier**, one per context: the same record layout, for the terms
  one check builds. Node numbers continue after the input's: a number below
  the input count names an input node, a larger one a node of this
  context's scratch. Scratch nodes may point at input nodes, never the
  reverse. Building a node whose children are all input nodes first looks
  it up in the input's table (read-only), so a rebuilt term that already
  exists in the input gets the input's number; then, and for every other
  node only, in the scratch table. A node with a scratch child cannot be in
  the input (its child would have been found there), so it skips the input
  probe: each new node costs one probe sequence per table it can be in, not
  nanoda's two lookups for every node (P5). Measured while instantiating
  every lambda body of `Init`: 51% of builds skipped the input probe, and
  86% of the input probes found an existing input node.
- **Memory is a region per check.** The tier is emptied when the check ends,
  whatever the outcome (ADR 0012 E4), by resetting its count and advancing
  the epoch of its tables and caches: no reference counting, no freeing of
  single nodes, no destruction of caches, the costs that take 21–23% and
  5.5–6.7% of Lean's time (P2).
- **Marks inside a check** stay LIFO, as `store-mark` and `store-rollback`
  are used today: rolling back to a mark returns the nodes made since and
  removes their table entries. With linear probing, undoing insertions in
  reverse order from a log of their slots restores the table exactly; if
  the table grew since the mark, it is rebuilt from the surviving nodes. A
  mark is valid exactly while it is on the tier's mark stack, which replaces
  the per-record identities that `store-mark` checks today.

### C4 Hash tables

- **One kind of table**: open addressing with linear probing over 32-bit
  slots holding a record number + 1 (0 is empty); the number of slots is a
  power of two; the table doubles when one more entry would pass 3/4 full,
  re-inserting every entry by its recomputed hash. A hash match is only a
  hint: an entry is equal only when its record compares equal field by field
  (plan §6.2), never by comparing sub-terms. Measured: 2.2–2.6 occupied
  slots compared per insertion while loading.
- **The input's table is sealed at most half full.** A lookup that misses
  reads every occupied slot of its run, each a node record elsewhere in
  memory, and scratch builds mostly miss. Measured on `Init`: building a
  node whose children are input nodes cost 1.7 µs against an input table
  73% full and 0.65 µs against one 36% full. Sealing rebuilds the table at
  the smallest power of two that is at most half full (Mathlib's is already
  39% full: 2²⁸ slots, 1.07 GB).
- **Why open addressing rather than chaining**: chaining needs a "next"
  field per entry (4 more bytes in every node, +25%) and scatters a lookup
  over memory; open addressing keeps a lookup within one or two cache lines
  (16 slots each), the table can be rebuilt or dropped without touching the
  records, and undoing insertions is exact (C3). Deletions, the weak point
  of linear probing, happen only by that undo.
- **The hash**: Murmur3's 32-bit finaliser (`fmix32`) applied to the fields
  in turn, every product masked to 32 bits, so 32- and 64-bit hosts compute
  the same values; strings are hashed byte by byte (FNV-1a), a word to add
  to `src/lib/bytes.fs`, the text module. Hash values are never written to
  files or used as identities.
- **Hash-consing** of nodes, levels, lists, literals and names, keyed by
  the whole record. Soundness never depends on it: two different numbers
  never mean "different terms"; equal numbers always mean equal terms,
  because only an equal record is ever returned. Hash-consing extends the
  exporter's sharing across declarations and to the scratch tier.
  Measured: the exporter already shares every equal node of the three
  exports; LeanForth does not rely on that.
- **Names to declarations** (replacing ADR 0012 E5's scan): since names are
  interned on reading, the table is a plain array indexed by name number,
  holding the newest input declaration of that name; each declaration
  record holds the previous one of the same name, so E5's rules see every
  earlier declaration of a name. 17 MB for Mathlib; all 729,263 lookups
  take 6.7 ms. ADR 0012 already requires the index to be checked against
  the scan in tests.
- **Constants resolved at load** (P3): sealing writes into each constant
  node's unused payload the number + 1 of the one input declaration of its
  name, or 0 when there is none or more than one (then the array and chain
  above decide). The payload is not part of the node's hash-consing key.
  Inferring a constant's type, unfolding it and reducing a recursor then
  need no name lookup; whether the declaration is final, accepted and
  earlier than the current one is still checked as E5 requires.
- **Caches** (plan §6.4), per context: inferred types (node → node, per
  mode), weak-head normal forms (node → node), and pairs shown equal or
  apart ((node, node) → outcome). Same table design with 8- to 16-byte
  slots; keys are node numbers, hashed with `fmix32`. Emptied with the
  scratch tier at the end of each check (an epoch number per slot makes that
  free). Never stores *unknown*, *exhausted*, *invalid* or *full* as
  success; verdicts must be identical with caches turned off (plan §6.4),
  and every cache counts its hits and misses (Lean's cannot be counted).
  Keeping successes about input-only terms across checks is a later
  optimisation that ADR 0012 E3 already permits.
- **Substitution memos** (P1, P3): one reusable table per context for
  instantiation, lifting and lowering, keyed by (node, binder offset), and
  one for universe substitution, keyed by (node or constant, interned level
  list); both emptied by the epoch, never allocated per call. Only nodes
  that can change are looked up: a node whose loose range shows it has no
  variable at or above the offset, or with no universe parameters, is
  returned unchanged before any lookup. Measured on `Init` (all lambda
  bodies instantiated): 23% of visits were skipped that way and 30% of the
  rest answered by the memo.

### C5 Growth and running out of memory

- Arenas and tables live on the heap (`ALLOCATE`, `RESIZE`; plan 1.1.5).
  Records are addressed by number, never by address, so `RESIZE` may move
  them; the rule is "never hold a record's address across an allocation"
  (plan §6.3).
- The input tier grows by doubling while it loads (one task), is trimmed to
  size when it is sealed, and never grows afterwards. Pre-sizing from the
  file size (about 59 bytes of export per node) avoids most re-hashing.
- Scratch tiers grow by doubling; only their own task reads them.
- Storage that other tasks read while it grows — the environment's slots,
  written by the publisher during parallel checking — uses fixed chunks
  reached through a directory, so a slot already written never moves
  (ADR 0012 E7).
- An allocation that fails leaves the store unchanged (Forth-2012 `RESIZE`
  keeps the old region) and gives **full** (ADR 0008), never a crash: the
  import reports a limit, a check ends *full*. So do the limits of C1.

### C6 Memory budget for all of Mathlib

From the measured counts (bytes in use; the prototype's figures):

| Part | Size |
| --- | ---: |
| 106.1 M node records × 16 B (with 242 k `letE` body records) | 1.70 GB |
| Expression hash table, 2²⁸ slots × 4 B (39% full) | 1.07 GB |
| Names (4.24 M × 16 B), name bytes, name table | 0.12 GB |
| Input declarations (729 k × 32 B), name-to-declaration array | 0.04 GB |
| Levels, lists, literals and their tables | 0.01 GB |
| **Input tier** | **2.94 GB** |
| Loading aids, freed after load: export-index maps (4 B per record) | 0.44 GB |
| Per worker: scratch tier and caches | not yet known; the assessment's 0.25–1 GB |

Six workers at 0.5 GB each would bring a run to about 6 GB, within this
machine's 25 GB available. The largest declaration reaches 95,123 distinct
nodes (1.5 MB of records); how many new terms a check builds is unknown
until the checker runs.

**Dropping theorem proofs after their check.** 75.5 M of Mathlib's 105.9 M
nodes (71%) are reachable only from theorem values. Freeing them would
leave about 30 M nodes, roughly 0.8 GB with their table. It is not part of
this design, for three reasons: Lean's kernel may unfold a theorem (ADR 0012
fact 6, recording ADR 0011 fact 2; the owner decides in phase 4, G5), so a
later check may need a proof back; a flat arena cannot free nodes scattered
through it, and whether a node is used only by proofs is known only after
the whole file is read, so it would need a first pass over the file to mark
them (1 bit per node) and a separate region for proof-only nodes; and the
whole input fits without it. The kernel profile reports that no theorem's
proof was unfolded in the corpora it measured, which makes dropping proofs
likely to be safe in practice, but G5 decides. Revisit it if a corpus does
not fit in about half of RAM (Fermat's Last Theorem with Mathlib is
reported to have 1.4 times Mathlib's constants and a 6 times larger
export).

### C7 Portability: the 32-bit access module

- `src/lib/u32.fs` (new, in this change; listed in `BYTE_MODULES` of
  `scripts/check-portable-forth.py`) is the only module that reads or
  writes memory in 32-bit units. `u32@ ( addr -- u )` and
  `u32! ( u addr -- )` use Gforth's `l@` and `l!` (both Gforth 0.7.3 and
  1.0 have them; `ul@` is obsolete in 1.0) after a check while loading that
  they are unsigned 32-bit access. Elsewhere they are the Forth-2012
  `u32-bytes@` and `u32-bytes!`: four characters with `C@`/`C!`, least
  significant byte first, an order the module fixes. `u32s ( n -- au )`
  gives the size of *n* fields; `u32-mask` is 2³²−1 on a 64-bit host and
  −1 (all bits) on a 32-bit one.
- The two versions may order bytes differently; this is invisible, since a
  field is only ever read by the version that wrote it, records are never
  written to files (FORTH_STYLE §8), and hashes are computed from values.
- Tests: `tests/lib/lib.fs` runs both versions on every host (round trips of
  boundary and 1,000 random values, neighbouring fields untouched, sizes),
  so `make test` covers them on Gforth 1.0 and, with `GFORTH=` the 0.7.3
  wrapper, on 0.7.3. Defining `lf-u32-portable` before loading forces the
  fallback for a whole program; the prototype loaded `Init` that way with
  the same digests, its load 1.1–1.4 times and its walks 2.6 times slower.

### C8 Rules that keep it sound

- Every record is checked when it is built: children point to existing
  nodes of the same or the input tier, tags and payloads are in range, the
  data word is computed from the children (never read from input). After
  that, "every stored node is valid" is an invariant of the tier, and the
  per-call whole-graph audits of today's code can go (assessment §5 item 4).
- Hash-consing, caches and the name index only make things faster: a wrong
  or missing entry costs time, never a verdict (C4). Tests run with them
  disabled and compare verdicts.
- No host address, cell layout or hash value is ever serialised.

*Note (2026-11-11, compact-store plan step S2, [kernel] review pending):*
today's term and level stores already read this way. A pass checks a
store's whole header (shape, seal, generation, count) once, at its root:
a handle (`lf-hterm-valid?`, `lf-hlevel-valid?`), `lf-term-root?`,
`lf-level-root?`, the pair checks or the count checks. Every read after
that (`lf-term-read`, `lf-term-valid?`, `lf-term-identity`, their level
twins and every walk's visit through `node-read`) checks only that the
index is allocated, `store-at?`: index < count <= capacity, which keeps
a read inside the block even when the count alone is corrupted. A pass
on a store with a broken seal or a poisoned generation is refused at its
root. C1's data word exists as an interface, `lf-term-data@`
(`src/core/terms.fs`), served by `src/kernel/caches.fs`'s skeleton memo
until step S3 keeps it in each record; tests reach records and identity
serials only through `tests/support/store-faults.fs`, so S3 can change
the layout in one file.

*Note (2026-11-11, compact-store plan step S6 (c), [kernel] review
pending; ADR 0014 Amendment 4):* "every record is checked when it is
built" does not yet cover all the structural audit reads (a constant's
stamp and live reference, the parameter context, a free variable's
entry), so the audit keeps every call site and drops only its repetition:
in a check a node is audited once per epoch, kept in its marks unit with
its identity (a rolled-back index made again is a new node), the epoch
following the generations the audit reads and, for nodes with a free
variable, the local context's. V1 and U2 now read the root's data word,
which S3 computes from the children at build, and walk only a root it
does not clear. The per-call graph walks of the audits are gone in the
common case; the call sites go when S4 and S5 make the remaining facts
part of the record (C1's constant payload, the tier's seal).

### C9 Migration and the plan tasks it covers

1. `src/lib/u32.fs` (done here) and a heap arena and hash-table library in
   `src/lib/` with `store:`'s checks and *full* on failure (plan 1.1.5,
   gaps 3, 4, 15–17 of plan §6).
2. The importer stage (plan 3.2.1): the prototype's handlers become
   `src/import/` code filling a sealed input tier from the NDJSON reader,
   with export-index maps; capacities become growth with a memory limit
   (plan 3.3.1).
3. Today's `store:` users move one at a time without behaviour change:
   `lf-terms`, `lf-levels` and `lf-names` keep their words
   (`lf-term-read`, `lf-term-tag@`, `lf-term-first@`, …) with the same stack
   effects, implemented over the compact records, with the five current
   term tags mapped onto C1's; modules that save and restore
   `lf-term-count` switch to marks. Every existing test and pinned-Lean
   comparison must give the same outcomes and fuel. Identity cells remain
   only where today's handles check them, until ADR 0012's environment
   handles replace them.
4. Names are interned through the hash table and constants found through
   the name-to-declaration array, checked against ADR 0012 E5's scan.
5. Universe lists become variable-length (6.2.0); walkers use explicit
   stacks sized from the data word's depth (6.2.0).
6. Caches, the substitution memos and one-probe node building (6.2.1–6.2.2,
   plan §6.4), each tested with caches off; the build and instantiate costs
   measured here (`bench.fs`) are the baseline the implementation is
   measured against (plan 6.5.1).

When implemented this covers plan tasks 1.1.5, 3.2.1 and 3.3.1 in part,
6.0.1 (this record turns the scale report into a design and a budget),
6.2.0 for universe lists, and 6.2.1–6.2.3; file-backed storage is not
needed (Rejected alternatives).

**Progress (2026-11-03).** Described in
[FORTH_LIBRARY.md](../development/FORTH_LIBRARY.md#the-compact-store).

- Step 1, done as library code, not yet used by the checker: growable heap
  stores with marks (`src/lib/slab.fs`, plan 1.1.5), hash tables
  (`htab.fs`), the C4 hashes (`hash32.fs`), hash-consed sets in two tiers
  (`cons.fs`) with interned lists and texts (`pools.fs`), standalone
  libraries; and the Lean layer of C1–C4 in `src/core/compact*.fs`: names,
  levels, variable-length universe and parameter lists (6.2.0's lists, no
  fixed limit), literals and 16-byte expression records, an input tier
  sealed read-only and scratch tiers with marks. Every record is checked
  when built (C8). A failed `ALLOCATE` or `RESIZE` and every C1 limit give
  *full* (C5). Two details differ from the text above. A mark is valid
  while its entry is on a stack of marked counts, and marks at one count
  share an entry, so a slab's marks behave exactly as `store.fs`'s (C3).
  Rolling back removes each given-back record from the table by Knuth's
  Algorithm R, whatever the table's growth since, instead of an undo log
  (C3).
- Step 2, done (2026-11-03) as the importer stage, not yet read by the
  checker: `src/import/stage.fs` and `stage-records.fs`, loaded by
  `src/main.fs`, fill an input tier from the NDJSON reader with the
  export's manifest checked by default, with the export-index maps, every
  declaration as C2's 32-byte record (kind and flags, name, parameter
  list, type, value, height, a tuple of the kind's other data — `all`,
  an inductive type's counts and constructors, a constructor's, a
  recursor's rules — and the previous declaration of the same name), the
  name-to-declaration array, and constants resolved at sealing as C4
  says. Details differ in three ways. A constant whose name no
  declaration of the export has makes sealing *invalid* (fail-closed;
  Lean's exporter never writes one). An `mdata` expression is staged
  without its data under a tag of its own (20) and every declaration
  that holds one is marked, instead of refusing the whole export
  (*unsupported*), so an export written with `--export-mdata` still
  loads and only those declarations are refused. A failed read rolls the
  stage back to empty through a tier mark. Capacities are growth with an
  optional byte limit (*full*; plan 3.3.1 in part). It stages `Init` with
  its manifest in 16.4 s (218 MB peak) and all of Mathlib in 326 s
  (3.41 GB peak; input tier 2.949 GB, 736,276 declaration records in
  23.6 MB, the array 17.0 MB); every one of Mathlib's 729,263 named
  declarations is found by its name, and all 1,426,722 constants are
  resolved ([NDJSON_READER.md, "Staging"](../development/NDJSON_READER.md#staging-into-the-compact-store)).
  Every fixture export of `tests/` and `Init` round-trip through it, the
  declarations included.
- The release hook step 3 needed is done (2026-11-03): `context-teardown`
  in `src/lib/context.fs` lets a scratch tier be a context member,
  freed by `context-free` ([ADR 0009, Amendment 1](0009-reentrant-state-and-parallel-checking.md#amendment-1-2026-11-03-context-members-that-own-heap-memory)).
- Step 3, done in part (2026-11-03, a [kernel] no-behaviour-change change;
  the review gate is open), with plan tasks 3.2.2 (v1) and 3.3.1:
  - The term, level, name, reference and declaration stores are heap stores
    (`store-heap-init` and `store-grow` in `src/lib/store.fs`: the header
    is a context member, the block grows by doubling up to the store's
    limit and is freed by a teardown word; growth that the limit, the heap
    or the test hook refuses gives *full*, nothing changed; when the
    block grew but a column of it then cannot, the record is refused as
    *full* with the block already grown, which is harmless). Their
    capacities are settings of each context (`lf-term-capacity!`,
    `lf-level-capacity!`, `lf-name-capacity!`, `lf-cref-capacity!`,
    `lf-input-capacity!`), defaults 64, 64, 64, 32 and 32 as before. Per
    index side data (the stamps of constants and Sorts, the passes' seen
    marks, images and memos, the printer's binder table) moved into
    columns that grow with their store (`src/lib/store-columns.fs`).
    Walk stacks, frames and binder contexts no longer follow the store's
    capacity: `lf-depth-limit` and `lf-level-depth-limit` keep them at 64.
  - Universe arguments are variable-length, in a pool after each
    reference's record (at most 64 per reference, was 8); a declaration
    takes 64 universe parameters (was 8). Plan task 6.2.0 (2026-11-04)
    removed these limits and the level context's: universe lists of any
    length, bounded by memory (see the plan's progress).
  - A context can attach a sealed input tier as its names
    (`lf-name-attach`): input names keep their stage numbers and need no
    per-call audit, new ones go to one scratch tier over the input,
    interned with them. The input keeps a name-to-declaration index, and
    under such a view the environment reads a name's chain instead of
    scanning every earlier declaration (E5 of ADR 0012, as C4 says);
    tests compare the chain with the scan (635 lookups of the fixtures,
    4,896 sampled in `Init`: no difference).
  - `src/import/feed.fs` gives a sealed stage to the checker in file
    order (plan 3.2.2): names through the view, levels, expressions and
    declarations copied into the context's stores, whose capacities it
    raises to fit.
  - Differences from the text above, to keep every verdict, fuel count
    and diagnostic: the context's own stores keep their three-cell nodes,
    identity cells and stamps, are not hash-consed and are counted and
    rolled back as before (handles check identities and stamps, tests
    corrupt raw slots, and hash-consing would move the points where a
    store fills), and the modules that save and restore counts by hand
    still do. The input's terms are copied, not read in place (about 80
    bytes per node with the columns), because the kernel reads terms and
    references through slot addresses and identities. Reading the input
    tier in place, hash-consed scratch terms and marks instead of saved
    counts remain for steps 3 to 6.
  - Evidence: every existing test passes and the pinned-Lean tables give
    the same verdicts; 2,000 random checker trials of 300 steps
    (`tests/support/checker-trial.fs`; 2,494,610 checker outcomes) give
    the same digest of every outcome, result, fuel, count and diagnostic
    as the code before the change, and a planted fault (term capacity 63)
    changes 30 of 50 trials; the failure-path suite injects refusals and
    THROWs into the stores' growth too (7,623 runs, every one fail-closed);
    nine new planted faults are caught. At larger capacities the three
    binder-domain rows that met the 64-node store get the table's answer
    (two rejected, D3+D4+D5; one unknown, K3), and the first-checker,
    binder-domain and universe-scope tables agree with no known difference
    (`lean-differential.py` tables `*-large`).
  - `Init` end to end with `gforth-fast`: staged with its manifest in
    16 s, fed in 80 s (59,349 declarations, 6,099,054 term nodes, 578
    levels, 56,957 references, 62 universe parameter names), checked in
    file order in 91 s at 100,000 fuel per declaration: 37 accepted
    (experimental, not independently audited; axioms: none), 0 rejected,
    59,025 unsupported (inductive types, literals and everything that uses
    them, K5), 162 exhausted, 73 unknown, 52 full, 0 invalid; peak
    resident memory 1.27 GB. At 10,000 fuel: 37, 0, 57,576, 1,618, 73, 45.
  - After the independent review rvKC (2026-11-04): the name order reads
    a fed stage's names (finding H1; before, ordering two universe
    parameters under the view was unknown), normalize counts its level
    frames and orders names iteratively (M1), level-make keeps its facts
    across calls and finds classes through an index (M2), and the store
    growth paths are tested shrunk and moved and ask the fault hook (M3).
    The first-checker, binder-domain and universe-scope tables also run
    fed, against pinned Lean (`test-*-fed-differential`). `Init` at
    10,000 fuel: 41 accepted, 0 rejected, 57,591 unsupported, 1,618
    exhausted, 54 unknown, 45 full (H1 had made 19 unknown: 4 are now
    accepted, 15 unsupported); fed in 11-14 s, checked in 9 s (38 s
    before M2), 1.27 GB peak. The 2,000 checker trials keep their digest
    in 5% fewer instructions than the code before the heap stores.
  - Marks instead of saved counts (2026-11-11, step S1 of the
    compact-store plan; no behaviour change, its [kernel] review pending):
    no module sets a store's count by hand any more. Every rollback point
    takes one joint mark (`src/core/scratch-marks.fs`): a store mark of
    the term, level and reference stores each, the local context's
    entries following their terms (they are made in node order). A
    rollback checks every family's mark first and refuses, *invalid* and
    nothing changed, a mark that is stale or of another store (C3); marks
    held in records are LIFO by construction, and two marks at the same
    position are not told apart (an out-of-order one then acts as a
    rollback to that position; pinned by a test row). Passes with a
    record keep the mark in it (inference's job, conversion, universe
    substitution, the probes); passes that hold only a number across
    their work (inference's steps on frames, the rebuild passes) push it
    on a mark stack per context that is strictly LIFO, so only the newest
    mark can be used. One difference from a tier mark: an inference step
    whose result is a Sort level it made gives back only its terms
    (`lf-scratch-discard`), checking every family's mark; once levels
    share the terms' tier (step S4) such a step must make its level again
    or keep its terms. Instantiation and opening read only nodes below a
    term-store mark instead of a saved count. Evidence: the first 1M
    lines of `Init` (`check --fast --fuel 100000`) give the same verdict
    and fuel lines and the same store capacities and allocation serials;
    the trial digest is unchanged (`abe54a7c0598`); 13 planted faults
    (a family left out, a mark out of order, a mark left on the stack)
    are caught.
  - Hash-consed compact term records (2026-11-11, step S3 of the
    compact-store plan, plan task 6.2.1; no verdict moves away from
    Lean's, its [kernel] review pending). A term is a record of four 32-bit fields
    (`src/core/terms.fs`): the checker's tag (its 13 tags, as before:
    a constant's fields a reference, a Sort's a level index), its
    first and second fields, and C1's data word, computed when the node
    is made (range, parameter bit, free-variable bit, depth; a range of
    all ones means no data: a leaf whose level or reference is not valid
    then, a concrete Sort, an unsupported form, and every node above
    one). `lf-term-data@` reads it. `lf-term-add` finds an equal record
    through a per-context table of `lib/htab.fs` and gives back the
    older node, or appends a new one and enters it; a rollback
    (`lf-term-rollback`, which the joint scratch mark and the input
    rollback use) takes the entries of the records it gives back out
    by Algorithm R, as `cons.fs` does; a reset empties the table; the
    feed sizes it from the stage's expressions. Differences from the
    plan's row, each for a reason:
    - The store stays a `store.fs` heap store with its 8-byte identity
      cells (the birth serials), seal, generation, capacity setting,
      marks and columns, with the table beside it, rather than a
      `cons.fs` set: a set's slab has no per-record identities and its
      marks are a mark stack, while handles, S1's joint marks and the
      fail-closed header tests need the store's. The table follows
      `cons.fs`'s rules (a hash is a hint; an entry is equal only when
      its allocated record is, field by field), so no answer depends
      on it. Moving onto `cons-extend` over the stage's tier is step
      S5, when identities retire.
    - Symbolic Sorts, constants and free variables are never shared
      (`lf-term-unshare`): their meaning is more than their fields (a
      Sort's and a constant's stamps, a free variable's local-context
      entry, which names its node by identity; a shared free variable
      would bring a dead one back as a new entry's). Contexts that keep
      data per node turn sharing off (`lf-term-sharing!`): the
      authoring words, the print command (binder names per node) and
      the old batch loader (a node per record).
    - The skeleton memo and key table are not retired. A node's number
      is its skeleton class only once levels and universe lists are
      interned (step S4): each universe substitution makes a new
      reference, and level nodes, per call, so two equal constants
      are two nodes and caches keyed by numbers would miss where
      skeletons hit. Measured on the first 1M lines of `Init`: with the
      caches keyed by node instead of skeleton, 142 fewer declarations
      are accepted (2 more run out of fuel, 140 that depend on them are
      unknown) and 18% more fuel is spent. Lean's node facts
      come from the data word: the caches' hooks ask the memo only for
      a node without data or with a free variable, whose liveness only
      the memo checks; for the others the word is the memo's facts (the
      same leaves known, the same rules, checked when the node is made).
      == of a node with itself no longer asks the memo.
    - Columns over every index of the term store: universe
      substitution's two (reached stamp, image) became a hash set of
      the call, emptied when its audit ends, and the sorted reached
      list with binary search for a child's image; the three stamp
      columns of constants and Sorts became a map from term index to a
      stamp unit, kept only for the nodes that have stamps. Level
      substitution's columns (over the small level store) stay until
      S4; the marking audits' marks and the open passes' results stay
      until S6 replaces those passes (audits only where input enters, a
      replace memo per call; since step S6 (c) the marks' units also
      hold the audit memo, plus a list of one run's nodes: C8's note);
      the printer's binder table
      (`src/present/binder-table.fs`, 40 bytes per node in every
      context of `bin/leanforth`) is not the checker's and stays a
      column (a candidate for the same map).
    - Natural literals keep every limb in their slab (a field is 32
      bits); a value, index or identity beyond 2³² − 1 is refused as
      *full* (C1's limits), so a negative or wider field cannot be
      stored any more.
    Identity under hash-consing (plan risk 3): a node rebuilt equal to
    an existing one is that older node. Rebuilding passes need only a
    live result with its identity (`lf-rebuild-identify`): a node the
    table gives back is allocated (rollbacks take their records'
    entries out), so live, and one made inside the pass is above its
    mark and goes with it on failure. Instantiation and opening read
    only nodes below their start mark: a node found below it is
    genuinely older, one the pass made is above it, as before. A store
    mark is checked by counts and identities, which a found node
    changes neither of. The caches keep a value with its identity, as
    before. The local context's entries stay in node order (free
    variables are never shared). The open passes no longer keep their
    bound-variable leaves while sharing (the store gives the live leaf
    back), so what a pass makes does not depend on an earlier check's
    leftovers. The derivation log copies an equal node once.
    Evidence: `make test` and `make check`; the 2,000 checker trials
    give main's digest (`6b6163500b54`) with sharing off, so the
    records, data words, literals, stamp map and reached set change
    nothing, and `902a42ce549d` with it on: 1,998 trials differ because
    node indices move and the trials' random choices follow them
    (outcomes over all trials: ok 1,165,166 → 1,166,038, invalid
    367,435 → 356,574, exhausted 470,759 → 476,867, unknown 403,346 →
    405,110, rejected 87,361 → 90,017, full 543 → 4). The first 1M
    lines of `Init` (`check --fast --no-manifest`, default fuel): the
    same verdict for every declaration (8,672 accepted, 518 unknown, 12
    exhausted); fuel 205,059,194 → 202,224,048 steps: 4,157 accepted
    declarations use less, none more (the largest change 1,451,797 →
    1,400,905, `Std.IterM.step_map`), because equal terms are one node,
    which the marking audits check once and == finds at once; fed nodes
    946,412 → 943,884 (let and projection leaves shared); peak resident
    memory 428 → 377 MB; check CPU 165.8 → 173.2 s (+4.5%: making a
    shared node costs about 0.4 µs against 0.1-0.2 µs unshared, and a
    rollback takes each record's entry out; measured, `gforth-fast`, a
    loaded machine). Full `Init` (same command): 21 verdicts move,
    every one to Lean's (Lean accepts all of `Init`), none away from
    it: 4 declarations that ran out of fuel are accepted with less
    (`Std.Iter.atIdxSlow?.induct_unfolding._unary`,
    `Std.Iter.forIn'_toList`,
    `Std.IterM.toList_filterMapWithPostcondition`,
    `Int.min_assoc._proof_1_1`), and 17 that were unknown only because
    they depend on those are accepted too: 54,535 → 54,556 accepted,
    94 → 90 exhausted, 4,720 → 4,703 unknown (every unknown a
    dependency of an exhausted root); fuel 1,546,142,904 →
    1,521,467,121; fed nodes 6,136,439 → 6,117,817; peak resident
    memory 1,580 → 1,279 MB; check CPU 1,384 → 1,408 s (+1.8%).
    Memory per term index, the printer's table aside: about 112 bytes
    before (24 record, 8 identity, 80 in columns) and 64 after (16
    record, 8 identity, 40 in columns: marks and open results), plus
    the table (4 bytes a slot, at most 3/4 full) and stamp units for
    about 1.4% of nodes. 9 new planted faults are caught (a collision
    taken for equality, an undo skipped, an equal node from a refusing
    store, a wrong data word, leaves without data words, shared free
    variables, a literal read from its slab index, the reached set
    kept, the binary search off by one); the faults of the code S3
    changed are re-targeted.
- Step S6 parts (a), (d), (e) (2026-11-11, agent S6A; ADR 0014
  Amendment 3, [kernel] review pending): C4's substitution memo
  (`src/kernel/replace-memo.fs`: one table per pass and context, entries
  keyed by node identity, offset and the call's stamp, taken out when an
  unstamped call ends) replaces the open passes' result column (24 bytes
  per term index), and every pass skips a node its data word shows
  unchanged.
  *Note (2026-11-11, agent PF; ADR 0014 Amendment 6, [kernel] review
  pending):* the memo keeps at most `lf-rmemo-cap` (2^20) stamped entries
  and is emptied when a stamped call begins above that, so on a term of
  more than about a million open nodes the closings inference remembers
  are lost. Inference closed an application's argument again for every
  substitution into a Pi body, which the arena's `let-ladder` paid 18.8M
  of its 39.0M units for; since Amendment 6 an argument is not closed for
  a body without loose bound variables (Lean's `instantiate` never reads
  it), and the copy a closing makes for a key takes its facts from its
  data word, without the free-variable memo's entries (the arena's
  `beta-ladder`: peak memory 1,111 → 804 MB).
- Interned levels, universe lists and constants (2026-11-11, step S4 of
  the compact-store plan, agent S4, branch `s4-levels`; ADR 0014
  Amendment 5; no verdict moves away from Lean's, its [kernel] review
  pending). Levels are hash-consed as terms are since S3: a table per
  context beside the level store (`src/core/levels.fs`), entries taken
  out by Algorithm R when a rollback gives records back
  (`lf-level-rollback`, used by the joint scratch marks and by level
  substitution's and normalization's own marks), the zero level entered
  at every reset. A constant reference is a name with its interned
  universe list (`src/core/constant-references.fs`): `lf-cref-new` gives
  back the live record of the same name, generation and level pairs, so
  the per-occurrence records are gone (one record per distinct constant
  of a check). Constants and symbolic Sorts are shared in the term table
  again, a found one given only while its stamps hold
  (`lf-term-reusable?`). So equal constants and Sorts are one node and a
  node's number is its class under Lean's `==`: the caches' skeleton
  memo and key table are retired and the result caches key a node by its
  identity (ADR 0014 Amendment 5). One switch, `lf-term-sharing!`,
  governs all three tables. Differences from the plan's row, each for a
  reason:
  - Levels and references keep their own `store.fs` stores beside the
    terms, not one tier, as S3 kept the terms' (identities, S1's joint
    marks, fail-closed header tests); the C2 list arena is not separate:
    a list is interned with its name, which is all equality of constants
    needs. One tier for all families is step S5.
  - So the symbolic-Sort and constant stamps stay: a store can still be
    reset or rolled back alone (tests, a level pass's own mark), and the
    stamps are what refuses a node whose level or reference went. They
    now also guard sharing: a found Sort or constant is given again only
    while its stamps hold, else it is made anew.
  - A constant's fields are (reference index, 0); the reference's
    identity is in its stamp unit, a full cell (review rvS36 L1: since
    S3 the 32-bit field made every constant *full* after 2^32 - 1
    references in a context). The audit reads the stamped identity.
  - Universe substitution skips a term whose data word shows no universe
    parameter (Lean's `has_param_univ`), and level comparison keeps its
    scope checks per level in a check (ADR 0014 Amendment 5); its own
    graph check stays (memoised per check since S6 (c)) until S5.
  Evidence: `make test`, `make check` (all Lean-compared tables the same
  verdicts) and `make test` on Gforth 0.7.3. The first 1M lines of
  `Init` (`check --fast --no-manifest`, default fuel, against main
  af93afb): with the caches keyed by node, every declaration keeps its
  verdict (S3 measured 142 fewer accepted when keyed by node before
  interning); with every part of the step 8,696 → 8,699 accepted, 501 →
  499 unknown, 5 → 4 exhausted, the 3 moves to Lean's verdict
  (`Array.extract_extract._proof_1_1` ran out of fuel, `Array.extract_extract`
  and `ByteArray.extract_extract` depended on it); fuel 109,613,586 →
  91,658,129 (−16%); check CPU 147.7 → 108.2 s (−27%); peak resident
  memory 313 → 266 MB. All of `Init` (same command, `--json`): 55,750 →
  55,772 accepted, 3,583 → 3,570 unknown, 16 → 7 exhausted; all 22 moves
  are to Lean's verdict (Lean accepts all of `Init`): 9 declarations that
  ran out of fuel and 13 that were unknown only through such a dependency
  are accepted, none moved away and no accepted declaration uses more
  fuel (53,419 use less; list `.claude/work/S4/init-moves.txt` of the
  agent's worktree); fuel 791,610,006 → 631,935,941 (−20%); check CPU
  1,045.7 → 807.4 s (−23%, `gforth-fast`, a loaded machine); peak
  resident memory 1,077 → 1,058 MB. The 2,000 checker trials:
  `056b65372109` → `e19c6368813f`, re-baselined: the trials' later random
  choices follow node indices and fuel, both of which move (fewer level
  and reference records, == and substitution spend less); outcomes over
  all trials ok 1,171,229 → 1,175,302, invalid 357,088 → 367,208,
  exhausted 467,820 → 457,164, unknown 407,009 → 406,080, rejected 91,459
  → 88,851, full 4 → 4. 29 planted faults `s4-*` (a level or reference
  hash collision taken as equal, a list interned twice, rollbacks and
  resets that keep entries, an equal record given where a new one would
  be refused, a found constant or Sort given again without its stamps or
  with a level or reference made again, a constant's identity in a
  32-bit field, a cache keyed by a stale node, a dead free variable under
  a node, == identity skipped, equal words taken as apart, a first pair
  taken as met, the parameter skip everywhere, the level memo without
  generation, identity or switch), all caught; three stale faults
  re-targeted; the nine on the retired skeleton memo removed.
- The input read in place (2026-11-11, step S5 of the compact-store
  plan, parts 1-3 of 5, agent S5, branch `s5-in-place`; plan task 6.2.2;
  no verdict moves, its [kernel] review pending). The term store has an
  *input view* (`src/core/terms.fs`): `lf-term-attach` makes a sealed
  stage tier's expressions the term numbers 0 .. N - 1, each the number
  the stage gave it, read in place from its C1 record, and the store's
  own records follow at N + r. A read translates the tag (the
  four binder tags of each kind to the checker's lambda or Pi: binder
  name and information are ignored, as Lean's kernel ignores them); the
  data word is the tier's (C1's, the same facts); a Sort, constant or
  literal takes the fields this context gave it (its level, reference,
  limbs or bytes) from a leaf table the feed fills. An input node is
  sealed: its identity is `invert` of its number (a negative number, no
  birth serial), its stamps are those the leaf table records, and the
  audit's marks for it are in a slab of the context. A node a check makes
  equal to an input node is that node: an application or bound variable
  is found in the tier's own table (C3's probe, through a set extending
  the tier that is never committed to), a binder in a name-blind binder
  table, a leaf in the leaf table by its fields. The feed
  (`src/import/feed.fs`) reads the stage in place by default and copies
  only what the view does not read -- a let, a projection, an `mdata`
  expression and every node above one, 2.7% of `Init`'s term numbers
  (167,638 records above 6,110,313 input numbers) -- in the checker's
  old shapes; a first pass enters every binder it reads in place, so
  that a let's lambda copied earlier than an equal input lambda is that
  lambda, as copying merged them (47 pairs in `Init`; without the pass
  22 declarations used more fuel in place, +920 in all). The copy of
  every expression stays behind a switch of each context
  (`lf-feed-copy!`, `src/core/input.fs`) and is forced for a feed with a
  binder hook: the print command keeps a column of binder names per term
  number. Part 3: the fixed scratch rooms above the input (1,048,576
  term nodes, 65,536 levels, 262,144 references) became a setting,
  `lf-input-room!` (0, the default: a check's scratch grows up to about
  2^31 records of each, *full* only when the heap refuses). Not done
  (parts 4-5, each its own task): native C1 shapes for lets and
  projections, so that nothing is copied; retiring the symbolic-Sort and
  constant stamps and the scratch identities under one tier mark (levels
  and references keep their own stores); the printer reading C1 records;
  deleting the copy. A cost added per input node: the audit's marks, 16
  bytes (about 1.7 GB for all of Mathlib), until step S6 (c) retires the
  marking audits; the binder table adds about 4 to 8 bytes per input
  binder. Also review rvS4's M1: rolling the input back takes the
  levels' and references' table entries out too (before, the tables
  kept one per record given back, growing with every declaration).
  Evidence: `make check`; every fed Lean table agrees; the CLI test
  `BothWays` compares the copied and in-place reports of 22 exports;
  the trial digest is unchanged (`f78118062cf9`, the trials use no
  feed). All of `Init` at the default 20,000,000 fuel, before the binder
  pass, with the fixed rooms: copied and in place both accept all
  59,349 declarations, and differ only in the fuel of those 22; peak
  resident memory 1,061 MB copied, 546 MB in place; feed 18.0 s copied,
  2.5 s in place; stage 13-15 s; check 998 s and 1,118 s (`gforth-fast`,
  a loaded machine). 23 planted faults `s5-*` (identity, leaf entry,
  probes, marks, stamps, fingerprint, detaching, copies, rooms, the
  binder pass, the literals' fields, rvS4 M1 and L1) are caught, and
  the faults of the code S5 changed are re-targeted.
- Lets and projections read in place, the copy retired (2026-11-11, step
  S5's parts 4-5, agent S5B, branch `s5b-native`; plan task 6.2.2; no
  verdict moves away from Lean's, its [kernel][import] review pending).
  - *Shapes.* A let is a binary node of its own, `LET(v, fun x : T =>
    b)`, tag `lf-tag-let` or `lf-tag-let-nondep` (Lean's `nonDep` flag,
    which `==` compares); a projection is `PROJECTION(leaf, e)`, tag
    `lf-tag-projection`, over today's projection leaf (name, index).
    Their children sit at the node's own depth (a binder is now a lambda
    or Pi only, `lf-term-binder-tag?`), so every pass that does not look
    at them walks them as binary nodes, and the places where Lean treats
    `Expr.letE` and `Expr.proj` specially (zeta and `reduce_proj` in
    `whnf_core`, `infer_let`, `infer_proj`, `is_app`/`get_app_fn`,
    `try_unfold_proj_app`, the parameter-uniformity walk, the printers,
    the authors' `$`) read them by tag; the audit also checks that a
    let's second child is a lambda and a projection's first a projection
    leaf. Before, a let was `app(app(leaf, v), lam)` (4 nodes for 2
    numbers) and a projection `app(leaf, e)`.
  - *Difference from C1's text and the plan row* (a letE record with
    three children, a proj record with one child and a payload): the
    checker's nodes keep two children each, a let's lambda being the
    third child's home. Every one of the checker's walkers and
    rebuilding passes (about 25, most of them frame steps) already
    handles binary nodes; ternary and unary nodes would need a third
    child path in each, for 0.27% of Mathlib's nodes. Lean's rules see
    the same terms either way.
  - *In place.* So that every child stays below its parent (the walks'
    `walk-child?`, rebuilding in ascending order), the view numbers the
    tier's record u as term 2u + 1 and what it carries as term 2u: a
    letE record's lambda (its type and the body its second record holds)
    and a proj record's leaf; `lf-term-base` is twice the expression
    count, and a let's body record and an mdata record are no term. A
    let, a projection and its leaf are leaves of the view's table, whose
    entries the feed gives: the let's lambda is the first input binder
    equal to it (an earlier input lambda, or its own), the projection's
    leaf the first input leaf of its name and index, so that equal nodes
    are one node as when copied and a check that makes one finds it (an
    equal lambda later in the file stays a node of its own: it comes
    after the let). The audit's units are one per tier record (a let's
    lambda uses its let's second record's) and one per leaf entry (a
    projection's leaf; about 24 MB for Mathlib, every leaf entry
    counted). The feed copies only an mdata expression and the nodes
    above it.
  - *The copy retired.* The copy of every expression and its switch
    (`lf-feed-copy!`, `lf-input-copy!`) are deleted, after the 22
    exports of the CLI's BothWays gave the same report both ways (now
    pinned as digests, AsCopied) and the 1M-line `Init` prefix the same
    9,202 verdicts (all accepted; fuel 98,211,787 copied, 98,211,880 in
    place: 11 declarations differ, 5 more and 6 less, an equal lambda
    after a let among the causes). The print command's side table reads
    an input binder's name and kind from its record
    (`lf-term-input-binder@`; a let's lambda has the let's name), so a
    feed with a binder hook reads in place too; the derivation log
    needed nothing (it names input objects by term number). The CLI's
    "term nodes" (`src/cli/check-run.fs`) now counts term numbers, about
    twice the expressions. After merging step S7 (parallel checking):
    its scheduler's dependency walk (`src/kernel/env-schedule.fs`) walks
    every binary node, lets and projections included (it missed their
    constants: planted fault `s5b-sched-skips-let`); its stamp array per
    term number (4 bytes) now spans twice the expressions, about 0.42 GB
    more for all of Mathlib, until it is indexed per record (as the
    audit's units are; plan task 7.2.1, "not done"); the worker contexts
    no longer copy the retired switch.
    Review rvS5B (agent FX11): a let the store builds now has the data
    word of Lean's letE and of the stage's input let (depth one more
    than the deepest of type, value and body: `lf-term-let-data`; it
    counted its lambda's level too), so Lean's `==` meets an input let
    and an equal store let with equal words. Chosen over masking the
    depth in `lf-meq-word`, which also weakens the hash test (pairs that
    differ only in depth are walked: measured fuel 518 to 532 on
    `Two`, 67 to 70 on `unfold`, 981 and others in `mixed-convert`).
    Pinned as `tests/core/check-declaration-ndjson.fs` and planted
    fault `let-data-counts-lambda`. The let arm of the uniformity walk is
    pinned by rows `uniform.let-other-argument` (rejected) and
    `uniform.let-uniform` (accepted) of `inductive-expected.lean`, both
    Lean's verdicts, and fault `ind-uniform-skips-let`.
  - *Stamps and scratch identities (part 2 of the step): none retired.*
    Symbolic-Sort stamps: level substitution and normalization roll the
    level store back alone by their own marks, and an inference step
    whose result is a Sort level gives back only its terms (S1), so a
    Sort node can outlive its level; constant stamps: the reference
    store is reset and rolled back apart from the terms (authoring and
    replay contexts, the input's rollback); scratch identities: handles
    (`generation-handles.fs`), the caches' values, the replace and audit
    memos and S1's mark checks read them. One tier mark covers all
    families only once levels and references are kept in the terms'
    tier, a step of its own.
  - *Evidence.* `make check` and `make test` on Gforth 0.7.3; every
    Lean-compared table the same verdicts; 22 new planted faults `s5b-*`
    (one replacing a fault on the retired switch) and 15 earlier ones
    re-targeted, all caught but two listed gaps (a let in a
    constructor type's uniformity walk; `try_unfold_proj_app`'s rows,
    whose fuel is not compared, a gap since task 5.2.2). All of `Init`
    (`check --fast --no-manifest`, default fuel, against main `6b3a518`):
    the same verdict for every declaration (59,349 accepted, as by
    Lean); fuel 664,030,007 → 663,857,513 (−0.03%), 7,194 declarations
    using less (at most 7,948 less) and 3 more (6 or 7 steps:
    `BitVec.zero_width_append`, `Std.Rio.toList_eq_ite_roo`,
    `Std.Ric.toList_eq_ite_roc`); peak resident memory 543 → 507 MB;
    stage 13.1 → 16.4 s, feed 2.1 → 2.5 s, check 1,078 → 1,437 s wall
    on a loaded machine (the 1M-line prefix run alternately with main:
    check 194 and 149 s CPU on main, 192 and 158 s here).
    Mathlib's first sixth (same command, 119,472 declarations): the same
    verdict for every declaration (119,374 accepted, 96 unknown, 2
    exhausted, before and after); fuel 3,385,277,118 → 3,384,047,970
    (−0.04%), 29,105 declarations using less and 4 more (36, 7, 4 and 1
    steps); peak resident memory 1,795 → 1,835 MB (+2%: the leaf entries
    of lets and projections and their audit units); stage 50.7 → 34.5 s,
    feed 7.2 → 5.3 s, check 6,420 → 5,034 s wall (machine load varied).
- Step S6 (b) and (c) are their own tasks.

## Amendment 1 (2026-11-04): constants Lean's kernel generates

*Context.* The owner approved plan task 5.2.1a on condition that, with no
flags, LeanForth's verdicts are exactly Lean's
([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md)). Lean's
`add_inductive` adds the recursors it generates to its environment --
`T.rec` for each type `T` of a block, `T.rec_1`, `T.rec_2`, ... for a
nested one -- whatever the export holds, so a declaration may use `T.rec`
in a file that never declares it (a tampered or hand-made file; lean4export
writes every recursor). Lean checks such a file; C4's sealing refused it as
naming an unknown constant (*invalid*).

*Change.* Sealing (`src/import/stage.fs`, `const-resolve`) keeps a
constant whose name no declaration has when the name is one the kernel
generates for a type of the file: its last part `rec` or `rec_<digits>`,
its prefix the name of a type declaration of the file. It resolves as a
name several declarations have (payload 0): the checked environment decides
at the check, from the type's slot (ADR 0015 decision 12: the recursor the
block generated, built again from its recipe, or no constant). Every other
name no declaration has is still an unknown constant: another last part
(`T.recOn`), a malformed one (`T.rec_`, `T.rec_x`), or a prefix that names
no type (a theorem, a constructor).

*Change (empty blocks).* An inductive record with no type, constructor or
recursor cannot come from lean4export, but Lean's kernel gives a verdict on
such a declaration: it rejects it (`emptyBlock`). The reader
(`src/import/ndjson.fs`, `v-types`) reads it (a block with no type but
with constructors or recursors stays malformed, *invalid*), the stage holds
it as any block, and the feed (`src/import/feed.fs`, `feed-empty-block`)
adds one input declaration for it, of kind `lf-kind-block`: no name, no
universe parameter, no type, no value, a member of its own block
(`core/input.fs`, `lf-input-empty-ok?`). The block check rejects it at
step 4, as Lean's `elim_nested_inductive_fn` does before anything else of
the declaration (diagnostic 78), and the file's other declarations are
checked as usual. The re-emitter writes the record back unchanged
(`ndjson-emit.fs`, `block-empty`).

*Evidence.* `tests/core/test_stage.py`: `B.rec` and `B.rec_1` (`B` a type
of the block fixture) load, resolved with payload 0; `B.recOn`, `B.rec_`,
`B.rec_x`, `t.rec` (`t` a theorem) and `A.mk.rec` (a constructor) stay
unknown constants (*invalid*), as before. The rows
`after.recursor-left-out-then-use-rec` and
`after.recursor-left-out-then-use-rec-no-level` of
`tests/reference/inductive-expected.lean` give Lean's verdicts (accepted;
`universeArity`, rejected), and so does `names.empty-block` (`emptyBlock`,
rejected). `tests/core/ndjson.fs`: an empty record is read and handed over
alone; one with no type but a constructor or a recursor stays malformed.
`tests/core/test_empty_block.py`: an empty block before the Bool block,
and two around it, are each rejected (diagnostic 78, step 4) while the
Bool block is accepted; a block with no type but a constructor leaves the
file *invalid*. `tests/core/test_ndjson_emit.py` re-emits the empty record
byte for byte. Seven planted faults (`stage-any-generated-*`,
`ndjson-empty-*`, `feed-empty-not-staged`, `ind-empty-*`) are caught. The
rest of C4, and every other refusal of the importer, is unchanged.

*Remaining difference, temporary (task 5.2.6).* Two kinds of file are
still refused as a whole (*invalid*) where pinned Lean 4.35.0 gives a
verdict per declaration (checked 2026-11-04): a file that names a constant
no declaration has, other than a generated recursor (Lean rejects the
declaration that names it: `unknownConstant`, by the kernel and in
replay; the rest of the file is checked), and an inductive record with
constructors or recursors but no type (Lean's replay refuses those:
"No such constructor", "No such recursor"). Plan task 5.2.6 makes the
importer stage them so that the checker gives those verdicts.

## Amendment 2 (2026-11-11): one input shared by a parallel check's workers

Step S8 of the compact-store plan (agent SH, branch `sh-shared-input`;
plan task 7.2.1; the owner's decision of 2026-11-11: "should be also for
other large libraries... or even all"). Storage only: no typing or
conversion rule changes, every verdict, diagnostic, fuel count and axiom
set stays (the verdict version is kept, ADR 0020 D3); its [kernel]
[runtime] review is pending.

*Before.* `check --jobs N` fed each of N worker contexts the sealed stage
again, so each held its own copy of the input's per-context part. For
Mathlib's first sixth (119,472 declarations, 35.3 M term numbers) one
context held 665 MB of it: the audit's marks of every input unit (16
bytes per unit, the slab doubled: 538 MB), the view's leaf and binder
tables (56 MB), the constant references (334,180; 44 MB) and the
declarations with their name index and inductive data (25 MB). All of
Mathlib at `--jobs 4` held about 19 GB, and feeding took about 7 s per
context for the sixth.

*Decision.*

1. **The audit's input marks are pages a check holds**
   (`core/constant-term-boundary.fs`). A unit is made in a page of 256
   units (4 KB) when first reached and listed; every check gives every
   page back when it begins (`lf-audit-afresh`, from `lf-check-begin`).
   A unit is read only by the marking run or the memo epoch that wrote
   it, and each check takes new run numbers and epochs at its start, so
   no mark outlives its check and giving the pages back changes no
   answer. The serial run gains too: a context holds only what its
   current check reached.
2. **A worker reads the driving context's input in place**
   (`import/feed.fs`'s `lf-feed-shared`, `cli/check-run.fs`):
   - the declarations, their name index and inductive data
     (`core/input.fs`'s `lf-input-borrow`: copies of three headers;
     written only while loading, then sealed);
   - the view's leaf and binder tables (`core/terms.fs`'s
     `lf-term-borrow`: copies of their headers, the hash tables frozen,
     so a find writes nothing, not even a statistic, and an entry cannot
     be added);
   - the constant references, as a tier under the worker's own
     (`core/constant-references.fs`'s `lf-cref-borrow`): numbers below
     the input's count are the source's records, read through copies of
     its store's, pairs pool's and (frozen) table's headers; the worker's
     checks make their own in its own store, numbered from that count,
     their pairs in its own pool after the source's. A reference sought is
     sought in the source's table first, then in the worker's own: as
     interning keeps one record per reference, at most one table holds
     it, and it is the record, under the number, that a context holding
     the whole input finds;
   - the stage's tier, read in place already (step S5), with the worker's
     own probe set over its frozen table and its own names' scratch tier.

   The worker makes only what its checks write beside or above the
   input: its levels (made from the stage as the feed makes them, so with
   the numbers and identities that the shared references' level pairs and
   Sort leaves name; 9,357 for the sixth), its level context and session,
   its literals' limbs and bytes (copied, since checks append to those
   slabs: 261 cells and 14,045 bytes for the sixth), and the feed's
   copies of mdata expressions and the nodes above them, if the source
   made any (none in Mathlib's export). Each copy is made with a horizon
   (`lf-term-horizon!`): it finds only the leaves the source's feed had
   entered when it made that copy, so it is the source's node (a test
   export, `tests/cli/jobs/horizon.ndjson`, copies a projection before
   its first input leaf). The worker's input fingerprint must then be the
   source's (`cli/check-run.fs`), else no worker is made and the run is
   the serial one.
3. **Nothing writes the shared input while jobs run.** The source makes
   nothing in its input's stores while workers read them (it publishes;
   every check runs in a worker) and outlives them (the scheduler frees
   them first); `lf-input-pristine?` refuses a source that made a
   reference since it sealed. The paths that could write the shared
   blocks are closed: adding a declaration or an inductive cell is
   refused after sealing, a leaf or binder entry or any growth of a
   frozen table is refused, a worker's reset first erases the copied
   headers (and makes empty stores of its own), and its teardown erases
   them before the teardown words that would free them. Test (`tests/cli/leanforth.fs`,
   "Shared input"): a digest of the blocks the workers read and of the
   fingerprint's parts but the names is the same after a parallel run as
   before it (the driving context may intern a name the checker looks up,
   in a scratch tier no worker reads).

*Why it keeps ADR 0012's rules.* E7's table always had the input as
"shared, written by the importer before tasks start, read by all"; it is
now true of the whole input, not only the stage. G-P1 (one writer): no
check writes the shared input; slots, records and the queue are written
as before. G-P2, G-P3, G-P5 and G-P6: the scheduler, publisher, readiness
sets and stops are unchanged (a worker that threw is freed, its copied
headers erased, and replaced by a new shared feed). G-P4 and
independence: each check still begins from the input alone with empty
caches, memos and marks (its own pages, given back), so its verdict,
diagnostic and fuel do not depend on its worker or the run's order, as
the measurements below confirm. G-P7: unchanged (the in-time witness).

*Measured* (2026-11-11, `check --fast --no-manifest --json --jobs N`,
`gforth-fast`, main `04f8d96` against the branch, run one after the other
on the 10-core WSL2 machine, which other agents' runs shared: load
average 12-23, so the wall times are noisy; peak resident memory from
`/usr/bin/time`). Every report is main's but for `measured`: the same
verdict, diagnostic, fuel and axiom set for every declaration, the same
counts and exit status; and at every N each report is the serial one.

| export, workers | peak memory, main → shared | feed (s) | wall (s) | CPU (s) | load |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Init`, 1 | 737 → 658 MB | 2.1 → 2.5 | 1,461 → 1,354 | 1,379 → 1,249 | 12-18 |
| `Init`, 4 | 1,525 → 957 MB | 14.3 → 2.0 | 547 → 511 | 1,416 → 1,439 | 18 |
| `Init`, 8 | 2,196 → 1,166 MB | 16.3 → 2.3 | 241 → 346 | 1,416 → 1,477 | 6-17 |
| Mathlib's first sixth, 8 | 7,710 → 4,688 MB | 129 → 8.2 | 3,243 → 2,773 | 7,930 → 7,930 | 15-22 |

`Init` (59,349 declarations): all accepted, fuel 663,921,845 in every
run; Mathlib's first sixth (`head -n 18482637`, 119,472 declarations):
119,374 accepted, 96 unknown, 2 exhausted, fuel 3,385,111,959, exit
status 3, both ways; the arena's 212 tests (bundle of 2026-11-10,
`--jobs 2`): every exit status and report the same. The `Init` run at 8
workers met different loads (6 for main, 17 for the branch); the CPU
time, less sensitive to load, differs by at most 5% and not in one
direction (the serial run used 9% less). A worker now costs `Init` about
64 MB (main: 182 MB), its scratch, caches and the mark pages of its
largest check; the per-worker cost left on the sixth is about 0.5 GB, the
scratch and caches of its largest checks, which sharing does not touch.
Repeated one after the other at load 17-25: `Init` at 8 workers 298 s
(main) and 263 s (shared), CPU 1,442 and 1,428 s; at 10 workers 244-481
s (three runs), at 12 threads on the 10 hardware threads (the pool's
size forced in a scratch copy: `--jobs` is cut to the cores) 233-326 s,
CPU 1,421-1,479 s either way, peak 1,221-1,280 and 1,314-1,356 MB. More
threads than hardware threads gave no gain beyond the noise: the slight
edge of 12 under load is CPU time taken from the other runs.

*Predicted for all of Mathlib at 8 workers* (729,263 declarations, 212 M
term numbers): from main's full run at 4 workers (`a43539e`, 2026-11-11:
peak 20,466 MB, stage 2,993 MB, check 20,199 s wall and 76,685 s CPU,
load shared) less the four extra copies of the input (about 2.5 GB each,
the sixth's 415 MB resident scaled by its term numbers), its per-worker
scratch is about 1 GB; so 8 workers sharing the input would hold about
13 GB (stage 3.0 + the driving context's input 0.8 + the scheduler's
stamps and the environment about 1.1 + 8 × about 1.05), against about 34
GB with a copy each. The CPU time is the sharing's as main's (the sixth:
the same), and the sixth's 7.1 busy cores at 8 workers on a quiet machine
(1,025 s check, 7,303 s CPU, ADR 0012 Amendment 2) give about 76,700 / 7.1
≈ 10,800 s of checking, plus about 260 s staging and 45 s feeding one
context (main: 207 s for five): about 3.1 hours on a quiet machine,
longer under load.

*Not shared, each worker's own:* its levels and level columns (about 1 MB
for the sixth), its names' scratch tier, the probe set, the mark pages'
directory (one cell per 256 input units: 0.5 MB for the sixth), the
literals' copy and any mdata copies. The scheduler's stamp array (4 bytes
per term number) is the driving context's alone. Planted faults `sh-*`
(seven; one a known defence in depth) and two re-targeted `s6c-*` are
caught.

## Consequences

- All of Mathlib's input fits in about 3 GB with one shared copy, so
  parallel workers cost only their scratch space.
- Loading becomes slower than reading alone: with the table pre-sized the
  prototype took 1.8 (`Init`) to 2.5 times (Mathlib: 256 s, about 4.3
  minutes, against 103 s) the reader's time with `gforth-fast`, and 3.2–3.7
  times on Mathlib when the table grew from small, because each doubling
  re-inserts every entry. The prototype is untuned; this is still a
  fraction of the checking time the assessment estimates (hours of CPU).
- The term printer, the importer and every kernel module read terms through
  accessor words, so the layout can change later behind them.
- Nothing about Lean's typing rules changes; this is storage only.

## Rejected alternatives

- **B-trees.** Built for keys kept in order on disk pages, with range
  queries; the checker only asks "is this exact key present?". A lookup
  visits log₍B₎ *n* pages and searches inside each, and inserting splits
  pages: more code and more memory reads than a hash table, for nothing the
  checker uses.
- **Balanced binary trees** (red-black, AVL). log₂ of 10⁸ is about 27
  dependent memory reads per lookup, and two child links per entry.
- **Trees without sharing.** One Mathlib declaration expands to 1.25×10¹⁴
  nodes (measured), 2 petabytes at 16 bytes each.
- **64-bit fields everywhere.** About twice the memory (the assessment
  estimates 6 GB for Mathlib) and half as many nodes per cache line;
  indices fit 32 bits with 40 times headroom.
- **Lean's 64-bit data word with its hash.** 4 more bytes per node
  (0.42 GB for Mathlib) that no lookup needs once the index is the term's
  identity; the record still has to be read to confirm a match.
- **A hash in each table slot** (64-bit slots), to skip reading records of
  non-matching entries: twice the table (2.1 GB for Mathlib) to save part of
  2.6 comparisons per insertion.
- **Multi-level 64-way tables** (the owner's question; Lean's
  `PersistentHashMap`): see the answer above; they serve versioned maps,
  which LeanForth does not need.
- **Chaining, Robin Hood or cuckoo hashing.** Chaining costs a link per
  entry; the other two are more complex than linear probing, whose measured
  cost is already low, and make exact undo harder.
- **Trusting the exporter's sharing** (node number = export index, no
  table). All three exports had no duplicate, but soundness must not depend
  on the exporter, other exporters may not share, and the scratch tier needs
  the input's table to find existing terms.
- **File-backed (memory-mapped) storage** (plan 6.2.3). Needs a C binding
  (a new dependency needing approval), depends on Gforth and the operating
  system, and would write a memory image to a file, which the portability
  rules forbid. Needed only if the input tier exceeds about half of the
  machine's memory, for example at Fermat's-Last-Theorem scale on this
  machine; dropping proofs (C6) would come first.
- **A copy of the input per worker.** Six copies of 2.9 GB is 17.6 GB; the
  shared read-only tier costs nothing per worker (the reason ADR 0009
  rejected operating-system processes).

## Decisions for the owner

1. **Accept this storage design as the basis for plan tasks 6.2.0–6.2.3**
   (16-byte nodes with 32-bit fields, two tiers, flat hash tables).
   *Recommendation: accept.* It answers your questions with measurements,
   fits all of Mathlib in about 3 GB, and changes no checking rule; each
   implementation step still goes through the [kernel] review with
   unchanged test results.
2. **Keep every theorem proof in memory for now** rather than dropping
   proofs after their check. *Recommendation: keep.* Everything fits;
   dropping proofs saves about 2 GB on Mathlib but depends on your phase 4
   answer about unfolding theorems (G5) and needs a second pass over the
   file. Revisit for corpora larger than Mathlib.
3. **Store equal terms once even though Lean's exporter already shares
   them** (no duplicate in all of Mathlib). The table costs memory (1.07 GB
   for Mathlib) and loading time (about 0.75 µs per node: an `Init` load
   took 13.5 s with it, 8.9 s without). *Recommendation: yes.* Correctness
   must not rest on the exporter, and checks need the table to recognise
   terms they rebuild.

## Reproduction

The prototype, its scripts and their outputs are in
[`docs/development/measurements/compact-store-2026-11-02/`](../development/measurements/compact-store-2026-11-02/README.md),
with the exact commands. Lean sources: `src/Lean/Expr.lean` SHA-256
`b9a91d9d170201c2a3622b9c55d694466f54e0e1b8f6068a2d296ff98650169c`
(toolchain copy and tag `v4.35.0` identical), `src/Lean/Data/SMap.lean`
`d4575d3c8853fedcdd7b8a28cd6985e4f1afe17f37db15d5f49a81adba2cdbc7`,
`src/Lean/Data/PersistentHashMap.lean`
`d63a21b3bdc0c616417d75c32c3e104cc185667229a8a899de3769c1a4252af4`,
`include/lean/lean.h`
`eb951e1171d39b828e7ad60aed0b90759598b678bfe58cf85c65a1559c021bf9`
(toolchain copies), and `src/kernel/expr.cpp` from the tag
`cb02c18964aca67289b8c1d64864355bb5c10fc93d55bd3c3c9646776af9c592`.
