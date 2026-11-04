# ADR 0016: the compact store for Mathlib-scale input

Status: **accepted** by the owner on 2026-11-03, with the three recommendations of
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
| constant (1.35%) | 1 tag | its declaration, resolved when the input is sealed (C4) | name | universe-argument list | parameters flag |
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
- Steps 4–6 not started.

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
