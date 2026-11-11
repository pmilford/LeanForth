# ADR 0020: the checked-environment snapshot

Status: **proposed**, 2026-11-11 (plan task 6.2.5 of the
[plan draft](../project/PLAN_DRAFT.md); agent SN0). A design only: nothing
in `src/` is changed. It needs the owner's [format] decision (snapshot
format 1, check report 0.3), [import] (a dependent export staged into a
loaded tier) and [kernel] (what a loaded snapshot vouches for: the import
rule I1 and the invariant I2 below). It builds on
[ADR 0012](0012-checked-environment.md) (the checked environment; E8, saved
results and the two run modes), [ADR 0016](0016-compact-store.md) (the
compact store, C1-C9, and its steps S1-S5) and
[ADR 0009](0009-reentrant-state-and-parallel-checking.md) (one publisher;
parallel verdicts equal serial ones), and designs for the store as it will
be after agents S5B (the checker reads lets and projections in place, the
copy deleted) and S7 (`--jobs`: a scheduler and parallel publishing).

## Summary in plain words

Checking all of Mathlib would take LeanForth about fifteen hours on one
worker (extrapolated from its first sixth). A *snapshot*
saves the result once, in one binary file: every name, universe level and
expression of the export exactly as the importer stored them, every
declaration, and every declaration's verdict with what the checked
environment keeps for it (its dependencies, its axioms). Loading the file
takes about a minute instead of re-checking. Physlib, or a new proof, is
then checked against it: each of its declarations that is the same as one
in the snapshot, and sees the same declarations around it, takes the saved
verdict; everything else is checked. The verdicts are exactly those of
checking the dependent export from scratch.

The file holds numbers and offsets only, in a fixed byte order, so it
loads on any host at any address, read or memory-mapped. It is not tied to
the LeanForth build: its header names the export (SHA-256 and manifest),
the file layout (*format version*) and the checker's rules (*verdict
version*). A loader refuses a snapshot whose versions, settings or hashes
differ, or that is cut short or altered. A change that cannot move a
verdict, such as a printer change or a speed change that keeps every fuel
count, keeps the verdict version, so old snapshots stay valid.

A saved verdict is not re-checked, so under the owner's answer to OQ-3 it
is for development and research only: text and JSON output label it, and
a final, full-trust run re-checks everything from the export and reads no
snapshot.

## The owner's requirements (2026-11-11) and where they are met

| Requirement ([plan row 6.2.5](../project/PLAN_DRAFT.md)) | Where |
| --- | --- |
| Check a library once, save its checked environment, load it to check new proofs or a dependent library | D1, D4, D5 |
| Position independent: indices and offsets only, fixed word size and byte order, memory-mapped or read | D2 |
| Not tied to the LeanForth build: printer and verdict-preserving speed changes keep it valid | D3 (the verdict version) |
| Header: export SHA-256 and manifest, format version, verdict version and the rule for bumping it | D3 |
| Results from a snapshot labelled (OQ-3); a full-trust run re-checks from the export | D4 |
| Refused: a verdict-version bump, a wrong export hash, a truncated or altered file | D6 |
| Load time and memory measured | D7 (estimates), step SN5 (measurement) |

## Facts

From LeanForth (measured, `gforth-fast`, a shared machine):

1. **The input tier** of all of Mathlib (106.1 M expressions, 4.24 M names,
   729,263 declarations) takes 2.94 GB in memory, of which 1.07 GB is the
   expression hash table and about 0.05 GB other tables and the
   name-to-declaration array ([ADR 0016 C6](0016-compact-store.md#c6-memory-budget-for-all-of-mathlib)).
   Every record is four (a declaration eight) 32-bit fields holding record
   numbers, never addresses (C1, C2); the tier is sealed and read-only
   while checks run (C3).
2. **Loading from NDJSON**: Mathlib's first sixth is staged and fed in
   51.6 s and 1.06 GB since step S5 (read in place)
   ([progress](../project/PROJECT_PROGRESS.md#full-mathlib)); about 5 min for
   the whole if it scales linearly. Its SHA-256 alone costs about 90 s
   (6.26 GB at about 70 MB/s, [FORTH_LIBRARY.md](../development/FORTH_LIBRARY.md)).
3. **Checking**: the first sixth took 8,810 s at the default fuel (before
   S5), so the whole about 15 hours on one worker.
4. **What a check reads of the environment**: the slots that the lookup
   `lf-env-lookup` (E5, `src/kernel/environment.fs`) returns for a name,
   with the generated-recursor holder and the quotient's state, and the
   records and fields of those slots. A slot holds the outcome, a copy of
   the input declaration, its dependencies (slot numbers), its axiom bits,
   provenance, an inductive block's warnings, recipe and shape, and the
   skipped and added marks. The checker's own term, level and reference
   stores, leaf tables, audit marks and caches are per context and built
   by the feed from the stage; their layout changes with almost every
   compact-store step.
5. **Saved results are already planned for**: a slot has a provenance
   field (`lf-provenance-saved`, ADR 0012 E8) that a check's candidate
   joins over its dependencies, as it joins axiom sets.

From Lean 4.35.0: Lean does not re-check imported modules; it loads their
`.olean` files, memory-mapped where possible, and trusts the build that
wrote them. Its checker replays a module's own declarations onto the
imported environment, and `leanchecker --fresh` re-checks everything (34
min 52 s for Mathlib on a 4-CPU runner,
[SCALE_ASSESSMENT.md](../project/SCALE_ASSESSMENT.md)). This ADR is
LeanForth's counterpart of the first, with OQ-3's labels, and keeps the
second as the final mode.

## Decision (proposed)

### D1 What is saved

The snapshot saves what the importer read and what the publisher wrote,
never what a particular build derives from them.

| Section | Contents | Why |
| --- | --- | --- |
| names | the name family's 16-byte records and its byte pool (C2) | names of declarations, constants, parameters, binders |
| levels | the level family's records (C1) | universe levels |
| lists | the universe-argument and parameter lists (C2's tuples) | constants are (name, list): the references |
| literals | the literal family's bytes (natVal digits, strVal UTF-8) | literals |
| expressions | the expression records, data words included (C1), constant payloads written as 0 | the terms of every declaration |
| declarations | the 32-byte staged records, with their kind data in the lists, and each one's export line | what was checked |
| slots | per declaration (about 64 bytes): outcome; provenance, skipped and added marks; axiom bits; warnings, recipe and shape; fuel used (64 bits); where its dependencies and lookups start and how many; its diagnostic as recorded (code, two numbers, step, an index into the site texts) | the verdicts |
| dependencies | slot numbers, 32 bits each (ADR 0012 E2's `decl-deps`) | axiom and provenance reports; the publisher's re-check |
| lookups | per declaration, every name its check looked up with the answer it got (slot + 1 or 0, outcome, generated-holder flag): two 32-bit fields each, sorted by name | the import rule (D5) |
| site texts | the diagnostics' site texts, once each | information only |
| manifest | the export's manifest, byte for byte | identity (D3) |
| information | a short JSON text: LeanForth commit and whether tracked files differed, version, host, engine, cell width | information only |

**Not saved, rebuilt when loading:** the hash tables of every family
(ADR 0016 C4: hash values and layouts that follow them are never written
to files), the name-to-declaration array (from the declarations' chain),
the constant payloads (computed again when the tier is sealed, since a
dependent run numbers declarations differently), and the export-index maps
(loading aids). **Not saved at all:** anything in a checker context (the
term store's own records, the level and reference stores, leaf tables,
audit marks, caches), environment identities and addresses. These are what
S5B, S7 and later steps change; leaving them out is what keeps a snapshot
valid across builds.

*Note (2026-11-11, plan step SN2, agent SN2; [format][import] review
pending):* the input tier's part is implemented, `src/import/snapshot-tier.fs`
(its header gives the layout): the first ten sections of the file are an
information section (format version 1, every section's count, the
metadata flag and texts), the name bytes, names, levels, lists, text
bytes, texts, expressions (a constant's payload written as 0),
declarations (the mdata mark written clear) and lines. Loading fills a
fresh stage, every record checked by its builder's own check with its data
word computed again and compared, pool offsets exactly consecutive, no
record twice, each declaration checked as a draft (flags, codes, kind
data, chain); the tables are built once at their sealed size
(`cons-load-room`, `cons-adopt` in `lib/cons.fs`). `stage-continue`
(`import/stage.fs`) reads a further export into a filled tier, equal
records keeping their numbers, the unknown-constant refusal limited to the
constants that read contains. Measured on all of `Init` (`gforth-fast`,
a loaded machine): file 106,688,512 bytes; saved in 1.7 s; loaded in 4.9 s
and sealed in 0.17 s, against 20.0 s to stage the NDJSON with its manifest;
peak resident memory 297 MB for load, seal and saving again (219 MB for
staging alone); saved again from the loaded stage, the same bytes; checked
from the loaded stage (`--jobs 3`), the same outcome and fuel for all
59,349 declarations as checked from the staged export
(`tests/support/tier-both-ways.fs`). A fresh check runs none of it: `check
--json` of `Init`'s first million lines is the same before and after.
Writing copies the expressions (to zero the payloads) and the
declarations, so a save holds those families twice for a moment.

### D2 The file layout

- **Little-endian fixed-width integers**, 32 bits, or 64 bits for file
  offsets, lengths and fuel; no cell, no address, no hash value. The format
  is defined byte by byte, as FORTH_STYLE §8 requires; a section is
  written or read as one block only where `src/lib/u32.fs` has checked
  that this host stores a 32-bit field in exactly that byte order (Gforth
  on x86 and ARM, and the portable fallback, which always does); any other
  host converts field by field. Both paths give the same bytes, which a
  test compares with the fallback forced. A 32-bit host reads the format
  too (64-bit fields as pairs) and reports *full* if it lacks the memory.
- **A header of 4,096 bytes**: an 8-byte magic (`89 4C 46 53 4E 41 50 0A`,
  "\x89LFSNAP\n", which a text-mode copy or a 7-bit transfer damages
  visibly), the format version, a byte-order check value, the identity of
  D3, the counts of every family, and the section table: per section its
  kind, unit size, count, offset and length (64 bits each) and SHA-256.
  The header's own SHA-256, over the header with that field zeroed, ends
  it.
- **Sections start at multiples of 4,096 bytes** and follow each other in
  a fixed order with zero padding between; a section's length is its unit
  size times its count. Every reference inside a section is a record
  number, a slot number, an index into a pool or a byte offset within a
  section. So the file can be mapped page by page, or read: LeanForth's
  loader reads with Forth-2012 `READ-FILE` into heap blocks, because
  standard Forth has no `mmap`; a mapped loader is a later option the
  layout already allows.
- **Deterministic**: the same export, settings and verdicts give the same
  bytes (no time stamp; the information section is the only part that
  names the build). Runs with `--jobs 1` and `--jobs N` give the same file
  (ADR 0009, G-P4).
- **Written safely**: to `FILE.partial`, then renamed to FILE
  (`RENAME-FILE`), so a crash or a failure never leaves a file that looks
  complete; on failure the writer deletes its own partial file by name and
  leaves an existing FILE untouched. A snapshot is written only after a run
  in which every slot became final.

### D3 Identity in the header

| Field | Holds | Compared when loading |
| --- | --- | --- |
| format version | the layout, 1 | must be one this build reads; a new layout needs a converter or the snapshot is written again |
| verdict version | the checker's rules, a number in one source file with a changelog (below) | must equal this build's |
| verdict settings | fuel per declaration, the allowlist version and bits | must equal the run's: `--fuel` defaults to the snapshot's, another value is refused |
| export identity | its SHA-256, bytes and lines; whether its manifest was enforced; `--any-lean-version` and the metadata it read | against the export in `replay` (D8); printed in every report |
| manifest | its SHA-256 and, in its section, its bytes (Lean and Mathlib versions, commit) | printed |
| base snapshot | the SHA-256 of the snapshot this run imported from, or zero | printed (D5) |
| LeanForth | commit, modified, version, host: information only | never compared |

**The verdict version and the rule for bumping it.** One constant,
`lf-verdict-version`, starting at 1, with a changelog of every bump and its
reason. It covers every field a snapshot stores for a slot except the
diagnostic: the outcome, axiom bits, dependencies, lookups and their
answers, warnings, recipe, shape and fuel used.

- **Bump** for any change that could change one of them anywhere: a Lean
  rule or its order, the fuel model or what a step costs, an audit that can
  refuse, the lookup rules (E5), the allowlist, the block check's derived
  fields, the importer's reading of an export.
- **Keep** only for a change that cannot change them by construction
  (printing, reports, the command line, I/O, documentation, tests, a speed
  change that keeps every fuel count and lookup), shown by the both-ways
  comparison: identical stored fields for every declaration of all of
  `Init`, the arena and a fixed Mathlib prefix, between a fresh check with
  the change and a snapshot written before it. The author records the
  evidence in the commit; the independent review checks it.
- **A guard in `make check`**: golden snapshots of the small pinned
  exports, committed with the verdict version that wrote them, are checked
  again from their exports and compared field by field. A change that
  moves a stored field without bumping the version fails the test; a bump
  makes the golden snapshots refused as stale, so the bump's commit must
  write them again. The guard catches only what the small exports reach;
  the comparison above covers the rest.

### D4 Loading, and what a loaded snapshot vouches for

Loading, in order, each step refusing before anything is published:
the header (magic, byte order, versions, settings, header SHA-256); the
section table against the file's size (D6); every section's SHA-256 (on
the job pool's workers once S7 has merged); every record checked as when
built (ADR 0016 C8: tags and payloads in range, every child a smaller
number of its family, data words computed again and compared, lists and
byte offsets inside their pools, declarations as the stage checks them,
slots' dependencies and lookups inside their pools and below their own
number); then, only if an export is staged into it (D5), the hash tables
rebuilt at their final size. The loader then acts as the publisher (ADR
0012 G-P1): before any check starts it fills the slots it takes from the
snapshot and makes them final with provenance *snapshot*.

**What a loaded snapshot vouches for** (trust boundary): that a LeanForth
build of this verdict version, with these settings, gave these verdicts to
the declarations of the export with this SHA-256, provided the file is the
one that build wrote. It does not vouch:

- that the checker is right: that is the [kernel] gate's question, and
  every accepted verdict stays *experimental, not independently audited*;
- that the file was not forged: the SHA-256s inside it catch damage, not a
  deliberate change, since whoever can write the file can write its hashes
  too (there is no signature). Every report prints the file's SHA-256 so
  that a user can record it elsewhere;
- that this build would give the same verdicts, beyond the verdict-version
  rule (D3): a bump that was missed is a risk the guard and the both-ways
  comparison reduce, not remove.

**Labels (OQ-3).** A run with `--snapshot` is a development and research
run (ADR 0012 E8: mode *development*); a run without one is final and
reads no saved result. Provenance spreads as ADR 0012 E8 says: a
declaration checked in this run that uses a snapshot result, directly or
not, is labelled too. Text:

```text
Nat.add_comm: accepted (experimental, not independently audited; from snapshot, not re-checked in this run); axioms: none
Physlib.foo: accepted (experimental, not independently audited; checked in this run, uses results from the snapshot); axioms: propext
snapshot: mathlib.lfsnap (sha256 3f2a…), export sha256 18448e5d…59c6, verdict version 1, written by LeanForth 52477e7: 690,112 results taken from it, not re-checked in this run
note: development and research mode: a final run re-checks everything from the export and reads no snapshot; only its results support a claim
```

JSON (check report 0.3, a [format] decision): `mode` `development`, a
`snapshot` member (file, SHA-256, format and verdict versions, export
identity, manifest SHA-256, base, the LeanForth information), and on each
declaration `provenance`: `checked`, `snapshot` or `uses-snapshot`. Exit
statuses follow the verdicts as in a final run; the label, not the status,
marks a development run.

### D5 A dependent library: Physlib on Mathlib

**Exact mode** (this design). The dependent export E′ is Lean's export of
the dependent library, which holds every declaration it uses (Mathlib's
among them); the snapshot S is Mathlib's. `leanforth check --snapshot S E′`:

1. loads S (D4) and stages E′ into S's tier, which is opened again for
   it: a record of E′ equal to one of S gets S's number (hash-consing,
   C4), so equal content is equal numbers. E′'s declarations are E′'s
   own, in E′'s order; S's declarations are not in the run's input. The
   unknown-constant refusal (plan task 5.2.6) applies to the constants E′
   itself contains, as when E′ is staged alone.
2. runs one import pass over E′ in order, before any check: declaration
   e(k) is **imported** from S's declaration s(d) when all of the import
   rule **I1** hold:
   1. *same content*: e(k)'s staged record equals s(d)'s field for field
      (name, kind and flags, parameters, type, value, hint, kind data), as
      numbers of the one tier; an inductive block only whole;
   2. *a reproducible verdict*: s(d)'s outcome is not *full* or *invalid*
      (those depend on memory or an internal fault);
   3. *the same answers*: for every name in s(d)'s lookup list, the
      lookup in E′ at k, by the environment's own lookup code over the
      slots decided so far, gives the recorded answer, with every slot it
      returns imported from the recorded one. A lookup that meets a slot
      not imported (to be checked in this run) is no match. The lookup of
      its own name (N2) is in the list, which also tells two equal
      declarations of one name apart.
   An imported slot is published with S's outcome and fields and
   provenance *snapshot*. Every other declaration is then checked as
   usual (scheduler, `--jobs`), its lookups seeing imported slots as
   final.
3. reports both kinds, with a count of E′'s declarations that share a name
   with one of S but differ in content (many of them mean S is of another
   library version).

**Why the verdicts are exactly a fresh check's.** The invariant **I2**
([kernel] review): *a check's outcome, fuel and recorded fields depend
only on its declaration's content, the run's verdict settings and verdict
version, and the answers of its lookups, with the records and fields of
the slots they return.* A check is deterministic, so if every lookup it
made in S gives the same answer in E′, it makes the same lookups in the
same order and ends the same way. By induction over E′'s order, every
imported slot holds what a fresh check of E′ would have published. So an
edited declaration is checked again, and so is everything whose lookups
reach it, and nothing else. I2 forbids state shared between checks that
changes a verdict or fuel; ADR 0016 C4's later cross-check caches must
keep it or bump the verdict version and revise I1. Tests enforce I2 by an
assertion in test builds: a check that reads a slot its recorded lookups
did not return fails.

**Costs.** Staging E′ still reads its NDJSON (about 5 min for an export
the size of Mathlib); the import pass replays about as many lookups as
there are dependencies (seconds). Checking is limited to what differs.

**Open-export mode** (later, not in this design's steps; an [import]
decision for the owner). An export holding only the dependent library's
own declarations, whose missing names resolve to S (Lean's `import`);
verdicts equal to a fresh check of S's export followed by E′; it saves the
staging time and needs the export to name its base (S's export SHA-256),
which today's exporter and manifest do not.

**Chained snapshots.** A run that imported from S may write its own
snapshot; its imported slots keep provenance *snapshot* and its header
names S as its base.

### D6 Failure modes: fail closed

Nothing is published and the run's stage and environment are freed on
every refusal; a `THROW` while loading passes on after the same cleanup.

| Case | Outcome | Says |
| --- | --- | --- |
| not a snapshot (magic), or a damaged byte-order value | invalid | not a LeanForth snapshot |
| another format version | unsupported | the format it has and the one this build reads: write it again |
| another verdict version | unsupported | stale: check the export again (or use the build that wrote it) |
| other verdict settings (fuel, allowlist) than the run's | invalid | the setting, both values |
| the file shorter than its sections (truncated); a section outside the file, overlapping another, not aligned, or with length other than unit times count | invalid | the section |
| the header's or a section's SHA-256 differs (altered) | invalid | the section |
| a record or slot fails its checks (D4) | invalid | the section and record number |
| `replay`'s export has another SHA-256 than the header's | finding `input-differs` | |
| no heap for a section or a table | full | |
| a read error | invalid | |
| writing fails (no room, rename refused) | full or invalid | the partial file is deleted; FILE untouched |
| `--snapshot` or `--save-snapshot` with `--record` (the small-export path) | refused (status 4) | |

### D7 Size and load time for all of Mathlib (estimates)

From the measured figures (Facts 1-3); the step plan measures them.

| Part | Size | Basis |
| --- | ---: | --- |
| expressions, 106.1 M × 16 B | 1.70 GB | C6 |
| names (4.24 M × 16 B) and their bytes | 0.09 GB | C6's 0.12 GB less its table |
| declarations (729,263 × 32 B) with their lines; levels, lists, literals | 0.04 GB | C2, C6 |
| slots, 729,263 × 64 B | 0.05 GB | D1 |
| dependencies (4 B) and lookups (8 B) | 0.18-0.35 GB | assumed 20-40 per declaration; measured on `Init` in step SN3 |
| **snapshot file** | **about 2.1 GB (2.0-2.2)** | against 2.94 GB in memory and 6.26 GB of NDJSON |

| Loading step (`gforth-fast`) | Time | Basis |
| --- | ---: | --- |
| read 2.1 GB | 1-3 s cached; up to 20 s from a slow disk | the disk |
| SHA-256 of every section | 30 s; about 6 s on 6 workers | 70 MB/s |
| check every record (C8) | 10-20 s | assumed 0.1-0.2 µs a record |
| rebuild the hash tables (only before staging an export) | 25-55 s | 2.2-2.6 slots compared per insertion (C4), one or two cache misses each |
| publish the slots | under 5 s | |
| **total: report Mathlib's verdicts again** | **about 20-60 s** | |
| **total: ready to stage a dependent export** | **about 45-115 s** | |

Against about 5 min to stage and feed Mathlib from NDJSON and about 15
hours to check it. Memory: about 2.1 GB for the loaded file, 3.2 GB with
the rebuilt tables, against 4.2 GB peak when staging from NDJSON (no
export-index maps); a dependent run then needs what checking E′ needs.
Storing the tables in the file would replace the 25-55 s rebuild by
reading and hashing 1.1 GB more (about 3-16 s), for a file of about
3.2 GB (a question for the owner).

### D8 Replay, and the run records

`leanforth replay EXPORT SNAPSHOT` checks the export again in a final run
and compares every slot field with the snapshot's (the both-ways
comparison), with findings in the manner of run-record replay
([RUN_RECORDS.md](../programming/RUN_RECORDS.md)): `input-differs` when the
export is not the snapshot's, `verdict-differs`, `accepted-not-established`
and so on. This replaces the planned run records 0.3 for exports of any
size; run records 0.1 and 0.2 stay as approved, for the small exports that
`check --record` reads.

## Implementation steps (summary)

Each step is independently testable and mergeable; the detailed plan, with
files, tests and planted faults, is kept with the agents' work notes.

| Step | What | After | Beside the Mathlib runs |
| --- | --- | --- | --- |
| SN1 | a standalone library for sectioned binary files: header, section table, per-section SHA-256, little-endian fields, partial file and rename, fail-closed reading | — | yes |
| SN2 | the input tier saved and loaded, every record checked, tables rebuilt; staging continued into a loaded tier | SN1 | yes |
| SN3 | the environment saved and reloaded: lookup lists, verdict version, header identity, `--save-snapshot` and `--snapshot` without an export, OQ-3 labels, check report 0.3 | SN2, S7 | yes, merged between runs (verdict-neutral) |
| SN4 | dependent exports: the import pass (I1), the I2 assertion | SN3 | yes |
| SN5 | `replay EXPORT SNAPSHOT`, the verdict-version guard, user and format docs, Mathlib's snapshot measured; Physlib when its export exists (6.1.8) | SN4 | uses the full run's output |

## Consequences

- Mathlib is checked once per verdict version; Physlib and new proofs are
  checked in the time it takes to stage their export and check what is
  new. Editing one declaration re-checks only what its lookups reach.
- A new rule for the project: every change states whether it keeps the
  verdict version, with evidence when it does.
- The checker records every lookup with its answer; a test-build
  assertion keeps that list complete (I2).
- ADR 0016 C7's "records are never written to files" becomes: never as a
  memory image; the snapshot writes them field by field in a fixed byte
  order (C8's "no host address, cell layout or hash value is serialised"
  still holds).
- Saved verdicts never support a claim: final runs and the outside audit
  re-check from the export.

## Rejected alternatives

- **Copying the heap image** (dumping the checker's stores): it holds
  addresses, cell layouts and the host's byte order, so it is not position
  independent, and its layout changes with almost every compact-store step,
  so every build would invalidate every snapshot.
- **Gforth's `savesystem`**: Gforth-specific (not Forth-2012), it saves the
  dictionary, not the heap where the stores live, and ties the file to the
  exact binary and build.
- **Re-checking always**: kept as the final mode, but fifteen hours per
  Physlib run is not usable for development.
- **Saving decoded, unchecked records only** (the 2026-11-02 "binary quick
  import"): saves minutes of reading, not hours of checking; it is D1's
  first sections without the verdicts.
- **Matching declarations by a hash of their content** instead of sharing
  the tier: a collision could import a wrong verdict, and a cryptographic
  hash of every expression costs more than the staging it would save.
- **Lean's import semantics in exact mode** (every declaration of S visible
  to E′): a dependent library that does not import a Mathlib module may
  reuse one of its names, which Lean accepts and S would reject (N2); the
  import rule keeps the fresh-check verdicts. It remains right for the
  later open-export mode, whose reference is S's export followed by E′.
- **A JSON snapshot**: several times larger and minutes to read.
- **Storing the hash tables now**: a faster load for a 50% larger file and
  a format tied to the hash function; left to measurement and the owner.

## Amendment 1 (2026-11-11): step SN3, and the owner's decisions F1 and F5

*Agent SN3; [kernel] (the lookup recording, I2) and [format] (snapshot
format 1, check report 0.3) review pending, and the owner's approval.*

**F1 (owner): lookup tables are rebuilt on load, never stored.** This
answers question 1 below: the file holds no hash table, address or hash
value but a name's stored data word (SN2's tier sections, unchanged), and
the loader builds every table at its final size.

**F5 (owner): layered snapshots.** A library's snapshot holds only its own
records and slots and its base's identity; loading is the base, then any
number of layers in order; a name defined with different content in two
layers is refused, as Lean refuses an import clash. Step SN3 writes and
reads base snapshots only; the format already has what layers need, so
SN4/SN5 add them without a format change:
- the header's caller fields 7 (the number of layers below this one, 0
  for a base) and 8-15 (the base's identity: its header's SHA-256, zero
  for a base);
- the identity section's fields 21-28: the first number of each tier
  section (name bytes, names, levels, lists, text bytes, texts,
  expressions, declarations), zero in a base; a layer's records and slots
  are numbered on from its base's counts, so every reference stays a
  number of the one loaded tier;
- the loader (SN4/SN5): the base as now, then each layer's tier sections
  entered after the base's records by the same record checks
  (`tier-read` continuing the numbering, as `stage-continue` does for an
  export), the clash check by name over the declarations, then the
  layer's slots published after the base's by the same publisher steps.
Today a snapshot with field 7 or 8-15 non-zero, or a first number other
than 0, is refused as *unsupported* (a layer).

**What SN3 implements** (`src/kernel/env-snapshot.fs`, whose header gives
the layout byte by byte; `src/kernel/verdict-version.fs`):
- *Lookups* (D1, D5, I2; `src/kernel/environment.fs`, "Lookups"): a
  check records in its candidate every name query it makes of the
  environment, deciding or aside, sorted by key (name number × 16 + kind)
  and distinct, each with its answer (the slot it gave + 1 or 0, times 16;
  8 for the generated recursor's holder; the outcome). The kinds are the
  queries' entry points: `lf-env-lookup-pass` (0), N2's `lf-env-fresh`
  (1), `lf-env-fresh-generated` (2) and `lf-env-unheld` (3),
  `lf-env-find` (4), `lf-env-first` for an inductive type (5), any slot
  (6) or another module's test (7, which an import cannot replay), and the
  quotient's `lf-env-quot-held` (8, under the anonymous name). Names a check
  made beyond its input (its own scratch names) are collapsed when
  published into one key that no import can match, so such a declaration
  is always checked again (8 declarations of `Init`). The publisher stores
  the list for *every* outcome (an import replays a rejection too) in a
  second pool beside the dependency pool, marked and rolled back with it.
  A list the heap cannot grow makes the declaration *full* (diagnostic
  100), never an incomplete list. Today's checker reads no constant
  payload (`import/stage.fs`), so there is no payload path to record; when
  ADR 0016 C9 steps 4-6 read payloads, each such read must record its
  lookup. A test build (`lf-env-i2-checks`) counts every slot a check
  reads through `lf-env-readable` that no recorded query answered: zero
  on every pinned export and fixture (`tests/core/env-snapshot.fs`).
- *Identity* (D3): the container (`lib/sections.fs`, SN1) has its own
  magic and 16 caller fields: 0 the mark "LFSN", 1 the snapshot format
  (1), 2 the verdict version, 3-4 the fuel, 5-6 the allowlist's version
  and bits, 7-15 the layers (above). The rest of D3's identity, which does
  not fit 16 fields, is the identity section (the export's SHA-256, bytes,
  lines, flags; the manifest's SHA-256), protected like every section by
  its SHA-256 in the header. The manifest's bytes and an information text
  (LeanForth's version, commit, Gforth, engine, cell width) are sections
  of their own; the information is the only part that names the build.
  The file's identity, printed in every report, is its header's SHA-256,
  which covers every section's.
- *Slots*: 72 bytes each (outcome; skipped, added and span marks;
  provenance; axiom bits; warnings; recipe; shape; fuel used, 64-bit;
  the counts of its dependencies and lookups; its diagnostic: code, two
  64-bit numbers, step, site), each list written in slot order, so the
  file never depends on the order of publication: `--jobs 1` and
  `--jobs 4` write the same bytes.
- *Loading as the publisher* (D4): after the header, table and tier (every
  record checked as SN2 says) and the environment's sections (every field
  in range, dependencies ascending and below their span's first slot,
  lookups' kinds and answers below it), the loader runs the publisher's
  own serial steps with a check word that fills each candidate from its
  saved slot, marked *saved*: the publisher re-checks it as a check's
  (dependencies usable and ascending, the axiom set their union with the
  axiom's own bit computed again, provenance, N2, kind) and publishes it
  final in a development environment; then every published slot is
  compared with its saved fields and lists (an out-of-order list, for
  example, is refused). A slot is labelled from its provenance: taken from
  the snapshot, checked here but resting on it (step SN4), or checked.
- *Failures* (D6): as the table says, except that the container's
  *rejected* (a SHA-256 that differs) is reported *invalid*, and a
  layered snapshot is *unsupported*.

**Measured on all of `Init`** (59,349 declarations; `gforth-fast`, a
loaded 10-core machine; the export with its manifest): every verdict,
fuel, axiom set and diagnostic of `check --jobs 4` identical to main's
(233916d) and to the snapshot's reload (`check --snapshot`); 20.2
dependencies and 36.1 lookups per declaration (at most 445 lookups);
file 132.9 MB (expressions 97.8 MB, lookups 17.1 MB, dependencies 4.8 MB,
slots 4.3 MB); writing it about 3 s; loading and reporting 10.0 s (read
and check 4.9 s, feed 1.8 s, publish and compare 2.1 s) at a peak of 0.69
GB. This corrects D7's assumption of 20-40 per declaration: Mathlib's
dependencies and lookups take about 729,263 × (4 × 20 + 8 × 36) bytes,
0.27 GB.

## Amendment 2 (2026-11-11): step SN4, dependent exports and layers

*Agent SN4; [kernel] (I1, I2: what a loaded snapshot vouches for) and
[import] (continued staging, layers) review pending, and the owner's
approval.*

**The import pass** (`src/kernel/env-import.fs`; D5 as written, with
these details). `check --snapshot S EXPORT` reads S's tier, keeps S's
declarations aside, reads the export on into the tier (`stage-continue`),
seals and feeds it; before any check one pass over the input in order
takes from S every declaration for which I1 holds. I1.1 compares the
staged records field by field but the chain and the mdata mark; a
block's member only with its whole block and at the same place. I1.3
asks every saved lookup again in the declaration's snapshot through
`lf-env-replay` (`environment.fs`: the key's name and kind, at the
check's own limit, at which every recorded query is made), records the
answers as a check does and compares the list with S's, each answer's
slot translated to S's numbering; the replay is no match when a query
met a slot not final below the limit (`lf-env-early?`, which
`lf-slot-final?` sets: the "lookup mode" of the plan), and every saved
dependency must have been taken. A slot S published with the one before
(a block's member) is taken only with that first, as its span; a member
S checked alone only when its block's first member was taken here. A
taken slot is published by the publisher's serial step with a check word
that asks the lookups again (so the slot's list holds this run's
answers), depends on the taken slots, and copies S's marks, fields and
outcome with provenance *snapshot*; the publisher re-checks it as a
check's. Keys of names beyond the input (scratch names, e.g. a nested
block's auxiliary types) and another module's tests are never replayed,
so those declarations and everything whose lookups reach them are always
checked again (35 of the 107 declarations of `tests/cli/nested.ndjson`).
The scheduler (`env-schedule.fs`) treats slots final before the run as
done, so `--jobs` checks the rest.

**Layers (F5).** A layer is written by `check --snapshot BASE
--save-snapshot LAYER EXPORT` after a run whose slots are all final: the
tier's records from BASE's counts on (identity fields 21-28 the counts,
header fields 7 = 1 and 8-15 BASE's header SHA-256), the declarations not
taken with their block records (chains numbered on from BASE's
declarations), and their slots, numbered on from BASE's slots, every
dependency and lookup answer numbered so (a taken slot as BASE's) and the
dependencies sorted again. A layer on layers is not written (refused).
Loading (`src/kernel/env-layers.fs`, `src/import/snapshot-layer.fs`):
the base as before, then each layer opened as a layer of that base (its
identity and counts compared), its records entered again by the tier's
builders, each part first mapped to its number here (a list built for
the kind its user says: a constant's levels, a declaration's parameters
and kind data), so sibling layers share their equal records; its
environment's sections checked as a base's (numbered on from the base's
slots); then each of its declarations, a block whole, is the same as
one loaded before (same content and outcome, axioms, warnings, recipe,
shape and fuel: loaded once), refused as a clash (a loaded name, none of
its content), or entered and its slot appended with its lists numbered
as loaded and sorted again. The loaded snapshots then read as one base,
for `--snapshot` alone and for the import pass.

**Evidence** (`tests/cli/test_leanforth.py` classes `Imports`, `Layers`;
`tests/mutants/faults.toml` entries `sn4-*`): both ways, the report of
the export checked against the snapshot equals its fresh check field by
field but for the labels, for (i) twelve exports against their own
snapshots, with the declarations not taken exactly those the model of
I1 predicts; (ii) a proof altered, (iii) a declaration moved after its
user, (iv) a name reused with other content, (v) two equal declarations
of one name, (vi) a block member changed, (vii) a slot saved full, and a
crafted lookup that matches only when an undecided slot is ignored; the
dependent fixtures (`tests/cli/dependent.lean`, `sibling.lean`, which
`tests/cli/export-check.sh` rebuilds with pinned Lean) with `--jobs 3`.
Layers: base and layer report what the layer's run reported; two
sibling layers load together (15 declarations, `Eq` and `rfl` once);
refused: a layer on another base, a layer first, a clash, a shared
declaration with other verdicts. Thirteen planted faults are caught;
one (a member published with its first taken alone) is equivalent to
the first-member rule.

**Measured** (`gforth-fast`, `--jobs 4`, a loaded 10-core machine). All
of `Init` checked against its own snapshot: every field of all 59,349
declarations equal to the fresh check (fuel included); 37,142 taken,
22,207 checked again -- exactly those whose lookups reach `Lean.Syntax`'s
nested block, the 8 declarations whose checks make names beyond the
input (the model in `test_leanforth.py`, `kept_back`, predicts the set);
392 s against 460 s fresh. Mathlib's first million lines (13,023
declarations, 5,231 of them named as in `Init`) checked against `Init`'s
snapshot: every verdict, the counts and the exit status equal to its
fresh check's, 1,108 taken, 805 sharing a name with `Init` but not its
content; but **fuel used differs on 2,151 declarations** (a few percent,
e.g. `LE` 326 fresh, 330 here, both checked in their run), so a check's
fuel depends on how the tier numbers its records, not only on its
content and lookups: I2 does not hold for fuel. Hence I1.2 also refuses
*exhausted* (a verdict that depends on fuel), and a taken slot reports
its snapshot run's fuel. 59 s against 41 s fresh (staging `Init`'s tier
and the larger feed cost more than the 1,108 checks saved).

**Open** (for the review): (1) fuel independent of the tier's numbering
(a kernel task; until then a declaration accepted near its budget could
be exhausted in another numbering); (2) nested blocks' scratch names
recorded so that an import can replay them (today they keep 37% of
`Init` from being taken); (3) an imported slot's diagnostic is S's, so a
slot number it names is S's, and N2 queries record no slot (the outcome
is compared, which decides the verdict); (4) answers are compared
exactly, so a declaration whose lookups reach a re-checked one is checked
again even when that one's verdict did not change (sound, slower).

## Questions for the owner

1. **Load speed against file size.** Rebuild the lookup tables when
   loading (file about 2.1 GB, about 45-115 s before Physlib's staging),
   or store them (about 3.2 GB, about 20-70 s)? *Recommendation: rebuild first,
   measure (SN5), and store them later only if loading matters next to the
   hours of checking; the smaller format is simpler to review.*
2. **Dependent libraries: exact mode first.** Physlib's export holds the
   Mathlib declarations it uses, and its verdicts are exactly those of
   checking that export alone; the faster open-export mode (Lean's
   `import`) comes later as an opt-in. *Recommendation: yes; exact verdicts
   first, as the owner's 100%-Lean rule asks.*
3. **Replay of any size through snapshots.** `replay EXPORT SNAPSHOT`
   replaces the planned run records 0.3; records 0.1 and 0.2 stay for small
   exports. *Recommendation: yes; one evidence format for large runs, no
   second large JSON format to approve.*
4. **No signature.** The hashes inside a snapshot catch damage, not
   forgery; that is enough for development and research runs, which never
   support a claim. *Recommendation: accept, print the file's SHA-256 in
   every report, and revisit signatures only if snapshots are shared
   between people.*
