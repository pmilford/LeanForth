# ADR 0005: structured names — proposal

Status: **accepted** (see the approval status below). Lean names
are needed for universe parameters, constants and declaration identities.
This proposal does not authorize any declaration or axiom.

Approval status: accepted 2026-11-12, gate: kernel, import and format, [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section "Approval round of 2026-11-12, night (approval pack)"; the owner approved it on the pack's recommendation

## Candidate representation

Represent anonymous names and chains of `str(prefix, component)` and
`num(prefix, component)`. Name equality depends on the full structured prefix,
the component kind and the exact string or natural-number component. Do not
merge numeric components with digit strings or normalize visually similar
Unicode spellings. A future importer must interpret Lean strings correctly,
validate its input encoding, handle Lean's natural-number range or report a
resource limit, and never equate names merely because their export indices match.

Interning is a candidate optimization: within one immutable table and lifetime,
the same structured name may receive the same ID. This depends on correctly
canonicalizing prefixes, protecting the storage and preventing ID reuse across
resets. A numeric ID alone does not establish Lean name identity across imports,
tables or lifetimes. Any serialization must encode structure and bytes, not a
host pointer or cell layout.

## Experimental evidence and limitations

`src/core/names.fs` uses global mutable bounded storage, byte strings
and nonnegative host-cell numeric components. It interns equivalent components
under the same prefix and checks basic storage bounds before reading strings.
It does not validate UTF-8, protect raw memory, authenticate stale IDs or prove
canonical uniqueness after corruption. Caller-supplied input addresses must be
readable. A test-only stream maps interned IDs into an experimental level
context; the IDs are not connected to trusted declaration or level checking.
`make test-name-differential` compares nine hand-selected cases with Lean
4.35.0; this is finite evidence, not proof of general name compatibility.

Before using name identity in trusted conversion or declaration lookup, a human
reviewer must examine encoding semantics, canonicalization, overflow, table
ownership and lifetimes, corruption handling, resource limits and integration
with Lean import. The existing symbolic-level comparison still depends on an
external opaque-ID identity assumption and is not made trusted by this arena.

## Amendment 1 (proposed, 2026-11-18): an index for the stored names, and an audit kept between calls

Approval status: proposed

Status: proposed for the [kernel] gate (branch `names-index`, from main
`b403ac21`). `src/core/names.fs` is read by the kernel and the import, so
the change goes through the gate in `AGENTS.md`; it changes no typing or
conversion rule and no outcome of a well-formed run. Plan: the
performance scan's item 1 (A1, A2;
the scan's report, PERFORMANCE_SCAN.md, on branch
`perf-scan`).

### The change

The name store has two modes. Under a view (`lf-name-attach`; ADR 0016
C3), the mode of every export check, names live in a compact tier that
finds them by hash and checks each when it is made (ADR 0016 C8). In the
stored mode (tests, the authoring words, and the front end of a `.lf`
check, which decodes library declarations into the run's own names) two
costs grew with the square of the names:

1. **The find** (`lf-name-find-num`/`-str`) read every entry until it met
   the name. It is replaced by a hash table on `lib/htab.fs` (hooks: the
   entry's kept hash, and a compare of kind, prefix and component), with
   the hash of `lib/hash32.fs` as the compact names use (kind, prefix,
   then the number or the bytes' FNV-1a). Each entry keeps its hash in a
   fifth cell, so the table can grow, and take out the names a rollback
   gave back, without reading their bytes.
2. **The audit** (`lf-name-storage-valid?`, run before every intern and by
   every reader that walks names) read every entry. It now keeps a record:
   the count, generation and byte use at its last pass. The next audit
   checks the header (count, byte use, generation, the store's seal) and
   the root entry as before, and then only the entries from the recorded
   count up. It reads every entry again after a reset (the generation
   moved), when byte use went down (a rollback, or a write), and after a
   failed audit.

**Same IDs.** An entry is made only after a find for it failed, so no two
entries are equal, and the index gives the one entry equal to a name: the
ID the linear search gave, in the same order. The index follows the store:
before a find, entries at or above the count (a rollback) leave the table;
a reset, an attach and a detach empty it (a table one large run grew is
made small again, `htab-renew`). A slot whose entry is at or above the
count is passed over. A table that cannot grow (no heap) refuses the new
name as names full, with the index's count in the diagnostic; an existing
name is still found.

### What the audit guaranteed before, and guarantees now

Nothing in LeanForth writes an entry after making it; the audit guards
against writes from outside the module (a memory fault of other code, or
a test that corrupts the store on purpose).

- **Before:** at every name operation and every check of the storage,
  every entry was read: a corrupted tag, a prefix that does not point
  backwards, or a string outside the bytes in use, anywhere in the store,
  failed the call (fail closed).
- **Now, still caught at the next call:** any corruption of the header
  (count, byte use, generation, seal), of the root entry, or of an entry
  the audit has not passed yet (the newest entries, and entries a raw
  write of the count exposes); any entry a find reaches (the find checks
  the entry before comparing it, and a corrupted one stops the find and
  refuses the name, so its bytes are never read).
- **Every walk of a name checks its chain** (`lf-name-chain-ok?`, review
  finding 1): each component is a name now, its prefix points back and its
  text lies in the bytes in use, one comparison per component. Name
  equality (`lf-name-ids?`, both IDs) and the printer (`lf-pp-name-to`,
  `lf-pp-hygienic?`) call it, so a name corrupted after its audit gives
  false or an invalid print, never a loop or a read out of bounds.
- **A full audit at the hand-over** (review finding 2): before the stored
  names are written for the kernel's check of a `.lf` text, or exported
  at all (`author/export.fs`'s `lfx-unwritable?`), every entry is read
  from entry 1 and every kept hash is recomputed from its entry and
  compared (`lf-name-audit-all?`); a failure refuses the export as
  invalid. It costs 2 ms for 27,000 names (`gforth-fast`), once per text.
  So what the kernel checks has had the old audit, plus the hash cell,
  which the old audit never read.
- **Now, no longer caught at the next call:** a write into an entry the
  audit already passed, when it leaves the header as it was. It is caught
  when a find or a walk meets that entry, or at the hand-over, or at the
  next full pass (a reset, byte use going down); an interning or a
  storage check that reads neither goes on. Compared with ADR 0016 C8 and
  its step S2 note (owner-approved 2026-11-04): the names under a view
  are checked when made and not audited again, as now; the term and
  level stores audit a node once per epoch and keep a bound check on
  every read (`store-at?`) and fuel on every walk; the stored names keep
  the chain check on every walk instead, and the hand-over audit.

Tests: in `tests/core/names.fs` an entry corrupted after its audit is
refused when its own name is interned and seen by an audit from entry 1
(`lf-name-entries-from?`) and by `lf-name-chain-ok?`, while the kept audit
passes; in `tests/core/run-record.fs` (`lf-env-viewed?`, fault
`rv-env-viewed-names`) the corrupted entry is the root, which every audit
reads; `tests/present/term-printer.fs` keeps main's case (a prefix pointed
forward on a name, now caught by the chain check: invalid) and adds the
root's; `tests/author/author.fs` refuses an export with a rewritten hash
or prefix.

### Alternatives rejected

- **Keep the full audit.** It is 69% of a `.lf` check against Init (about
  59 s of 86 s; 207,781 audits visiting 2.99 billion entries) and grows
  with the square of the names: hours for Mathlib's 43,808 instances.
- **Remove the audit.** The header, root and new-entry checks cost one
  pass over each entry once and keep every check the view and the term
  store make; removing them would make the stored mode weaker than both.
- **A running checksum of all entries.** Checking it reads every entry,
  the cost removed; keeping it current only proves the module's own
  writes.
- **The full audit only for readers outside interning** (name equality,
  the printer, the environment's checks), the kept audit for interning:
  keeps the old guarantee for those readers, but their calls alone are
  about 38,000 full audits in the Init `.lf` check (about 7 s) and still
  grow with the square of the names. The full audit runs instead at one
  defined point, the hand-over above.
- **Run the front end's names as a view over the library's tier** (the
  scan's other option): a larger change of the front end and its IDs; it
  may follow, and this change does not prevent it.

### Evidence

All on the shared 10-core WSL2 machine, load average 3 to 6, Gforth 1.0.0,
git archives of main `b403ac21` and the branch at `4535e786`
(evidence in the branch worktree's `.claude/work/names-index/`).
**Again after the review's fixes** (the chain check, the hand-over audit,
`hash-3`), branch at `15d1983f`: all of Init 59,349 accepted, none
differing from main in any field, fuel 654,719,715, the snapshot byte for
byte main's (`e120cf67…`; 595 s wall, 1,156 s CPU); the seven `.lf` texts
byte for byte main's with the same exit codes, those that check in
13.1–15.5 s; 37 name-related faults run, all caught. The figures below
are the first head's.

- **Kernel identity on all of Init** (`bin/leanforth check --json --jobs 2
  --save-snapshot`, `gforth-fast`): 59,349 declarations accepted in both,
  none differing in any field, fuel 654,719,715 in both; the two snapshot
  files byte for byte the same (SHA-256 `e120cf67…`). Time: main 610 s
  wall / 1,179 s CPU, the branch 568 s / 1,101 s (not slower; the export
  check runs the names under a view, which this change does not touch).
- **`.lf` checks against Init through the snapshot** (`check --snapshot
  init.lfsnap --elab-data init.elab.ndjson`, `gforth-fast`): the output of
  seven texts byte for byte the same on main and the branch, with the same
  exit codes (`s1-rfl`, `01-zero-add`, `01-zero-add-rw`, `03-zero-add-exact`,
  `04-nested-ih`, `05-unsolved`, `06-sorry`: exits 0, 2, 0, 0, 0, 4, 0).
  Time of the five that check: main 73–80 s, the branch 13.1–14.1 s.
- **Tests**: `tests/core/names.fs` gains the index against the linear search
  as reference on 6,000 mixed names, rollback (names given back leave the
  index; a block shrunk below them), reset and detach (stale IDs), the
  index out of room, and the kept audit's restart rules; the focused
  targets `test-core`, `test-run-records`, `test-present`,
  `test-environment` pass.
- **Faults**: 11 new (`ni-*`) and `core-names-entry-after-root` re-targeted,
  all caught; the 14 existing name faults still caught.
