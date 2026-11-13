# Decisions: an index

One line per decision, newest groups last, each pointing to the record that holds it: an ADR in
[docs/adr/](../adr/) (each carries an "Approval status" line) or a section of
[OWNER_DECISIONS.md](OWNER_DECISIONS.md) (the owner's own answers, with dates and gates). Where a decision's rationale
or rejected alternatives were recorded only here, they are kept in condensed form after the link ("Rejected:"). Until
2026-11-12 this file held the full text of each entry (last updated 2026-11-04, except the last entry); the full text
is in git history (`git log -- docs/project/DECISIONS.md`). New decisions go to an ADR or to OWNER_DECISIONS.md and
are indexed here.

## Bootstrap and policy

- **Bootstrap boundary.** The first Forth module is a host smoke test, not a proof kernel; Gforth cell arithmetic and
  execution are host assumptions, and the CI distribution Gforth is a separate compatibility check. No separate record.
- **Kernel and execution design.** Indexed DAGs against pointer trees, per-check arenas against reference counting,
  FFI outside the kernel: settled later by [ADR 0016](../adr/0016-compact-store.md) and
  [ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md); typing rules in
  [ADR 0001](../adr/0001-core-fragment.md) and [ADR 0002](../adr/0002-core-rules.md) (status unclear there).
- **First examples: a polymorphic composition proof and a bounded integer clamp.** Both now exist; see
  [PROJECT_PROGRESS.md](PROJECT_PROGRESS.md) and [PROGRAM_EXAMPLE.md](../programming/PROGRAM_EXAMPLE.md).
- **Symbolic universes and the Sort boundary.** [ADR 0004](../adr/0004-symbolic-universes.md),
  [ADR 0007](../adr/0007-sort-representation-boundary.md). Rejected: treating universe parameters as arbitrary
  concrete numbers or as axioms (neither checks a polymorphic declaration).
- **Owner policy decisions, 2026-11-02** ([OWNER_DECISIONS.md, "Recorded answers"](OWNER_DECISIONS.md#recorded-answers)):
  Lean is the referee; narrow first checker with three outcomes; cautious equality first; axioms only
  `propext`, `Classical.choice`, `Quot.sound`. Rejected: blocking on an outside expert (stalls the project), AI review
  alone (shared blind spots), data types in the first checker (too large), full Lean equality at once, no axioms ever
  or whatever Lean allows (Mathlib unusable, or Lean's compiler silently trusted). The label requirement was withdrawn
  2026-11-12.
- **2026-11-03: behave identically to Lean; rejection rules and compact store accepted**
  ([OWNER_DECISIONS.md](OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)). Rejected: keeping
  LeanForth deliberately more cautious than Lean where Lean decides (identical first, improvements later).
- **Axioms and the default are Lean, 2026-11-03**
  ([OWNER_DECISIONS.md](OWNER_DECISIONS.md#data-types-axioms-and-imports-2026-11-03-late-night)): Lean's verdict by
  default, NOT PROVED marked, stricter behaviour only behind opt-in flags.
- **MiniForth reviewed as related work, 2026-11-03** ([review](../development/MINIFORTH_REVIEW.md)): adopted early
  binding, a Lean well-formedness check, fuel-free semantics proved equivalent, verification conditions as proved
  rules. Rejected: unbounded integers, a late-bound global dictionary, Lean quotation syntax as canonical form, a
  mandatory ELSE, use as a test oracle; it has no licence, so no code is copied.

## Tooling, layout and refactors (2026-11-02, owner approved where marked)

- **Tooling, CI and agent handover.** `AGENTS.md` is the single rule set and `.claude/CLAUDE.md` imports it; the
  Makefile calls the pinned Lean binary directly; installers verify SHA-256; `make test` and `make check` are the
  aggregate targets; docs live in `user/`, `programming/`, `development/`, `project/`, `reviews/`, `adr/`
  ([docs/README.md](../README.md)); the two ADRs numbered 0005 were disambiguated (Sort boundary became 0007).
  Rejected: relying on the elan proxy (silently downloads 3 GB), running the elan installer script in CI (unpinned
  download), Forth-only CI (left about 40 Lean comparisons unchecked), moving `adr/` under a design folder.
  GitHub CI has been off since 2026-11-11 ([OWNER_DECISIONS.md](OWNER_DECISIONS.md#approval-round-of-2026-11-11)).
- **Source layout (owner approved)** ([src/README.md](../../src/README.md)): `lib/`, `core/`, `kernel/`, `import/`,
  `program/`, one loader `main.fs`; the split was computed from which words each module uses. The kernel is developed
  in `kernel/` and nothing counts as verified until the owner says so after the review gate. Rejected: `core/` versus
  `experimental/` (names said nothing), an empty `kernel/` reserved for reviewed code, keeping superseded copies in
  `core/`, one wordlist per folder (needed an ADR; became [ADR 0010](../adr/0010-wordlists.md)).
- **Forth library and the bottom-layer refactor.** Term, level and name stores share `src/lib/store.fs` and
  `node.fs`; public words and stack effects unchanged, evidence by old/new differential. Store shape fields became
  writable cells, so the shape is checked at definition and sealed with a check value (corruption fails closed).
  Rejected: renaming public words now (touches 100 test files), `require` of single library files (double-load risk
  on hosts that do not normalise paths), trusting the shape fields, locals.
- **Walk records, paired walks, and the kernel refactor in parallel groups.** `src/lib/walk.fs` holds the work-stack
  loop once (`walk:`, `walk2:`, `frames:`), `outcome.fs` replaces per-module status constants
  ([ADR 0008](../adr/0008-outcome-vocabulary.md)); five agents refactored groups A-E in parallel worktrees, merged one
  at a time, with about 17 million randomized comparisons against the old code. Open at the time: three recursion
  patterns coexist. Rejected: a per-walker execution-token table, one generic visitor with a handler table, per-module
  status constants with equal values, module-by-module conversion in one session, groups editing shared library
  files.
- **Legacy retired, 2026-11-02** ([OWNER_DECISIONS.md](OWNER_DECISIONS.md#legacy-retirement-and-the-first-checkers-rules-2026-11-02-evening)):
  `src/legacy/` (28 modules) and `tests/legacy/` deleted by exact path after every legacy-only case had a test of
  current code. Accepted losses: the pair arena, two-tier raw index, standalone constant probes, concrete-universe
  overflow handling. Two intended semantic changes: syntactic comparison treats Sorts with equal level syntax as equal;
  conversion reduces binder domains instead of requiring them to match. Rejected: porting the four legacy-only
  capabilities first, keeping legacy as a reference copy.
- **Each module requires its direct dependencies** (owner direction; `main.fs` requires only its five top modules).
  Why `require`: Gforth loads the file once even through different relative paths, `include` reloads and would create
  a second term store. Rejected: requiring single library files, keeping the order in `main.fs` and every test.
- **Tag `refactor-parallel`** (`ada6dba`), placed after the review fixes of the context conversion so no known open
  finding sat in the tagged version.
- **Test speed: parallel make and the pinned-Lean cache** ([TESTING_STRATEGY.md](../development/TESTING_STRATEGY.md)):
  8 jobs by default; Lean's run replayed from a cache keyed on the SHA-256 of toolchain, options, source and
  `LEAN_PATH`, so an upgraded Lean never replays an older verdict; the Forth side always runs; CI runs with
  `LEAN_CACHE=0`. Rejected: caching whole make targets (a stale pass could hide a fault in our own code), no cache
  (345 s per run, so run less often), parallelism only in CI.

## Checker and import designs

- **Outcome vocabulary and the split of exhausted and full, 2026-11-02**
  ([ADR 0008](../adr/0008-outcome-vocabulary.md), [OWNER_DECISIONS.md](OWNER_DECISIONS.md#planning-answers-2026-11-02-later-the-same-day)):
  *exhausted* (2) is fuel, *full* (6) is room, fuel decides when both are out; evidence on 616 randomized seeds.
  Rejected: renumbering (breaks tests), one combined code (hides which limit to raise), moving work-stack and depth
  checks behind a fuel check, keeping *exhausted* for a corrupted limit.
- **Re-entrancy and parallelism by Forth tasks** ([ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)):
  one image, a task pool, no process sharding (one copy of the environment, no serialization, 0.7.3's cooperative
  tasker still tests interleaving in CI). Development runs may reuse saved results labelled not re-checked; final
  runs never do (rejected: always re-checking in development, slow at Mathlib scale).
- **Exceptions: `THROW` only inside one operation** ([ADR 0018](../adr/0018-exceptions.md), accepted 2026-11-03).
  Rejected: outcomes only (plumbing, hand-written rollback), throwing every non-ok outcome, throwing outcome numbers,
  Gforth's `exception` numbers, catching host errors in inner boundaries. A Gforth 1.0 worker-backtrace heap
  corruption found in the pilot is fixed in `src/lib/task.fs`.
- **Wordlists: a public and a private list per group** ([ADR 0010](../adr/0010-wordlists.md), accepted 2026-11-03).
  Rejected: export lists through `SYNONYM` (0.7.3 needs a non-standard adapter), one wordlist per module, a single
  public list (kept as fallback for hosts with eight search-order entries), everything in `FORTH-WORDLIST`.
- **Compact store for Mathlib-scale input** ([ADR 0016](../adr/0016-compact-store.md), accepted 2026-11-03).
  Rejected: B-trees, unshared trees (10^14 nodes), 64-bit fields (about twice the memory), a stored hash, chaining,
  file-backed storage, one input copy per worker.
- **Stores that grow on the heap, 2026-11-03** (agent KC; [ADR 0016](../adr/0016-compact-store.md) C9 step 3): doubling
  heap blocks with per-context capacities and the old values as defaults, so verdicts, fuel counts and diagnostics
  stay identical; growth refused gives *full*. Cost then: `Init` up to 1.27 GB, about 2.2 times slower on random
  trials. Rejected: bigger fixed capacities (cost every check, still a ceiling, move the points where tests reach
  *full*); reading the compact store's terms in place for now (later done as S5, see
  [OWNER_DECISIONS.md](OWNER_DECISIONS.md#approval-round-of-2026-11-12)).
- **The importer's two passes must read the same bytes, 2026-11-03/04** (review rvRP3): a checked read keeps the first
  pass's SHA-256 and requires the second to equal it; every recorded run compares it with `input.sha256`
  ([OWNER_DECISIONS.md](OWNER_DECISIONS.md#import-read-approved-fixed-limits-to-become-dynamic-2026-11-04)). Rejected:
  narrowing the documented claim to exclude a change during the first pass (plain checks stay exposed).
- **Forth NDJSON reader, and no binary quick import yet** ([NDJSON_READER.md](../development/NDJSON_READER.md);
  [OWNER_DECISIONS.md](OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)): reads in 1 min 43 s on
  all of Mathlib. Rejected: a binary quick import (reading is far cheaper than exporting or checking, and a second
  format needs its own specification and tests).

## Authoring and program track

- **LeanForth Forth syntax** ([ADR 0017](../adr/0017-leanforth-syntax.md), accepted 2026-11-02): theorem text is
  words run by Forth's own interpreter with only LeanForth's wordlists visible; names case-sensitive through a
  re-reading spelling check; notes (`note"`, `ai-note"`) kept but never checked. Rejected: a string-parsed syntax, a
  reader with its own lookup, Gforth-only case-sensitive wordlists or recognizers, forbidding case-only differences,
  one wordlist per binder, plain-word connectives (`app`, `proof`, `succ`, `max` are common Mathlib binder names),
  brackets or S-expressions, unchecked first-match lookup, universe arguments inside tokens, notes kept apart from the
  source.
- **Program words in two modes** ([ADR 0019](../adr/0019-program-words-two-modes.md); answers in
  [OWNER_DECISIONS.md](OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)): Forth's own interpreter
  reads the file and each word's verification meaning writes the IR; a portable mode shift is primary, the alias
  vocabulary kept beside it. Rejected: dual-mode words testing a flag (run mode no longer plain Gforth), "verify while
  loading" (the file's code would run inside the verifier), Gforth recognizers, symbolic results as the obligations
  themselves, running in the checker's process.
- **Program reader (the older text reader): names ignore ASCII case; no division before CONSTANT; the reader splits
  lines itself** (2026-11-02, reviews of the old reader; case rule in
  [OWNER_DECISIONS.md](OWNER_DECISIONS.md#progress-marks-and-program-reader-names-2026-11-02-night)). Rejected:
  refusing upper-case names (refuses the standard spelling), exact comparison (unsound against a case-insensitive
  host), refusing a definition whose name the host already defines (acceptance would depend on the reading session).
  Receipt schema 0.1 was tightened in place because it was an unapproved draft with no receipts.
- **Program receipts 0.3 and the clamp proofs re-checked by LeanForth, 2026-11-12** (plan 5.5.1;
  [OWNER_DECISIONS.md](OWNER_DECISIONS.md#program-track-leanforth-re-checks-leans-program-proofs-2026-11-12-evening-plan-551)):
  0.3 is 0.2 without `check.label`; the 23.6 MB export is pinned by a committed manifest and made again by
  `make check`; a receipt never says more than LeanForth's verdict. Rejected: committing the export (23.6 MB), a
  structured `proofsBy` field (a format change beyond the owner's decision).
