# Backlog Forth review FRK: src/kernel (2026-11-12, main 3ac0558)

Reviewer: forth-reviewer (Opus), brief `.claude/work/briefs/FORTH-REVIEW.md`. Saved by the coordinator, condensed.
Read in full: env-snapshot, env-import, env-layers, env-schedule, inductive-nested, infer-proj, iota, caches,
replace-memo; in part: check-declaration 200-433, check-block 560-759, environment 1-420, env-publish 280-420, defeq
960-1050, the mixed-* leaf dispatches; the rest by grep, metrics and `require` chains. Not line by line: whnf, defeq
1-960, inductive-block, inductive-recursor, level-*, quot, string-literals, reduce-nat. Ran: forth-metrics, tests/core
env-snapshot.fs, env-import.fs, environment-tasks-serial.fs (exit 0), one probe for F1. Not run: make test/check,
mutants, Gforth 0.7.3. No block coverage (make coverage broken; probable cause scripts/gforth-strict.sh:31-33 drops a
LEANFORTH_GFORTH under scripts/, including the coverage wrapper).

## 0. Findings (bugs, trust boundary, docs)

- **F1 medium, reproduced: `lf-sched-add` breaks its contract** (env-schedule.fs:461-464). On "full" the context and
  the ats entry are already pushed; the caller (cli/check-run.fs:456) frees the context while the scheduler keeps it:
  a later job can run on a freed context, read past the slab, and `lf-sch-free-workers` frees it twice. Probe: jobs
  slab limited to one unit, second `lf-sched-add` → 6 (full) with 2 workers, 1 job, 2 ats. Fix: reserve room in all
  three slabs, then push.
- **F2 medium, architecture/trust boundary:** env-snapshot.fs:92-94, env-import.fs:82, env-layers.fs:42-44 require
  ../import/, pulling 7 import modules and 3 present modules (print-names, print-job, binder-table) into kernel/,
  against kernel/README.md:162 and src/README.md ("the checker never loads present/"). The core checker
  (check-declaration and its requires) is not affected. Fix: move the three snapshot-format modules to src/import/,
  move `/rr-step`'s diagnostic fields to core/diagnostics.fs, add a `require`-direction check to make test.
- **F3 low-medium:** `imp-fill` discards the lookup replay's result (env-import.fs:295); check it and plant a fault.
- **F4 low, not reproduced:** `canon-key` ignores `name-copy`'s outcome (env-snapshot.fs:459-461); a key past the
  stage's names with tier 0 could crash or write a garbage key; return an outcome and pass it up.
- **F5 low:** `sl-sane?` (653) does not range-check warnings, recipe, shape (fields 4-6); `answer-ok?` (689) not the
  holder bit; cheap checks to add.
- **F6 low:** outcomes combined with OR then `room>outcome` (env-schedule.fs:175-178, 438-443, 463): an invalid slab
  shape reported as full.
- **F7 docs:** kernel/README.md:63-64 and INDUCTIVE_BLOCKS.md:200 still say nested blocks are unsupported; src/README.md
  omits shared state `lf-sched`, `snap-loading`, `snap-stale-allowed`, `snap-site-tables`, `snap-outers`,
  `imp-current`; ADR 0020 still "proposed" though approved; env-snapshot.fs:2 calls itself [kernel] code.

## 1. Verdict

The checker's core is well factored and idiomatic: 3,619 words, 62% of 1-2 lines, 35% of 3-5, 83 of 6-10 (mostly
CASE dispatch), 1 over 10 (`snap-header`); every word has a stack comment; no locals; per-check state in context
records; xt tables for dispatch; one outcome vocabulary. The frame-step passes (defeq, whnf, mixed-*) use `>r`/`r>`
heavily (2,169, 469 in defeq) but locally and consistently. Globals 37 (5 VARIABLEs, 28 mostly read-only CREATE
tables). Worst code: the new snapshot trio — env-snapshot.fs (119 deep shuffles, 55 PICKs, three hand-written sorts,
raw byte layouts), env-layers.fs (47 PICKs and a ROLL, 6-input `lay-init`, record cursors as registers),
env-import.fs (31 PICKs, a repeated early-exit phrase); then iota.fs and infer-proj.fs (4-6-item frames), caches.fs
and replace-memo.fs (raw entry offsets, key passed through a record field).

## 2. Refactoring batches (behaviour-preserving)

- **A** (low): one combinator copied five times (`lf-check-then`, `lf-blk-then`, `lf-nest-then`, `lf-genrec-then`,
  `lf-iproj-then`) → `ok-and ( outcome xt -- outcome )` in lib/outcome.fs; `ok-with ( x outcome xt -- x outcome )`
  for the `dup ok? 0= if nip exit then drop` ladders (snap-build, lay-room, lay-arrays, lay-merge, imp-keep, imp-input,
  layer-room).
- **B** (medium; stored snapshot format): name the lookup key/answer bit layout once in environment.fs
  (`lf-look-name`, `-kind`, `-outcome`, `-reslot`, `-renumber`; keep `rshift` for 32-bit) and `/look-entry`.
- **C** env-snapshot.fs (low-medium): C1 drive `put-env` by the `same-fields` table; C2 one insertion sort for the
  three copies; C3 `snap-header`/`snap-checks` refusals via `snap-must`/`snap-placed`; C4 `snap-span`; C5 magic
  numbers (109, 559, 603, 494); C6 `snap-loading`, `imp-current` VARIABLEs → one context member.
- **D** env-layers.fs: D1 `lay-ly-start` `3 roll`, 6-input `lay-init`; D2 `staged-members` for a loop copied at
  env-layers:165, env-import:144, :218; D3 named slot ranges in `verdict-same?`; D4 iterate `lay-units` on the record.
- **E** env-import.fs (medium, import rule I1): E1 `takable?` exits, `3dup` (guarded); E2 `s-block`/`e-block` one
  loop; E3 split `ldecl-add`; E4 `/staged-content`.
- **F** env-schedule.fs: F1's fix, F6's combinators, accessors for `lf-sched lf-sch-<slab>` (~80 uses).
- **G** (medium, checker passes): shared leaf dispatch for mixed-instantiate/-open/-shift (`lf-rebuild-inert?`,
  `lf-rebuild-leaf`); `lf-tag-levelless?` in mixed-level-substitute.
- **H** (medium-high, iota and projection rules): H1 factor the whnf-then-Pi opening of `lf-iproj-param`/`-field`/
  `-end`; H2 `lf-iota-nip3`/`nip4` for ~9 failure endings, split `lf-iota-expand`.
- **I** caches.fs, replace-memo.fs (medium): I1 entry records instead of raw offsets; I2 pass the key's address
  instead of a record field (safe today only by call order); I3 one memo implementation.
- **J** small: literal store numbers in check-declaration.fs:314, 322, 347-350; B3 field numbers in
  check-block.fs:637-656; unprefixed short names in the snapshot trio (`take`, `saved`, `canon`, …) → prefixes or
  ADR 0010 privacy.

## 3. Test gaps (no block coverage)

No Forth test file requires: env-signature, generated-recursor, inductive-block, inductive-nested,
inductive-recursor, infer-proj, iota, quot, reduce-nat, mixed-head, mixed-rebuild, verdict-version (reached through
the NDJSON case tables and the CLI only). Classes 3 (stack effects and outcomes of `lf-iota`, the projection hook,
`lf-nest-translate`/`-restore-all`, `lf-genrec`, `lf-envsig-run`) and 5 (fuel exhaustion and full stores inside each
pass) have no direct tests → tests/core/<module>.fs. env-schedule: class 6 (F1, a maker that throws, re-init), class
5 (arrays full, heap push refused). env-snapshot: class 2 (bad slot fields, sites, answers, sections, identities),
class 5 (allocation refused: full, FILE untouched, no FILE.partial, blocks freed), class 6 (two saves, snap-free after
each failed step). env-import/env-layers: interrupted pass, layer of a layer, unit past its declarations, unmapped
key. caches/replace-memo: table cannot grow → a miss; memo crowding; entries left by a THROW. Missing planted faults:
`lf-sched-add` rollback, `imp-fill` replay flag, `answer-ok?` mask, `site-ok?` bound, `sl-sane?` bound, `first-taken?`
and `e-open?` forced true; none for mixed-beta and mixed-signature-audit; only 2 each for level-value, reduce-nat,
mixed-instantiate, level-geq.

## 4. Libraries

Insertion sort (three copies) → lib/sort.fs; binary min-heap on a slab (env-schedule:194-220) → lib/heap.fs;
identity-checked hash memo (caches.fs, replace-memo.fs) → lib/memo.fs; 32-bit arrays in heap blocks (`ua@`, `ly@`,
`lay-zeros`, `imp-block`) → lib/u32.fs; the outcome combinators → lib/outcome.fs.

## 5. Portability

`BOUNDS` (a Gforth extension) is used 11 times in kernel/ and also in lib/, core/, cli/, and portability.fs does not
define it: add `[undefined] bounds [if] : bounds ( addr u -- addr+u addr ) over + swap ; [then]` (and `3dup`).
env-schedule.fs:655-659 reads /proc/sys/kernel/arch while loading (falls back to serial off Linux): put it behind an
adapter. Snapshot files use only `u32-le@`/`u32-le!`. Cell width: `fld2@`/`fld2!` keep only the low cell on 32-bit;
`4 rshift` vs `/mod` agree only for non-negative cells. Nothing run with 32-bit cells or 0.7.3.
