# Forth and correctness review of refactor-frk (651da64..37a1515), 2026-11-12 — not blocking

Reviewer: forth-reviewer (Opus), read-only; read with `git diff 651da64 37a1515`, tests run in a git-archive copy of
37a1515. Scope: 4 commits, FRK batches A, B and C without C2 and C6. Files: src/kernel/check-block.fs,
check-declaration.fs, env-import.fs, env-layers.fs, env-snapshot.fs, environment.fs, generated-recursor.fs,
inductive-nested.fs, infer-proj.fs; src/lib/outcome.fs; tests, faults, baseline. Rules: .claude/work/briefs/REFACTOR.md.
Findings: 0 high, 0 medium, 3 low, 3 info. Every change is behaviour-identical by trace.

## 1. Correctness, change by change (outcome, fuel and stored state equal unless stated)
- **Batch A, one step combinator.** The five private combinators lf-check-then, lf-blk-then, lf-nest-then,
  lf-genrec-then and lf-iproj-then all had the body `over ok? if nip execute else drop then`; lib/outcome.fs `ok-and`
  has exactly that body, so all 16 call sites behave identically; same order, same short-circuit; no fuel spent in the
  combinator.
- **Batch A, ok-with ladders.** `ok-with ( x outcome xt -- x outcome )` is `over ok? if nip over swap execute else drop
  then`, replacing each `dup step dup ok? 0= if nip exit then drop` ladder. Traced: imp-keep; imp-input (split into
  imp-staged-room, imp-input-slots — imp-n stored before imp-from-room, as before — imp-from-room, imp-to-room);
  layer-room; lay-arrays; lay-room (`2 pick base-grow` → `rot base-grow`, same arguments); lay-merge; snap-build's
  tail. Same steps, same order, same first failure, same fields stored.
- **Batch B, the lookup layout named** (environment.fs): lf-look-low `15 and`; lf-look-high `4 rshift`; lf-look-above
  ( x u ) gives (u << 4) | low(x). Callers identical (answer-taken, lay-answer, answer-renum, lay-key, canon-key — the
  same bits since the low 4 bits of name << 4 are 0 — key-ok?, key-quot-ok?, key-beyond?, outer-key, answer-low?).
  /look-entry 2 cells as before. Stored keys and answers bit-identical.
- **Batch C, env-snapshot.fs.** snap-unit-table gives 4, 72, 4, 8, 1, 1, 1 as before; /snap-look 8, /snap-key 4,
  /snap-dep 4, sum-fields# 8, sh-fields# 16, firsts# 8 (si-firsts + firsts# = 29), `tp-decls 1- cells` = 7 cells, each
  at every former literal. put-env writes the same-fields table's seven fields, then marks and provenance, each to a
  distinct field: bytes identical. snap-header and snap-checks became ok-with chains of named steps refusing through
  snap-refuse with the same outcome, the same reason text, at the same first failing check; snap-placed picks the
  same xt, outcome and text. snap-span replaces the open-coded (block, size) pair. Snapshot bytes identical by trace,
  agreeing with the implementer's sha256 1dcdcdee…4fb6b (sections 0-15 equal).
- No public word's stack effect changed; the removed private combinators had no other users. Fuel cannot move: no
  walk, fuel charge or check step changed. Init evidence is the implementer's (59,349 accepted, fuel 654,719,715, 0
  differences), not re-run. CPU: the checking path executes the same code; ok-with adds one EXECUTE per step only in
  snapshot and layer load and save. The implementer's back-to-back CPU pair was pending at review time.

## 2. Findings
- **L1 (tests, changed words).** Two reviewer faults survive tests/core/env-snapshot.fs and env-import.fs: (a)
  firsts-zero? checking only 7 of the 8 firsts (no test has a base snapshot whose eighth first, identity field 28, is
  nonzero); (b) lay-ends not storing lay-site0 (no layered-load test has a base with a non-empty sites section). Both
  behaviour-identical today; add the cases and plant `frk-firsts-zero-short` and `frk-lay-site0-lost`.
- **L2 (fault list).** cd-no-restart (lf-check-value without lf-check-restart) survives without being listed, also on
  651da64; its case no longer fills the term store in step 7. Re-point it or list it as a gap.
- **L3 (style).** snap-must ( snap flag outcome c-addr -- outcome ) takes 4 items; a `why` entry of two cells (outcome,
  text) would make it ( snap flag why -- outcome ).
- **I1 (naming).** lib/outcome.fs holds both `outcome-and` and `ok-and`; `ok-step`/`ok-step-with` would say what they
  do. env-schedule's lf-sch-and could use outcome-and.
- **I2.** The C2 skip (insertion sorts wait for lib/sort.fs) and the C6 skip (not identical after a THROW) are
  recorded; keep both as plan tasks.
- **I3.** The CPU pair was still pending.

## 3. Forth style (forth-metrics, 10 files, base → head)
Words 1215→1259; 1-2 line words 721→759; 6-10 line words 36→30; over 10 lines 1→0 (snap-header). Deep shuffles
308→297, return-stack ops 592→575; globals 19 and long lines 0 unchanged. env-snapshot 117→106 shuffles, 193→176
return-stack ops; env-import 6-10 line words 4→2; env-layers 5→3. tests/forth-quality-baseline.json changes only
downward. Idiom: one shared vocabulary instead of five copies; named layout constants instead of 4, 8, 15, 16, 29; the
snapshot header checks as an ok-with chain; the same-fields table drives both writing and comparing.

## 4. Tests and faults
29 faults new or changed in the range: 28 caught, cd-no-restart survives (L2); `mutants --check` 1346 entries, 0
stale. Reviewer's 8 faults: 6 caught, 2 survived (L1). Gforth 1.0.0 and 0.7.3, all exit 0: tests/lib/lib.fs,
core/env-snapshot.fs, env-import.fs, check-declaration.fs, check-block.fs, inductive-nested.fs, environment.fs. Not
run: make test or check, Init, the CPU pair, coverage. AI review does not replace the owner's [kernel] approval.

## Summary for the owner
1. What changed: the kernel code was tidied without changing what it does: five identical helper words became one
   shared word; the numbers describing how a snapshot stores its lookups got names; the snapshot-file checks became a
   list of small named steps.
2. Evidence: every changed word checked by hand: the same results, fuel and stored data on success and failure. Kernel
   tests pass on both Gforth versions; 28 of 29 planted faults caught (the survivor survived before this branch). The
   implementer reports all of Init identical (every result and fuel count) and a byte-identical snapshot.
3. Risks: low. Two small test gaps (L1) and one stale planted fault (L2); none hides a behaviour change. Speed
   comparison pending, but the checking path runs the same code.
4. Recommendation: approve. Fix L1 and L2 before or soon after the merge, record C2 and C6 as plan tasks, wait for the
   speed comparison before calling it done.
