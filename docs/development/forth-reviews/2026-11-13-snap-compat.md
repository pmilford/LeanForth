# Forth and correctness review of snap-compat (c834e0e..0e1021c), 2026-11-13 — blocking

Range c834e0e..0e1021c (9 commits, 025f4eb to 0e1021c). Findings: 0 high, 2 medium, 7 low, 4 info, 6 style. AI review;
the owner's [format], [kernel] and [import] gates remain. Blocking: M1 breaks the rule the gate is asked to approve
(nothing stale shown as this build's result); latent today (every in-window file needs step 9, which reaches
everything); fix is one line plus one test.

## Owner summary
1. LeanForth now loads a snapshot made under one of the two previous rule versions: it prints how many results it will
   check again, re-checks everything the rule changes since could affect, keeps the rest; `--save-snapshot NEW` saves
   the result as a current snapshot.
2. Today change 9 affects everything, so older snapshots are re-checked in full; every result equals a fresh check (the
   reviewer's tests and the implementer's Init measurement); the test snapshots rebuild byte for byte from the builds
   that made them; 21 of 22 planted faults caught (the 22nd a known equivalent).
3. Risks (only once a future rule change is narrower than "everything"): `--snapshot-stale-ok` can call a result
   current when it rests on an old one (M1); an upgrade made without the export cannot notice a change in how exports
   are read (M2).
4. Recommendation: approve after M1's one-line fix and test; add a rule for M2 to the design before the first narrow
   change; accept the relaxed "copied from the old file" mark in base snapshots until c6 (labels only, never a
   verdict).

## Answers
- A carried result cannot differ from a fresh check with today's table (window 7-9; any v7/v8 file includes step 9,
  reach everything). Entries vs the changelog: 3, 4, 5, 9 reach everything (correct); 6, 7 reach-block-any (sound);
  8 reach-block-nested (sound: the publisher gives every span member the block's recipe); 2 reach-scratch-names (an
  unevaluated bit: counts as everything). The differential catches a wrong entry (step 9 narrowed: impliesSelf carried
  with fuel 65 vs 68 fresh), though the Python model's guard catches it first (L2).
- A stale verdict reported as this build's: yes in two ways (M1 code, M2 design); everything else labelled correctly.
- Fail-closed: v6/v10 refused (2); damage (cut short, byte changed, outcome out of range) 4; provenance 4, 7 in a base
  and 2 in a layer 4; mixed versions refused (2); forged saved axioms stop invalid; every answer slot a reach
  evaluation reads is bounded by the loader.
- Determinism across --jobs: the hook runs only in the driving task; I3's record written at hand-over; a "wait" (2)
  answer is asked again once every slot below is final; tests compare outcomes, fuel and the carried set between two
  workers and serial; an upgrade written with --jobs 2 is the same bytes. Edges: L4, L5, L6.
- Fuel identity: a carried slot gets its saved fuel; C4 (--fuel must be the file's) enforced by the loader.
- Provenance relaxation: affects neither verdicts nor reports (snap-fill publishes every slot as "saved"); loses
  traceability of upgraded bases; acceptable; keep c6's lineage section.

## Findings
- **M1 (medium, blocking):** with `--snapshot-stale-ok`, a carry run labels users of stale results as carried
  (check-run.fs:553 `ck-same`, :581 `ck-deferred?`, :1069 `ck-filling`; env-import.fs:484 `imp-same`): ck-filling makes
  snap-fill the check word so the rest is published stale, but ck-same/imp-same still compare the stale slot with
  itself (always equal), so a user deferred for its answers is carried, labelled "this build's changes since cannot
  affect it". Probe (scratchpad/probe/stale-carry.fs, v9/nested.lfsnap, a pretended step 10 reaching definitions): 16
  users of 40 stale definitions carried, e.g. `HAdd: accepted (from snapshot of verdict version 9, carried …)`. Fix:
  `: ck-rechecking? ( -- flag ) ck-carrying? snap-stale-allowed @ 0= and ;` used by ck-same, ck-deferred? and
  ck-filling; a test in tests/core/env-import.fs (with --snapshot-stale-ok and reach-kind-definition, ck-carried# equals
  the first pass's count; why-answers why# 16; a user's verdict text says stale); a planted fault dropping the
  condition.
- **M2 (medium, design, [import]):** an upgrade without the export keeps the old build's reading of the export
  (SNAPSHOT_COMPATIBILITY.md:326 C1, :417; verdict-version.fs:121): with no export the input is OLD's tier (the older
  build's staging); if the importer changed, re-checked results are not this build's for the export, yet reported and
  written as version 9. Latent (no step 2-9 changed the importer). Fix: a reach bit `reach-reading` (an importer
  change takes `reach-all reach-reading or`); a base whose steps since hold it is refused without an export
  (unsupported, "check the export again"), stale with the flag; amend S-R in the design and verdict-version.fs.
- **L1:** `cli-window-note` (leanforth.fs:587) says "this build reads snapshots of verdict versions 7 to 9" while
  refusing an 8 because of layers (c7): add `cli-layered-note`.
- **L2:** the Python model (test_leanforth.py:3211, 3228-3245) is the first version's (C5 as I1.3) and decides only
  three bits: model I3, test it under a pretended `{10: reach-block-nested}` table on v9/nested (35 checked again), let
  snapc-step9-narrowed be caught by the differential.
- **L3:** `ck-stale#` can go negative in a failed carry run with --snapshot-stale-ok (-51 seen): `: ck-stale# ( -- n )
  ck-verdicts? if ck-saved# ck-carried# - else 0 then ;`.
- **L4:** a failed decision in a parallel run does not stop where the serial run stops (check-run.fs:590
  `ck-pre-failed`): add a hook answer 3 = stop at d with a dispatch table.
- **L5 (latent until c7):** `early?` (env-import.fs:314) keeps only the last candidate's value: OR it in.
- **L6:** the hook's "never answer 2 again" contract is not enforced (env-schedule.fs:577-581): a guard turning a
  frontier "2" into "check it".
- **L7:** an export run on an older base writes a version-9 layer nothing can load: until c7 refuse --save-snapshot in
  a carry import as misuse ("upgrade the base first").
- Info: I1 entries 2-8 can never take effect (precedent only); I2 `--snapshot ./x --save-snapshot x` overwrites its own
  input (safe but destroys OLD; the same-name guard compares names only); I3 the documented departures; I4 18 new
  snapc-* faults plus 4 updated (22).

## Style
1349 words (+97) in 7 files; no new long words; shuffles 211 and return-stack ops 402 unchanged; one more global
(lf-verdict-steps, a constant table). S1 `imp-held` used as a register (keep reach bits on the stack: own-holds,
saved-holds, looks-hold, d-holds); S2 repeated phrases (ck-rechecking?, step-why, ck-fact-of); S3 magic numbers in
kind-reach (reach-kinds#); S4 an IF chain in cli-why-again. (CASE); S5 `why` takes four items; good: the reach table
as data, the window check at load, a three-word hook, short CLI words, Forth-2012 only.

## Tests and runs
Covered: every outcome, malformed input, interfaces, 24 differential runs, upgrade, --jobs 2 bytes, stale-ok, fixtures
with SHA-256. Gaps: M1's case, heap refusals for the new allocations (keep-sds, input-maps, same-maps), faults for M1,
cli-window-note, ck-stale#. Runs (git archive copy, `ulimit -u 500`, nice -n 19): env-import.fs, env-snapshot.fs on
Gforth 1.0.0 and 0.7.3; test_leanforth.py ReachTable OlderSnapshots (6 OK, 24 runs, 0 carried, 1176 checked again, 0
differences) and Snapshots Imports Layers (26 OK); `mutants --check` 1352, 0 stale; the 22 faults: 21 caught;
write-snapshot-fixtures.sh for 7301204 and 2ad871e reproduce the v7/v8 SHA-256s; the M1 probe; the step-9-narrowed
copy; the L1, L7, I2 CLI cases. Not run: make test/check, coverage (a mis-typed coverage call overwrote a file in the
reviewer's scratch copy, restored from git; coverage unverified), Init, Jobs CLI classes, pinned Lean.

## Re-check of 0e1021c..72d1dae (2026-11-13): not blocking

One commit (72d1dae). Findings now: 0 high, 0 medium, 2 low, 3 info. M1, M2, L1, L2, L6, L7 fixed and verified; L3
and L4 fixed but untested; L5 fixed, untested until c7.

Owner summary: (1) LeanForth loads a snapshot made under one of the two previous rule versions, prints how many results
it will check again, re-checks everything the changes since could affect, keeps the rest, and can save the result as a
current snapshot. (2) Today every older snapshot is re-checked in full and equals a fresh check; both problems are fixed
and checked: `--snapshot-stale-ok` no longer passes off a result resting on an old one as current, and after a change
in how exports are read an old snapshot can no longer be used without its export; all 22 planted faults caught. (3)
Risks: two small fixes have no test yet (a stopped parallel run, a count after a failed run); a wrong future "reach"
note is still caught only by the comparison tests on the fixtures. (4) Recommendation: approve; add the two small tests
or record them as plan tasks; accept the relaxed "copied from the old file" mark in base snapshots until c6 (labels
only).

- M1 fixed: `ck-rechecking?` (check-run.fs:557) guards ck-same, ck-deferred?, ck-pre! and ck-filling; the probe now
  gives 51 carried with --snapshot-stale-ok (the first pass; the 16 users stay stale, stale# 56) and 67 without; test
  and fault snapc-stale-rechecks; the forged-definitions run is still refused invalid (right: inconsistent file).
- M2 fixed: tested in a copy whose step 9 entry was `reach-all reach-reading or` on v8/unfold: snapshot alone status 2
  "export reading" with a note; with --snapshot-stale-ok all stale; with the export both declarations checked again;
  upgrade refused (2), no file; a v9 snapshot unaffected; S-R amended in verdict-version.fs and the design.
- L1 refusal reasons "older base with layers"/"older layer" with notes (CLI tests; reviewer fault caught). L2 the model
  runs after the differential; with step 9 narrowed the differential itself fails (fuel 65 vs 68);
  test_model_pretended predicts 35. L6 a frontier "wait" counts as 0 (snapc-frontier-wait caught). L7 no layer written
  after an export checked against an older base (status 4, no file; snapc-carry-import-saved caught). Heap refusals:
  every carry-load allocation gives full; the 11 ok ones are the seal's slab trims (a refused shrink keeps the larger
  block, as stage-seal does); the test pins 11.
- **L3 (low, test gap):** the `ck-stale#` guard (check-run.fs:1150) is untested (restoring the old formula survives):
  add `T{ ... ck-outcome ck-stale# -> outcome-invalid 0 }T`.
- **L4 (low, test gap):** hook answer 3 is untested (`ck-pre-failed` answering 0, and `lf-sch-pre-stop` without
  `lf-sch-stop!`, survive): a unit test like L6's.
- Info: I1 L5's OR is right, untested until c7; I2 S1 and S5 kept (accepted); nits reach-kinds# literal 5,
  ck-import-facts repeating ck-fact-of; I3 the Python model assumes every re-checked slot answers as saved (errs safe);
  the design doc cites .claude/work/pending-reports (point it at docs/development/forth-reviews once logged).
- Style: no new long words; shuffles 211 and return-stack ops 402 unchanged; no new globals; new words each 1-3 lines.
- Runs (git archive of 72d1dae, `ulimit -u 500`, nice -n 19): env-import.fs and env-snapshot.fs on Gforth 1.0.0 and
  0.7.3; test_leanforth.py ReachTable OlderSnapshots Snapshots Imports Layers 33 OK; `mutants --check` 1356, 0 stale;
  the 22 snapc-* faults caught; reviewer faults: L1's caught, L3, both L4 and L5 survived. Not run: make test/check,
  coverage, Init, Jobs classes, pinned Lean.

## Re-check of 72d1dae..edb5554 (2026-11-13): not blocking

1aa68b8 and edb5554. Findings: 0 high, 0 medium, 0 low, 1 info. The reviewer's L3 and L4 faults are now caught (the
new test forges the definitions in a --snapshot-stale-ok run: invalid, more than 0 carried, stale count 0; the unit
test checks answer 3 sets the stop to d, marks d done, and ck-pre-failed gives 3 and records the fault);
snapc-stale-count-negative, snapc-pre-failed-checks, snapc-pre-stop-unset caught; L1's fault still caught; L5's still
survives (needs twin candidates, first in c7). Nits change no behaviour (reach-kinds# = 22 - 18 + 1 = 5; ck-import-facts
through ck-taken? and ck-fact-of runs only after ck-passing?, where ck-taken? is exactly `imp-source 0< 0=`). edb5554's
test reads the "export reading" note. Info: the design names this report as plain text (not a link).
Updated owner summary: (1) loads a snapshot made under one of the two previous rule versions, prints how many results
it will check again, re-checks everything the changes since could affect, keeps the rest, can save it as current; (2)
today every older snapshot is re-checked in full and equals a fresh check; every problem the review found is fixed and
tested; 25 planted faults caught; (3) risk: a future rule change with a wrong "reach" note would be caught only by the
comparison tests on the test snapshots, so each such note is reviewed with its change and result-moving changes are
merged once a day; (4) recommendation: approve; accept the relaxed "copied from the old file" mark until c6 (labels
only). Runs (git archive of edb5554, `ulimit -u 500`, nice -n 10): env-import.fs on Gforth 1.0.0 and 0.7.3;
`mutants --check` 1359, 0 stale; the 3 new faults caught; reviewer faults 4 of 5 caught (L5 expected); test_leanforth.py
Imports OlderSnapshots 16 OK. Not run by the reviewer: make check, coverage (reported passing by the implementer).

## Merge resolution 5a9d65a (2026-11-13): not blocking

Resolution-only review under the owner's rules of 2026-11-13. Merge 5a9d65a (parents edb5554 and 437feb84, base
c834e0e). Findings: 0. The resolution keeps both sides' behaviour; no lost refusal; allocation failures still give full.
The reviewer re-ran the three-way merge per file with `git merge-file` in scratch: check-json.fs, check-run.fs,
leanforth.fs and the two test files are byte-identical to a clean auto-merge; env-import.fs (3 conflicts) and
env-snapshot.fs (2) differ from the auto-merge only in the listed hunks.

- env-import.fs: `imp-keep` main's ok-with chain with keep-sds between keep-slots and keep-names (the branch's order;
  every step stops on its first non-ok outcome); `imp-input` main's imp-staged-room and imp-input-slots (still invalid
  on a count mismatch), then from, why, to and same-maps — the branch's allocation order; `answer-taken` keeps s-of,
  and main's `lf-look-reslot` equals the old `4 lshift swap 15 and or`; `key-holds`: `lf-look-kind` equals the removed
  `key-kind`; `carry-free` releases the same five blocks before `/imp erase`.
- env-snapshot.fs: `snap-header` main's chain in the same order (marked, format, verdict, fuel, allowlist, placement);
  `head-verdict` hands snap-version-why to snap-must with the branch's arguments; the reason is computed before
  snap-fresh?, which writes only snap-carry and snap-stale, so the order does not matter; `fields-upto?` uses main's
  same-field and field-of; `alike?`'s first five entries still outcome, axioms, warnings, recipe, shape.
- faults.toml: 1722 ids, none lost or duplicated; sn4-answer-untranslated and frk-imp-keep-no-names re-targeted.
- Style: no more long words than main (env-import.fs 2, env-snapshot.fs 4); deep shuffles 51, 106 and return-stack
  operations 68, 176 unchanged.
- Ran (git archive of 5a9d65a, `ulimit -u 500`, nice -n 10): tests/core/env-import.fs and env-snapshot.fs on Gforth
  1.0.0 (pass; every allocation refused gives full apart from the 11 tolerated seal trims); the stale-carry probe (plain
  67 carried; --snapshot-stale-ok 51 carried, 16 users stale, stale 56; forged invalid, stale 0 — M1 holds); the
  reach-reading copy (alone refused "export reading" status 2; --snapshot-stale-ok 2 stale; with the export both
  checked again; upgrade refused, no file — M2 holds); refusal probes "older base with layers", "older layer" (L1) and
  the layer after an export checked against an older base not written, status 4 (L7). Not run (resolution-only rule):
  suites and mutants; the implementer recorded make check, coverage-check, 0.7.3 and mutants --check on 5a9d65a.
