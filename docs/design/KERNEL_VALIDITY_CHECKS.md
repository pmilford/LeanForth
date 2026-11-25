# Validity checks out of the kernel's inner walks

Status (2026-11-25): **designed, not reviewed; no code.** The owner approved starting the speed work with
the kernel's own validity checks "as a short design with review first" (2026-11-25). Plan: the Later
list's "Parallel running and speed", item 4 (a), candidate 1 of the kernel speed measurement
(the development folder's KERNEL_SPEED.md on branch `kernel-speed-measure`, not on main yet). Every number is
**measured** (Init's profile run 2 of 2026-11-25, `.claude/work/init-profile-2026-11-25/` of the main
checkout, as shares of its 57,421 samples; call counts from run 1's counted copy; the 952 s of Init at
one worker from run 1) or marked **estimate**. A share in points is a share of those 952 s. Source
references are `file:line` on main at `0c0c49ac`.

## 0. One page for the owner

**What is slow.** The kernel spends 36% of its time (measured, inclusive) inside its own validity
checks. The largest single item: every time the type checker asks "may I look things up in the
environment?" (to probe a cache, to read a constant, to decide whether the audit memo is on), the
answer is computed from scratch by `lf-env-current` (`src/kernel/environment.fs:463`): it checks
that the current environment's identity, length and two pools are sound, that the context's input
fingerprint matches, and that the input is intact, which re-validates the marks of five stores and
two slabs (`lf-input-intact?`, `src/core/input.fs:337`). That is about 360 ns a call, 384 million
calls on Init: **15 points of the 952 s** (142 s), of which 11.8 points are the input's marks alone.

**What changes.** None of these facts can change while one declaration is being checked: the
current environment is changed or freed only outside jobs and checks (`lf-env-may-write`,
`environment.fs:381`), the input is rolled back only to its own marks, and the check's start
(`lf-env-begin`) and its hand-over to the publisher (`lf-env-still?`, `lf-env-target`,
`src/kernel/env-publish.fs:567` and `:188`) already run the full check. Slice 1 records, when a
check begins, which environment it began on (one cell in the check's own candidate record, so
nothing shared and nothing new at module level). Inside the check, "may I look things up?" then
compares two cells (same environment address, same identity) instead of re-validating everything.
The record is cleared when the check finishes and before the hand-over, so every exit still runs the
full check. In Forth terms: a guard moves from the inner loop to the loop's entry and exit, and the
inner loop keeps a two-cell tripwire.

**Why it is safe.** No input can change those facts: LeanForth never runs its input as Forth, so a
malformed export can only reach the checks that read the export's data (bounds of indices, tags,
ranges), and every one of those stays where it is. What the moved checks protect against is a bug
in LeanForth itself (a rollback below the input's marks, a broken store seal, an environment freed
under a running check). Those are still caught: at the check's start, at its step 7 rollback, by the
store roots every pass checks, and at the hand-over, which refuses to publish (invalid, run stops).
The verdicts on every export and every malformed input are the same by construction; the evidence
is section 4.

**The gain.** Slice 1: **12.5 to 14 points, about 120-133 s of 952 s (estimate)**, Init from 24.8 to
about 21.5 times Lean. Slices 2 and 3 (the memo tables' and the audit's per-operation re-checks)
add 1 to 3 points. Together **about 13 to 17 points (125-160 s)**, so Init about 790-825 s, 20.6-21.5
times Lean. This is less than the 25-32 points the speed document projected for candidate 1: 9.5
points it counted as validity are not checks that can move (the per-read range check and the
input-or-store dispatch of every node read, which belong to candidate 3, "field reads inlined", and
the term store's rollback work), and 3.1 points are the cache keys' liveness rule, candidate 6
(section 5).

**The cost.** Slice 1: about 30-40 lines of Forth, 70-100 lines of tests, 4-6 planted faults; about
0.7-1.0 M tokens with its Forth review, full tier and done check (estimate). Slices 2 and 3: about
40-80 lines each, 0.5-0.8 M tokens each (estimate).

**Risks.** (a) A kernel bug that breaks the input in the middle of a check is caught at the
hand-over instead of at the next lookup: the published verdict is the same (invalid, run stops), the
diagnostic recorded inside the check may differ; a test pins it before the change (section 3).
(b) The environment's pools are read by two unchecked words whose soundness today comes from the
full check made just before them; slice 1 keeps a pool check on those paths unless the architect
step proves it redundant (section 2). (c) Slices 2 and 3 depend on facts not yet verified (who
writes a memo's header, whether a context member can move during a check); where they cannot be
verified the check stays and the slice shrinks.

**Recommendation.** Approve slice 1 now; it is the cheapest large win and touches two kernel files.
Decide slices 2 and 3 after slice 1's measurement. Treat the work as behaviour-preserving
refactoring (Forth review and the full tier with every pinned-Lean comparison, reported afterwards,
under the owner's decision of 2026-11-19), not as a change of what the checker accepts.

## 1. What each hot check protects against, and where its facts change

The validity family of run 2 is 35.93% inclusive. Partitioned by the outermost validity word on each
sampled stack (measured; the full table is in appendix A):

| Outermost check | Points | What it protects against | Where its fact can change | This design |
| --- | ---: | --- | --- | --- |
| `lf-env-ours` (via `lf-whnf-env?` 11.87, `lf-env-snapshot` 3.08) | 14.95 | a stale or freed environment, another context's check, an input rolled back below its marks or reset, a broken pool | `lf-env-use`, `lf-env-free` (outside jobs and checks only); `lf-input-rollback`, a new input (`input.fs:484`); the publisher growing a pool | slice 1 |
| `memo-live?` (memo-find, -put, -count) | 1.87 | a memo whose table or entry slab was freed, never made, or corrupted | `lib/memo.fs`'s init, free, empty and growth | slice 2 |
| `lf-term-pair-valid?` in `lf-term-binary` | 1.64 | children outside the store; a broken term store header | store rollback, reset, poison | slice 2: its header check (0.45) only |
| `lf-hterm-valid?`, `lf-cref-valid?` in the audits | 1.25 | a stale term or reference handle in the audit's input | generation changes of the stores | slice 3 |
| `lf-term-valid?` (identity, data, reads), `lf-term-input?` | 8.02 | an index outside the store (the per-read range check of ADR 0016 C8, `terms.fs:426-438`); `lf-term-input?` is no check but the input-or-store dispatch (`terms.fs:216`) | data read from the export | **stays** (candidate 3) |
| `lf-input-all?` under `lf-input-rollback` | 1.48 | none: the samples are the rollback's own work (`lf-term-rollback` 1.42) | after each check | **stays** |
| `lf-fvars-live?` (cache keys) | 3.12 | a cached result for a node whose free variables left the local context | the local context | **stays** (candidate 6, a cache rule) |
| 15 small checks, each 0.46 or less (`lf-fvar-live?`, `store-mark`, `slab-live?`, `memo-valid?`, ...) | 3.60 | various | various | stays (but `lf-rmemo-live?`, 0.22, slice 2) |

**The invariant slice 1 needs (verified against the code).** Between a successful `lf-env-begin`
(`environment.fs:623-625`, which runs the full `lf-env-current` in `lf-env-start`, `:615-617`) and
`lf-env-finish` (`:633`) in the same context:

1. *The current environment does not change.* `lf-envs` is one shared record (`environment.fs:122-127`);
   its current cell is written only by `lf-env-use` (`:525-527`) and `lf-env-forget` (`:516-518`),
   both behind `lf-env-may-write` or `lf-env-choosable?`, which refuse inside a job or a check
   (`context-in-job?`, `src/lib/context.fs:159`; a check runs with `context-check-owner`,
   `env-publish.fs:594-596`). Verified for the check's own context. For the other threads of a
   parallel run: the scheduler makes and frees the environment outside the run; **to be verified in
   the architect step** by reading `env-schedule.fs` for any `lf-env-use` or `lf-env-free` while
   workers run. If one exists, the stamp still catches it (the identity compare below).
2. *Its identity, length and fingerprint do not change.* Written at creation (`lf-env-fields`,
   `lf-env-identity+`, `:472-476`) and cleared by `lf-env-forget`; the serial only grows.
3. *The input stays intact.* Its stores and slabs are rolled back inside a check only to their own
   marks, at step 7 (`check-declaration.fs:216`), by `lf-input-rollback`, which runs the full
   `lf-input-intact?` itself and fails the check when it does not hold (`input.fs:479-482`). Records
   below the marks are never written (`input.fs:8-19`). A reset (`store-clear`) of an input store
   inside a check would break it: **to be verified** by the architect step's grep of every
   `store-clear`, `store-poison`, new input (`input.fs:484`) and slab reset reachable from
   `lf-check-declaration` (today's tests break the seal on purpose: section 3).
4. *The pools stay sound.* Only the publisher writes them; growing one copies it into a new block
   and makes the new one current in one cell, the old one sealed (`environment.fs:418-427`).

Under 1-4, `lf-env-ours` gives the same answer at every call inside the check as at its start, so
one full check at the start and one at the exit cover every inner call.

**Which checks stay at each entry, and which leave the walk (slice 1).**

- *Stay, full, unchanged:* `lf-env-begin` (start); `lf-check-begin`'s `lf-env-checking` and
  `lf-input-read` (`check-declaration.fs:366-370`); step 7's `lf-input-rollback`; the hand-over's
  `lf-env-still?` and `lf-env-target` and the publisher's dependency re-check (`lf-recheck-deps?`,
  through `lf-env-readable`); every view (`lf-env-view`, the import, the command line), which never
  holds a stamp; every bounds check of data read from the export; every pass's store root
  (`lf-term-count-valid?`, `lf-term-root?`, `terms.fs:436-440`).
- *Leave the walk:* inside a check, `lf-env-ours` answers from the stamp when it matches, so
  `lf-whnf-env?` (`whnf.fs:175-176`), `lf-caches-on?` (`caches.fs:219-221`), `lf-audit-on?`
  (`constant-term-boundary.fs:339-341`, through the hook set at `check-declaration.fs:298`),
  `lf-env-snapshot`, `lf-env-readable`, the lookups and the iota, delta and quotient rules no longer
  re-run `lf-env-valid?`.
- *Kept inside on the pool readers unless proved redundant:* `lf-dep-at` and `lf-look-cell`
  (`environment.fs:1331`, `:1334`) read a pool with an unchecked `store-slot`; today the full check
  just before them is what makes that safe. Slice 1's architect step lists every caller reachable
  inside a check; if any is, that path calls `lf-env-pooled?` (0.0-1.3 points of the gain, the
  inclusive cost of `lf-env-pooled?`, measured).

## 2. Slice 1: the checked-environment stamp

- A field `lf-cand-held` in the candidate record `/lf-cand` (a context record, `environment.fs:220`),
  so each worker has its own and nothing new is shared ([PARALLEL_REVIEW.md](../development/PARALLEL_REVIEW.md)'s
  re-entrancy rules). It holds the environment the check began on, 0 for none.
- `lf-env-start` sets it once the full `lf-env-current` has passed (with `lf-env-snap!`).
  `lf-env-clear` (`:601-602`, which erases the record) and `lf-env-finish` clear it, and so does
  `lf-env-hand-over-at` (`env-publish.fs:571-572`) before `lf-env-still?`, so the exit check is full
  even for a check word that does not end with `lf-env-finish` (a test's own word given to
  `lf-env-run`).
- `lf-env-ours` (`:593-594`) first asks `lf-env-held?`: the held cell is not 0, `lf-env` is that
  address, and its identity is the candidate's identity (so an environment freed and replaced at the
  same address, the case `lf-env-is?` guards at `:643-648`, still fails the compare). On a match it
  gives `(env true)`; otherwise it runs today's body. A mismatch is never trusted: the full check
  decides, so a stamp can only skip work, never change an answer while the invariant holds.
- A test-build cross-check, as I2's (`environment.fs:354-366`): with `lf-env-held-checks` defined
  before loading, every matched stamp also runs the full `lf-env-current` and counts a disagreement
  in one atomic counter; the unit tests and the decide slice run with it and require 0. The default
  build never compiles it, so the shipped verdicts depend only on code that every other test runs.

**Size (estimate).** 25-40 lines in `environment.fs` and `env-publish.fs`; tests 70-100 lines;
faults 4-6.

**Tests** (in `tests/core/environment.fs` and `tests/core/check-declaration.fs`, written first,
against today's code, then kept):
1. Pin today's results: the seal rows (`tests/core/check-declaration.fs:695-733`), plus two new rows
   that break, in the middle of a check, a fact only `lf-input-intact?` sees (the name bytes' count,
   `lf-name-used`; a literal slab's mark): published invalid, run stopped, diagnostic recorded
   (whatever today's code records; the slice must keep it or report the difference to the owner).
2. The stamp's life: none before `lf-env-begin`, set after it, cleared by `lf-env-finish`,
   `lf-env-clear`, `lf-env-view`, a nested `lf-env-begin`, and the hand-over; a spent context and a
   refused start leave none.
3. Mismatch falls back: between begin and a `lf-whnf-env?` call (outside a job, as a test may),
   `lf-env-use` of another environment, `lf-env-free` of the held one, and a new environment at the
   freed address each give today's answer (false, with `lf-diag-no-snapshot` where today records it).
4. Front-end users of the kernel's environment words (`tests/front/meta-env.fs`, `whnf.fs`,
   `infer.fs`, `defeq.fs`) unchanged.
5. Faults: the stamp set without the full check; not cleared at finish; not cleared at the
   hand-over (caught by test 1's new rows, which also make `fx9-env-still-always` killable: drop its
   "equivalent" note); the identity compare dropped (caught by test 3); the cross-check's counter
   never counting.

**Command and measurement.** `time bin/leanforth check --jobs 1 --no-manifest --resources --json
.claude/work/IM/init.ndjson` (Init at one worker; before: 952 s, run 1) and the same at `--jobs 4`,
both before and after on the same day with the load average noted; then `make profile-check` (from
branch `kernel-speed-measure`) at one worker, where `lf-env-current`'s inclusive share must fall from
14.60% to under 0.5% and `lf-env-ours`'s from 14.95% to about 1% (estimate: two compares, 20-30 ns,
on 384 M calls).

## 3. Fail-closed: the tests and faults that reach the moved checks

Found by `grep` of `tests/` and `tests/mutants/faults.toml` for the words slice 1 touches (the
`faults.d/` batches are searched again in the architect step):

| Test or fault | What it does | How it stays caught |
| --- | --- | --- |
| `tests/core/check-declaration.fs:729-733`, seal rows 0-3 | term or level seal broken at the root or after step 8 | at the root: `lf-env-begin` and `lf-input-read` (unchanged); mid-check: the store roots of every pass (unchanged) and the hand-over's full check (unchanged, now reached with no stamp) |
| `tests/core/environment.fs:103-169` | `lf-input-intact?` and `lf-input-rollback` on intact, rolled-back and reset inputs | `lf-input-intact?` and `lf-input-rollback` unchanged |
| `tests/core/failure-paths.fs:143` | input intact after a refused allocation | unchanged |
| `fx9-input-intact-always` (`faults.toml:8779`) | `lf-input-intact?` always true; listed equivalent | still equivalent at the root; slice 1's new rows may make it killable (then drop the note) |
| `fx9-env-still-always` (`faults.toml:8790`) | `lf-env-still?` always true; listed equivalent | killed by slice 1's new mid-check rows |
| faults at `faults.toml:319`, `:327`, `:494`, `:502`, `:527` | `lf-env-begin`, `lf-env-new-ok?`, `lf-env-thrown`, `lf-env-hand-over-at`, the publisher's finished test | words unchanged except `lf-env-hand-over-at` (one more call): its fault's `old` text is updated in the slice |
| faults at `:1206`, `:8562`, `:8841`, `:10708`, `:10761`, `:10769` | `lf-whnf-env?` in whnf, `lf-audit-on?` in the reach tests | the words keep their text and their answers |

**A debug or "paranoid" build: not for the verdicts.** A build that compiled the inner checks back in
for the test suites would make the tests exercise code the user never runs, and the user's verdicts
would come from code no test runs alone. Recommendation: no such mode. The shipped build is the
tested build; the stamp falls back to the full check on any mismatch; the only test-only code is the
cross-check counter of section 2 (as I2's, `environment.fs:354-366`), which checks the invariant on
real runs and never decides a verdict.

## 4. Trust and evidence

Behaviour-preserving by intent: identical verdicts, diagnostics and fuel on every export and every
malformed input. Fuel cannot change: the checks cost none themselves, and the two answers that do
steer fuel, whether the caches and the audit memo are on (`caches.fs:100-114`), are the same from the
stamp as from the full check while the invariant holds. Evidence, recorded in the slice's report:

- `make check` (every pinned-Lean comparison, `make test-differential` with the Mathlib slice),
  `make test-unit` on `gforth-fast`, `make mutants` (the fault table) and `make test-compact-faults`.
- Init's JSON report before and after, byte-identical once the timing fields (`measured`, the
  resources block) are removed; the same for the Mathlib slice (`reference-mathlib-slice`).
- The parallel run's planted wrong declaration rejected at `--jobs 1`, `2` and the default
  ([PARALLEL_REVIEW.md](../development/PARALLEL_REVIEW.md)); the decide slice
  (`tests/front/decide-slice.ndjson`) with the cross-check build, counter 0.
- `make cover-changed` on the touched files.

**Gate.** Nothing changes what the checker accepts, rejects, reads or writes; no input reaches the
moved facts. Under the owner's decision of 2026-11-19 (`docs/project/OWNER_DECISIONS.md`, "The kernel
is code like any other") this is ordinary work: the Forth review, the full tier with every
pinned-Lean comparison, and a report afterwards. The one point that would need the owner: if test 1
of section 2 shows that the diagnostic inside a mid-check break differs and cannot be kept, the
slice stops and asks.

## 5. Gain per slice, with overlaps removed

Each slice is net of the ones before it (appendix A gives the basis). Seconds are points × 9.52.

| Slice | Basis (points, run 2) | Taken (points, estimate) | Seconds | Init after (s) | Times Lean |
| --- | --- | ---: | ---: | ---: | ---: |
| 1 environment stamp | 14.95 (`lf-env-ours`) | 12.5-14.0 | 119-133 | 819-833 | 21.3-21.7 |
| 2 memo liveness, constructor header | 1.87 + 0.45 + 0.22 | 0.4-2.0 | 4-19 | 800-829 | 20.8-21.6 |
| 3 audit handles | 1.25 | 0.5-1.0 | 5-10 | 790-824 | 20.6-21.5 |

Slice 1's range: the fast path's own cost (0.8-1.2 points) and the pool check kept on readers
(0-1.3). Slice 2's low end is the constructor alone, if a memo's liveness cannot be shown fixed
within a check. The speed document's 25-32 points for candidate 1 also counted the per-read checks
and dispatch (8.0), the rollback's work (1.5) and the cache keys (3.1, candidate 6); its section 10
table is corrected in slice 1's branch.

## 6. Slices 2 and 3

**Slice 2: per-operation re-checks of tables.** (a) `memo-live?` (`src/lib/memo.fs:143`) re-checks the
seal and shape of the memo's hash table and entry slab on every find, put and count (1.87 points; its
callers two out: `lf-rmemo@` 0.51, `lf-rmemo-kept` 0.47, the caches' `memo-at` 0.42, `memo-cut`
0.37). A library change: the memo checks itself fully where its liveness can change (init, free,
empty, growth) and at the start of a pass (`lf-rmemo-begin`, `lf-caches-clear`), and per operation
only the range of the slot it reads (as `store-at?` does for stores, `store.fs:163-171`). Precondition
the architect verifies: no word outside `memo.fs` writes a memo's header, and no context member moves
during a check (`lib/context.fs`). Otherwise (a) is dropped. (b) `lf-term-binary` checks the term store's
header twice per new node: in `lf-term-pair-valid?` (`terms.fs:917-918`, 0.45 points) and again in
`store-open?` on every path of `lf-term-add` (`terms.fs:839-840`, `store.fs:203-204`). Keep the
first (it runs before any side effect, so outcomes and diagnostics stay the same); only for
`lf-term-binary`'s call, after that check, the found and new paths use a `store` word that tests
room, serial and the fault hook without the header (`store-room-open?`, and a `store-new` beside it,
in `src/lib/store.fs` with their own tests); every other caller of `lf-term-add` (leaves, references)
keeps `store-open?`. Worth 0.45 points at most: done only if it stays under about 30 lines. Size of
the slice 30-70 lines; command and measurement as slice 1.

**Slice 3: audit handles.** `lf-cterm-check` (4.56 inclusive) re-validates a generation handle per
audited node (`lf-hterm-valid?` 0.47, from `lf-mcompare-audit` and `lf-mls-graph`) and a reference per
constant (`lf-cref-valid?` 0.49 in `lf-cref-record`). The audit's root already holds the stores'
generations (`lf-audit-same?`, `constant-term-boundary.fs:344-346`); the inner checks become range
checks. Size 20-40 lines. Done only if slice 2's measurement confirms its predicted share.

## 7. Reuse

- Existing words used: `lf-env-current`, `lf-env-mine?`, `lf-env-clear`, `lf-env-snap!`,
  `lf-env-finish`, `?keep` (environment.fs); `store-at?` and `store-count-valid?` (lib/store.fs); the
  I2 test-build pattern and `task+!` (lib/task.fs) for the cross-check counter; `htab-live?`,
  `slab-live?` (slice 2).
- New words: `lf-env-held?`, `lf-env-hold`, `lf-env-unhold` (kernel-specific, environment.fs);
  `store-room-open?` (general, src/lib/store.fs, slice 2); a range-only memo probe in lib/memo.fs
  (general, slice 2). No copy of an existing word: `store-open?` is rewritten as
  `store-count-valid?` and `store-room-open?`, so the room test lives once.
- Copies replaced: none found; `lf-whnf-env?` and `lf-caches-on?` already share `lf-env-ours`.

## 8. Work in flight on the same files

- Branch `kernel-speed-measure`: adds the library word `timed`, touches `env-schedule.fs`
  (`lf-sch-timing`) and `cli/check-run.fs`, and brings `make profile-check` and the speed document.
  Slice 1 touches neither file but needs its measuring tools: start slice 1 after it merges, or
  rebase on it before measuring.
- Simp slice SL1a (front end: `src/front/meta-config.fs`, `whnf.fs`, `defeq.fs`, `discr-keys.fs`):
  no shared file. The front end's tests call the kernel's environment words, so slice 1's tier runs
  them (it does: a kernel change runs `make check`).
- Slice 2 changes `src/lib/store.fs` and `src/lib/memo.fs`, which every module loads: it waits for
  no branch with open changes there (checked at its start with `git log main..` of open branches).

## 9. Questions for the owner

1. **The honest gain is about 13-17 points (125-160 s), not 25-32.** The rest of what the profile
   called validity is the per-read range check and node dispatch (candidate 3) and the cache keys'
   rule (candidate 6). Recommendation: accept, and correct the speed document's table in slice 1's
   branch; the remaining points are still reachable through candidates 3 and 6.
2. **No separate paranoid build.** Recommendation: ship one build; keep only a test-build counter
   that compares the stamp with the full check. Reason: a mode that changes what code runs would
   leave the user's verdicts resting on code the suites do not run alone.
3. **Ordinary work or gate?** Recommendation: ordinary work (Forth review, full tier, every pinned-Lean
   comparison, report afterwards), because no verdict, diagnostic or fuel changes and no input reaches
   the moved facts; the slice stops and asks only if a mid-check diagnostic cannot be kept.

## Appendix A. The validity family by outermost word (run 2, measured)

`python3 scripts/profile-summary.py` families; each sample counted once, at its outermost validity
word; total 35.93 points. Callers are the immediate caller of that word.

| Word | Points | Main callers (points) |
| --- | ---: | --- |
| lf-env-ours | 14.95 | lf-whnf-env? 11.87, lf-env-snapshot 3.08 |
| lf-term-valid? | 5.30 | lf-term-identity 1.60, lf-term-data@ 1.27, lf-open-readable? 0.94, lf-term-read 0.56, lf-term-child-data 0.37 |
| lf-fvars-live? | 3.12 | lf-term-facts 3.12 (lf-node-key 1.59, lf-cs-facts 0.90, lf-closed-id 0.60) |
| lf-term-input? | 2.72 | lf-term-tag@ 0.85, lf-term-first@ 0.68, lf-term-data-word 0.33, lf-term-second@ 0.27 |
| memo-live? | 1.87 | memo-find 0.68, memo-count 0.61, memo-put 0.57 |
| lf-term-pair-valid? | 1.64 | lf-term-binary 1.61 (its header check 0.45) |
| lf-input-all? | 1.48 | lf-input-rollback 1.48 (lf-term-rollback 1.42) |
| lf-hterm-valid? | 0.65 | lf-cterm-check 0.47, lf-mls-ready? 0.18 |
| lf-cref-valid? | 0.60 | lf-cref-record 0.49, lf-cterm-source? 0.12 |
| 15 others, 0.46 or less | 3.60 | lf-fvar-live? 0.46, store-mark 0.44, store-count-valid? 0.38, lf-lscope-context-valid? 0.37, slab-live? 0.30, between? 0.29, memo-valid? 0.23, lf-rmemo-live? 0.22, ... |

Inside `lf-env-current` (14.60 points, 8,381 samples): `lf-input-intact?` 11.79, `lf-env-live?` 2.05
(`lf-env-pooled?` 1.33, `lf-env-sane?` 0.61). About 362 ns a call: 14.60% of 952 s over 384.3 M calls
(estimate from measured figures).

## Appendix B. Against the speed document's assumed invariant

The speed document's candidate 1 states an invariant "to be verified". Against the code:

- (a) "no store is rolled back ... while a pass runs": holds for passes, but a check rolls the input's
  stores back inside the check, between steps 6 and 7 (`check-declaration.fs:213-218`), to the input
  marks and with its own full check. A per-check stamp is therefore correct only because that
  rollback goes to the marks and checks itself; slice 1 relies on that, not on (a).
- (c) "the shared environment read only through handles checked at entry": not so today. The pools
  are read through unchecked `store-slot` (`environment.fs:1331`, `:1334`), made safe by the full
  check that `lf-env-readable` runs just before, and a parallel run's publisher replaces a pool's
  block while workers read (`:418-427`). Slice 1 keeps a pool check on those paths unless shown
  unreachable inside a check.
- "`lf-env-current` once per pass": once per check suffices, since the start and the hand-over
  already run it in full (`environment.fs:615-617`, `env-publish.fs:567`, `:188`).
- The validity family counts `lf-term-input?` (a dispatch, `terms.fs:216`), `lf-term-valid?` (the
  per-read range check that ADR 0016 C8 already reduced to `store-at?`) and the rollback's work under
  `lf-input-all?`: 9.5 points that moving checks cannot remove.
