# Review: names-index, `b403ac21..596ca3df` ([kernel] gate, ADR 0005 Amendment 1)
Findings: 0 block the gate, 4 should be fixed before merge, 1 reuse pass (blocking unless planned), 4 notes; 2 style findings. Reviewer: forth-reviewer (Opus), read-only.

**Verdict: approve with the named changes (findings 1 to 5).** IDs are the same, refusals fail closed and the evidence holds. But the weaker audit is not yet backed by the cheap checks that would keep its loss small, and `make test` fails on the branch.

## For the owner (plain language)
Before: before every name operation the store re-read every entry, so damage anywhere (only possible from a memory bug in other code or a test) stopped the next operation. Now: each entry is checked once, when it is new. Every lookup checks the entries it touches. Damage to an older entry is noticed only when something reads that entry. The view mode (every export check) and the term and level stores already work this way, so the claim is fair. One gap is real, and I showed it: a reader that walks a damaged name (name equality, the printer) can now loop forever. I ran main's own printer test on the branch and it never finished. Before, the same input gave "invalid". No verdict can turn into "accepted" unless memory is already corrupt. I would accept the change for a proof checker after two cheap additions:
(a) Name walks check each step: one comparison per component, so damage gives "invalid" instead of a hang.
(b) One full audit when a `.lf` text hands its names to the kernel: about 27,000 entries on Init, once per text.
Speed: `.lf` checks against Init drop from 73–80 s to 13–14 s, and Init's results are identical.

## Findings
1. **Should fix before merge: a corrupted audited name hangs readers that the comments say are safe.** `src/core/name-equal.fs:22-23` and `src/present/print-names.fs:31-33` still say that passing `lf-name-storage-valid?` guarantees prefixes point backwards, so walks end. That is no longer true. Reproduction: main's `tests/present/term-printer.fs` on the branch is killed after 300 s. Name 1's prefix is set to 50, and entry 50 still holds prefix 1, so `lf-name-depth` cycles. `lf-name-storage-valid?` is true, `1 lf-name-entries-from?` is false. `lf-name-text` spans are unchecked too, so out-of-bounds reads are possible in `lf-name-same?`, the printer and `lfx-name`. Fix, O(depth), in names.fs:
   `: lf-name-chain-ok? ( id -- flag ) begin dup while dup lf-name-part-ok? 0= if drop false exit then lf-name-prefix@ repeat drop true ;`
   Call it in `lf-name-ids?` (both IDs), `lf-pp-name-to` and `lfx-name`. Restore the old printer case (`corrupt-prefix` on t2, expecting invalid invalid) and add a fault.
2. **Should fix before merge: a full audit at the hand-over (the cheap stronger variant).** In the `.lf` flow no full pass runs unless byte use goes down. `lfc-produce` (`src/cli/check-lf.fs:213`) writes the stored names into the stage that the kernel checks. Begin it with `1 lf-name-entries-from? lf-name-hashes-ok? and 0= if outcome-invalid exit then`, where `lf-name-hashes-ok?` checks each kept hash against `lf-name-sought-hash` recomputed from its entry (see 7). Also run it before any other export of stored names. Optional: a running checksum of the 5 cells, folded in by `lf-name-audited` and checked at the same point. It also catches well-formed rewrites, which the old audit never caught. I recommend the structural pass plus the hash check. The checksum costs the same pass and adds content detection.
3. **Should fix before merge: `make test` fails.** `scripts/check-duplicates.py` exits 1 on the branch and 0 on main. It finds 3 group members missing from `tests/duplicates-baseline.json`: names.fs:333 `lf-name-str-refused` (3a1dbea59edb), :247 `lf-name-sought?` (8c62bb325216), :245 `lf-name-part?` (b441222231c7). All are idiom shapes. Add them with reasons; the implementer ran only focused targets.
4. **Should fix before merge: a test gap, the index with no block** (`htab-init`/`htab-renew` out of heap). The path at names.fs:298 and the `htab-live?` check at :288 are never run. My planted F7 (`lf-name-index-ready drop`) and F8 (`htab-live?` replaced by `true`) both survive `tests/core/names.fs`. By probe, the real code fails closed: after `lf-name-table htab-free`, every intern returns false with a names-full diagnostic, and a reset makes the table again. Add that test and the two faults. `coverage-check` will probably flag these blocks.
5. **Reuse pass (blocking unless planned): a fifth copy of the three-field hash.** `lf-name-sought-hash` (names.fs:231-232) is `a hash-fmix b hash-step c hash-step`. The same hash is `lf-fields-hash` (terms.fs:301; levels.fs uses it too), `quad-hash` (compact-levels.fs:53), `name-hash!` (compact-names.fs:86), and hash32.fs's own example. Add `: hash-3 ( a b c -- h ) rot hash-fmix rot hash-step swap hash-step ;` to `src/lib/hash32.fs`, use it in names.fs and terms.fs, and give the compact-* copies a 9.4.8k plan row.
6. **Note:** the claims about ADR 0016 C8 hold for view-mode names: `lf-name-all-checked`, and compact-names.fs:50-56 reads u32 fields unchecked. They hold for terms and levels as far as no re-audit goes (S6(c): once per epoch). Those reads, however, keep a bound on every read (`store-at?`, store.fs:167) and walks have fuel. Stored-name walks have neither. Say so in the ADR.
7. **Note:** the hash cell is never audited. A rewritten cell misplaces the entry when the table grows, and an equal name then gets a second ID (fault ni-hash-not-kept shows this). `lf-input-newest` detects duplicate declarations by name ID, so the hash check in 2 matters.
8. **Note:** a block shrunk below given-back entries (`lfc-rooms-back` can shrink it) leaves stale slots until a reset. The find compares content, so they are harmless (tested); only `htab-count` grows.
9. **Note:** `lf-name-table-make` drops `htab-init`'s outcome while `lf-names-make` aborts on no heap. The result is fail-closed, but the two are inconsistent; one comment is enough.

## The three changed tests (Q2)
- names.fs:36-47. Before: after `lf-entry-payload` of entry 1 is corrupted, `0 7 lf-name-num -> false`, so any intern failed. After: `lf-name-storage-valid? 1 lf-name-entries-from? 2 lf-name-entries-from? -> true false true`, and only the entry's own name is refused (`0 s" u" lf-name-str ... -> false false`). An honest statement of the new contract, but the protection is gone (main's line fails on the branch).
- run-record.fs `viewed-cases`. `last-tag` (the newest entry) became `root-tag` (entry 0). Main's version gives INCORRECT RESULT on the branch. "Not viewed when any entry is bad" became "when the root or header is bad". Acceptable restatement; fault rv-env-viewed-names is still caught.
- term-printer.fs. `corrupt-prefix ( id )` on t2 became `corrupt-root`. **Not a mere restatement:** main's case now hangs (finding 1). The change hides a non-termination. Restore the case after fix 1.

## Identity, fail-closed, restart (Q3, Q4)
Read: an entry is made only after a failed find; `lf-name-same` compares kind, prefix and the component itself, and passes over IDs at or above the count. Rollback: `lf-name-index-sync` unlists by kept hash before any find. Every add follows an audit in the same call (`lf-name-num-args?`/`-str-args?`), so a count that went down lowers the audit's count before any rewrite. A same-size rewrite in place therefore cannot escape the audit. Byte use going down restarts the audit. The generation saturates at -1 (store.fs:223-224), which fails every audit, and never wraps. Every refusal returns false: a corrupted entry met by a find returns false without a diagnostic; a full or dead index returns false with names-full. Nothing reports ok on a refusal.

## Evidence (Q5)
Checked in `.claude/worktrees/agent-ab44f57a23cd91c7c/.claude/work/names-index/` and the scratch `runs/`:
- Both snapshots have SHA-256 e120cf67c5355d69…
- The report JSONs differ only in 9 `measured.*` fields: 59,349 accepted, fuel 654,719,715.
- `lf-set.txt`: 6 `.lf` outputs and exit codes identical. s1-rfl was timed once; the 3+3 timing runs were not finished.
- The Init export check runs names under a view, so it pins the layout and reset path, not the index. The index evidence is the `.lf` texts.

Not run, by them or me: `make coverage-check`, check-rest/pinned-Lean, the Gforth 0.7.3 suite (I ran only names.fs on 0.7.3: passes), Mathlib, the full `make test` (it would fail, finding 3).

## Mathlib (Q7)
Stored names are about 9% of the library's (26,701 of 295,432 on Init). At about 700k names: 2^20 u32 slots (4 MB), entries at 40 B (+25% over 4 cells), IDs well below htab's 2^32-2 (capacity is capped at 2^31-1). Doublings re-place entries by kept hash, without reading bytes. `htab-renew` frees a big table at each text's reset. A byte rollback costs one full pass, O(names), per rollback. Hashes mix only the low 32 bits of numbers; the compare uses the full value. No problem expected; not measured.

## Probes run (Gforth 1.0.0 unless stated; scratch copies only)
- P1 identity, about 4,000 operations: duplicates; 300-byte names; n and n+2^32; names differing in the last byte; numerals as strings; two mark/rollback/re-intern rounds; a numbers-only rollback; exhaustion; reset with stale IDs. Run on main, branch, branch with constant hash, branch with a 1-bit hash: all 4 outputs identical (md5 aa5d8179…). Stale IDs refused; full refuses new names and finds existing ones.
- P2: main's three old tests on the branch: results as above.
- P3, my faults: F1 detach keeps index, F2 rollback leaves name findable (unlist and count check removed), F3 no restart on shrink (`nip` for the used test), F5 audit count never lowered, F6 rehash returns 0: all caught by tests/core/names.fs. F7 and F8 survive (finding 4).
- P4: the dead-index probe (finding 4). P5: the branch's names, run-record and term-printer tests pass.

## Reuse
Searched FORTH_LIBRARY.md, LIBRARY_WORDS.md, `grep -rn` over src/ for `hash-fmix|hash-bytes|htab-hooks!|htab-remove|htab-renew|else drop false then`, and the sought-record and rollback patterns in terms.fs, levels.fs and constant-references.fs. Ran check-duplicates (finding 3) and check-lib-callers (clean; bigint has its plan row). htab.fs and hash32.fs are used through their documented interfaces: hooks record, `htab-ready` before `htab-put`, `htab-renew`, removal by hash. One deviation: rehash reads a kept hash instead of recomputing it, which the ADR justifies. The only finding is 5.

## Forth style
`forth-metrics.py --words 10 src/core/names.fs`: 127 words (main 98); 81% are 1-2 lines and 24 are 3-5; none over 5 lines. Globals 3 (main 2), context members 6, rstack 17 (23), shuffles 3 (4), 3 long lines. The third global, `lf-name-hooks`, is the read-only hooks record that every htab owner uses (terms.fs:575, levels.fs:88). It is needed because htab takes a hooks address. The baseline raise is justified.
- S1: `lf-name-sought`'s `slot` and `ready` fields are registers between `lf-name-lookup` and `lf-name-append`, and `lf-name-same` drops its key to read the context member. Keep the slot on the stack: `lf-name-lookup ( -- id true true | false true | slot false )`, `lf-name-append ( slot xt -- id true | false )`. Give the hook the key: `: lf-name-same ( n key htab -- flag ) drop over lf-name-count @ u< 0= if 2drop false exit then over lf-name-entry-checked? if swap lf-name-slot swap lf-name-sought? else 2drop true then ;` with `lf-name-sought? ( entry key -- flag )`.
- S2: the double-flag result of `lf-name-lookup` would read better as an outcome (ok/invalid/full) plus id or slot.
Neither trades away validation.

Not done: no human review of the gate (still required); no coverage, Lean or Mathlib runs. My scratch dir was shared with the implementer's runs: I re-extracted `main/` from the same commit, b403ac21, and added br*, m-*, oldtests, probes.

## Re-check, `596ca3df..b035cde6`
Findings: 0 block the gate, 1 should be fixed before merge (tests only), 3 notes.
**Verdict: approve with one named change: two tests and their faults (R1). No code change is needed.**

**For the owner.** Before this branch, every name operation re-read the whole name store, so damage from a memory bug elsewhere stopped the next operation. Now:
- each name is checked once, when it is made;
- every lookup checks the entries it touches;
- name equality and the printer check every part of a name before walking it, so a damaged name gives "not equal" or "invalid", never a hang;
- before a `.lf` text's names go to the kernel, the whole store is audited again and every entry's stored hash is recomputed. That hash is computed from the name's kind, prefix and text, so this hand-over also catches a rewritten letter or number, which the old audit never did.

What is lost: damage to an old name between two hand-overs is noticed late, and only if a reader that is not yet checked meets it (front-end code, R3). It cannot reach a verdict. Init is identical and `.lf` checks are about 6 times faster. I would approve once R1 is in.

**Answers to the coordinator's six questions**
1. **Finding 1 is fixed.**
   - `lf-name-chain-ok?` (names.fs:454) checks, at every step: the ID is valid, the prefix is lower than the ID, and the text lies inside the bytes in use. The prefix strictly decreases, so the walk always ends.
   - It is called from `lf-name-ids?` (both IDs), `lf-pp-name-to` and `lf-pp-hygienic?`.
   - `lfx-name` is not checked directly but is covered: every export goes `lfx-export` → `lfx-checked` → `lfx-unwritable?` → `lf-name-audit-all?`, and a store that passes the full audit has well-formed chains.
   - Main's original tests on b035cde6: nothing hangs.
     - term-printer: `lf-print-name` of the damaged name gives invalid again. The print of an unrelated term is now ok instead of invalid, which is the intended new behaviour; the branch's test says so.
     - names.fs: still `0 7 lf-name-num -> false` (the accepted contract change).
     - run-record: `viewed-cases` still differs (an accepted restatement).
2. **Finding 2 is fixed, at least as strongly as I asked.**
   - The only writers of `lfx-names` are `lf-author-export` and `lf-author-export-reached`, and both pass through `lfx-checked` (export.fs:335-348).
   - `lfc-write` (check-lf.fs:211) is the one path from a `.lf` text to the stage. Snapshots are written from the stage tier (view mode), never from the stored names.
   - `lf-name-audit-all?` is the full structural pass plus recomputing every kept hash.
   - My probe changed one thing at a time: a number payload, a prefix rewritten to another valid lower ID, one byte of a name's text, the hash cell. Each made the audit false, and restoring the value made it true again. A self-cycle prefix: `lf-name-chain-ok?` returns false and the walk ends.
   - Unverified: whether the front end runs kernel words in-process on the stored names. Even so, verdicts come from the stage check.
3. **Finding 3 is fixed, fairly.** `check-duplicates.py` exits 0: 282 groups, none new or grown.
   - `lf-name-str-refused` and `lf-name-part?` joined their idiom groups (`x? if a else drop b then`; `x if a else b then`).
   - `lf-name-sought?` now reads both parts instead of short-circuiting. This is safe: the entry is checked first, and a number's text is 0 bytes long. But it bends the code to the duplicate checker.
4. **Finding 4 is fixed.** F7 and F8 are now caught: names.fs:311 crashes with "Invalid memory address", which the test target counts as a failure. The new test runs the no-block path, and the real code fails closed.
5. **Finding 5 is fixed, with no behaviour change.**
   - `hash-3` (hash32.fs:44) has exactly the body of the removed `lf-fields-hash`: `rot hash-fmix rot hash-step swap hash-step`, so the hashes are bit-identical.
   - Init after the fixes: snapshot SHA-256 e120cf67…, 59,349 accepted, fuel 654,719,715. Checked by me from `runs/init-branch2.*`, whose `src/` equals b035cde6's.
   - All seven `.lf` texts give byte-identical output; s1-rfl takes 12.3–15.8 s against main's 71.7–74.5 s.
   - Kernel-loaded files changed in the whole branch `b403ac21..b035cde6`:
     - `lib/hash32.fs`: one new word, `hash-3`.
     - `core/terms.fs`: `lf-fields-hash` removed and 7 call sites changed to `hash-3`.
     - `core/levels.fs`: 2 call sites changed to `hash-3`.
     - `core/names.fs`: the index, the kept audit, the 5-cell entry, `lf-name-chain-ok?`, `lf-name-audit-all?`.
     - `core/name-equal.fs`: `lf-name-ids?` now chain-checks both IDs.
   - The kernel files that require `name-equal.fs` are mixed-compare, level-normalize and inductive-nested.
   - Not kernel-loaded: `present/print-names.fs` and `author/export.fs`.
   - So the gate is wider than names.fs in name only for terms and levels (the code is identical). It is wider in behaviour for `name-equal.fs`: an ID whose chain fails is now "not equal", at O(depth) cost per call. Well-formed input gives the same result, as Init shows.
6. **Nothing new blocks.** Metrics: names.fs has 134 words, 79% of them 1–2 lines and none over 5; 3 globals; 3 deep shuffles. print-names.fs and export.fs have no words over 5 lines. S1 is done: the slot now travels on the stack and the record field is gone.

**Findings**
- **R1. Should fix before merge (tests only).** Two of my seven new planted faults survive:
  - F10: `lf-name-ids?` reverted to `lf-name-valid?` passes names.fs, author.fs and term-printer.fs. The kernel-reachable equality check has no test.
  - F12: `lf-name-hashes-ok?` skipping the newest entry passes everything. The tests damage entries 1 and 2, never the last.
  - Add `T{ <id on a cycle> <other id> lf-name-equal? -> false }T` plus a test that rewrites the newest entry's hash, and both as faults.
  - The other five are caught: F7, F8, F11 and F13 directly, and F9 (part check removed from the chain) by the hang hitting the timeout.
- **R2. Note:** 19 other files still walk names without a chain check (cli name-text, print and check-lf; front meta-env, elab-term and lib-decode; kernel environment and defeq). In the `.lf` flow the kernel reads the stage, where every name was checked when made. A front-end walk over damaged stored names can still hang before the hand-over, but cannot give a verdict. Give it a plan row.
- **R3. Note:** what is lost is now only this: damage to an old entry between two hand-overs is noticed late, and only by a reader without the chain check (R2).
- **R4. Not re-run:** check-rest/pinned Lean, the Gforth 0.7.3 suite, Mathlib. The implementer reports a `coverage-check` pass on b035cde6; I did not repeat it.

Probes (Gforth 1.0.0, scratch copy of b035cde6):
- main's three original test files;
- the branch's names, term-printer, author and hash32 tests (all pass);
- the rewrite probe in point 2;
- faults F7 to F13 against names.fs, author.fs and term-printer.fs.
