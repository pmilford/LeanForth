# Forth review: tactic-move, the tactic library's shared helpers and intro, exact and rfl on the goal layer (2026-11-19)

Branch tactic-move, range 944f36e1..e82b7e51; reviewer forth-reviewer (Opus), independent.

Findings: 0 high, 4 medium (2 blocking), 3 low. **Verdict: changes needed.** "No behaviour change" holds.

## Findings
**B1 (medium, blocking: duplication).** New private copies of general words:
- `mtg-seen?` (meta-tactic/goal.fs:226) and `tle-holds?` (telescope.fs:202) repeat `lf-view-find dup if nip then`, as do goals.fs:97 and mvars.fs:264. Add `lf-view-has? ( view fvar -- flag )` to lctx-views.fs.
- `mtg-open?` (goal.fs:225) is the third copy of `['] lf-mvar-open? lf-term-holds?` (also apply.fs:191, tactic-rewrite.fs:199). Share one word.
- `tmg-then` (tactic-msg.fs:63) is `ok-with nip`.
- `lfr-drops` (tactic-run.fs:328) repeats lib/text-run.fs:61. Add `ndrop` to lib.
- `mtg-defeq` (goal.fs:258) and `lf-tac-defeq` (meta-must.fs:104) differ only in the mode. Use one `lf-defeq-elab-at ( t s mode -- flag outcome )`.

**M1 (medium, blocking: re-entrancy).** `lf-with-record` (meta-must.fs:24, 132) gives xt a frame address that a nested claim on the same slab invalidates.
- Reproduced: after a nested 5000-unit claim, the frame had moved and the outer's store hit freed memory.
- Today's callers re-read the frame with `slab-last`, but C3, C4 and LA build on this word.
- Fix: pass nothing or the index, and document it.

**M2 (medium, record it).** The "flags set outright" fidelity item is not written anywhere.
- `lf-tac-defeq` sets `lf-defeq-elab` and default transparency; `mtg-defeq` sets the flags.
- So fix J's opaque bit is lost inside `lf-tac-elab-ensuring`.
- Fix: note it in both comments and plan 9.4.8l.

**M3 (medium, tests).** Faults the unit tests miss:
- M7/M8: `lf-goal-not-assigned` removed from `lf-goal-refl` (goal.fs:285) or `mti-start` (:217).
- M20: `lf-tac-with-synth`'s status dropped. It also survives apply/check.py, and the word has no unit test of pass, failure or restore.
- M14: `tcr-kinds` always 0 (tactic-core.fs:131). It also survives `check_s2 --tactics`.
- M6: the `lf-tac-inline` guard removed (tactic-msg.fs:90). Its test should check `lfa-err-inline`.

**L1 (low).** `owns()` (check-tactic-plugins.py:55) matches the basename, so `tactics/sub/rfl.fs` may set `tac-k-rfl`. Compare the full path. An older hole: a constant alias of a fixed kind is accepted. The cases that should be refused are refused.

**L2 (low, style).**
- `3 roll` in `tmg-order` (tactic-msg.fs:83); `tmg-sorts` returns 5 cells.
- `lf-goal-intro-n` takes 5 inputs.
- `2!` across separately named fields (`mti-fill` :172, `tcr-cells!`, `lfw-sides`) ties correctness to field order.

**L3 (low, docs).** These still present tactic-basic.fs as current: FE1G_TACTICS.md:632, LF_LIBRARIES.md:103/226/568, TACTIC_PLUGINS.md:80-279. tests/duplicates-baseline.json keeps stale entries.

## Word list
- Every C1/C2 word of table 1 is present, documented and has a fault; table 2's old names are gone.
- Deviations accepted, and each fits C3/C4/LA: `lf-tac-.name`; caller cells for intro-n (they must not be in a slab the call grows); the step record in C1; `lf-tac-forget-lean`.
- Goal layer requires only tactic-run.fs and tactic-msg.fs. No new globals: `mti-frames` and `mrf-frames` are context slabs.
- Left for LA: `tf`, `tlb`/`tle`, `ap`, `abl-cells`, `trw`, `ti`/`ta`, `tc`, `kab`, and the `lf-tac-elab` defer (moved, not new).

## Reuse
Searched lib and src/ by name and by shape; `check-duplicates.py`: none new (its threshold misses these); `check-lib-callers.py`: clean.

## Style
`forth-metrics.py` (13 files): 585 words, 0 over 5 lines, 26 deep shuffles. The ratchet holds and no baseline was raised.

## What I ran
On archive copies, Gforth 1.0; no suites, Lean, Init or Mathlib.
- No golden changed.
- A 29-case intro/exact/rfl probe: old and new give identical codes, texts and terms.
- All 68 tests/front `.lf` files: check output and elab-dump identical.
- 17 planted faults: 12 caught, 5 survived (M3).
- Plug-in rule probes. Coverage was not re-measured.

## Re-check, and review of commit set C3 (2026-11-19, e82b7e51..dd03a525)

Findings: 0 high, 0 medium, 2 low (not blocking). **VERDICT: ready to merge at dd03a525.**

### A. Earlier findings
- **B1: closed.** `check-duplicates.py` finds no new copies.
  - `irx-discard` may wait: it predates the branch, a committed receipt pins its file, and plan (T) names it.
  - The src/import copies (feed.fs:160, ndjson.fs:1021) also predate the branch, but have no plan row. **N1 (low):** add one.
- **M1: closed; the rule is sound.**
  - Frames nest strictly, and the exit cut makes the outer frame last again, after a throw too.
  - Reproduced: the block moved, yet the outer frame's value read back correctly; an inner throw left count 1, then 0.
  - Caveat: "last" is dynamic scope. An outer call's callback running while an inner frame of the same slab is open would read the inner's frame. No caller does this, and the comment states the rule.
- **M2: closed.**
- **M3: closed.** I re-planted M6, M7, M8, M14 and M20 on dd03a525: all caught.
- **L1: closed.** `tactics/sub/rfl.fs` and the constant alias are now refused.
- **L2, L3: closed.**

### B. C3
- `lf-goal-rewrite ( goal e heq symm? -- new proof goals )` is in meta-tactic/rewrite.fs, as the word list says.
  - One frame per call; `trw-mvars` and its `tac-state:` are gone.
  - Re-entrant: the nested test passes and fault N11 is caught.
- tactics/rewrite.fs holds only rw's own words.
- **N2 (low):** the new-goals test in `trw-open?` repeats the proof's open-metavariable test; a fault there survives as equivalent. Drop the test, or comment why it stays.
- **No behaviour change:**
  - No golden differs from 944f36e1.
  - 20 rewrite probes on 944f36e1, e82b7e51 and dd03a525 give identical answers, texts, step logs and proof terms. They covered:
    - a hypothesis rule; add_comm alone and with arguments;
    - no pattern (215); a definition name (99);
    - a failing second rule (the state after the first is shown);
    - try-rfl closing and not closing; `by-rewrite[` then rfl;
    - rw in induction cases; 218 twice; an empty bracket.
  - No `.lf` text reaches `<-`, 216, 217 or 219; library tests cover them.
- **Debt paid:** 9 of 10 planted rewrite faults caught; the tenth is N2.
- Metrics clean; the ratchet holds.
