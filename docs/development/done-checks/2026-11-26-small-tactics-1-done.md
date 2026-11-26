# Done check: small tactics 1 (2026-11-26)

Independent done checker (Sonnet), on main 1a1e2a27. Its report follows unchanged except for the scratch path.

**Coordinator's resolution (2026-11-26):** the checker's verdict was NOT DONE for two record items only, both of which could not exist before its own run: this report, now saved here, and the entries in PROJECT_PROGRESS.md and the plan (row 9.4.8z13), now written. Every behaviour claim passed: stage "works end to end" by its own proofs, so with the records in place the group is done. The Forth review and its re-check are [2026-11-26-small-tactics-1.md](../forth-reviews/2026-11-26-small-tactics-1.md); the tier passed on a90c95ec (exit 0). Its note that the reference never shows a complete small file per word is taken into plan row 9.4.8z12.

---

DONE CHECK: small tactics 1

**Verdict: NOT DONE. Stage reached: works end to end.** The words work on my own `.lf` proofs. The record is missing: there is no done-check report for this group, and PROJECT_PROGRESS.md and the TB2 plan row don't mention the group. I did not review Forth or run CI, which "done" also needs.

All commands were run at the repo root under `ulimit -u 500`, nice 10, with `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE`. My files are in `the checker's scratch directory: `.

**Claim 1: accepted theorems (exit 0, "NAME: accepted; axioms: none"; `fx_one` and `fx_two` say `axioms: Quot.sound`)**

| File | Word | Exit | Output |
|---|---|---|---|
| a1.lf | `by-funext[ x ]` on `' Nat.succ ' Nat.succ =`, then `by-rfl` | 0 | fx_one: accepted; axioms: Quot.sound |
| a2.lf | `by-funext` (same goal) | 0 | fx_two: accepted |
| w1.lf | `by-funext` on `0 0 + 0 =` (no function equation) | 0 | accepted. The doc says nothing changes here, so it matches. |
| b1.lf | `a b = Decidable by-have-by: d`, `by-infer-instance`, `by-end` | 0 | it_b: accepted |
| b2.lf | `a b = by-rename: k`, then `' k by-exact` | 0 | ren_b: accepted |
| b3.lf | `a b + by-generalize: x at[ h ]` | 0 | gen_b: accepted |
| b4.lf | `a b + by-generalize-eq: k x at[ h ]` | 0 | geneq_b: accepted |
| b6.lf, c1.lf | `by-skip`; `by-done` after `by-rfl` | 0 | sk, dn: accepted |
| b7.lf | `3 by-iterate by-skip by-end` | 0 | itr: accepted |
| c2.lf | `2 by-iterate by-constructor by-end` on `(a=b ∧ a=b) ∧ a=b` | 0 | it_and: accepted |

An unsolved-goal `by-done` and 4 other wrong uses are refused. None is accepted.

| File | Wrong use | Exit | Output |
|---|---|---|---|
| b5.lf | `by-done` with a goal left | 4 | error 89: unsolved goals |
| w2.lf | `a a = by-rename: k` with no such hypothesis | 4 | error 482: Failed to find a hypothesis with type |
| w3.lf | `2 by-iterate by-rfl by-end` | 4 | error 90: No goals to be solved |
| w4.lf | `by-infer-instance` on an equation | 4 | error 110: type class instance expected |
| w5.lf | `by-generalize: x at[ nope ]` | 4 | error 455: Unknown identifier `nope` |

One thing I hit on the way: `it_a` (a theorem whose statement is `Decidable (a = b)`) was rejected with diagnostic 57, "theorem type not a proposition". That is correct, since `Decidable` is a `Type`.

**Claim 2: class-typed parameter.**
- q.lf is `theorem q True Decidable explicit: d  True Decidable.decide Bool.true = := by by-rfl end q`.
- LeanForth: exit 2, "error 139 ... not supported yet", at `end`. It is not accepted.
- Pinned Lean on `theorem q (d : Decidable True) : decide True = true := by rfl`: exit 1, "Tactic `rfl` failed ... decide True is not definitionally equal to true". So Lean refuses it too.
- The `.lf` text needs `Decidable.decide`; plain `decide` is error 1, an unknown name.

**Claim 3: depth.**
- b9.lf, `235 by-iterate by-skip by-end`: exit 2, "error 99 ... not supported yet". Pinned Lean accepts `iterate 235 skip`; the docs already say LeanForth is stricter here.
- b8.lf, `100 by-iterate by-skip by-end`: exit 0, accepted.

**Claim 4: Lean twins.** I ran pinned Lean 4.35.0 on `fx_one` (`funext x; rfl`), `gen_b` (`generalize k : a + b = x at h`), `it_and` (`iterate 2 constructor`), `ren_b` (`rename a = b => k`), `d100` and `d235`. Exit 0, no output, all accepted.

**Claim 5: docs.**
- LANGUAGE_REFERENCE.md rows (lines 2006-2014 and section D.11, lines 2967-3072) match what I saw:
  - Errors 482, 89, 90, 110, 455, 139 and 99 and the depth bounds all agree with the runs.
  - Line 2009 correctly gives 110 for a goal that is not a class.
  - Line 2012 says `by-skip` does nothing.
- The statement syntax is only implicit in the reference. It never shows `Decidable.decide`, or that a hypothesis is written `a b = explicit: h`. I got both from trial and error. A short full-file example per word would help.
- Stale or missing wording:
  - PROJECT_PROGRESS.md has no entry for small tactics 1 (grep finds only an unrelated line 205). Its "Now" list never says that `small-tactics-1`, `-fix` and `-fix2` are merged, and `small-tactics-1-fix2` is an ancestor of main. Nothing reports the group at any stage.
  - The TB2 row, PLAN_DRAFT.md:695, does not name this group.
  - PLAN_DRAFT.md:851 (9.4.8z12) says "Not started". That is right for the leftovers, but the row is the only place the group is mentioned.
  - `docs/development/done-checks/` has no `small-tactics-1` report. Commit 103f741c records a "re-check", not a done check. The group cannot be called done until the coordinator saves this report there and cites it in the plan row.

**Not checked:**
- Node-for-node term comparison with Lean: `tests/front/tactics/batch-small-1/check.py` was not run, and the Lean twins were not compared term by term. Lean only confirmed that it accepts them.
- `by-funext` on a two-argument function (93), `at[ * ]`, `by-iterate` nested sums, and Init or Mathlib runs.
- The other two Lean-twin wrong uses (`by-rename` with no match, `by-done`).
- CI jobs, coverage and the Forth review log. I read none of these.
