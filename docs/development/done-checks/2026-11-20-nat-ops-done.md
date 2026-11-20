# Done check: 9.4.8l (AW), nat-ops refuse a non-literal operand (2026-11-20)
Checker: done-checker (independent); main 81c6f2b3, ulimit -u 500, nice -n 10, stdin /dev/null, CPU mode day.

Verdict: DONE for "A user can run every Nat-arithmetic check as before (same verdicts), while the shared Nat operation words answer invalid, not a made-up literal, for a non-literal operand and for the predecessor of 0." Stage: works end to end for the user side (no verdict changes); the refusal is reached only by unit tests (no user command reaches it, by design: callers pass only literals). Not run by me: tier, CI, cover-changed.

| # | Command | Exit / seen | Result |
| --- | --- | --- | --- |
| 1a | check tests/reference/{constant-fixture,composition,poly-identity}.ndjson | 0,0,0; "3 declarations: 3 accepted", "1: 1 accepted" x2; axioms none | PASS (but these have no real Nat arithmetic; only the three decide runs below exercise nat-ops) |
| 1b | check --env decide-slice --elab-data ... dc-ops.lf | 0; "1273 declarations: 1273 accepted"; propext, Classical.choice, Quot.sound allowlisted; none NOT PROVED | PASS |
| 1c | same, dc-arith.lf | 0; "1269 declarations: 1269 accepted" | PASS |
| 1d | same, w-dc-add.lf | 4; "error 250 at 8:3 (token by-decide): Tactic decide proved that the proposition 2 + 2 = 5 is false" | PASS |
| 2 | gforth tests/core/nat-ops.fs; tests/core/reduce-nat.fs; tests/front/reduce-nat.fs | 0,0,0; "nat-ops test: all tests passed", "reduce-nat test: all tests passed" (core file's last line not shown in my tail, exit 0) | PASS |
| 3 | mutants.py --only aw-nat-ops-first-unchecked,aw-kernel-second-only,aw-kernel-pred-of-zero | 0; "3 run, 3 caught, 0 survived" | PASS |
| 4 | make test-kernel-reduction JOBS=3 | 0 (output tail only gforth-strict lines and redefinition warnings; I did not see the comparison's summary line) | PASS (summary not read) |
| 5 | headers and plan row read | see below | PASS with wording notes |

## Test lines asserting invalid (item 2)
- first operand non-literal: tests/core/nat-ops.fs:190 (all 14 ops: :192-:194 grid via all-refused?, line 193 first operand); kernel tests/core/reduce-nat.fs:173-174 and grid :180; front tests/front/reduce-nat.fs:110-111 and grid :115.
- second operand: nat-ops.fs:191 (pow) and grid :194 (`3 nlit k-nat`); reduce-nat.fs:173 (`3 nat k-app`); front :110.
- both: nat-ops.fs:192 (shiftLeft) and grid :195 (`k-nat k-app`, `k-app k-app`); reduce-nat.fs:180 (`k-app k-nat`) and :174; front :116.
- Nat.succ of a non-literal: nat-ops.fs:198-199; reduce-nat.fs:175-176 (kernel succ); front :114-115 (lf-meta-nat-succ).
- predecessor of literal 0 and of a non-literal: tests/core/reduce-nat.fs:195-200 (k-nat, k-app, `0 nat`; also checks no node made, no diagnostic); literal still answers: :205 (pred of 1 = 0).
- constructor of a non-literal: NOT a distinct assertion I could find. reduce-nat.fs:185-191 says "the predecessor and the constructor form" but the test lines :195-200 call lf-reduce-nat-pred only; the constructor path is covered through the shared lf-nat-lit-by (nat-ops.fs:208-210, `ran1` on k-nat and k-app). Gap: please confirm a lf-reduce-nat-constructor-of-non-literal test, or reword the comment (reduce-nat.fs:185).
- Extra: first operand with a huge exponent, invalid not 92/unsupported: reduce-nat.fs:181-182 (comment only; see :172 test line); front :117-120.

## Documentation
- src/core/nat-ops.fs:21-23,39-42: "invalid (-1) when a or b is no literal leaf", succ likewise. Matches.
- src/kernel/reduce-nat.fs:22-23,63-72,82: non-literal and predecessor of literal 0: invalid, -1, no diagnostic. Matches the tests.
- docs/project/PLAN_DRAFT.md:826 row (AW): says "Written and tested alone, reviewed, the review's fixes made; not integrated ... Remaining (the coordinator's): the change tier with its pinned-Lean comparisons, the done check and the push." It does not say done. Matches the stage: it is a no-verdict-change hardening; the user commands run but do not reach the refusal.

## Limits
- tests/reference/*.ndjson has no Nat arithmetic worth the name; item 1 relies on the decide runs (1273 and 1269 declarations incl. mul, mod, gcd) for the "nothing changes" claim. No Init snapshot or Mathlib run.
- Refusal is not user-reachable: callers pass only literals; the claim "no verdict the checker can reach changes" is shown by identical results on those runs plus the row's kernel grid (not rerun by me).
- Row says valid nodes and op index 0-13 are assumed (AY): out-of-range nodes are read, not refused.
- Tier, CI, cover-changed, Forth review log not run by me.

## Wording
- PLAN_DRAFT.md:826: after this report, "not integrated" can become "integrated; done check <this file>"; do not write "done" until the tier is recorded.
- reduce-nat.fs:185 comment names the constructor form but the test below tests only the predecessor; add the assertion or reword.

## Added by the coordinator (2026-11-20)

- The checker's one test gap is not a gap: the constructor's refusal is asserted directly in
  `tests/core/reduce-nat.fs` at lines 198-199 (`111 k-nat lf-reduce-nat-constructor 111 k-app lf-reduce-nat-constructor
  -> 111 -1 outcome-invalid 111 -1 outcome-invalid`) and 202-203 (`unary-refused?`: no diagnostic, no node made); the
  checker read only the predecessor's lines beside them.
- The tier it did not run: `make tier` exit 0 on the branch's final head (`cover-changed`, `make test`, `make test-unit`
  on gforth-fast, `check-rest` with every pinned-Lean comparison, the branch's 20 planted faults, all caught), and
  `scripts/push.sh` recorded the push of 81c6f2b3 in docs/development/ci-results.log.
- The kernel grid the plan row cites was run three times by others the same morning (implementer, reviewer, re-check),
  byte-identical on its 8,823 literal lines each time.

