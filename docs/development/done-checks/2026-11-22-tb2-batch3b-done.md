# Done check: plan row TB2, batch 3b (2026-11-22)

Independent done checker (Sonnet), on main eb6a35e5. The stale wording it lists (item 5) was corrected in the
commit that added this report, which also added to the language reference the command line with its data files
(item 1), the note that `by-intro[ ]` needs `by-revert[ ]` first in this statement form (item 2) and the checker's
theorem with named holes as a worked example (item 3). The Forth review is logged
([2026-11-22-tb2-batch3b.md](../forth-reviews/2026-11-22-tb2-batch3b.md)) and the full tier passed on this head
(`/tmp/tb2-batch3b-final-tier.log`, pushed by `scripts/push.sh`).

DONE CHECK: TB2 batch 3b
Verdict: DONE for the user-facing claim, reached stage "works end to end". Not "done" in the DONE_CHECKER.md sense: I did not check the Forth review log, coverage, CI or the plan row. The reference itself (LANGUAGE_REFERENCE.md:1329) still says "tested on branch tb2-batch3b, not done".

Claim as a user reads it: a user can write `at[ h1 h2 ]`, `by-intro[ ]`, `by-revert[ ]`, `by-clear[ ]`, `by-rename-i[ ]`, the holes `_`, `?_`, `?: NAME` and `t by-refine` in LeanForth text and have `bin/leanforth check` accept or refuse it.

Setup: HEAD eb6a35e5 on `main`, CPU_MODE day, one command at a time under nice -n 10, no make targets. I learned the syntax only from docs/user/LANGUAGE_REFERENCE.md (lines 120-150, 1326-1387 and the table at 1435-1443). I looked at one test only for the command line and data files: tests/front/tactics/batch-e/check.py names tests/front/decide-slice.ndjson and tests/front/decide-slice.elab.ndjson. I also saw one test's header (w-revert-unknown.lf) while looking for the syntax. The reference's own F.2 examples use s1-slice and s2-slice instead.
Command, from the repo root:
  bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf
My files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done3b/ (t1..t7, w1..w4 `.lf`).

| File | Uses | Expected | Observed |
| --- | --- | --- | --- |
| t1 | `by-rw[ ' h ] at[ h2 ]`, then `' h2 by-exact` | accept | exit 0, `t1: accepted; axioms: none` |
| t2 | `by-revert[ h k ]`, `by-intro[ x y ]`, `x by-exact` | accept | exit 0, accepted |
| t3 | `by-clear[ k ]`, `' h by-exact` | accept | exit 0, accepted |
| t4 | `' And.intro ?_ $ ?_ $ by-refine`, two `by-exact` steps (two `?_` goals) | accept | exit 0, accepted |
| t5 | `' And.intro ?: left $ ?: right $ by-refine`, then `by-case: right =>` and `by-case: left =>` | accept | exit 0, accepted (goals closed by name, in reverse order) |
| t6 | `_ Eq.refl by-refine` (a `_` unification fills) | accept | exit 0, accepted |
| t7 | `by-revert[ h k ]`, `by-intro[ _ _ ]`, `by-rename-i[ x y ]`, `x by-exact` | accept | exit 0, accepted |
| w1 | wrong term in a refine hole (`' k` where `a = b` is wanted) | refuse | exit 4: "error 96 at 8:7 (by-exact): Type mismatch k : b = a, expected a = b" |
| w2 | `_ by-refine` on `a = b` (a `_` unification cannot solve) | refuse | exit 4: "error 461 at 5:5 (by-refine): don't know how to synthesize placeholder", with context `a b : Nat ⊢ a = b` |
| w3 | `by-revert[ h k` with no `]` | refuse | exit 4: "error 458 at 7:16: a list of names ends with ] on its line" |
| w4 | t1 with the old `at: h2` | refuse | exit 4: "error 1 at 7:16 (token at:): unknown name", so `at:` is no longer a word |

Every refusal exits 4, because the text is refused before the kernel sees it, not 1. That matches the reference: errors 96, 461 and 458 are LeanForth's own, not kernel rejections. A wrong proof that gets past the elaborator and fails in the kernel (exit 1) was not probed.

Axiom report: t1..t7 each print `tN: accepted; axioms: none`. The run also re-checks the 1291 library declarations. The summary line reads "accepted: 1291; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED". `--strict-axioms` on t4 gave exit 0 and the same lines. That is right, since nothing is NOT PROVED (AI_TOOLS.md:47 says exit 6 only when something is). I did not run a `by-sorry` theorem under it.

Where the reference was wrong, unclear or insufficient (I wrote all seven proofs correctly first time):
1. The reference gives no complete theorem skeleton at 1326-1387 and never says which `--env` and `--elab-data` files exist for these tactics. F.2 (1898-1909) names s1-slice and s2-slice. I used decide-slice, which I found only through check.py. s1/s2 may well work too; I did not try.
2. The reference does not say you cannot state `a = b → b = a → a = b` in natural form (`->` is kernel-form only, 722 and 1178). By-intro goals therefore have to come from `by-revert[ ]` first. 1341 hints at this but never says it outright.
3. A hole `?: NAME` as the head of a by-case block is shown only as a tag. The reference does not show `by-case: right =>` ... `by-end` closing a refine goal, nor that the order of the blocks is free. It worked.
4. The reference describes `at[ ]` as "right after by-rw[ ], by-rewrite[ ], by-rwa[ ], by-change, by-symm, by-delta" (1435). It is never said that `at[ h2 ]` can sit on a new line, or that it must come directly after those words. I put it on the same line.
5. Line 1329 says "tested on branch `tb2-batch3b`" while the work is on `main`. That wording is out of date.
6. Wording check: the exit code for a refused LeanForth text is 4 ("invalid ... was not checked"), while the F.2 text says "4 refused". This is acceptable. I found no "proved" or "full" overclaim in the section. The checker's output says "accepted", not "proved".

Not checked:
- the plan row TB2 and PROJECT_PROGRESS status;
- the Forth review log, coverage and CI;
- comparison with pinned Lean (the reference says check.py does it; I did not run it);
- `at[ * ]`, `by-rwa[ ] at[ ]`, `by-change at[ ]`, `by-symm at[ ]`;
- the other error codes in the reference (454, 455, 459, 460, 94, 139, 211, 440-442);
- `by-intro[ ]` with no names;
- `by-apply` and `by-have:` with holes;
- the natural-form `Init` or Mathlib scale;
- whether a `by-intro[ ]` goal can come from a `¬` or a binder written directly.

Stage per DONE_CHECKER.md: works end to end for the listed words, on my own small theorems, using LeanForth text as the input. The "done" row needs the items above.
