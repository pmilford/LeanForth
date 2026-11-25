# Done check: tactic blocks slice 3

DONE CHECK: tactic blocks slice 3
Verdict: DONE for the claim "integrated and works end to end" (stage: works end to end, with the documentation gaps below). I did not judge the plan-row "done" status.

Setup: I ran each file with `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf`. GFORTH was the project gforth, `ulimit -u 500`, stdin from /dev/null. The spellings come only from docs/user/LANGUAGE_REFERENCE.md:1803-1934. Files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-blocks3/. Every theorem has `Nat a b`, `h : a b =` and `k : b a =` as hypotheses. G is the goal `a b = b a = ∧`.

Accepted (exit 0, "tN: accepted; axioms: none"):
- t1, goal G: `by-constructor`, `by-try ' k by-exact by-end` (fails on a = b), `' h by-exact`, `' k by-exact`. Exit 0.
- t2, goal `a b =`: `by-try by-rfl by-end` (fails), then `' h by-exact`. Exit 0.
- t7, goal `a a =`: `by-try by-rfl by-end` (succeeds and closes the goal). Exit 0.
- t3, goal G: `by-constructor <;> by-first | ' k by-exact | ' h by-exact by-end`. The first alternative fails on a = b and the second closes it. Exit 0.
- t5, goal `a b = a b = ∧ b a = ∧`: `by-repeat by-constructor by-end`, then h, h, k. Exit 0.
- t6, goal G: `by-constructor`, `by-any-goals ' h by-exact by-end`, `' k by-exact`. Exit 0.

Rejected or not accepted. Exit 4 means invalid text, which is the rejection code for these; I never saw exit 1.
- w1, goal `b a =`: `by-try ' h by-exact by-end` and nothing else. The goal stays open and the theorem is rejected. Exit 4.
- w2, goal `b a =`: `by-first | ' h by-exact | by-rfl by-end`. Every alternative fails. Exit 4.
- t4, goal G: `by-constructor`, then `by-first | ' k by-exact | ' k by-exact by-end`. Both alternatives fail on a = b. It prints a type mismatch. Exit 4.
- w3, goal G: `by-any-goals ' k by-exact by-end` after `by-constructor`, then `' k by-exact`. Exit 4, type mismatch.
- w4, goal G: `by-repeat by-constructor by-end` then `' h by-exact`. Goals are left over. Exit 4.
- w5, goal `a b =`: `by-any-goals ' k by-exact by-end`. Exit 4, "error 469 ... Tactic failed on all goals:" at 6:3, as documented.
- u1, the documented 490 case: `by-try b a = by-have-by: j { ' h by-exact } by-end by-end`, then `' h by-exact`. Exit 2 (unsupported), not accepted, as documented at LANGUAGE_REFERENCE.md:1932.

Pinned Lean 4.35.0 (no imports, toolchain binary), on the Lean translations:
- t1 (`try exact k`) and t6 (`any_goals exact h`) give no error, so both are accepted.
- w1 (`try exact h` only) gives "unsolved goals".
- t4 (`first | exact k | exact k`) gives "Type mismatch".
- So LeanForth and Lean agree on all four.

Documentation gaps:
- No blocking gap. I wrote working proofs from the reference alone. The worked examples at lines 1850-1906 are enough to learn the spellings.
- docs/user/LANGUAGE_REFERENCE.md:1804-1805 still says "tested on its branch `tb2-blocks3`, not merged, not done". main at 6eb58a5b runs these words, so the text is stale or contradicts the claim. Reword it to state the stage the done checker found, or drop the branch wording.
- LANGUAGE_REFERENCE.md:2016 still marks `by-try`, `by-first`, `by-any-goals` and `by-repeat` with `**` (not yet implemented) and "designed". It also lists `by-all-goals` and `<;>` in that row. That contradicts the slice-3 section. Split the row: the four slice-3 words are implemented.
- LANGUAGE_REFERENCE.md:1691 ("no text can reach it until `by-try` and `by-first` exist") and :2397 describe `by-try` and `by-first` as future. Check both.
- The reference never says that a rejected proof exits 4, not 1. The task listed 1 as "rejected". Document the exit code for a wrong proof.
- I did not run any `make` target or the test suite.

## After the report (coordinator, 2026-11-25 09:36)

The stale passages of `docs/user/LANGUAGE_REFERENCE.md` the checker lists (the section's status, the
combinator row marked `**`, two passages calling `by-try` and `by-first` future) and the exit code of a
refused proof text (4) were corrected in the same commit as this file. Stage: **done**.
