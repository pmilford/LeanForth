# Done check: plan row TB2, case patterns slice E2b (2026-11-25)

Independent done checker (Sonnet), on main 31ec9f5e (pushed by `scripts/push.sh`; Forth review
[2026-11-24-tb2-patterns-e2b.md](../forth-reviews/2026-11-24-tb2-patterns-e2b.md) logged with its re-check; full tier
passed on that head). The commit that added this report added to the reference what this and the earlier checkers
had to guess: a section "Writing a statement: the forms a first proof needs" (variables, hypotheses, applications,
and, or, not, iff, exists, False/True/Empty hypotheses, and that `by-exact` is not for a negated goal), and the
status date.

DONE CHECK: TB2 patterns E2b

Verdict: DONE, at stage "works end to end" for the two claims as worded. HEAD was 31ec9f5e "Extend the log of slice E2b to the library word".

Command, run from the repo root for each of my own files (`nice -n 10` and the scratchpad path were my additions):
`bin/leanforth check --env tests/front/patterns-slice.ndjson --elab-data tests/front/patterns-slice.elab.ndjson FILE.lf`
The files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/donee2b/. The reference names patterns-slice for these tactics, so I used it. I did not run decide-slice.

I wrote the syntax from docs/user/LANGUAGE_REFERENCE.md lines 80-95, 1215-1233 and 1342-1363, and did not read batch-h2.

| File | What it proves | Expected | Observed |
|---|---|---|---|
| g1 | `k : ¬a=b` ⊢ `¬(a=b ∧ b=a)`, by `by-contra[ << x y >> ] by-contradiction` | accepted | exit 0, "g1: accepted; axioms: none" |
| g2 | `¬¬(a=a)`, by `by-contra[ h ] by-contradiction` | accepted | exit 0, axioms none |
| g3 | `k : ¬a=b`, `e : a=b` ⊢ `a=b`, by `by-contra: - by-contradiction` | accepted | exit 0, axioms none |
| g4 | `h : False` ⊢ `a=b`, by `by-contradiction` | accepted | exit 0, axioms none |
| g5 | `x : Empty` ⊢ `a = Nat.succ a`, by `by-contradiction` | accepted | exit 0, axioms none |
| g6 | same as g3 with `by-contra: _` | accepted | exit 0, axioms none |
| g7 | `k : ¬a=b` ⊢ `¬a=b`, by `by-contra[ Rfl ] ' k by-absurd ' Rfl by-exact` | accepted, which shows a hypothesis named `Rfl` exists | exit 0, axioms none (after my first attempt failed, see below) |
| w1 | `h : True` ⊢ `a=b`, by `by-contradiction` | refused | exit 4, error 449 "Tactic `contradiction` failed" |
| w2 | `h : False ∧ a=a` ⊢ `a=b`, by `by-contradiction` | refused | exit 4, error 449 |
| w3 | `by-contra[ x y ]` with two patterns | refused | exit 4, error 474 "take one pattern" |
| w4 | `by-contra: - ' hh by-exact`, using a name the `-` was meant to clear | refused | exit 4, error 1 "unknown name" |
| w5 | `¬a=b` with `by-contra[ Rfl ] by-contradiction` | refused | exit 4, error 449; the printed goal shows `Rfl : a = b ⊢ False`, so `Rfl` is a plain name and the equation was not taken apart |

Notes on the table:
- In w4 the name I used, `hh`, never existed. That refusal does not show that `-` cleared a hypothesis. I did not test a name that was introduced and then cleared.
- No wrong variant was accepted, and no refusal was dressed up as exit 0 or 2.

Reference problems:
- Line 7 still says "Status date: 2026-11-15". The E2b text was added after that date, so the header is stale.
- Lines 1348-1356 give the `by-contra[` example only as a statement fragment: no `theorem` or `end` lines, and no `:= by`. I had to take the wrapper from lines 80-95. A reader could not write it on the first try from this entry alone.
- Lines 1222-1223 and 1351-1353 spell the example in a compressed form. For instance `b a = ¬ explicit: k` is a hypothesis and the final `¬` closes the goal. This is not explained at that spot, so I guessed the binder form for `False`, `True` and `∧` hypotheses (`False explicit: h`, `False a a = ∧ explicit: h`) from the pattern. It worked. The reference does not say how to state `False`, `True` or `∧` hypotheses.
- My first g7 attempt used `' k by-exact` on a goal `a=b → False`. It exited 2 with error 133, "implicit lambda (plan FE2)". The reference does not say that `by-exact` cannot be used when the goal is a negation. Lines 1344 and 1243 only show the `by-absurd` route. I fixed it with `' k by-absurd ' Rfl by-exact`.
- Lines 1228-1229 say "None found: 449". It matches what I saw for w1, w2 and w5. Line 1842 says `rfl` is a leaf pattern but never says a capital `Rfl` is only a name. The behaviour is correct but undocumented.
- I found no "tested on its branch" wording in the reference (grep returned nothing).

Not checked:
- I did not run the reference's own examples (`bc_tuple`, `em_empty`) or the `by-contra.lf` and `empty.lf` files.
- I did not try the unsupported cases at lines 1229-1233 (`a ≤ b`, `true = false`), alternative patterns `a | b`, `rfl`/`-` inside `by-contra[ ]`, or `by-contra-core`.
- I did not test `-` or `_` as `by-contra[ - ]` and `by-contra[ _ ]`. Only the `by-contra: -` and `by-contra: _` forms were run.
- I did not run the decide-slice environment, the Lean comparison, or `--strict-axioms`.
- I did not check the plan row, PROJECT_PROGRESS.md or the review log. I did not run `make` or the test suites.

The tail of every accepted run reads "accepted: 1316; ... none NOT PROVED". I did not look into what that last phrase means.
