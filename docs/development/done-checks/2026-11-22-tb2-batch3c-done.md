# Done check: plan row TB2, batch 3c (2026-11-22)

Independent done checker (Sonnet), on main d66c4f28 (pushed as ae670877's range by `scripts/push.sh`; Forth review
[2026-11-22-tb2-batch3c.md](../forth-reviews/2026-11-22-tb2-batch3c.md) logged; full tier passed on that head).
The commit that added this report corrected the reference as items 1 and 3 to 5 ask: the status wording, the exact
text of 131 for a wrong-typed item, and two whole theorems (a nested "and", an "iff") with the note that a tactic
word needs `:= by`. Items 6 and 7 (statement syntax of ∧, ↔, Exists; by-exists's count) are already stated in the
reference where the checker found them.

DONE CHECK: TB2 batch 3c
Verdict: DONE for the claimed behavior, which works end to end. I wrote 12 theorems from LANGUAGE_REFERENCE.md alone and did not read tests/front/tactics/batch-f/. The reference text itself still needs the corrections below before it can say "done".
Head: main at d66c4f28, as asked.
Command, from the repository root, with nice -n 10 and one run at a time:
  bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf
My files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done3c/ (t1..t7, t6b, w1..w4, each .lf).
Exit codes: 0 accepted, 1 rejected, 2 unsupported, 4 invalid. Every accepted run printed "<name>: accepted; axioms: none" and "1291 declarations: 1291 accepted".

| File | Test | Expected | Observed |
|---|---|---|---|
| t1 | `<< ' h ' k >> by-exact` for a=b ∧ b=a | accept | exit 0 |
| t2 | `⟨ ' h ' k ' h ⟩ by-exact`, three items for a nested ∧ | accept | exit 0 |
| t3 | Iff from two directions: `<< ' Eq.symm ' Eq.symm >> by-exact` | accept | exit 0 |
| t4 | `<< ?_ ?_ >> by-refine`, then `' h by-exact`, `' k by-exact` | accept | exit 0 |
| t5 | `by-exists[ ' h`, a `\` comment line, then `' k ]`, over three lines (a=b ∧ b=a ∧ a=b) | accept | exit 0 |
| t6 | `by-revert[ h`, `\ between`, `k ]` over three lines, then `by-intro[ x`, `( c ) y ]`, then `<< ' x ' y >> by-exact` | accept | exit 0 |
| t6b | `<<` over four lines with a `\` comment between the items | accept | exit 0 |
| t7 | `by-exists[ a ]` proving `' Eq a $ Exists` | accept | exit 0 |
| w1 | too few items: `<< ' h >>` for ∧ | reject | exit 4, error 466 "Constructor `And.intro` has 2 explicit field, but only 1 was provided" |
| w2 | `<< ' h ' k >>` for an ∨ goal | reject | exit 4, error 465 "more than one constructor", with Lean's note |
| w3 | `by-revert[ h` and `k` with no `]`, followed by more proof lines | 458 at the opening word, not accepted | exit 4, error 458 at 6:3 `by-revert[` "this list is never closed". No theorem line was printed. |
| w4 | wrong term inside: `<< ' h ' h >>` (the second item has the wrong type) | reject | exit 2 (unsupported), error 131 "not supported yet: a coercion (plan FE4)". It was not accepted. |

Two of my own mistakes were caught by good errors, so I fixed the files and re-ran them. I wrote `:=` with no `by`, which gave error 81, and I gave by-exists 3 items plus the added `?_` for 3 conjuncts, which gave error 467. Both messages were clear.

Where the reference was wrong, stale or insufficient (all in docs/user/LANGUAGE_REFERENCE.md):
1. Line 1421 says "tested on its branch", and lines 1423-1424 say "not done until its review and done check". They are stale once this report is cited, and the branch is now main. Suggested wording: "tested; compared with pinned Lean node for node by ...; done-checked 2026-11-22 (report cited in the plan row)".
2. Lines 1418-1424 name the test files and the plan row, but I found no "on its line" wording. Line 1447 says "Lean reports it at ⟨"; that is fine.
3. Line 1483 says an item of another type gives 131 "where Lean reports an application type mismatch". w4 printed 131 with the text "not supported yet: a coercion (plan FE4)", and that message is misleading for a plainly wrong term. The reference should show this message, or the message should be fixed. The answer is unsupported (exit 2), not rejected (exit 1), so a user with a wrong term never gets "rejected".
4. No Iff example is shown. I had to guess `<< ' Eq.symm ' Eq.symm >>` for an Iff. It worked, but the reference should show one example (around line 1426-1449).
5. No example is written as a whole theorem with `:= by` followed by `<< >> by-exact`. The only worked theorem (lines 1496-1506) is the by-have one. I wrote `:=` followed directly by `<< ... >> by-exact` and got error 81. Add one sentence: a tactic word needs `:= by`.
6. The statement syntax for ∧, ↔ and Exists (postfix, and `' Eq a $ Exists`) is found only through line 1436 and the notation table (line 716). It is thin for a first try. A "Mathematically / LeanForth / Lean" example for a nested ∧ would fix that.
7. `by-exists[ ]` counts: the example at line 1456 shows 2 items for 3 conjuncts, because `?_` is added. Line 1454 states this, but it is easy to miss. I got it wrong first (error 467).

Not checked:
- The other multi-line lists: `by-rewrite[ ]`, `by-rwa[ ]`, `by-exacts[ ]`, `by-clear[ ]`, `by-rename-i[ ]`, `at[ ]`.
- `by-have:` with `<< >>`, the `<< >>` as an argument, and holes inside `<< >>` (`_`, `?_` inside by-exact).
- Errors 462, 463, 464, 467 and 83 on their own.
- A 458 for a `by-intro[` or `at[` list, and a 458 caused by `end` or `:=`.
- Whether `--steps` shows per-line places.
- The reference's worked theorem at lines 1496-1506.
- The documentation of `⟨ ⟩` in the glossary beyond reading it.
- Comparison with pinned Lean; I ran no make targets or test suites, as instructed.
