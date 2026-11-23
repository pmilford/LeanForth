# Done check: plan row TB2, blocks slice 1 (2026-11-22)

Independent done checker (Sonnet), on main 00d6dbf5 (pushed by `scripts/push.sh`, origin/main f4b67864; Forth review
[2026-11-22-tb2-blocks1.md](../forth-reviews/2026-11-22-tb2-blocks1.md) logged; full tier passed on that head).
The commit that added this report corrected the reference as its items 1 to 6 ask (status wording; the order of
function and value with `$`; how a three-part "and" nests; 131 as an answer to a wrong term; where the statement
layout is explained; that the library's declarations print first). Its observation that a file's first error
ends the run, so a correct theorem beside a wrong one gets no verdict, is documented behaviour and now a "Later"
item of PROJECT_PROGRESS.md.

DONE CHECK: TB2 blocks slice 1. Verdict: DONE for the behaviour; the documents are stale and not yet DONE. Stage reached: works end to end on my own LeanForth text. Head was 00d6dbf5. I did not run make or the suites.

Command (repo root, nice -n 10; the same command for every file):
bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf
My files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/doneb1/ (good.lf, w1-w6.lf, multi*.lf). I wrote the syntax from LANGUAGE_REFERENCE.md only and did not read tests/front/tactics/blocks-1/.

Good theorems, all in good.lf. One run gave exit 0, and each of g1-g7 printed "gN: accepted; axioms: none".
| id | what it is | expected | observed |
| g1 | `<< ?_ ?_ >> by-refine`, then `{ }` per goal | accepted | accepted |
| g2 | three-part "and" with `{ }` nested two deep | accepted | accepted |
| g3 | braces spanning 3 and 5 lines | accepted | accepted |
| g4 | have-by whose proof is `Eq.symm h`, then `' k by-exact` after `by-end` | accepted | accepted |
| g5 | have-by inside a brace, k used after `by-end` | accepted | accepted |
| g6 | `by-constructor` / `by-focus` ... `by-end`, then a brace | accepted | accepted |
| g7 | `by-case: left =>` ... `by-end`, then a brace | accepted | accepted |
Not run: I did not write the reference's `by-case:` with a `{ }` inside it as its own theorem. g7 has the brace outside the case.

Wrong variants. None was accepted. Exit codes: 0 accepted, 1 rejected, 2 unsupported, 4 invalid.
| file | fault | observed |
| w1 | `{ }` over an open goal | exit 4, error 89 at the `}` (7:5), "unsolved goals, case left ... ⊢ a = b" |
| w2 | `Eq.symm h` (type b=a) closing a goal a=b | exit 2, error 131 "not supported yet: a coercion (plan FE4)". Not accepted, but the answer is "unsupported", not a type mismatch. |
| w3 | `x` made inside the first `{ }` by `by-have:`, used after the `}` | exit 4, error 1 "unknown name" at `x` (8:7) |
| w4 | have-by of b=a whose block is `' h by-exact` | exit 4, error 96 type mismatch (h : a = b, expected b = a) |
| w5 | a lone `}` after a closed brace | exit 4, error 83 "no block of this word's kind is open ... } closes {" |
| w6 | wrong term inside the second brace (have-by in brace) | exit 4, error 96 type mismatch |
I did not try `by-intro[ ]` inside a brace.

Multi-theorem files. The expectation "first not accepted, second accepted" does not hold.
- multi.lf (w2, then g1): exit 2, one error line, nothing accepted.
- multi2.lf (w4, then g1): exit 4, one error, the good theorem g1 is not reported.
- multi3.lf (g1, then w4): exit 4, one error, the good theorem g1 is not reported either.
The whole file is not checked and no per-theorem verdict is printed after an error. This matches LANGUAGE_REFERENCE.md:223 and :655 ("The first error ends the run"). If the owner expected per-theorem verdicts, they do not exist yet.

Where the reference was wrong, stale or too thin:
1. LANGUAGE_REFERENCE.md:1543-1546 still says "written and tested on branch `tb2-blocks1` ... not done-checked yet". This is stale now that the work is on main and checked end to end. Corrected wording: "on main; done-checked 2026-11-22 (report ...)". Only cite DONE after the coordinator saves this report and the CI gates are green.
2. Lines 1550-1565 show no example of `<< ?_ ?_ >> by-refine` followed by braces. The reference does not say that a one-line `{ }` tactic list is a `by-exact` plus its argument words. Tick order was my first-try failure. `' h ' Eq.symm $ by-exact` gave error 131 "coercion". The reference's line 1575 example writes `' Eq.symm ' h $`. Please add one sentence that the function comes first and `$` applies it.
3. The reference never says how `∧` nests in a statement. `a b = a b = ∧ a b = ∧` parses as (A∧B)∧C, not A∧(B∧C). I hit this on my second try (error 96 mismatch). I needed `a b = a b = a b = ∧ ∧` for a right-nested and. Please add a note, ideally with a three-part example near lines 1589-1607.
4. Error 131 as the answer to a wrong term (w2) reads like a missing feature, not a wrong proof. Line 1556 says rejections are 89/90. Say that a wrong term inside a brace can come out as 96 or as 131 "unsupported" (exit 2).
5. The statement and hypothesis layout (`explicit:`, postfix statement) is explained only at about lines 1140-1167, far from the blocks section. Add a link there.
6. Line 1589 says "checked with bin/leanforth check ...". This is accurate. The output ends with the line "accepted: 1297; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED", which is the end of the whole decide-slice environment run, not of my theorems. A reader would not know that my theorems are the last 7 of 1297 lines. Note that the env's declarations print first and the user theorems last.

Wording check: the claim "checked by LeanForth" is fine. Each accepted theorem is checked by the kernel from LeanForth text (axioms: none). No "proved" or "LeanForth version" overstatement found in the blocks section.

Not checked:
- Names given in a brace may be reused (`br_names`).
- Errors 82, 85, 72 and 90, and the `by-induction-with` alternatives.
- Comparison with Lean.
- Timing. Each run took about 0.4 s.
- Gforth 0.7.3 and the Lean tools.
- Whether CI and the coverage gates for this row are green.
- The have-by "89 at by-have-by:" error. I did not write a have-by with goals left open.
