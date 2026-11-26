# Done check: simp at hypotheses and rules from hypotheses that are not equations

DONE CHECK: simp at hypotheses and hypothesis rules

**Verdict: NOT DONE at the stage "works end to end" (the word "done" is not yet earned). It is DONE as a feature check, with one stale-wording gap.** The claim holds in every case I ran. FE9 at `docs/project/PLAN_DRAFT.md:756` still says "not reviewed, not merged, not done" for simp-group-2, although the code is on main ea791fac. That row needs a status update.

I learned the spelling from `docs/user/LANGUAGE_REFERENCE.md` D.10 (lines 2644-2857) and lines 156-196. I did not read `tests/`. Every theorem is mine. My files are in `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-simp2/` (t1-t9, w1-w4, u1, each `.lf`). Each ran as `bin/leanforth check --env tests/front/simp-slice.ndjson --elab-data tests/front/simp-slice.elab.ndjson FILE.lf`. I ran it with `GFORTH=.tools/gforth/bin/gforth`, `ulimit -u 500`, stdin from `/dev/null` and `nice -n 10`, one process at a time. Each run takes about 15-20 s.

**Accepted (exit 0), 9 of 9.** The last column is pinned Lean 4.35.0's verdict on my Lean twin. All six twins are in `l.lean`, which lean accepted with exit 0 and no output.

| File | Statement | Rules and `at` form | Exit | Lean twin |
|---|---|---|---|---|
| t1 | `a 0 + b = explicit: h`, goal `a b =` | `' Nat.add_zero` at[ h ], then `' h by-exact` | 0 | accepted |
| t2 | `h : a = b`, `k : a 0 + c =` | `' h ' Nat.add_zero` at[ k \|- ], then `' k by-exact` (both change) | 0 | not run |
| t3 | same statement as t2 | at[ * ] | 0 | accepted |
| t4 | `a b ≤ ¬` hn, `a b ≤` k, goal `c d =` | `' hn` at[ k ]; k becomes False and closes the unrelated goal | 0 | accepted |
| t5 | `a b ≤ b a ≤ ↔` h, `b a ≤` hq, goal `a b ≤` | `' h` on the target | 0 | not run |
| t6 | same `↔` h, `hq : a b ≤`, goal `b a ≤` | `' h <-` (right to left) | 0 | accepted |
| t7 | `a b = b c = ∧` h, goal `a c =` | `' h` (both halves chain a→b→c) | 0 | accepted |
| t8 | `a b = ¬` hn (a `¬` of an equation), `a b =` k, goal `c d =` | `' hn` at[ k ] | 0 | accepted |
| t9 | `a b ≤ ¬` hn, `k : a ≤ b ∧ b ≤ a` | `' hn ' false_and` at[ k ], goal `False` | 0 | not run |

- t4, t7, t8 and t9 printed `axioms: propext`. t1-t3 printed `axioms: none`.
- t9 was my own guess that `false_and` is in the slice library, and it was. It rewrites a `¬` inside a larger hypothesis.

**Refused or unsupported, 5 of 5.**

| File | Case | Exit | Message | Lean |
|---|---|---|---|---|
| w1 | `at[ h ]` where nothing changes | 4 | error 500 "`simp` made no progress" | exit 1, "`simp` made no progress" |
| w2 | wrong final step after a correct simp | 4 | type mismatch: `a = b` given, `b = a` expected | not run |
| w3 | `at[ nosuch ]` | 4 | error 455 "Unknown identifier `nosuch`" | not run |
| w4 | `h : a = b`, `k : a = c`; `' h` at[ k ] makes k into `b = c`, then I used `k` against goal `a c =` (the old form) | 4 | "has type `b = c` but is expected to have type `a = c`" | exit 1, same Type mismatch |
| u1 | `' Nat.add` (a definition to unfold, listed in D.10 as not supported) | 2 | "error 99 ... not supported yet", with the goal printed | not run |

Lean was run directly from the pinned toolchain binary, with no imports and no elan proxy. That gives four accepted and two refused with Lean, as you asked. The `.lf` files t1, t3, t4, t6, t7, t8 were accepted and w1, w4 refused. The two verdicts agree in every case.

**Stage reached: works end to end** for the claimed forms:
- `at[ h ]`, `at[ h1 h2 ]` (not run by me), `at[ h |- ]` and `at[ * ]`.
- Rules from `↔`, `¬`, `≠` (by its `¬ =` spelling) and `∧`, and `' h <-` on an `↔`.

I did not run `at[ h1 h2 ]`, the `<-` errors 502 and 503, or `≠` through a real `≠` token. The reference writes `≠` as `a b = ¬`, which t8 used. I did not examine in this check whether any code or checks beyond that exist.

**Documentation gaps and stale wording.**
- `docs/project/PLAN_DRAFT.md:756` (FE9) still calls simp-group-2 "written and tested on its branch, not reviewed, not merged, not done" and begins "the rest of simp not started". Both are stale if the code is on main and reviewed. Suggested wording: "slices SL1a-2 and the first part of SL1b are on main (ea791fac), reviewed (cite the review), done check <this report>".
- The reference had no gap. I wrote working proofs from D.10 alone. Two minor omissions:
  - `at[ * ]` is shown only through the `h` and `k` example at lines 2753-2758.
  - The postfix spelling of `≠` as `a b = ¬` is stated only at line 2668 in prose and in the statement table at line 174 as `¬`. A one-line "`≠` is written `a b = ¬`" next to line 174 would help.
- `docs/user/LANGUAGE_REFERENCE.md:2647-2648` names "slices SL1a-1, SL1a-2 and part of SL1b" correctly, so it is not stale. `LANGUAGE_REFERENCE.md:2000` also matches what I ran.

I modified no tracked files and did not touch PID 1453023.

## After the report (coordinator, 2026-11-26 02:52)

- Plan row FE9 says merged and done for this group, and the statement table of the language reference gives
  the spelling of "a is not b", in the same commit as this file.
- The checker did not run `at[ h1 h2 ]` or errors 502 and 503; the Forth review's probes p03, p04 and
  p17 to p19 did ([2026-11-25-simp-group-2.md](../forth-reviews/2026-11-25-simp-group-2.md)): Lean's
  verdicts, texts and terms.

Stage: **done** for simp group 2 (slice SL1a-2 and the hypothesis-rule part of SL1b).
