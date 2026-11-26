# Done check: simp under binders, through `if`, and elaboration data format 4.1

DONE CHECK: simp under binders, through if, format 4.1
Verdict: DONE as to behaviour (works end to end on main 121b1d0f). Stale documentation wording remains (see gaps), so the plan row cannot be called "done" until it is fixed.

Claim: A user can, with by-simp-only[ ], rewrite under an arrow and under ∀ (goals made with by-revert), through `c t e ite` (condition, branch, both) and in `decide p = decide q` goals, and `bin/leanforth check` reads elaboration data format 4.1 and prints ", N realized congruence theorems". Correct proofs are accepted and wrong ones refused as Lean 4.35.0's simp only does.

Method: spelling learned only from LANGUAGE_REFERENCE.md, lines 156-196 and D.10 at 2644-2940. I read nothing under tests/ and changed nothing in the repository. Every run used `bin/leanforth check --env tests/front/simp-slice.ndjson --elab-data tests/front/simp-slice.elab.ndjson F.lf`, with GFORTH set, ulimit -u 500, </dev/null, nice 10, one process at a time. My files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-simp3/ (t1..t6, w1..w3, u1 as .lf; L.lean holds the Lean twins).

Theorems (exit code from LeanForth; verdict from Lean 4.35.0 on the twins, no imports, toolchain binary):
- t1, exit 0: `' h by-revert` then `by-simp-only[ ' h2 ]`, then `by-intro: h ' h by-exact`. Under an arrow, goal a=b → c=b with h2: a=c. Lean accepts.
- t2, exit 0: the reference's ∀ example, `' a by-revert by-simp-only[ ' Nat.add_zero ]`, then `by-intro: a ' True.intro by-exact`. Under ∀. Axioms propext, Quot.sound. I did not run a Lean twin. The reference gives one, but I did not run it.
- t3, exit 0: `a 0 = 1 2 ite b 0 = 1 2 ite =` with h: a=b, `by-simp-only[ ' h ]`. Condition rewritten. Lean accepts.
- t4, exit 0: `c 0 = a 1 + 7 ite c 0 = b 1 + 7 ite =`, `' h`. Only the branch is rewritten. Lean accepts.
- t5, exit 0: nested `a 0 = a 1 = 1 2 ite 3 ite` against the same with b, `' h`. No Lean twin run.
- t6, exit 0: `a 0 = Decidable.decide b 0 = Decidable.decide =`, `' h`. This is the decide goal; the reference states it with an = hypothesis, not an ↔. Lean accepts.
- w1, exit 4: a `by-revert` goal where the only rule `' h3` (h3 : d = e) does not match. Error 500 "`simp` made no progress". Lean refuses with "`simp` made no progress".
- w3, exit 4: the `ite` goal closed by simp, then `' h by-exact`. Error 90 "No goals to be solved". Lean refuses with the same message.
- w2, exit 0: both sides are the same `if` and h is unused. It is true, so acceptance is right. Lean also accepts it, but it is not a refusal test. I did not write a rule that fails to match under the `if` and gets refused.
- u1, exit 2: two binders with a body using both variables, `' b by-revert ' a by-revert`, then `by-simp-only[ ' Nat.add_zero ]`. Error 99 at by-simp-only[ ("not supported yet"), goal shown `(a b : Nat) → a + 0 + (b + 0) = a + b`. This matches D.10 lines 2930-2933.
Lean accepted t1, t3, t4, t6 and w2, and refused w1 and w3. That is four accepted and two refused as asked.
My first t4, t5 and w1 attempts failed because of my own mistakes, not the tool: wrong postfix shape, error 18 and error 119, and a rule that did match, which gave a type mismatch. The fixed versions above are the ones reported.

Count line (t3 run): "elaboration data: 106 instances, 11 default instances, 430 reducibility statuses, 4 eliminators, 970 instances left out, 61 classes, 125 tags, 239 matchers, 100 projections, 31 smart-unfolding bodies, 9 congruence lemmas, 33 defeq tags, 5 realized congruence theorems". The checked env was 2028 declarations, all accepted.

Documentation gaps: none blocking. I wrote every working proof from the reference alone. I had to infer how to state a nested `ite` and a branch-only rewrite. The reference gives only the condition example, so a nested or branch-only example would help (LANGUAGE_REFERENCE.md ~2838). The `decide` example (line 2856) uses an = hypothesis. The reference does not say how to state it from an ↔ hypothesis, and I did not try.

Stale wording (docs say "not merged" but the code is on main, and I ran it from main):
- docs/project/PLAN_DRAFT.md:756 (FE9): "simp group 3 (binders, `if` and congruence, format 4.1) Forth-reviewed on its branch, not merged". git branch --merged main lists simp-group-3. The row also needs the report of this done check cited.
- docs/programming/ELABORATION_DATA.md:35-39: "`leanforth check` reads the data but no verdict uses it yet ... the elaborator (s1-elab) is not merged." This is false for 4.1. The realized congruence theorems are used by the simp verdict (t6 is accepted through Decidable.decide.congr_simp). Corrected wording: "leanforth check reads the data; by-simp-only[ ] uses the instances and, in format 4.1, the realized congruence theorems".
- docs/project/PROJECT_PROGRESS.md:46 area still describes simp group 2 as "not merged, not done". Group 2 is merged (PLAN_DRAFT.md:756 itself says on main 60c294eb). I did not read the rest of the line.
- LANGUAGE_REFERENCE.md:2864-2875 and ELABORATION_DATA.md:845-854 are accurate. D.10's unsupported list matches the behaviour I saw for u1.
Not checked: code review, the logged Forth review, CI status and coverage. The "done" stage also needs those.

## After the report (coordinator, 2026-11-26 04:27)

- The other requirements of "done" hold on main cdba6027: the Forth review with its fix round
  ([2026-11-26-simp-group-3.md](../forth-reviews/2026-11-26-simp-group-3.md)), the full tier (exit 0; 47
  faults run, 46 caught, 1 listed equivalent), branch coverage clean, the push's local CI (121b1d0f).
- The stale wording the checker lists (plan row FE9, ELABORATION_DATA.md's status of the data's use) was
  corrected in the same commit as this file; the dated entries of PROJECT_PROGRESS.md it names are that
  day's history and stay.
- "Node for node" terms: `tests/front/tactics/simp-3/check.py` in the tier, and the review's 19 own probes.

Stage: **done** for simp group 3. Left for group 4 (plan row 9.4.8z10): conditional rules (the discharger),
dsimp of dependent arguments, a rule under two binders using both variables, then plain `by-simp`.
