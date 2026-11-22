# Done check: plan row TB2, batch 2a (2026-11-21)

Independent done checker (Sonnet), on main 838bb14e. Its own files were in its scratch folder and are not kept.

DONE (with two wording corrections; stage: works end to end for the six words on main 838bb14e)

Claim: a user can write by-have:, by-have, by-have-goal:, by-let:, by-suffices: and by-replace: in LeanForth proof text, have `bin/leanforth check` accept the theorem, see wrong proofs refused with Lean's message, and have the older tactics unchanged.

Acceptance list (ulimit -u 500, no make, fresh shell at repo root):
1. batch-b/check.py: exit 0. "2 files accepted, terms equal pinned Lean's node for node, step logs as golden; 6 wrong twins refused with Lean's messages; 2 not supported yet (exit 2)".
2. batch-b/check.py --lean: exit 0. "batch-b.lean gives batch-b.golden; pinned Lean prints the 6 wrong twins' messages".
3. batch-b/test.fs: all tests passed (exit 0). author/author.fs: all tests passed (exit 0).
4. My own file, written from LANGUAGE_REFERENCE.md lines 1181-1216 and its theorem syntax; I read the batch-b .lf files only to confirm layout. The reference was enough for every word.
   - File: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/mine.lf. It has 6 theorems: m_have_twice (k used in both And.intro branches), m_this, m_goal, m_let (Nat.le_refl x $ unfolds the value), m_suff, m_repl.
   - Command: `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson mine.lf`. Exit 0. Output includes "m_have_twice: accepted; axioms: none" and the same for the other five, and "1275 declarations: 1275 accepted". The count includes the env's 1269 Lean-exported declarations.
   - My first m_suff was wrong because I gave e the wrong type (the reference text was correct). The checker refused it with error 96 and "Type mismatch ... expected a ≤ b". I fixed the file and reran it.
   - Wrong variant w1.lf (have whose value h : b ≤ a does not prove a ≤ b): exit 4. First message: "error 96 at 6:15 (by-have:): Type mismatch h has type b ≤ a but is expected to have type a ≤ b". Pinned Lean on the twin `have k : a ≤ b := h` prints the identical Type mismatch text.
   - Wrong variant w2.lf (b a ≤ by-have-goal: k, closed in the wrong order): exit 4. First message: "error 96 at 7:7 (by-exact): Type mismatch h has type a ≤ b but is expected to have type b ≤ a". Pinned Lean cannot run `have_goal`, which is a Mathlib tactic ("unknown tactic"). My core-Lean twin `refine (fun (k : b ≤ a) => ?_) ?_` with `exact h` gives the same mismatch text. batch-b/check.py --lean already compares this case on its own twin.
5. batch-a/check.py exit 0 (3 accepted, 12 wrong twins refused, 4 unsupported). exfalso/check.py exit 0 (3 accepted, 1 wrong twin refused).
6. LANGUAGE_REFERENCE.md has all six words. The table at lines 1248-1253 has a stack comment and a Lean form for each, and the examples are at 1192-1216. LOG.md line 151 has the row for 2026-11-21-tb2-batch2a.md: 1 blocking and 5 fix-before-merge findings listed, with 4 plan tasks. The row says the fixes are f5abe672, and the progress note says findings 1-8 and 10 are fixed. I did not check the fixes in the code. check_registry.py exit 0 (313 lines as golden, 25 tactic files, 6 registrations refused).

Gaps and wording:
- Scope: I ran 6 positive and 2 negative cases of my own, plus the 2 positive files and 6 wrong twins of the harness. Two unported forms (`by-have: _`, and by-have with a metavariable-leaving value) answer 99 or 93 as documented. I did not rerun exit 2 myself outside the harness (the harness reports "2 not supported yet (exit 2)").
- The claim's wording "wrong proofs are refused with Lean's message" is true for the Type mismatch text. For `by-have-goal:` the Lean form is the Mathlib tactic have_goal, so pinned Lean 4.35.0 alone cannot run it. State this wherever the claim is made.
- docs/project/PLAN_DRAFT.md:695 (row TB2) and docs/project/PROJECT_PROGRESS.md:32 still say batch 2a is "tested on branch tb2-batch2a (not done)", not merged, not done-checked. That is now out of date: the work is on main at 838bb14e. Corrected wording: "batch 2a: DONE on main 838bb14e (done check 2026-11-21-tb2-batch2a-done.md)", once the coordinator saves this report there. Findings 9 (and the survivors, the six-wide stack effects and the Unknown-identifier message) remain plan tasks; keep that in the row.
- Neither document claims more than I saw. The doc heading says "compared with pinned Lean node for node", which is what check.py --lean shows for the two accepted files. My own six theorems were not compared node for node with Lean.
- I did not run make, coverage or the CI jobs. "Done" also needs the coverage, CI and review-gate parts of DONE_CHECKER.md. Those are outside this checker's runs; the Forth review is logged.
