# Done check: by-simp-only[ ] on the target

DONE CHECK: by-simp-only
Verdict: MIXED. Works end to end for everything I tried, but "done" is not yet allowed. The plan row still says "not merged, not done", the Forth review is only partly closed (its remainder is plan 9.4.8z2), and no done-check report is cited. Stage reached: works end to end on main 86e2448b, as seen by this check.

Claim: A user can write a LeanForth theorem proved by `by-simp-only[ ... ]` on the target, and `bin/leanforth check` accepts correct ones and refuses wrong ones as Lean 4.35.0's `simp only [...]` does.

Setup: I learned the spelling only from LANGUAGE_REFERENCE.md lines 156-184 and 2632-2745. I read nothing under tests/ and changed no tracked file. Every run used `GFORTH=.tools/gforth/bin/gforth`, `ulimit -u 500`, `</dev/null` and `nice -n 10`, with the command `bin/leanforth check --env tests/front/simp-slice.ndjson --elab-data tests/front/simp-slice.elab.ndjson FILE.lf`. All files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-simp1/. Each run takes about 20 s because it checks the 1996-declaration library.

Accepted (exit 0, each printed `NAME: accepted`):
- t1: `n 0 + n =` with `' Nat.add_zero`. Axioms: propext.
- t2: `n 1 * 0 + n =` with `' Nat.add_zero ' Nat.mul_one`.
- t3: `0 n 1 * + n =` with `' Nat.zero_add ' Nat.mul_one`.
- t4: `a b = explicit: h`, goal `a 1 + b 1 + =`, with `' h`.
- t5: same h, goal `b 0 + a =`, with `' h <- ' Nat.add_zero`.
- t6: `n n = n n = ∧` with `' and_self`.
- t7: statement `True`, with `by-simp-only[ ]`. Axioms: none.
- t8: proposition hypothesis `a b ≤ explicit: h`, goal `a b ≤`, with `' h`.
- t9: `n 0 * 0 =` with `' Nat.mul_zero`.

Refused or not supported:
- w1: `n n 1 + =` with `[ ]`. Exit 4, "error 500 ... `simp` made no progress".
- w2: false `n 0 + n 1 + =` with `' Nat.add_zero`. Exit 4, unsolved goal `n = n + 1`.
- w3: `' Nat.add_nothing`. Exit 4, "error 1 ... unknown name".
- n1: `' Nat.add_comm`, which D.10 lists as not supported. Exit 2 (error 99, goal shown), not accepted.

Lean 4.35.0 (`.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, file l.lean, Init only, exit 1 overall):
- t2, t5, t6 and t8 as `simp only [...]` produced no error, so Lean accepts them.
- w1 gives "`simp` made no progress", matching LeanForth.
- w2 gives "unsolved goals ... ⊢ n = n + 1", matching LeanForth.
- I did not run Lean on t1, t3, t4, t7, t9, w3 or n1.

Documentation gaps: none blocking. Every proof worked first time from the reference, using the postfix forms in the table at LANGUAGE_REFERENCE.md:163-178.
- LANGUAGE_REFERENCE.md:2662-2684 has no `' h <-` example, though line 2655 explains it clearly.
- The reference does not show the `True` statement form. I guessed `  True` as the statement line and it worked. The table at lines 163-178 lists `True` only as a hypothesis type.
- The reference does not show how a `≤` statement is spelled (`a b ≤`). Line 2653 uses `a ≤ b` only as prose.

Stale wording:
- docs/project/PLAN_DRAFT.md:756 (row FE9) says "written, tested and Forth-reviewed on branch `simp-sl1a-1` ... not merged, not done". The code runs on main 86e2448b, so "not merged" is stale. Suggested wording: "merged to main (86e2448b); works end to end per done check <date>; not done until the review remainder (plan 9.4.8z2) is closed".
- The same row names the branch `simp-sl1a-1` as the place where the code lives. Update that too.
- LANGUAGE_REFERENCE.md:156-159 says each form in that table was accepted by an independent checker. That is correct for the forms already there, but this check adds `True` as a statement and `≤` as a hypothesis and statement. Add them if wanted.
- I found no other "not merged" or "planned" wording about simp in LANGUAGE_REFERENCE.md.

Wording to flag: LANGUAGE_REFERENCE.md:2638-2640 says the term is Lean's "node for node". I did not run `tests/front/tactics/simp-1/check.py`. What I did show is that LeanForth and Lean agree on accept or refuse for the cases above. Keep "node for node" only if you cite that script's run. Also, a LeanForth acceptance here means the kernel re-checked the term. It is not "LeanForth proved".

Not covered: a hypothesis rule given as `<-` on a library lemma, `at[ ]`, and the other D.10 "not supported" shapes beyond `Nat.add_comm`.

## After the report (coordinator, 2026-11-25 16:43)

- "Node for node": the comparison of each accepted test theorem's term with pinned Lean's is
  `tests/front/tactics/simp-1/check.py`, which the tier ran on the merged head 92d58dd4 (exit 0, recorded by
  `scripts/push.sh` for main 86e2448b); the Forth review compared 21 more of its own
  ([2026-11-25-simp-sl1a-1.md](../forth-reviews/2026-11-25-simp-sl1a-1.md)). The done checker showed
  agreement on accepted and refused, as it says.
- The review's remainder (plan row 9.4.8z2: the kernel copies of two shared words, two Lean errors answered
  as "not supported yet", one style item) is planned work on other words; it does not change what this
  slice claims.
- The reference gained what the checker had to guess (`True` as a statement, `a b ≤`, a `' h <-` example),
  and plan row FE9 says merged, in the same commit as this file.

Stage: **done** for slice SL1a-1 (`by-simp-only[ ]` on the target). Simp at hypotheses, `by-simp` and the
rest of the simp plan are not started.
