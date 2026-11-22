# Done check: plan row TB2, batch 1 (2026-11-21)

Independent done checker (Sonnet), on main 18001014. The acceptance list was the implementer's, with a step in which the checker wrote its own proofs.

DONE (TB2 batch 1; stage: works end to end, with documented partial coverage). Head 18001014 on main. All commands run under ulimit -u 500; own files in /tmp/tb2-done/ (mine.lf, bad.lf, bad.lean).

Claim: A user can write the nine words (by-change, by-show, by-swap, by-specialize, by-revert, by-delta, by-contradiction, by-trivial, by-absurd) in LeanForth proof text and have bin/leanforth check kernel-accept it; wrong proofs refused with Lean's message; unported cases exit 2.

1. check.py (GFORTH=$G) exit 0: "3 files accepted, terms equal pinned Lean's node for node, step logs valid and as golden; 12 wrong twins refused with Lean's messages; 4 not supported yet (exit 2)".
2. check.py --lean (LEAN=$L) exit 0: "batch-a.lean gives batch-a.golden; pinned Lean prints the 12 wrong twins' messages".
3. $G batch-a/test.fs exit 0: "all tests passed".
4. Own file /tmp/tb2-done/mine.lf with nine theorems, one per word (my_change, my_swap, my_contra, my_triv, my_abs, my_show, my_rv, my_sp, my_de), run with `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson`: exit 0, each "accepted; axioms: none", "1278 declarations: 1278 accepted". Wrong variant bad.lf (`x y < by-change` on goal x ≥ y): exit 4, "error 443 'change' tactic failed, pattern x < y is not definitionally equal to target x ≥ y". Pinned Lean on the Lean twin bad.lean prints the same text (LeanForth adds its error number and position).
5. x-cn-le.lf: exit 2, "unsupported: ... error 99 ... by-contradiction: not supported yet: this case of the tactic". Not accepted.
6. LANGUAGE_REFERENCE.md:1127-1177 (prose and examples) and table rows :1202-1210 document all nine words with error codes and a Lean-form column. forth-reviews/LOG.md:150 logs the review 2026-11-21-tb2-batch1.md: 1 blocking and 4 fix-before-merge findings all marked fixed; 1 plan task (finding 6, by-contradiction at indexed-family hypotheses such as ≤, not started).
7. check_registry.py exit 0: "301 lines as golden; ... 6 registrations refused; harness self-test passed".

Gaps: every word worked from the documentation alone. Not independently exercised by me: wrong twins of the other eight words (covered only by steps 1 and 2); by-specialize on a function-type hypothesis (docs say test.fs covers it). by-swap and by-absurd are documented as Batteries tactics; I did not check whether Batteries is needed. The pinned-Lean golden passes.
Coverage is partial by design: by-contradiction, and by-trivial through it, answer unsupported (exit 2) at the first hypothesis of an indexed family (finding 6).
Wording to fix: docs/project/PLAN_DRAFT.md:695 still says "integrated on branch tb2-batch1 ... not merged, not done-checked". Suggested: "batch 1 works end to end on main (done-checker 2026-11-21); by-contradiction at indexed-family hypotheses (finding 6) not started". Write "checked by the kernel from LeanForth text", not "LeanForth proved".
