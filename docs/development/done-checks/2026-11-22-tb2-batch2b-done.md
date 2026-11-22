# Done check: plan row TB2, batch 2b (2026-11-22)

Independent done checker (Sonnet), on main 059d9554. Verdict for the code claim: DONE on every acceptance item run; the checker marks the report MIXED because the plan and progress wording still said "on the branch" (to be corrected with the next merge), and because it did not write its own `by-next` proof (the batch's own tests cover it).

MIXED (stage: works end to end; "done" not shown because the status wording is stale)

Claim: A user can write `<-` in `by-rw[ ]`, `by-rwa[ ]`, `by-exacts[ ]`, `by-cases:`, `by-contra:` / `by-contra`, `by-symm`, `by-and-intros` and `by-next` / `by-case: _` in LeanForth text and have `bin/leanforth check` accept it. Wrong proofs are refused and unported forms exit 2.
Stage: works end to end for everything I ran. `by-next` / `by-case: _` was not run by me. I only ran the batch's own test files and my own file, which does not use it.

Commands, all from /home/peter/code/LeanForth with `ulimit -u 500`; G, L and the paths as in your brief:
1. `GFORTH=$G python3 tests/front/tactics/batch-c/check.py` → exit 0. "7 files accepted, terms equal pinned Lean's node for node, step logs valid and as golden; 9 wrong twins refused with Lean's messages; 4 not supported yet (exit 2)".
2. `... check.py --lean` → exit 0. "batch-c.lean gives batch-c.golden; pinned Lean prints the 9 wrong twins' messages".
3. `$G tests/front/tactics/batch-c/test.fs -e bye`, `tests/front/tactic-lib.fs`, `tests/lib/runs.fs` → each exit 0, "all tests passed".
4. My own file /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/my.lf, 8 theorems. The command was `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE` → exit 0, all "accepted":
   - m_rw (`<-`), m_rwa, m_exacts, m_contra (`by-contra:`), m_symm and m_ai (`by-and-intros`): axioms none.
   - m_dec (decidable, `x y = by-cases:`): axioms none.
   - m_cls (`Nat Nonempty by-cases:`): axioms propext, Classical.choice, Quot.sound. This matches the claim.
   - Wrong variants, both exit 4:
     - w1.lf, `by-rw[ ' Nat.add_zero <- ]`: error 219 "Invalid rewrite argument: The pattern to be substituted is a metavariable (`?n`) in this equality  ?n = ?n + 0". Pinned Lean on the twin `rw [← Nat.add_zero]` gives the identical message.
     - w2.lf, `by-exacts[ ' q ' p ' p ]`: error 90 "No goals to be solved". Pinned Lean on the `exact q; exact p; exact p` twin gives "No goals to be solved". Batteries' `exacts` does not exist in the core Lean I ran ("unknown tactic"), so the exact twin is not available. The batch's own check.py checks this form and passed.
5. `bin/leanforth check ... tests/front/tactics/batch-c/cases.lf` → exit 0. bc_dec and bc_tags: axioms none. bc_classical: axioms propext, Classical.choice, Quot.sound. `x-ra-le.lf` → exit 2 (unsupported, not accepted).
6. batch-b/check.py → exit 0 (2 files accepted, 6 wrong twins, 2 unsupported). batch-a/check.py → exit 0 (3 files accepted, 12 wrong twins, 4 unsupported).
7. `tests/front/check_registry.py` → exit 0. docs/development/forth-reviews/LOG.md:152 has the 2026-11-21 tb2-batch2b row. LANGUAGE_REFERENCE.md:1218-1272 and the word table at 1318-1328 give each word with its stack comment, Lean form and an example name. The by-rwa limit is at lines 1233-1239 and 1319. The axioms wording is at 1247-1251 and 1321.

Could not make work from the reference alone:
- LANGUAGE_REFERENCE.md:1218-1272 gives only the proof bodies (`rs_hyp`, `ra_basic` and so on). It does not give the `theorem ... explicit: h ... := by ... end NAME` frame or the hypothesis syntax, so I took those from tests/front/tactics/batch-c/*.lf. I opened rw.lf, intros.lf, contra.lf, exacts.lf and symm.lf for the frame, and cases.lf for by-cases. Suggest adding one complete theorem with its header to the batch 2b section.
- Every word then worked on the first try, except that my first wrong `<-` pattern (`Nat.add_zero`) was a metavariable. That is a Lean fidelity point, not a bug.

Wording that claims more than I saw (these are stale, not overstated in what works):
- docs/project/PROJECT_PROGRESS.md:32 and :33, and the PLAN_DRAFT.md:695 TB2 status line, say batch 2b is "on branch `tb2-batch2b`, not merged". It is on main (head 059d9554). The status says "tested alone" or "tested on the branch", and the "Next" text there also needs updating. After this report, say "done-checked: DONE" and cite the report, but only once the coordinator saves it under done-checks/.
- LANGUAGE_REFERENCE.md:1220 says "tested on the branch". Corrected: "on main, compared with pinned Lean node for node by batch-c/check.py".
- LANGUAGE_REFERENCE.md:1242 and :1320 label `by-exacts[ ]` as "Lean (Batteries)". That is correct, but the exact Lean twin does not run on pinned core Lean, so the comparison there rests on check.py's own twin.
- I did not read the plan row's remaining sub-steps, so I cannot say none is "not started". The progress text says findings 7 and 8 of the Forth review are plan tasks in row TB2, which are known limits. By-rwa and by-rfl on non-`=` goals are exit 2.

Verdict for the code claim: DONE on every acceptance item run, with no placeholder found. The plan and progress wording must be corrected to "merged on main, done-checked" before it says done.
