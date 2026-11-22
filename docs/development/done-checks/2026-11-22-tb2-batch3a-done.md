# Done check: plan row TB2, batch 3a (2026-11-22)

Independent done checker (Sonnet), on main cfaab355. The stale status wording it lists was corrected in the commit that added this report.

DONE (with stale-wording corrections; head cfaab355, `ulimit -u 500`, no make, nothing tracked modified)

Claim: A user can write a trailing `at: h ...` (`|-` for the goal) after by-rw[ ], by-rewrite[ ], by-rwa[ ], `T by-change`, by-symm in LeanForth text and have `bin/leanforth check` accept it, as a port of Lean's `... at h`, with wrong forms refused and unported forms answered unsupported.
Stage: works end to end for the forms I ran. I did not run by-rewrite[ ], `|-`, or the `by-rfl` on `a <= a` unsupported case myself; batch-d covers them (item 1: "5 not supported yet (exit 2)"). I did not read batch-d to see whether it includes the `a <= a` case.

1. batch-d/check.py: exit 0. "3 files accepted, terms equal pinned Lean's node for node, step logs valid and as golden; 7 wrong twins refused with Lean's messages; 5 not supported yet (exit 2)".
2. batch-d/check.py --lean: exit 0. "batch-d.lean gives batch-d.golden; pinned Lean prints the 7 wrong twins' messages".
3. batch-d/test.fs: exit 0, "all tests passed".
4. My own file, /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/dc3a/my.lf (7 theorems). Command: `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE` → exit 0, "t1..t7: accepted; axioms: none", "1297 declarations: 1297 accepted".
   - t1: rw at h2, then ' h2 by-exact. t2: rw at two hypotheses (h3 h4). t3: `<-` at h2. t4: rwa at h2. t5: `a b = by-change at: h`. t6: by-symm at: h. t7: by-rwa[ ' h ] with goal `a c <=`.
   - Frame: the "A complete tactic proof" table in LANGUAGE_REFERENCE.md:1123-1140 was enough. All 7 theorems were accepted on the first run, and I opened no tests. Gap: the table never shows the `<=` or `=` hypothesis spelling for a `<-` rule beyond line 1257, but that line sufficed.
   - Wrong variants (exit 4 each):
     - w1, pattern absent. LeanForth: "error 215 ... Tactic `rewrite` failed: Did not find an occurrence of the pattern / a / in the target expression / c <= c". Pinned Lean (l.lean, same twin): "Tactic `rewrite` failed: Did not find an occurrence of the pattern a in the target expression c <= c" plus the same context. Same text.
     - w2, unknown hypothesis. LeanForth: "error 455 ... Unknown identifier `nope`". Lean: "error(lean.unknownIdentifier): Unknown identifier `nope`". Same.
     - w3, `' h2 by-exact at: h2`. LeanForth: "error 453 ... at: follows no tactic word that takes a location". Lean has no twin: its parser rejects it differently, which is fine.
   - Unsupported: `at: *` → exit 2, "error 99 ... not supported yet".
5. `Nat explicit: a Nat explicit: b a b = explicit: at:` → exit 4, "error 78 ... a reserved word: a syntax word cannot name a binder". It says "reserved word", so it meets the item.
6. batch-c, batch-b and batch-a check.py: exit 0 each.
7. check_registry.py: exit 0 ("340 lines as golden; ... 31 tactic files, sorted; 6 registrations refused"). LOG.md:153 has the row for the review that fixes 375a3342 (one grep hit for "tb2-batch3a"), and docs/development/forth-reviews/2026-11-22-tb2-batch3a.md exists. LANGUAGE_REFERENCE.md documents `at:` at lines 1268-1285 and the glossary row at 1366, with the Lean form, an example and the tactics that take it. by-rfl's rules are at line 1329 and in section D.3.
   - Not checked by me: that line 1329 says an `a <= a` goal answers 93 (not "accepted"). Line 1265-1267 says the same.

Gaps and stale wording to fix (main already contains batch 3a: `git branch --contains 375a3342` lists main):
- docs/user/LANGUAGE_REFERENCE.md:1251-1252: "tested on its branch ..., not done yet" is stale (merged on main). Also line 1127-1128 "(batch 3a, tested on its branch)". Corrected: "on main since cfaab355, done-checked by [this report]" once it is saved.
- docs/project/PROJECT_PROGRESS.md:33: "tested on branch `tb2-batch3a` (not done: not reviewed, not merged, not done-checked)" and "Next: the Forth review, the merge, the done check" are stale. The review is logged (LOG.md:153) and the work is merged. Corrected: "merged on main; done checker: DONE".
- docs/project/PLAN_DRAFT.md:695, row TB2: "Status ... tested alone (batch 3a, on its branch, below)" is stale. Corrected: "batch 3a works end to end (done check <date>-tb2-batch3a-done.md, DONE on cfaab355)". That row is very long and I only read its start; check for further "on its branch" or "not started" fragments about 3a.
- Claims not shown by my run: `at: *`, delta that changes a hypothesis and `x R x` for relations other than `=` and `↔` are unsupported (documented in the docs and PROGRESS "Not yet"). `by-rewrite[ ]` and `|-` I ran only through batch-d. The "full Lean fidelity" of every `at` form is only as wide as the 17 theorems in batch-d and my 7.
- The wording "each a port of Lean's ... at h" is supported for rw, rwa, change and symm by the node-for-node comparison. For delta, only the refusal (448) is tested; where it would change a hypothesis it is 99 (unsupported). The claim should say "by-delta at a hypothesis it would change: unsupported", as the docs already do.

Verdict: DONE for the claim as scoped (the unported forms answer unsupported, never accepted); documents need the three stale-status corrections above.
