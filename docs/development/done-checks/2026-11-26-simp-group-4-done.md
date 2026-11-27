# Done check: simp group 4, plain `by-simp` (2026-11-26)

Independent done checker (Sonnet), on main 6febe59b. Its report follows unchanged except for the scratch path.

**Coordinator's resolution (2026-11-26, 22:58).** The checker's verdict was MIXED for one behaviour (row 2f) and for stale documents.

- Row 2f is a property of the small test slice, not of `by-simp`. The slice `tests/front/simp-slice.ndjson` holds 194 default lemmas and leaves 4,203 out; a goal or hypothesis that is not closed outright (`a = b`) meets a left-out candidate and answers 99, as the reference's list of unsupported cases says ("a left-out lemma reached in candidate order"). I re-ran the checker's own files against all of Init (`bin/leanforth check --snapshot .claude/work/parallel-init/init-1.lfsn --elab-data INIT-4.1-DATA FILE.lf`, the data written by `ELAB_FORMAT=4.1 scripts/export-elab.sh`): h4, h4b, h7, h8 and h10 are each accepted (exit 0, "accepted (checked in this run, uses results from the snapshot)"), and the wrong goals bad1 (`a + 1 = a`) and bad3 (`a + 1 = b`) are refused with Lean's own error 89 "unsolved goals" (exit 4); bad2 (`2 + 3 = 6`) stays 99 (a guarded simproc). The reference now says that the slice answers 99 where Init's full data does not.
- The counts: 385 written and 255 not is the figure after the review's fix round (the harness now also refuses a statement whose printed text Lean elaborates differently); 393 and 247 were pass 3's. The reference is corrected; the measurement README keeps both, dated.
- The stale status lines in PROJECT_PROGRESS.md and the plan are rewritten in the commit that adds this file.

With that, the stage is **done** for what the group claims: plain `by-simp`, `by-simp[ ]` and `at[ ]` with Init's default set on the supported shapes, 57 of Init's 640 one-line simp theorems with pinned Lean's term and none with another (`make reference-simp-init`, run by the checker itself: exit 0). Forth review and re-check: [2026-11-26-simp-group-4.md](../forth-reviews/2026-11-26-simp-group-4.md). What is left is plan row 9.4.8z14.

---

DONE CHECK: simp group 4

**Verdict: MIXED. Stage reached: works end to end for the supported shapes. Not "done".** Plain `by-simp`, the `by-simp[ ]` forms and `at[ ]` work on my own `.lf` files, and the Lean twins agree. One shape the reference lists as supported fails, and several documents give wrong numbers or stale status. I did not check the CI, review-gate or coverage parts of "done".

Entry point for every `.lf` run, from the repository root under `ulimit -u 500`:
`bin/leanforth check --env tests/front/simp-slice.ndjson --elab-data tests/front/simp-slice.elab.ndjson FILE.lf`
My files are in `the checker's scratch directory `.

| # | Claim and input | Exit | Decisive output |
|---|---|---|---|
| 1 | A user can close goals with `by-simp` (`ok1.lf`: `a+0=a`, `2+3=5`, `7*6+2=44`, `if True then a else b = a`, `¬¬(a=a)`, `0+a=a`) | 0 | t1 to t6 each "accepted; axioms: propext", plus "2033 declarations: 2033 accepted" |
| 2a | `by-simp[ ' h ]` (`h1`) | 0 | `u1: accepted` |
| 2b | `by-simp[ ' h <- ]` (`h2`) | 0 | `u2: accepted` |
| 2c | `by-simp[ ' Nat.add_zero ]` (`h6`, goal `a+0=a`) | 0 | `u6: accepted` |
| 2d | `by-simp at[ h ]` where h becomes `True` (`h9`: `h : ¬(a=a)`, goal False) | 0 | `u9: accepted` |
| 2e | `by-simp[ ' h1 ] at[ h2 ]` (`h5`) | 0 | `u5: accepted; axioms: none` |
| 2f | `by-simp at[ h ]` where h becomes a non-trivial hypothesis (`h4`, `h4b`, `h7`, `h8`, `h10`; e.g. `h : a+0=b`) | 2 | error 99 at `by-simp`, goal `a = b`, not accepted |
| 3 | Wrong or unprovable goals (`bad1`, `bad2`, `bad3`) | 2 | `a+1=a`, `2+3=6` and `a+1=b` each give error 99, "the LeanForth text was not checked" |
| 3 | Shapes the reference says are unsupported | 2 | `uns1` (`x+1=0`, `reduceCtorEq`) and `uns3` (`' Nat.add_zero <-`) each give error 99 |
| 4 | Pinned Lean on 8 twins (`tw.lean`: `simp`, `simp [h]`, `simp [← h]`, `simp [h1] at h2`, `simp at h`, and a wrong one) | 1 | Only the deliberately wrong `a+1=a` fails ("unsolved goals ⊢ False"); the other 7 are accepted |
| 5 | The "elaboration data:" line | 0 | `194 default simp lemmas, 4203 left out, 207 simprocs, 2 definitions to unfold` |
| 6 | Bad data: `del2.ndjson` is `simp-slice.elab.ndjson` with one `simp_lemma` line deleted | 4 | "error 20: records differ in number from the header; the LeanForth text was not checked" |
| 7 | `make reference-simp-init` with `INIT_EXPORT=.claude/work/IM/init.ndjson`, `JOBS=2`, `nice -n 10`, 2m40s | 0 | "57 of 640 accepted with terms equal to pinned Lean's re-run node for node (L = 636); 385 written, 255 cannot be written"; "0 accepted with a different term; 0 accepted where Lean's re-run fails" |

Notes on the table:
- Claim 1: all six statements could be written.
- Row 2f: Lean's `simp at h` gives `h : a = b` here, and the Lean twin of `u1` (`simp [h]`) is accepted. This is the "not accepted" failure I found. The reference lists `at[ h ]` as supported and names no such gap.
- Rows 3 and 2f: every wrong or unsupported goal answered 99 and exit 2. I saw none answered with Lean's own "simp made no progress" or unsolved-goal error. All are "not accepted", so claim 3 holds, but the refusal is a not-supported-yet answer, not a diagnosis.
- Row 6: my first deletion hit the header line (exit 4, error 5). The second is the real record deletion above. I did not try a tamper that keeps the count consistent.
- Row 7: K = 57 and the zero-wrong-term line reproduce the README. The "written" count (385, so 255 cannot be written) differs from the README and the reference, which say 393 and 247.
- `uns2` (`by-simp[ ' h <- ]` with a hypothesis `h`) is accepted. That is correct, since `<-` on a hypothesis is supported; only a theorem with `<-` is unsupported.

**Docs findings (the stale items are in the "not reviewed, not merged" family you asked about):**
- `docs/project/PROJECT_PROGRESS.md:32` says simp group 4 is "written and tested on its branch, not reviewed, not merged". It is on main and Forth-reviewed. The review is `docs/development/forth-reviews/2026-11-26-simp-group-4.md`, and the plan names its fix branch `simp-group-4-fix`.
- `docs/project/PLAN_DRAFT.md:849` (9.4.8z10) says "Not started" for simp group 4. Line 853 (9.4.8z14) says "Not started", and its leftovers are unfinished. The FE9 row at line 756 has a status of 02:52 that predates group 4.
- `docs/user/LANGUAGE_REFERENCE.md:3209` and `docs/development/measurements/simp-init-2026-11-26/README.md:217` say "393 can be written" and "247 cannot be written". The run printed 385 and 255. Corrected wording: "385 can be written". Check whether the README number is from an older pass.
- `docs/user/LANGUAGE_REFERENCE.md:3167-3171` (D.12): add that `at[ h ]` where `h` simplifies to something other than `True` or `False` is not supported yet (error 99, exit 2).
- `docs/user/LANGUAGE_REFERENCE.md:2000` also says `by-simp` is "Lean's default simp set", but it is only a subset (see the 99 list at D.12). The wording "closes goals with Lean's default simp set" overstates; say "with the default simp set read from the data, for the shapes not listed as unsupported".
- The README line 17 says "there is no make target yet", and the harness section further down says there is one. This is minor.

**Not checked:**
- Both CI jobs, Gforth 0.7.3, `make check`, coverage, and the Forth review's blocking findings (only that the review file exists).
- The Mathlib route and the speed claims.
- The `at[ * ]` form on my own files (the `v4` run accepted `by-simp[ ' h ] at[ * ]` incidentally).
- `by-simp[ ' h ]` with several rules or a term item.
- Whether each accepted term matches Lean's node for node on my own files. Only the harness checks that, over Init.
