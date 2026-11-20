# Done check: S3a-ops C2-C4, Lean's symbols as words (2026-11-20)
Checker: done-checker (independent); main a35f8d00, ulimit -u 500, nice -n 10, stdin /dev/null, one command at a time, CPU mode day (make JOBS=2).

Verdict: MIXED -> DONE for `- / % ^ < > ≥ ≤ ≠ ¬ ∧ ∨ ↔` with by-decide on Init's snapshot; NOT DONE for `∣` (error 93 with by-decide, documented). Row 14 (make tier) not run (forbidden).
Claim: "A user can write the symbols in a .lf theorem, each also typed on a plain keyboard, each meaning what it means in Lean 4.35.0; LeanForth's kernel checks it; a false one is refused with Lean's message." Stage: works end to end on Init's snapshot for all but `∣`.

| # | Command | Exit / seen | Result |
| 1 | check --snapshot INIT --elab-data INIT.elab --steps - dc-symbols.lf, dc-symbols-init.lf | 0, 0; 9 (sy_mul..sy_iff) and 5 (sy_divmod, sy_mersenne, sy_euler, sy_taxicab, sy_pow_cmp) "checked in this run; axioms: none" (13 s each) | PASS |
| 2 | same on dc-ascii.lf, dc-ascii-init.lf | 0, 0; 9 as_* and 5 as_* accepted, axioms none | PASS |
| 3 | make reference-decide-init JOBS=2 GFORTH=G LEAN=L | 0 (146 s); "116 theorems of 11 files accepted ... axioms none, terms node for node pinned Lean's (each ASCII file's its symbol file's); 4 wrong twins refused with Lean's messages; 2 not supported yet (exit 2); 5 #check lines as pinned Lean's" | PASS |
| 4 | GFORTH=G check.py (decide) | 0 (45 s); 6 files accepted, terms equal Lean's, 19 wrong twins refused, 2 not supported | PASS |
| 5 | LEAN=L check.py --lean | 0; golden reproduced, Lean prints the 23 wrong twins' messages | PASS |
| 6 | check_front.py | 0; 18 statements read as pinned Lean expands them | PASS |
| 7 | G and gforth-fast on front.fs, text-run.fs, author.fs, decide/test.fs | 0 on all 8 runs (text-run.fs prints nothing, exit 0) | PASS |
| 8 | check_registry.py | 0; 275 lines as golden, 6 registrations refused | PASS |
| 9 | mutants.py --check; --only the 9 named plus the review's 8 | 0, 3191 entries 0 stale; 17 run, 17 caught | PASS |
| 10 | make cover-changed BASE=main | 0 but "nothing to check" (main is merged: empty). With BASE=8b6272c1: 0, 80 unit files, every block on a changed line ran (76 s) | PASS (base must be 8b6272c1) |
| 11 | check-duplicates --new-words --base 8b6272c1; forth-metrics (4 files); check-forth-quality.py | 0 each; no new copy; ratchet holds, review log covers changes | PASS |
| 12 | make check-docs; check-progress.py | 0; 0 | PASS |
| 13 | scripts/pre-tier.sh | 0 (58 s), "all checks passed" | PASS |
| 14 | make tier | not run (wide suite forbidden) | NOT RUN |
| 15 | test_mathlib_slice.py, test_test_classes.py, test_tested_tree.py, make check-test-classes | 0 each; "51 unit and 95 end-to-end targets" | PASS |

## My own theorems (sym-done/, written from LANGUAGE_REFERENCE.md lines 248-303 and D.7 only)
Command: bin/leanforth check --snapshot .claude/work/parallel-init/init-1.lfsn --elab-data .claude/work/IM/init.elab.ndjson --steps - F.lf
a.lf (symbols): n_pow `2 10 ^ 1024 =`; n_sub `10 20 - 0 =`; n_mod `100 7 % 2 =  100 7 / 14 =  ∧`; n_cmp `20 10 >  3 4 ≠  ∧  7 8 =  ¬  ∧`; n_or `3 2 ^ 9 =  9 3 <  ∨  5 5 ≥  ∧`, each `by-decide`. Exit 0; all five "accepted (checked in this run); axioms: none".
b.lf (ASCII): the same with `/\` for ∧, `Ne` for ≠, `Not` for ¬, `\/` for ∨, `>=` for ≥. Exit 0; all five accepted, axioms none.
c1.lf (symbols) `5 3 >  1 1 ≠  ∧`: exit 4; "error 250 at 4:3 (token `by-decide`): Tactic `decide` proved that the proposition / 5 > 3 ∧ 1 ≠ 1 / is false".
c2.lf (ASCII) `7 3 % 2 =  1 1 Ne  /\`: exit 4; error 250, "... proposition 7 % 3 = 2 ∧ 1 ≠ 1 is false" (printed with symbols).
Lean twins (pinned 4.35.0 `lean`, t.lean, f.lean): n_pow, n_mod, n_cmp, n_or by `decide`: exit 0, no output (grouping parenthesised as postfix gives it). f.lean `theorem f_sym : 5 > 3 ∧ 1 ≠ 1 := by decide`: exit 1, "Tactic `decide` proved that the proposition / 5 > 3 ∧ 1 ≠ 1 / is false": identical text.

## Three newcomer mistakes (each exit != 0, nothing accepted)
1. `2^3 8 =` : exit 4, "error 35 at 2:3 (token `2^3`): not a LeanForth word or number: numbers are plain decimals of at most 9 digits". Understandable; does not say "put spaces round ^".
2. Infix `2 ^ 3 = 8`: exit 4, "error 3 at 2:5 (token `^`): missing value: this word would use the stack below its binder or declaration". Correct but a newcomer will not see "write the operands first" from it (docs say postfix, line 236).
3. `3 12 ∣` with by-decide: exit 2, "error 93 ... not supported yet: a type inference, reduction or let binder the tactic needs (FE1c) / ⊢ 3 ∣ 12". Matches LANGUAGE_REFERENCE.md:1504-1507 (documented answer; no verdict, no crash).

## Limits a user meets
- Only Init's snapshot was used (no Mathlib). The CLI prints "development and research mode: a final run re-checks everything from the export ... only its results support a claim"; my results are snapshot-mode, with the 59349 Init declarations taken from the snapshot, not re-checked.
- Init's snapshot contains one sorry-dependent declaration ("1 NOT PROVED"); my theorems depend on no axiom.
- `∣` is not usable with by-decide (93); `3 12 ∣ #check` works (reference row 3, not run by me separately).
- `^` and `/` on numerals need all of Init (dc-symbols-init), not decide's slice; `2 ^ 300` is 93.
- Statements closed only (no variables, 251). The first error ends a file, so each false theorem needs its own file.
- Postfix order: operators after operands; no infix.

## Wording problems (not fixed)
- docs/user/examples/decide-showcase.txt:25-26: "(the symbols > ≥ ≠ ∧ are not LeanForth words yet, so the page writes Lean's names for them: GT.gt, GE.ge, Ne, And)" is false now: they are words (LANGUAGE_REFERENCE.md:261-265). Suggest "(the symbols > ≥ ≠ ∧ are LeanForth words; this page keeps Lean's names GT.gt, GE.ge, Ne, And, which build the same terms)". The page's title line 1 ("twenty-two theorems") not checked.
- Checklist row 10 (ops-symbols-checklist.md:34) names BASE=main, which does nothing on main; say BASE=8b6272c1. Row 14 is the coordinator's and unfilled; do not cite this report for the tier.
- LANGUAGE_REFERENCE.md:1436-1437 "work as in Lean" is accurate for the listed words (∣ excluded); the task's claim sentence, which includes `∣`, overstates: `∣` is a word and `#check` prints, but no theorem with it is checked yet.
- LANGUAGE_REFERENCE.md:1390-ish earlier "proved by by-decide" is not present in D.7 now (it says "checked by LeanForth's kernel"): fine.

## Added by the coordinator (2026-11-20)

- The verdict as recorded: the symbol words are DONE for `+ - * / % ^ = ≠ < > ≤ ≥ ¬ ∧ ∨ ↔` and their typed
  spellings. For `∣` the WORD is done (it builds Lean's term: `n m ∣` and `i j ∣` are among the 116 theorems
  `make reference-decide-init` compares node for node with pinned Lean, and the independent review's probes p10,
  p35 and p42), but no theorem about divisibility can yet be closed by `by-decide` (error 93, plan FE1c), as the
  language reference says. The README and the plan say it the same way.
- Row 14, the tier: `make tier` exit 0 on the branch's final head 54dc548d (cover-changed, make test, make
  test-unit on gforth-fast, check-rest, 22 planted faults, all caught); `scripts/push.sh` recorded the push of
  a35f8d00 in docs/development/ci-results.log.
- The wording problems: the showcase page was regenerated the same morning (symbols, typed ASCII and powers) and
  no longer says the symbols are missing; checklist row 10 now names the branch's base.
- The two newcomer messages the checker found unhelpful (a symbol glued to a number, error 35; infix order,
  error 3) are plan 9.4.8l (BD).

