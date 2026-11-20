# Acceptance checklist: tactic batch 1 (plan row TB1)

Written 2026-11-19, before the code, by the implementing agent of branch `tactic-batch-1`; the
done checker runs it again. The batch: `by-left`, `by-right`, `by-exfalso`, `by-intros`,
`by-clear`, each a port of Lean 4.35.0's tactic of that name (owner, 2026-11-19, "Tactics in
batches" in [OWNER_DECISIONS.md](../../project/OWNER_DECISIONS.md)); the architect's word list
is `.claude/work/briefs/TACTIC-BATCH1-WORDLIST.md`. `G` is Gforth 1.0.0's `gforth`, `F` its
`gforth-fast`, `L` pinned Lean 4.35.0's `lean`, all absolute paths; every command runs from the
repository root under `ulimit -u 500` with stdin `/dev/null`. "Accepted" means LeanForth's kernel
checked the term the tactic built; the term is compared with the one pinned Lean builds.

Each line: the criterion, the command, the expected result. The last column is filled in when the
command is run on the branch's final head (result and exit code).

## Per tactic, end to end against pinned Lean

| # | Criterion | Command | Expected | Result |
| --- | --- | --- | --- | --- |
| 1 | `by-left`: right proofs accepted, terms node for node pinned Lean's, step logs as golden; wrong twins refused with Lean's message (385, 386 and apply's 380 with "the term") | `GFORTH=$G python3 tests/front/tactics/left/check.py` | exit 0, "left: N files accepted … wrong twins refused with Lean's messages" | exit 0: 2 files accepted, terms node for node pinned Lean's, step logs as golden; 3 wrong twins (386, 385, 380 'the term') |
| 2 | `by-left`: pinned Lean builds the golden terms and prints the wrong twins' messages | `LEAN=$L python3 tests/front/tactics/left/check.py --lean` | exit 0, golden unchanged | exit 0: golden unchanged, pinned Lean prints the 3 wrong twins' messages |
| 3 | `by-right`: as 1 (387, 388) | `GFORTH=$G python3 tests/front/tactics/right/check.py` | exit 0 | exit 0: 2 files accepted (Or.inr; Nat.le.step then refl); 2 wrong twins (387, 388) |
| 4 | `by-right`: as 2 | `LEAN=$L python3 tests/front/tactics/right/check.py --lean` | exit 0 | exit 0 |
| 5 | `by-exfalso`: as 1 (exact's 96 after exfalso) | `GFORTH=$G python3 tests/front/tactics/exfalso/check.py` | exit 0 | exit 0: 3 files accepted (the tag kept under apply And.intro); 1 wrong twin (96) |
| 6 | `by-exfalso`: as 2 | `LEAN=$L python3 tests/front/tactics/exfalso/check.py --lean` | exit 0 | exit 0 |
| 7 | `by-intros`: as 1 (assumption's 381 after intros on `¬a = b`); `by-intro` and `by-intros` on implicit and strict-implicit binders give pinned Lean's term and binder kinds | `GFORTH=$G python3 tests/front/tactics/intros/check.py` | exit 0 | exit 0: 2 files accepted; 1 wrong twin (381); 3 goals with implicit and strict-implicit binders introduced as pinned Lean's, terms and binder kinds (in_implicit, in_strict, is_implicit) |
| 8 | `by-intros`: as 2 | `LEAN=$L python3 tests/front/tactics/intros/check.py --lean` | exit 0 | exit 0 |
| 9 | `by-clear`: as 1 (441 depends, 442 target, 389 not a variable) | `GFORTH=$G python3 tests/front/tactics/clear/check.py` | exit 0 | exit 0: 2 files accepted; 3 wrong twins (441, 442, 389) |
| 10 | `by-clear`: as 2 | `LEAN=$L python3 tests/front/tactics/clear/check.py --lean` | exit 0 | exit 0 |
| 11 | Each step writes a step-log line (schema-valid, in NAME/steps.golden) | part of 1, 3, 5, 7, 9 (`check_log`, `check_steps`) | as there | exit 0 (within 1, 3, 5, 7, 9) |

## Unit tests on both engines

| # | Criterion | Command | Expected | Result |
| --- | --- | --- | --- | --- |
| 12 | The shared library words (`lf-tac-ex`, `lf-match-const-induct`, `lf-lift-meta-tactic1`, `lf-goals1`, `lf-with-cells`) | `$G tests/front/tactic-lib.fs` and `$F tests/front/tactic-lib.fs` | exit 0, "all tests passed" | exit 0 on gforth and gforth-fast |
| 13 | `lf-goal-nth-constructor` (0, 1, 3 constructors, a pi goal, an assigned goal, the load abort) | `$G tests/front/tactics/left/test.fs`, `$F` the same | exit 0 | exit 0 on gforth and gforth-fast |
| 14 | right's record | `$G tests/front/tactics/right/test.fs`, `$F` the same | exit 0 | exit 0 on gforth and gforth-fast |
| 15 | `lf-goal-exfalso` (Sort 0, Sort 1, Sort u; tag and context kept) | `$G tests/front/tactics/exfalso/test.fs`, `$F` the same | exit 0 | exit 0 on gforth and gforth-fast |
| 16 | `lf-intros-size`, `lf-goal-intros`, `lf-goal-intro-n`'s names 0 and kinds 0 (implicit and strict accepted, instance, unknown and let 99) | `$G tests/front/tactics/intros/test.fs`, `$F` the same | exit 0 | exit 0 on gforth and gforth-fast |
| 17 | `lf-goal-clear!` (each of Lean's three messages, the assigned goal) and getFVarId | `$G tests/front/tactics/clear/test.fs`, `$F` the same | exit 0 | exit 0 on gforth and gforth-fast |

## Faults, coverage, existing results

| # | Criterion | Command | Expected | Result |
| --- | --- | --- | --- | --- |
| 18 | Every planted fault of the batch caught, the table well formed and no fault changed without its id named | `python3 scripts/mutants.py --check` then `python3 scripts/mutants.py --gforth $G --only IDS` (the batch's ids) | exit 0, every one caught | --check exit 0 (2964 entries, 0 stale, 0 unnamed); --only the batch's 48 ids: exit 0, 46 caught, 2 survived as listed (known equivalent: tb1-get-fvar-postponing, tb1-clear-self-dependent) |
| 19 | No new never-run block in a new or changed file (no coverage debt) | `make cover FILE=F GFORTH=$G JOBS=3` for each new or changed `src/` file | each file's never-run count at or below its baseline | make cover with the batch's unit tests (TESTS=...): goal.fs, tactic-core.fs, tactic-msg.fs, meta-must.fs, assumption.fs, elim.fs and every plug-in 0 never run; constructor.fs 1, goals.fs 6, lctx-views.fs 8, each its baseline's older lines; the tier's check is now row 20 |
| 20 | Every line the branch added or changed in `src/` run by a unit test (the tier's check since the owner's decision of 2026-11-19, replacing the coverage-focus ratchet) | `make cover-changed BASE=main GFORTH=$G` (run as branch `branch-coverage`'s `scripts/coverage.py --changed main` until it reaches main) | exit 0, every block on a changed line ran | exit 0: every block on a changed line ran (29 files, 46 unit test files; branch-coverage's scripts/coverage.py at acf7f11a, run on the head as make cover-changed will once it is on main) |
| 21 | Existing tactics unchanged (S1/S2 goldens, earlier plug-ins) | `GFORTH=$G python3 tests/front/check_s2.py`, `--lean`; `check_tactics.py`, `--lean`; each `tests/front/tactics/*/check.py`, plain and `--lean` | exit 0 each | exit 0 each: check_s2 (12 files, 42 lines, 22 wrong proofs) and --lean; check_tactics and --lean; apply, assumption, constructor, left, right, exfalso, intros and clear check.py, plain and --lean |
| 22 | The showcase, with `zero_add_ex`'s new Lean twin | `make test-showcase GFORTH=$G` | exit 0 | exit 0 (check_showcase: all tests passed) |
| 23 | Duplicates do not rise; style ratchet holds | `python3 scripts/check-duplicates.py`; `python3 scripts/forth-metrics.py` on each changed Forth file; `python3 scripts/check-forth-quality.py` | exit 0 | duplicates exit 0 (205 groups, none new or grown); check-forth-quality exit 0 (ratchet holds: baseline entries added for the 5 plug-ins, goal.fs shuffles 2 -> 3, in this batch's reviewed commits) |
| 24 | Whole-repository cheap checks | `GFORTH=$G LEAN=$L scripts/pre-tier.sh` | "pre-tier: all checks passed" | exit 0: pre-tier: all checks passed |

## Documentation

| # | Criterion | Command | Expected | Result |
| --- | --- | --- | --- | --- |
| 25 | A language-reference entry per word, in the form of the existing tactic entries (plain sentences, the Lean equivalent, two sample uses from checked test files) | `grep -n -e 'by-left' -e 'by-right' -e 'by-exfalso' -e 'by-intros' -e 'by-clear' docs/user/LANGUAGE_REFERENCE.md` | a row and a paragraph each | a row and a paragraph each (section D, 'Left, right, exfalso, intros, clear', and D.1) |
| 26 | The words and codes in LEANFORTH_WORDS.md, the library words in TACTIC_PLUGINS.md appendix D, the schema's word list | `make check-docs GFORTH=$G`; `GFORTH=$G python3 tests/front/check_registry.py` | exit 0 | make check-docs exit 0; check_registry exit 0 (248 lines as golden); check_author exit 0 (catalogue and LEANFORTH_WORDS.md agree) |
