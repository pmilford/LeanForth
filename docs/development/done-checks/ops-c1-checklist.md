# Acceptance checklist: slice S3a-ops, step C1, reduceDT's unfoldDefinition? (plan row S3)

Written 2026-11-20 by the implementing agent of branch `ops-c1` (from main 84d614a5), from the C1
lines of sections 3 and 4 of the architect's word list `.claude/work/briefs/OPS-WORDLIST.md`; the
done checker runs it again. C1 makes the discrimination-tree keys (`src/front/discr-keys.fs`) unfold
definitions as Lean 4.35.0's DiscrTree `reduceDT` does (Meta/DiscrTree/Main.lean:203-245): whnfCore,
`unfoldDefinition?` (`lf-meta-unfold`, `src/front/whnf.fs`), strict eta, and at a root no unfolding
into a bad key (`reduceUntilBadKey`, `isBadKey`). Untrusted front-end code: only the kernel's check of
the finished term accepts a theorem. `G` is Gforth 1.0.0's `gforth`, `F` its `gforth-fast`, `L`
pinned Lean 4.35.0's `lean`, all absolute paths; `INIT` is
`.claude/work/parallel-init/init-1.lfsn` and `INIT.elab` `.claude/work/IM/init.elab.ndjson` of the
main checkout; every command runs from the repository root under `ulimit -u 500` with stdin
`/dev/null`. "Accepted" means LeanForth's kernel checked the term `by-decide` built; on decide's
slice the term is also compared node for node with pinned Lean's. Every line is a make target the
tier runs or one command that finishes in under two minutes.

| # | Criterion | Command | Expected | Result |
| --- | --- | --- | --- | --- |
| 1 | The demo file works for a user on all of Init | `bin/leanforth check --snapshot INIT --elab-data INIT.elab --steps - tests/front/tactics/decide/dc-ops.lf` | exit 0; each of its 10 theorems "accepted; axioms: none"; step log rule `decide` | exit 0 (34 s): d_mul, d_pythag, d_gauss, d_gt, d_ge, d_ne, d_compare, d_leap, d_perfect, d_mul_big accepted, axioms none; 10 steps with `"tactic":"decide"` |
| 2 | Slice theorems node for node pinned Lean's, step logs as golden; wrong twins 250 with Lean's text | `GFORTH=$G python3 tests/front/tactics/decide/check.py` (target `test-tactic-decide-e2e`) | exit 0 | exit 0 (30 s): 3 files accepted (dc-ops.lf's 10 new), terms equal pinned Lean's, step logs as golden (20 lines added, none changed); 13 wrong twins refused (new: `6 * 7 = 43`, `10 > 20`, `3 ≠ 3`, `10 ≥ 11`, error 250 with Lean's text); 2 not supported (exit 2) |
| 3 | Init's files accepted, Init's wrong twins refused, `∣` never accepted | `GFORTH=$G python3 tests/front/tactics/decide/check.py --init INIT INIT.elab` | exit 0 | exit 0 (72 s): 31 theorems of 5 files accepted, axioms none (dc-ops-init.lf: d_divmod, d_mersenne, d_euler, d_taxicab, d_pow_cmp); `2 ^ 32 + 1 = 641 * 6700419` and `17 / 5 = 3 ∧ 17 % 5 = 3` refused, 250, Lean's text; `3 12 Dvd.dvd` error 93, exit 2 |
| 4 | Pinned Lean proves every Lean twin, writes the same golden, refuses the wrong twins with that text | `LEAN=$L python3 tests/front/tactics/decide/check.py --lean` | exit 0, golden only grown | exit 0: goal-layer.golden grew by 20 lines (d_mul ... d_mul_big), none changed; pinned Lean prints the 15 wrong twins' messages (6 new) |
| 5 | Instance keys and searches match Lean on all of Init | `make reference-synth GFORTH=$G LEAN=$L` | exit 0; 0 refused; unverified 538 → the measured remainder; candidates in Lean's order on 16 problems | exit 0 (44 s): 2,938 checked, 2,508 ok, 430 unsupported (538 on main 84d614a5), 0 refused; getInstances 16 of 16 in Lean's order, new: `Decidable (20 > 10)` [instDecidableRelLt, Std.instDecidableLT, Nat.decLt], `HMul ?a ?b ?c` [instHMul, Vector.instHMul, Lean.Omega.LinearCombo.instHMulInt, Lean.Omega.IntList.instHMulInt], `Mul ?a` (24 candidates); searches 24 of 30 and the 6 known gaps, unchanged. The 430, not traced one by one: 177 have a lambda in their type after the telescope, where ignoreArg's tests need inferType of a lambda-headed application or of nested lambdas (`src/front/infer.fs`, plan FE1c; traced for Nat.decidable_dvd); Lean.TSyntax's coercions meet a string literal's key (S5) in a syntax kind's name; the rest (LawfulFunctor-like classes and others) wait for a trace |
| 6 | Unit tests on both engines | `make test-instances GFORTH=$G`, the same with `GFORTH=$F`; `$G` and `$F tests/front/tactics/decide/test.fs` | exit 0 each | exit 0 each: instances.fs (GE.ge keyed as LE.le, Decidable (20 ≥ 10) as Decidable (10 ≤ 20), outParam twice unfolded, a root's partial GE.ge kept and below the root other, an abbreviation unfolded below the root, id left at reducible and unfolded at default, Decidable.isTrue keyed as Decidable.intro, a matcher at default stuck as Lean's), discr-tree, instances-bad, instances-late, instances-odd (114 stays 114), synth.fs; decide's test.fs (Lean.Omega.IntList.instHMulInt verified, `6 7 * 42 =`, `20 10 GT.gt`, `3 4 Ne` accepted through text) |
| 7 | Every outcome of the changed words | within 6 (instances.fs) and `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson --elab-fuel 50 tests/front/tactics/decide/dc-ops.lf` | unfoldDefinition?'s unsupported (no smart-unfolding facts), exhausted (each budget from 0) and full (each heap request and each term refused in turn, tests/support/meta-sweeps.fs) passed on, never another answer; `--elab-fuel 50`: exit 3, nothing accepted | as expected: the sweeps in instances.fs pass; `--elab-fuel 50` exit 3, 0 accepted |
| 8 | The kernel is the judge on the new statements | `python3 scripts/mutants.py --gforth $G --only fe-decide-skip-whnf-mul` | caught: the kernel rejects `6 * 7 = 43` | caught (exit 1, 9.9 s) |
| 9 | Planted faults | `python3 scripts/mutants.py --check`; `python3 scripts/mutants.py --gforth $G --only dk-unfold-never,dk-root-ignores-badkey,dk-unfold-once,fe-decide-skip-whnf-mul` | 0 stale; each caught | `--check`: 3,135 entries, 0 stale; 4 run, 4 caught; decide.toml's 9 faults also caught on the larger slice |
| 10 | No never-run block on a changed line | `make cover-changed BASE=main JOBS=3 GFORTH=$G` | exit 0 | exit 0 (17 s): discr-keys.fs, 10 changed code lines, 24 blocks, every one ran (19 unit test files) |
| 11 | Style | `python3 scripts/forth-metrics.py src/front/discr-keys.fs` | no word over five lines, every word a stack comment; shuffles within the ratchet | 101 words, 68 of 1-2 lines, 33 of 3-5, none longer; no missing stack comment; deep shuffles 13 (baseline 14), return-stack operations 17 as on main |
| 12 | Docs and plan | `make check-docs`; `python3 scripts/check-progress.py` | exit 0 | see 13 (both are in pre-tier); LANGUAGE_REFERENCE's by-decide section (three forms, a sample from dc-ops.lf, "checked by LeanForth's kernel", the `6 7 * 42 =` note removed), PLAN_DRAFT S2 and S3 rows, S1_INTERFACE §9's counts |
| 13 | Whole-repository checks | `GFORTH=$G LEAN=$L scripts/pre-tier.sh` | all passed | exit 0 on 5774af21, all 17 checks passed (the first run failed the style ratchet, discr-keys.fs shuffles 15 > 14, fixed in 5774af21: 13); rows 2, 3, 4 and 5 run again on 5774af21, the same results |
| 14 | The tier | `make tier GFORTH=$G LEAN=$L` | all passed | the coordinator's |

The slice: `tests/front/decide-slice.roots` gains GT.gt, GE.ge, Ne (already in its closure) and the
two HMul candidates Lean tries for a numeral `*` (`Lean.Omega.IntList.instHMulInt`, then
`Vector.instHMul` for `HMul Nat ?b ?c`, from pinned Lean's `trace.Meta.synthInstance`): 870 → 1,027
declarations, 44,420 → 65,538 lines (2.4 → 3.5 MB), one check of a file 8.0 → 10.7 s; cut by
`scripts/export-slice.py` from Init's pinned export, renumbered by `scripts/ndjson-reexport.sh` (a
fixed point), its manifest by `scripts/export_manifest.py`, its data by `scripts/export-elab.sh`.
