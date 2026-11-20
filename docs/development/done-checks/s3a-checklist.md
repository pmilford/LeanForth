# Acceptance checklist: slice S3a, `by-decide` (plan row S3)

Written 2026-11-19, before the code, by the implementing agent of branch `s3a-decide` (from
`tactic-batch-1`), from section 6 of the architect's word list
`.claude/work/briefs/S3-DECIDE-WORDLIST.md`; the done checker runs it again. S3a is `by-decide`, a
port of Lean 4.35.0's `decide` (`Elab/Tactic/Decide.lean`) on closed decidable facts about Nat and
Bool, with the front end's `reduceNat?` it needs, the kernel's Nat operation table shared as
`src/core/nat-ops.fs`, and `by-native-decide` as a refusal word. `G` is Gforth 1.0.0's `gforth`,
`F` its `gforth-fast`, `L` pinned Lean 4.35.0's `lean`, all absolute paths; every command runs
from the repository root under `ulimit -u 500` with stdin `/dev/null`. "Accepted" means
LeanForth's kernel checked the term the tactic built; the term is compared with pinned Lean's.

Each line: the criterion, the command, the expected result. The last column is filled in when the
command is run on the branch's final head (result and exit code).

| # | Criterion | Command | Expected | Result |
| --- | --- | --- | --- | --- |
| 1 | Group A's 16 statements accepted, terms node for node pinned Lean's, step log valid with rule `decide`; each wrong twin refused with its code, Lean's first line and detail (250 false, 251 free variables, 125 no instance, 253 failed to reduce, 90 no goal, 86 a value left over, 254 `by-native-decide`) | `GFORTH=$G python3 tests/front/tactics/decide/check.py` | exit 0 | exit 0: 12 of group A (dc-arith.lf, dc-logic.lf) accepted on decide's slice, terms node for node pinned Lean's, step logs as golden; 9 wrong twins (250 x3, 251 x2, 122, 253 x2, 90); 254 and 93 exit 2; 86 (LeanForth's own). No instance is 122, Meta's "failed to synthesize", not 125 (the elaborator's text) |
| 2 | Pinned Lean builds the same golden terms and refuses each Lean twin with that text | `LEAN=$L python3 tests/front/tactics/decide/check.py --lean` | exit 0, golden unchanged | exit 0: goal-layer.golden unchanged (this branch added 32 lines, changed none); pinned Lean prints the 9 twins' messages |
| 3 | On all of Init (the done checker's run) | `bin/leanforth check --snapshot init.lfsnap --elab-data init.elab.ndjson --steps - tests/front/tactics/decide/dc-*.lf` | each theorem "accepted; axioms: none", exit 0 | exit 0: `check.py --init .claude/work/parallel-init/init-1.lfsn .claude/work/IM/init.elab.ndjson` (dc-init.lf, dc-arith.lf, dc-logic.lf): all 16 accepted, axioms none, 50 s; dc_hyp's hypothesis is True (1 = 1 stops with 139, plan FE2) |
| 4 | The kernel is the judge: fault `fe-decide-skip-whnf` hands over the term for `2 2 + 5 =` | `python3 scripts/mutants.py --gforth $G --only fe-decide-skip-whnf` | caught: the kernel rejects | caught (exit 1); by hand the kernel answers `w_dc_add: rejected`, argument type mismatch |
| 5 | whnf and the builders against pinned Lean (folds, `Nat.zero`, the original term unfolded when no fold, exponents 256 and 257, `mkDecide`, `mkAppOptM`) | `LEAN=$L GFORTH=$G python3 tests/front/check_whnf.py` | equal, or listed gaps unsupported | exit 0 with pinned Lean (commit C2): 142 of 150 equal, the 8 listed gaps older than this branch, its 26 new cases (17 whnfD, 9 builders) all equal; 257 is in tests/front/reduce-nat.fs (Lean's warning is an error in this run); `--golden` on the final head exit 0 |
| 6 | Unit tests on both engines | `$G` and `$F` on `tests/front/tactics/decide/test.fs`, `tests/front/reduce-nat.fs`, `tests/core/nat-ops.fs`, `tests/front/tactic-lib.fs`, `tests/front/whnf.fs` | exit 0 each | exit 0 on gforth and gforth-fast, with tests/core/reduce-nat.fs, tests/core/defeq.fs, tests/front/defeq.fs, infer.fs and tactics/apply/test.fs too |
| 7 | Every outcome: exhausted (`--elab-fuel 50`: exit 3, never accepted); unsupported (an exponent of 300: exit 2, error 93); a goal with a metavariable (252, unit test); deterministic over two runs and `--jobs 2` | within 1 and 6 | as stated | as stated (check.py's own check; decide's test.fs: 252, a let variable unsupported, an exponent of 300 unsupported) |
| 8 | Planted faults of the new words all caught | `python3 scripts/mutants.py --check`; `--only` the S3a ids (`tests/mutants/faults.d/s3a.toml`, `decide.toml`) | every one caught | `--check`: 0 stale; 46 run, 46 caught (s3a.toml 17, decide.toml 9, the 20 re-targeted or moved with their lines); dq-nat-zero-never, run with LEAN, caught |
| 9 | No never-run block on a line the branch added or changed | `make cover-changed BASE=tactic-batch-1 JOBS=4 GFORTH=$G` | exit 0 | exit 0: every block on a changed line ran (18 files, 76 unit test files, 77 s) |
| 10 | Kernel and earlier results unchanged after the nat-ops move | `make test-kernel-reduction GFORTH=$G`; the full tier `make tier GFORTH=$G LEAN=$L` (the coordinator) | exit 0 | make test-kernel-reduction exit 0; tests/core/check-block.fs exit 0; the full tier is the coordinator's |
| 11 | Duplicates do not rise (the kernel's table moved, three at-least copies and apply's synth copy gone); style ratchet | `python3 scripts/check-duplicates.py`; `python3 scripts/forth-metrics.py`; `python3 scripts/check-forth-quality.py` | exit 0 | exit 0: 205 groups, none new or grown; the ratchet holds (decide.fs's two registration globals in the baseline) |
| 12 | Documentation | `make check-docs`; `grep -n by-decide docs/user/LANGUAGE_REFERENCE.md` | `by-decide` and `by-native-decide` in the language reference (sentences, the Lean equivalent, two checked samples); codes in LEANFORTH_WORDS; TACTIC_PLUGINS; FORTH_LIBRARY's nat-ops profile | exit 0; D.7 rewritten; codes 122 and 250-254 in LEANFORTH_WORDS; TACTIC_PLUGINS D and E; FORTH_LIBRARY's nat-ops profile; FRONT_LAYERS |
| 13 | Whole-repository checks | `scripts/pre-tier.sh` | all passed | |
