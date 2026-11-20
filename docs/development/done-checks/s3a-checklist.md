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
| 1 | Group A's 16 statements accepted, terms node for node pinned Lean's, step log valid with rule `decide`; each wrong twin refused with its code, Lean's first line and detail (250 false, 251 free variables, 125 no instance, 253 failed to reduce, 90 no goal, 86 a value left over, 254 `by-native-decide`) | `GFORTH=$G python3 tests/front/tactics/decide/check.py` | exit 0 | |
| 2 | Pinned Lean builds the same golden terms and refuses each Lean twin with that text | `LEAN=$L python3 tests/front/tactics/decide/check.py --lean` | exit 0, golden unchanged | |
| 3 | On all of Init (the done checker's run) | `bin/leanforth check --snapshot init.lfsnap --elab-data init.elab.ndjson --steps - tests/front/tactics/decide/dc-*.lf` | each theorem "accepted; axioms: none", exit 0 | |
| 4 | The kernel is the judge: fault `fe-decide-skip-whnf` hands over the term for `2 2 + 5 =` | `python3 scripts/mutants.py --gforth $G --only fe-decide-skip-whnf` | caught: the kernel rejects | |
| 5 | whnf and the builders against pinned Lean (folds, `Nat.zero`, the original term unfolded when no fold, exponents 256 and 257, `mkDecide`, `mkAppOptM`) | `LEAN=$L GFORTH=$G python3 tests/front/check_whnf.py` | equal, or listed gaps unsupported | |
| 6 | Unit tests on both engines | `$G` and `$F` on `tests/front/tactics/decide/test.fs`, `tests/front/reduce-nat.fs`, `tests/core/nat-ops.fs`, `tests/front/tactic-lib.fs`, `tests/front/whnf.fs` | exit 0 each | |
| 7 | Every outcome: exhausted (`--elab-fuel 50`: exit 3, never accepted); unsupported (an exponent of 300: exit 2, error 93); a goal with a metavariable (252, unit test); deterministic over two runs and `--jobs 2` | within 1 and 6 | as stated | |
| 8 | Planted faults of the new words all caught | `python3 scripts/mutants.py --check`; `--only` the S3a ids (`tests/mutants/faults.d/s3a.toml`, `decide.toml`) | every one caught | |
| 9 | No never-run block on a line the branch added or changed | `make cover-changed BASE=tactic-batch-1 JOBS=4 GFORTH=$G` | exit 0 | |
| 10 | Kernel and earlier results unchanged after the nat-ops move | `make test-kernel-reduction GFORTH=$G`; the full tier `make tier GFORTH=$G LEAN=$L` (the coordinator) | exit 0 | |
| 11 | Duplicates do not rise (the kernel's table moved, three at-least copies and apply's synth copy gone); style ratchet | `python3 scripts/check-duplicates.py`; `python3 scripts/forth-metrics.py`; `python3 scripts/check-forth-quality.py` | exit 0 | |
| 12 | Documentation | `make check-docs`; `grep -n by-decide docs/user/LANGUAGE_REFERENCE.md` | `by-decide` and `by-native-decide` in the language reference (sentences, the Lean equivalent, two checked samples); codes in LEANFORTH_WORDS; TACTIC_PLUGINS; FORTH_LIBRARY's nat-ops profile | |
| 13 | Whole-repository checks | `scripts/pre-tier.sh` | all passed | |
