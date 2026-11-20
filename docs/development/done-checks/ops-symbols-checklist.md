# Acceptance checklist: slice S3a-ops, steps C2-C4, Lean's symbols as words (plan row S3)

Written 2026-11-20 by the implementing agent of branch `ops-symbols` (from main 8b6272c1), from
sections 3 (C2-C6) and 4 of the architect's word list `.claude/work/briefs/OPS-WORDLIST.md` and the
owner's two answers of 2026-11-20 ([OWNER_DECISIONS.md](../../project/OWNER_DECISIONS.md), "Two
answers of 2026-11-20, morning"): the symbols `< > ≥ ≠ - / %` and `¬ ∧ ∨ ↔ ∣` as words, `^` as "to
the power" (Lean's `rightact%`), on the condition that every symbol that is not ASCII can be typed on
a plain keyboard (Lean's own ASCII notation where pinned Lean 4.35.0 has one: `<=` `>=` `/\` `\/`
`<->`; else the constant's name: `Ne`, `Not`, `Dvd.dvd`). The done checker runs it again. Untrusted
front-end code: only the kernel's check of the finished term accepts a theorem. `G` is Gforth
1.0.0's `gforth`, `F` its `gforth-fast`, `L` pinned Lean 4.35.0's `lean`, all absolute paths; `INIT`
is `.claude/work/parallel-init/init-1.lfsn` and `INIT.elab` `.claude/work/IM/init.elab.ndjson` of
the main checkout; every command runs from the repository root under `ulimit -u 500` with stdin
`/dev/null`. "Accepted" means LeanForth's kernel checked the term `by-decide` built. Every line is a
make target the tier runs or one command that finishes in under two minutes.

| # | Criterion | Command | Expected | Result |
| --- | --- | --- | --- | --- |
| 1 | The talk file works for a user on all of Init | `bin/leanforth check --snapshot INIT --elab-data INIT.elab --steps - tests/front/tactics/decide/dc-symbols.lf` | exit 0; each of its 14 theorems (the talk's ten and `¬ ∨ ↔ ^ >` four) "accepted ... axioms: none" | exit 0 (head 1e48754a): sy_mul ... sy_pow_cmp, 14 accepted, axioms none; 14 steps with `"tactic":"decide"` |
| 2 | The same theorems typed on a plain keyboard | `bin/leanforth check --snapshot INIT --elab-data INIT.elab tests/front/tactics/decide/dc-ascii.lf` | exit 0; 14 accepted, axioms none; every token of its theorems ASCII | exit 0: as_mul ... as_pow_cmp, 14 accepted |
| 3 | Init's files accepted, every term node for node pinned Lean's, the ASCII file's equal to the symbol file's, Init's wrong twins refused, `∣` never accepted, `#check` as Lean's | `GFORTH=$G python3 tests/front/tactics/decide/check.py --init INIT INIT.elab` | exit 0 | exit 0 (50 s): 59 theorems of 7 files accepted, axioms none, their types and values node for node goal-layer.golden's (pinned Lean's; dc-ops-init.lf's five and the 28 sy_/as_ theorems newly compared), dc-ascii.lf's 28 lines equal to dc-symbols.lf's; 4 wrong twins refused with Lean's text (new: `w-sy-euler.lf`, `w-sy-divmod.lf`); 2 not supported, error 93, exit 2 (new: `x-sy-dvd.lf`, `3 12 ∣`); `c-sy-check.lf` prints Lean's five `#check` lines (`3 ∣ 12 : Prop`, `2 ^ 3 ^ 2 : Nat`, ...) |
| 4 | Slice theorems as before; symbol-word wrong twins refused with Lean's text | `GFORTH=$G python3 tests/front/tactics/decide/check.py` (target `test-tactic-decide-e2e`) | exit 0 | exit 0: 3 files accepted, terms node for node, step logs as golden; 19 wrong twins refused (new: `w-sy-lt`, `-ne`, `-ge` typed `>=`, `-or` typed `\/`, `-iff` typed `<->`, `-not`: `  20 < 10`, `  3 ≠ 3`, `  10 ≥ 11`, `  1 = 0 ∨ 2 = 3`, `  2 = 2 ↔ 2 = 3`, `  ¬2 = 2`, each "is false") |
| 5 | Pinned Lean proves every Lean twin, writes the same golden, refuses the wrong twins with that text, prints the `#check` lines | `LEAN=$L python3 tests/front/tactics/decide/check.py --lean` | exit 0, golden only grown | exit 0: goal-layer.golden grew by 66 lines (d_divmod ... d_pow_cmp, sy_*, as_*), none changed; 23 wrong twins' messages (8 new); c-sy-check.lean's five lines |
| 6 | Reader words build Lean's macro expansion | `LEAN=$L GFORTH=$G python3 tests/front/check_front.py` (in `reference-front`) | exit 0 | exit 0: 18 statements as pinned Lean expands them (12 new: `-` `/` `%` `>` `≥` `>=` `<=` `≠`, `rightact% HPow.hPow` three times, `And✝` from `∧` and `/\`) |
| 7 | Unit tests on both engines | `$G` and `$F` on `tests/front/front.fs`, `tests/lib/text-run.fs`, `tests/author/author.fs`, `tests/front/tactics/decide/test.fs` | exit 0 each | exit 0 each, both engines: front.fs (each word's node and operand order, ASCII spellings the same node, `\/` a word not a comment, error 3 for a missing value, 38 for a library without the constant, 58 in kernel form, `^` kept the universe word there, Forth's `-` `/` `<=` `>=` unchanged, registration refusals: a missing row, a spelling the row lacks, a word twice, a word reserved twice; elaborated on S2's slice: a Bool exponent 119 not 131, an operator exponent its own tree 139, a notation name the root constant inside `namespace Foo` with a `Foo.And`); text-run.fs (`text-trim`); author.fs (58 for `-` `<=` `\/` `∧` in kernel form, `root: ∧` and `root: <=` printed for constants so named) |
| 8 | The registry: every notation word reserved and a syntax word | `GFORTH=$G python3 tests/front/check_registry.py` (in `make test`) | exit 0 | exit 0 after `--write`: 21 reserved lines (`+ = * ≤` moved after `#check`, 17 new), each "word" |
| 9 | Planted faults | `python3 scripts/mutants.py --check`; `python3 scripts/mutants.py --gforth $G --only rd-op-swaps-operands,rd-sub-as-binrel,rd-op-skips-row-check,rd-named-takes-spelling,rd-syn-namespace-resolve,et-rightact-enters-rhs,et-analyze-counts-exponent,et-coe-exponent,lib-text-trim-keeps-start` | 0 stale; each caught | 3,149 entries, 0 stale; 9 run, 9 caught |
| 10 | No never-run block on a changed line | `make cover-changed BASE=main JOBS=3 GFORTH=$G LEAN=$L` | exit 0 | exit 0 (41 s): words.fs 9 blocks, elab-term.fs 38, reader.fs 41, text-run.fs 2, every one ran |
| 11 | Duplicates and style | `python3 scripts/check-duplicates.py --new-words --base main`; `python3 scripts/forth-metrics.py src/front/reader.fs src/front/elab-term.fs src/author/words.fs src/lib/text-run.fs`; `python3 scripts/check-forth-quality.py` | no new copy; ratchet holds, no baseline raised | none; 187 baseline groups, none new or grown; ratchet holds, no baseline raised: reader.fs 67 words, none over five lines, globals 0, shuffles 5 (baseline 6), return-stack 16 (18); elab-term.fs shuffles 12 (14); words.fs globals 59 (62) |
| 12 | Docs and plan | `make check-docs`; `python3 scripts/check-progress.py` | exit 0 | in row 13; LANGUAGE_REFERENCE's "say it as" rows, the table "How to type each symbol", A.1's rows, the postfix paragraph, D.7's three forms from dc-symbols.lf and dc-ascii.lf; LEANFORTH_SYNTAX, LEANFORTH_WORDS, FORTH_LIBRARY (`text-trim`), FE2_TERMS question 2 answered, PLAN_DRAFT rows S3 and FE2, PROJECT_PROGRESS |
| 13 | Whole-repository checks | `GFORTH=$G LEAN=$L scripts/pre-tier.sh` | all passed | exit 0 on 1e48754a, all checks passed (20); rows 3-8 and 10 run again on 1e48754a, the same results |
| 14 | The tier | `make tier GFORTH=$G LEAN=$L` | all passed | the coordinator's |

The slice of decide is unchanged: the first instances Lean tries for a numeral `/` and `^`
(`System.FilePath.instHDivString`, `Fin.instNatPow`) would grow it from 1,027 declarations to 4,286
and 1,836 (`scripts/export-slice.py` on Init's export, measured 2026-11-20), so the files with `/`,
`-` and `^` run against Init's snapshot, where `tests/front/elab-dump.fs`'s `cli-dump` prints each
term as the command line's check hands it to the kernel, for the node-for-node comparison.
