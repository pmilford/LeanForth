# Measurements for the front end on Mathlib (2026-11-17)

Inputs, commands and results behind [MATHLIB_FRONT.md](../../../design/MATHLIB_FRONT.md). Every number below is
from a command run on 2026-11-17 on the shared development machine (10 cores, 39 GB, other agents running; all runs
`ulimit -u 500`, `nice -n 10`, at most 3 of them at once), so times are upper bounds, not clean measurements.
Nothing under `.tools/`, the Mathlib export or the Mathlib snapshot was written; work files were kept in the
design branch's worktree under `.claude/work/MF/` (not committed).

## Inputs

| Input | Where | Size | Identity |
| --- | --- | ---: | --- |
| Mathlib export (lean4export 3.1.0, Mathlib `v4.35.0` commit `56a0058`) | `.tools/mathlib/mathlib.ndjson` (no manifest beside it) | 6,258,342,501 B; 110,895,826 lines | sha256 `18448e5d…59c6` |
| its manifest | `.claude/work/IM/mathlib.ndjson.manifest.json` (and a copy in the simp-data tool's worktree) | 1,117 B | no `elab_records_sha256` |
| Mathlib snapshot (build `d789e45f`, verdict version 9) | `.claude/work/overnight/mathlib-d789e45f.lfsnap` | 2,301,415,424 B | sha256 `fad771ef…2135` |
| Mathlib RAW, format 4, without the 11 sunfold records format 3 cannot say | simp-data tool worktree, `.claude/work/SIMPDATA/mathlib/mathlib.raw4.filtered` | 117,543,327 B | — |
| Mathlib format-3 data made for these runs | `.claude/work/MF/mathlib.elab3.ndjson` | 45,542,284 B | records sha256 `23875375…0cfc` |
| the same without the second `instHSMul` default record (step-around, below) | `.claude/work/MF/m2.elab3.ndjson` | 45,542,197 B | — |
| Init snapshot, data | `.claude/work/showcase/init.lfsnap`; `.claude/work/S1DONE/init.elab.ndjson` | 132,923,392 B; 3,747,307 B | — |
| front end | branch `s2-finish-2` at `cb12814d`, extracted with `git archive` into `.claude/work/MF/s2` | — | — |

Format-3 data for Mathlib, made from the format-4 RAW (no Lean run):
`python3 .claude/work/MF/raw4to3.py RAW4.filtered .claude/work/MF/mathlib.raw3 scripts` (228,483 records kept, 106,693
records of format 4's kinds and 93,754 defeq tags dropped), then `python3 scripts/export_elab.py --format 3
.claude/work/MF/mathlib.raw3 .claude/work/MF/mathlib.ndjson .claude/work/MF/mathlib.elab3.ndjson`: 80.2 s, 1.63 GB
peak. Counts: 2,450 class, 43,808 instance, 470 instance_left_out, 52 default_instance, 85,147 reducibility, 152
eliminator, 44,264 tag, 25,047 matcher, 15,463 projection, 1,777 sunfold (85 naming what the export lacks). Init's
format-3 file: 290 class, 2,938 instance (in 277 classes), 31 left out, 34 default instance, 387 sunfold.

## Runs (`bin/leanforth` of `s2-finish-2`, `GFORTH=.tools/gforth/bin/gforth-fast`)

`S` = `--snapshot .claude/work/overnight/mathlib-d789e45f.lfsnap`; `SI` = `--snapshot .claude/work/showcase/init.lfsnap`.

| # | Command (from `.claude/work/MF/s2`) | Result | Wall, peak |
| --- | --- | --- | --- |
| 1 | `check S --elab-data ../mathlib.elab3.ndjson tests/front/s1-rfl.lf` | exit 4: `the elaboration data was refused at line 46753 (error 16): a default instance named twice` | 128 s, 3.55 GB |
| 2 | the same with `../m2.elab3.ndjson` (line 46,753 dropped by `drop_lines.py`, header count and SHA-256 fixed) | no answer after 42 min (it was in the instance table's first query, which checks all 43,808 records); stopped | over 42 min, 4.79 GB and growing slowly |
| 3 | `check S --elab-data ../m2.elab3.ndjson tests/author/01-identity.lf` (kernel form: the data read, no instance query) | exit 0; prints all 729,264 verdicts (97 MB of output) | 294 s, 9.61 GB |
| 4 | `check S --elab-data ../m2.elab3.ndjson ../unknown.lf` (stops at its first token, after the data is read) | exit 2, error 70 | 157 s, 3.57 GB |
| 5 | `check S tests/front/s1-rfl.lf` (no data) | exit 4, error 110 (no instances) | 149 s, 4.34 GB |
| 6 | `check SI tests/front/s1-rfl.lf` (no data) | exit 4 | 7.3 s, 288 MB |
| 7 | `check SI --elab-data …/S1DONE/init.elab.ndjson tests/author/01-identity.lf` | exit 0 | 17.1 s, 617 MB |
| 8 | `check SI --elab-data …/init.elab.ndjson tests/front/s1-rfl.lf` | exit 0, `t: accepted` | 112 s, 635 MB |
| 9 | `check SI --elab-data …/init.elab.ndjson tests/front/03-zero-add-exact.lf` | exit 0, accepted | 105 s, 635 MB |

**The Mathlib slice** (`.claude/work/MF/`): `python3 -I scripts/export-slice.py MATHLIB add_zero add_comm Real
Real.instAdd Real.instZero Real.instAddMonoid Real.instAddCommSemigroup AddMonoid.toAddZeroClass
AddCommSemigroup.toAddCommMagma Zero.toOfNat0 instHAdd instOfNatNat > mf-slice.ndjson` (4,827 of 712,205 declaration
records, 331,150 lines, 17.6 MB; 498 s, 1.58 GB); `python3 scripts/export_manifest.py mf-slice.ndjson
--mathlib-commit 56a0058…`; `python3 scripts/export_elab.py --format 3 --bind mathlib.raw3 mf-slice.ndjson
mf-slice.elab3.ndjson` (570 instance, 13,194 instance_left_out, 13 default_instance, 28 sunfold; 4.0 MB; 4.9 s).
Slice B adds the four roots `Lean.Grind.CommRing.OfCommSemiring.instOfNatQ`, `Std.Time.WallTime.instHAddOffset_1`,
`Lean.Grind.CommRing.OfCommSemiring.instAddQ`, `Pi.instZero` (the first candidates Lean's order tries for `OfNat ?α
0`, `HAdd ?α ?β ?γ`, `Add ?α`, `Zero ?α`, found with `tried.py`, which sorts a root's records as `getInstances`
does): 4,906 records, 334,990 lines; 346 s. Each data file had its second `instHSMul` default record dropped
(`drop_lines.py`), so the runs use `--no-manifest`.

| # | Command (`check --no-manifest --env SLICE --elab-data DATA FILE`) | Result | Wall, peak |
| --- | --- | --- | --- |
| 10 | slice A, its data as written and bound by its manifest (no `--no-manifest`), `s1-rfl.lf` | exit 4, error 16 at line 13,969 (O2, as on all of Mathlib) | 1.7 s, 59 MB |
| 11 | slice A, the repeat dropped, `s1-rfl.lf` and `mf-real.lf` | exit 2, error 119: the search tries an instance the slice left out | 4.1 s, 67 MB |
| 12 | slice B, `s1-rfl.lf` | exit 0, `t: accepted; axioms: none`, 5,470 accepted | 47 s, 75 MB |
| 13 | slice B, `03-zero-add-exact.lf` | exit 0, `zero_add_ex: accepted; axioms: none` | 47 s, 74 MB |
| 14 | slice B, `mf-real-rfl.lf` (`theorem real_refl Real explicit: x  x 0 + x 0 + = := by by-rfl end real_refl`) | exit 0, `real_refl: accepted; axioms: propext, Classical.choice, Quot.sound` | 45 s, 75 MB |
| 15 | slice B, `mf-real.lf` | exit 2, error 139 at `by-exact` (9:72): "not supported yet: an elaboration step (plans FE2-FE5, S2)", at `add_zero` (9:63) | 4.9 s, 67 MB |
| 16 | slice B, `real_add_comm` alone | exit 2, error 93 at `by-rw[`: "not supported yet: a type inference, reduction or let binder the tactic needs (FE1c)", goal `x y : Real ⊢ x + y = y + x` | 4.6 s, 67 MB |

The terms of runs 12-14 were not compared with Lean's here (MF2 and MF3 do that).

From 6-9: on `Init` the snapshot loads in about 7 s and the data in about 10 s; the rest of runs 8 and 9 (about 90 s)
is the instance table's first query, which checks every one of the 2,938 instance records (FE1E §4 "When") before the
search starts: about 30 ms per record. From 4 and 5: Mathlib's snapshot and data load in about 2.5 minutes and 3.6
GB, the data's share small (run 1 had read 46,753 of its 228,483 lines when it stopped).

## Pinned Lean on the acceptance target (`run-lean.sh FILE`, pinned Lean 4.35.0, Mathlib's `.lake` builds)

| File | Exit | Wall, peak | What it shows |
| --- | --- | --- | --- |
| `mf-real.lean` | 0 | 1.28 s, 1.73 GB | both theorems accepted; their `pp.all` terms; axioms `propext`, `Classical.choice`, `Quot.sound` for both |
| `mf-real-wrong.lean` | 1 | 1.13 s, 1.72 GB | `Type mismatch: add_zero x has type x + 0 = x but is expected to have type x + 1 = x` |
| `mf-synth.lean` | 0 | 1.71 s, 1.71 GB | the instance searches: depth 1-3, 1-6 candidates listed per goal, one tried |
| `mf-defeq.lean` | 0 | 1.74 s, 1.72 GB | 344 `isDefEq` trace lines for the two proofs; the delta steps unfold `instHAdd`, `AddZero.toAdd`, `AddZeroClass.toAdd`, `AddMonoid.toAdd`, `Real.instAdd`, `Add.add`, `OfNat.ofNat`, `Zero.zero` |
| `mf-import-all.lean` (`import Mathlib`) | 0 | 7.56 s then 4.12 s, 6.90 GB | what a Lean user waits for with all of Mathlib |

`mf-real.lean`'s first statement, as Lean elaborates it (`pp.all`):
`∀ (x : Real), @Eq Real (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) x (@OfNat.ofNat Real 0
(@Zero.toOfNat0 Real Real.instZero))) x`, proved by `fun x => @add_zero Real (@AddMonoid.toAddZeroClass Real
Real.instAddMonoid) x`. `Real.instAddMonoid` and `Real.instAddCommSemigroup` are `inferInstance`, `Real.instAdd` is
`{ add := Real.add✝ }` (a private definition).

## Sizes

- **Instances:** 43,808 records (Init 2,938) in 2,311 classes (Init 277), 470 left out; the largest classes `SizeOf`
  3,594, `Inhabited` 2,159, `Decidable` 1,022; for the target `Add` 234, `Zero` 251, `HAdd` 106, `OfNat` 66; the
  longest key list 1,160 keys.
- **Data lines:** longest 137,535 bytes (a sunfold body; Init 11,219), about 28,600 JSON tokens at most (counted by
  separators); longest name among the data's records 235 bytes.
- **Export:** 712,205 declaration records (729,263 declarations with constructors and recursors), 105.9 million
  expression records, 4,241,558 names (Init: 57,919 records, 6.1 million expressions, 295,431 names).

## Files

`mf-real.lean`, `mf-real-wrong.lean`, `mf-real.lf` (the LeanForth twin), `mf-synth.lean`, `mf-defeq.lean`,
`mf-import-all.lean`, their `.out` files, `run-lean.sh`; the helper scripts `raw4to3.py` and `drop_lines.py`
and `tried.py` (measurement only: they make data no tool would write, to step around one refusal and reach the
next); `mf-namespaces.lean` (42,379 namespaces in all of Mathlib, 6.1 s).
