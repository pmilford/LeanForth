# Simp data measurements (2026-11-17)

Throwaway evidence for [SIMP_DATA.md](../../../design/SIMP_DATA.md): what pinned Lean 4.35.0 keeps for `simp` and
Mathlib's `norm_num` outside the export, counted on `Init` and on all of Mathlib. Not a product tool; the extraction
tool the design proposes extends `scripts/export_elab.lean` instead.

| File | What it does |
| --- | --- |
| `count_simp.lean` | imports the modules and writes one JSON line per simp set, simp lemma (in the shape of the proposed `simp` record), `@[simp]` definition to unfold, simproc set and simproc, congruence lemma, plus the declared simprocs and the `defeq` tag totals |
| `count_normnum.lean` | imports Mathlib and writes one line per value of `norm_num`'s extension tree |
| `analyse.py` | counts by set and checks every name against an export (`scripts/export_elab.py`'s `export_decls`) |
| `nn.py` | counts the `norm_num` lines |
| `mentions.py` | counts source mentions of each default simproc and of the `simp`-family tactic words |
| `run.sh` | runs a Lean script with the pinned toolchain and Mathlib's build on `LEAN_PATH` |

Commands, from this folder (`TOOLS` is the main checkout's `.tools` when run from a worktree; `OUT` a scratch folder):

```text
TOOLS=$TOOLS bash run.sh count_simp.lean $OUT/init.simp.ndjson Init          # 2.0 s, 2.0 GB
TOOLS=$TOOLS bash run.sh count_simp.lean $OUT/mathlib.simp.ndjson Mathlib    # 13.5 s (28.6 s cold), 9.1 GB
TOOLS=$TOOLS bash run.sh count_normnum.lean $OUT/mathlib.normnum.ndjson Mathlib   # 7.4 s, 8.7 GB
python3 analyse.py $OUT/init.simp.ndjson INIT_EXPORT > init.out                # INIT_EXPORT: S1's done-check export
python3 analyse.py $OUT/mathlib.simp.ndjson $TOOLS/mathlib/mathlib.ndjson > mathlib.out   # 67 s, 1.5 GB
python3 nn.py $OUT/mathlib.normnum.ndjson > normnum.out
python3 mentions.py $OUT/mathlib.simp.ndjson $TOOLS/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init \
  $TOOLS/mathlib/mathlib4/Mathlib > mentions.out
```

`INIT_EXPORT` was `.claude/work/S1DONE/init.ndjson` (59,349 declarations, the export of S1's done check); the Mathlib
export was the night build's (729,263 declarations). The JSON outputs (4.5 MB for `Init`, 63 MB for Mathlib) are not
kept; the `.out` files are. In `mentions.out` the bare word `simp` also counts `@[simp]` attributes; the `simp only`,
`simpa`, `dsimp`, `ring` and `norm_num` counts are tactic calls (and a few words in comments).
