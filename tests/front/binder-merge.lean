/-
Two theorems whose types differ only in a binder's kind (plan row
FE1c-bk, a known difference from Lean found 2026-11-18). lean4export
3.1.0 writes one expression node for expressions equal up to binder kinds
and names (Lean's `BEq Expr`, `Expr.eqv`), so both declarations of its
export name type node 480, implicit: the export says `BK.expl` takes `{n}`
where Lean's `BK.expl` takes `(n)`. tests/front/binder-merge.ndjson is
this file's export by the pinned exporter:

  lean -o BK.olean binder-merge.lean   (as module BK)
  scripts/export.sh binder-merge.ndjson BK -- BK.impl BK.expl

In Lean, `example (n : Nat) : n + 0 = n := by exact BK.expl n` is
accepted and `... := by exact BK.expl` is refused (type mismatch).
LeanForth reads the export's kinds (front/lib-decode.fs lf-tier-kinds),
implicit for BK.expl, unless the elaboration data carries Lean's own
(format 3.2, plan FE1c-bk): tests/front/binder-merge.elab.ndjson, made by

  LEAN_PATH=. lean --run scripts/export_elab.lean BK > bk.raw
  python3 scripts/export_elab.py bk.raw binder-merge.ndjson binder-merge.elab.ndjson

has BK.expl's record, explicit, which tests/front/menv-run.fs reads.
In Init, 1405 pairs of declarations share a type node this way (for
example `id` and `inferInstance`, whose instance-implicit binder the
export writes as explicit; `congrArg` and `have_val_congr'`).
-/
namespace BK
/-- Exported first: its type node is the one both share. -/
theorem impl {n : Nat} : n + 0 = n := rfl
theorem expl (n : Nat) : n + 0 = n := rfl
end BK
