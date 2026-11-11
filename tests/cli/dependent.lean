-- A library on top of tests/cli/inductive.lean, for `leanforth check
-- --snapshot` (plan task 6.2.5, step SN4; ADR 0020 D5): its export holds
-- Two's block, Two.cases and Two.swap again, with what the new theorems
-- use (Eq and rfl), so that checked against a snapshot of inductive.ndjson
-- the declarations of inductive.lean are taken from the snapshot and the
-- rest are checked. Exported with scripts/export.sh; tests/cli/export-check.sh
-- rebuilds the export and its manifest and compares them with the committed
-- files.
import LeanForthInductive

theorem Two.swap_swap (t : Two) : Two.swap (Two.swap t) = t :=
  Two.rec (motive := fun t => Two.swap (Two.swap t) = t) rfl rfl t

theorem Two.swap_swap_first : Two.swap (Two.swap Two.first) = Two.first :=
  Two.swap_swap Two.first

theorem Two.cases_first (motive : Two → Prop) (a : motive Two.first)
    (b : motive Two.second) : motive Two.first :=
  Two.cases motive a b Two.first

#print axioms Two.swap_swap_first
