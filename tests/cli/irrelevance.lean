-- A correct theorem whose check needs proof irrelevance: `h` proves `P a`,
-- the statement says `P b`, and `a` and `b` are two proofs of `A`, equal
-- because they are proofs of the same proposition. Lean's kernel equates
-- them; LeanForth does not port proof irrelevance yet (plan task 4.2.5),
-- so `leanforth check` answers unknown, exit 2
-- (docs/user/COMMAND_LINE.md). tests/cli/export-check.sh rebuilds the
-- export and its manifest and compares them with the committed files.
theorem irrelevant {A : Prop} {P : A → Prop} (a b : A) (h : P a) : P b := h

#print axioms irrelevant
