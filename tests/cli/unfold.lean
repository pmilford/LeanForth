-- A correct theorem whose check needs a definition unfolded: the value
-- `fun a => a` has type `A → A`, the statement says `Implies A A`, and the
-- two are equal only by the definition of Implies. Lean's kernel unfolds
-- it; LeanForth's first checker does not unfold yet (plan phase 4), so
-- `leanforth check` answers unknown, exit 2, after accepting Implies
-- (docs/user/COMMAND_LINE.md). tests/cli/export-check.sh rebuilds the
-- export and its manifest and compares them with the committed files.
def Implies (A B : Prop) : Prop := A → B

theorem impliesSelf {A : Prop} : Implies A A := fun a => a

#print axioms impliesSelf
