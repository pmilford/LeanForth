-- A correct theorem whose check needs a definition unfolded: the value
-- `fun a => a` has type `A → A`, the statement says `Implies A A`, and the
-- two are equal only by the definition of Implies. Lean's kernel unfolds
-- it, and so does LeanForth since plan task 4.2.2d (lazy delta reduction):
-- `leanforth check` accepts both declarations, exit 0
-- (docs/user/COMMAND_LINE.md). tests/cli/export-check.sh rebuilds the
-- export and its manifest and compares them with the committed files.
def Implies (A B : Prop) : Prop := A → B

theorem impliesSelf {A : Prop} : Implies A A := fun a => a

#print axioms impliesSelf
