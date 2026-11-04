-- An export with an inductive type, which `leanforth check` reads through
-- the importer stage and checks (plan task 5.2.1a: a block that is not
-- recursive, indexed or mutual): the block Two (its type, constructors and
-- recursor), a theorem proved with the recursor and a definition computed
-- with it, each accepted without axioms (docs/user/COMMAND_LINE.md).
-- Exported with scripts/export.sh; tests/cli/export-check.sh rebuilds the
-- export and its manifest and compares them with the committed files.
inductive Two where
  | first
  | second

theorem Two.cases (motive : Two → Prop) (a : motive Two.first) (b : motive Two.second)
    (t : Two) : motive t :=
  Two.rec a b t

-- Noncomputable: Lean's compiler does not compile recursors; the kernel
-- checks the definition all the same.
noncomputable def Two.swap (t : Two) : Two :=
  Two.rec (motive := fun _ => Two) Two.second Two.first t

#print axioms Two.cases
