-- A mutual block with a parameter and an index (plan row FE6; review
-- fe6a-2 N3): each recursor has two motives, each motive's type binds the
-- parameter and the index, and casesOn keeps one motive and its own minor
-- premises (src/front/cases-several.fs). Built and exported by
-- tests/front/constructions-init.sh, which compares the result with the
-- committed tests/front/several.ndjson; tests/front/constructions.fs
-- compares LeanForth's casesOn, recOn and ctorIdx of both types with
-- these, node for node.
namespace FE6

mutual
inductive Even (α : Type) : Nat → Type where
  | zero : α → Even α 0
  | succ : Odd α n → Even α (n + 1)
inductive Odd (α : Type) : Nat → Type where
  | succ : Even α n → Odd α (n + 1)
end

theorem even_zero (a : Nat) : Even.zero a = Even.zero a := rfl

end FE6

#print axioms FE6.even_zero
