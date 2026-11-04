/-!
# Small inductive blocks, exported for ADR 0015

`tests/reference/inductive-check.sh` compiles this file with pinned Lean
4.35.0, exports the declarations below with the toolchain's `leanexport` and
compares the result byte for byte with `blocks.ndjson`. The export shows what
LeanForth's reader receives for each kind of inductive block: the types,
constructors and recursors of a block on one line, recursors with their
computation rules. Reference observations only; nothing here is LeanForth
code.

Mathematics, LeanForth words and Lean for the first three are in ADR 0015,
"Three examples".
-/

universe u

namespace LeanForthBlocks

/-- Natural numbers: two constructors, one recursive field. -/
inductive N : Type where
  | zero : N
  | succ : N → N

/-- Conjunction: a structure in `Prop` whose fields are proofs. -/
structure Both (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

/-- Equality: two parameters, one index; the recursor has `k` set. -/
inductive Same {α : Sort u} : α → α → Prop where
  | refl (a : α) : Same a a

/-- Disjunction: two constructors in `Prop`, so it eliminates only into `Prop`. -/
inductive Either (a b : Prop) : Prop where
  | inl : a → Either a b
  | inr : b → Either a b

mutual
/-- Even and odd numbers: a mutual block of predicates with an index. -/
inductive Even : Nat → Prop where
  | zero : Even Nat.zero
  | succ (n : Nat) : Odd n → Even (Nat.succ n)

inductive Odd : Nat → Prop where
  | succ (n : Nat) : Even n → Odd (Nat.succ n)
end

/-- Trees with a list of subtrees: a nested block (an auxiliary recursor
`Tree.rec_1` for the nested `List Tree`). -/
inductive Tree : Type where
  | node : List Tree → Tree

/-- A structure with data fields; `Point.x` is a projection. -/
structure Point where
  x : Nat
  y : Nat

end LeanForthBlocks
