-- Nested inductive types written by Lean 4.35.0 itself (plan task 5.2.5b;
-- review rvUNNI, its RvNest.lean): nesting through an indexed family (VT in
-- Vec VT n, the index a field), through a mutual block (AT in A AT, both of
-- whose types become auxiliary types), through Prod inside List with a
-- parameter (Q), and List R beside List (List R) (R); then structural
-- recursion over VT, which Lean compiles to VT.rec and the auxiliary
-- recursor VT.rec_1, and theorems proved by rfl that reduce through them
-- (iota on an indexed auxiliary type) and through R's recursor. Each is
-- accepted without axioms (docs/user/COMMAND_LINE.md). Exported with
-- scripts/export.sh; tests/cli/export-check.sh rebuilds the export and its
-- manifest and compares them with the committed files.
namespace RvNest

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

/-- Nesting through an indexed family, the index a field. -/
inductive VT where
  | node : (n : Nat) → Vec VT n → VT

mutual
inductive A (α : Type) where
  | a0 : A α
  | a1 : α → B α → A α
inductive B (α : Type) where
  | b0 : A α → B α
end

/-- Nesting through a mutual block (both its types become auxiliary types). -/
inductive AT where
  | mk : A AT → AT

/-- Nesting through Prod inside List, with a parameter. -/
inductive Q (α : Type) where
  | mk : List (α × Q α) → Q α

/-- Two nestings of List: List R and List (List R). -/
inductive R where
  | mk : List R → List (List R) → R

/-- Structural recursion over the nested type (uses VT.rec and VT.rec_1). -/
def VT.size : VT → Nat
  | .node _ v => 1 + go v
where go {n : Nat} : Vec VT n → Nat
  | .nil => 0
  | .cons t v => t.size + go v

theorem VT.size_leaf : VT.size (.node 0 .nil) = 1 := rfl
theorem VT.size_two : VT.size (.node 1 (.cons (.node 0 .nil) .nil)) = 2 := rfl

def R.count : R → Nat
  | .mk xs xss => 1 + xs.length + xss.length

theorem R.count_mk : R.count (.mk [] [[]]) = 2 := rfl

end RvNest

#print axioms RvNest.VT.size_two
