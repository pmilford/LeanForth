/-
Every record kind of lean4export 3.1.0, and every class of byte Lean's
JSON printer writes differently, for the re-export test
(tests/core/test_ndjson_emit.py; docs/development/NDJSON_READER.md,
"Re-export"). tests/core/reexport/kinds.ndjson is this file's export by
the pinned exporter, made and compared again by
tests/core/reexport/lean-check.sh (`make reference-reexport`):

  leanexport --export-mdata --export-unsafe LeanForthReexportKinds -- NAMES

with the names that script lists. Exporting a constant exports everything
it depends on, so the file also holds Nat, String, Quot and their kin.
-/
namespace ReexportKinds

universe u v

/-- A natural number literal beyond 64 bits (natVal). -/
def big : Nat := 340282366920938463463374607431768211457

/-- `let` (letE), and `have` (letE with nondep, kept by --export-mdata). -/
def twice (n : Nat) : Nat := let m := n + 1; m + m
def kept (n : Nat) : Nat := have m := n + 1; m + m

/-- An abbreviation (hints abbrev) and a projection (proj, in Prod.fst). -/
abbrev Small := Fin 3
def first (p : Nat × Nat) : Nat := p.1

/-- Universe levels: param, succ, max and imax. -/
def pairType (α : Type u) (β : Type v) : Type (max u v) := α × β
def arrow (α : Sort u) (β : Sort v) : Sort (imax u v) := α → β

/-- The quotient package (quot records of every kind). -/
def parity : Quot (fun (_ _ : Nat) => True) := Quot.mk _ 3

/-- An opaque constant, an unsafe and a partial definition. -/
opaque hidden : Nat
unsafe def risky : Nat := 7
partial def spin (n : Nat) : Nat := spin n

/-- A theorem that uses propext, which the exporter writes as an axiom. -/
theorem iffEq (a b : Prop) (h : a ↔ b) : a = b := propext h

-- Inductive blocks: mutual with indices, nested, reflexive, and a
-- structure.
mutual
inductive Even : Nat → Prop
  | zero : Even 0
  | succ {n : Nat} : Odd n → Even (n + 1)
inductive Odd : Nat → Prop
  | succ {n : Nat} : Even n → Odd (n + 1)
end
inductive Tree where
  | leaf : Tree
  | node : List Tree → Tree
inductive Wide where
  | mk : (Nat → Wide) → Wide
structure Point where
  x : Nat
  y : Nat

/-- Names with spaces, quotes, backslashes and other characters. -/
def «with space» : Nat := 1
def «quote"and\back» : Nat := 2
def αβγ : Nat := 3

end ReexportKinds
