-- A theorem whose check makes, by instantiation, a let equal to its
-- claim's but for its name (review rvRS F2): the other half of
-- tests/cli/cross_snapshot.py's let pair with let-zd.lean, whose let is
-- named x. Lean's == ignores a let's name (expr_eq_fn.cpp 104-109), so
-- B's fuel must not depend on whether Zd's let is in the tier.
-- tests/cli/export-check.sh rebuilds the export and its manifest and
-- compares them with the committed files.
theorem B : (let z : Nat := 0; z) = (let z : Nat := 0; z) :=
  (fun n : Nat => (rfl : (let y : Nat := n; y) = (let y : Nat := n; y))) 0

#print axioms B
