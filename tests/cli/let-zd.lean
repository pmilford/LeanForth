-- A definition whose value is a let named x (review rvRS F2). With
-- let-b.lean it makes tests/cli/cross_snapshot.py's let pair: B's check
-- makes a let equal to this one but for its name, which Lean's == ignores
-- (expr_eq_fn.cpp 104-109), so B must use the same fuel fresh and against
-- this export's snapshot (ADR 0014 Amendment 7, rule 1 for lets).
-- tests/cli/export-check.sh rebuilds the export and its manifest and
-- compares them with the committed files.
def Zd : Nat := let x : Nat := 0; x

#print axioms Zd
