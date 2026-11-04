-- Lean source of tests/author/07-add-comm.lf (see author-01-identity.lean).
-- Printed without the + and = notation, as the term printer prints it.
theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm n m

set_option pp.unicode.fun true
set_option pp.notation false in
#print add_comm'
