-- Lean source of tests/author/07-add-comm.lf (see author-01-identity.lean).
-- Printed with every argument, as the term printer prints a library's constants.
theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm n m

set_option pp.unicode.fun true
set_option pp.explicit true in
#print add_comm'
