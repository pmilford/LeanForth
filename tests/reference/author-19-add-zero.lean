-- Lean source of tests/author/19-add-zero.lf (see author-01-identity.lean).
-- A proof term of its own: Eq.refl n, with n + 0 reducing to n.
theorem add_zero' (n : Nat) : n + 0 = n := Eq.refl n

set_option pp.unicode.fun true
set_option pp.explicit true in
#print add_zero'
