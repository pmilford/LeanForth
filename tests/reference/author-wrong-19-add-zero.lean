-- Lean source of tests/author/wrong/19-add-zero.lf: pinned Lean refuses it
-- (0 + n does not reduce to n), as LeanForth's check rejects the text.
theorem zero_add_refl (n : Nat) : 0 + n = n := Eq.refl n
