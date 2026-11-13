-- Lean source of tests/author/wrong/07-add-comm.lf: pinned Lean refuses it
-- (a type mismatch), as LeanForth's check rejects the text.
theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm m n
