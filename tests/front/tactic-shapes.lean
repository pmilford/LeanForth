-- The shapes of tactic proofs whose reading FE1g-2 decided by pinned Lean
-- (src/front/tactic-syntax.fs; tests/front/check_tactics.py --lean runs
-- this file and checks each theorem's first error, or that it has none).
-- s1: an empty `by` parses; running it leaves the goal unsolved.
theorem s1 (n : Nat) : 0 + n = n := by
-- s2: `induction ... with` and no alternative parses; running it finds
-- the alternatives missing.
theorem s2 (n : Nat) : 0 + n = n := by
  induction n with
-- s3: `rw []`, no rule, is a proof.
theorem s3 (n : Nat) : n = n := by
  rw []
-- s4: an alternative with no tactic does not parse.
theorem s4 (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
  | succ k ih => rw [Nat.add_succ, ih]
-- s5: a dotted hypothesis name is a name.
theorem s5 (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ a.b ih => rw [Nat.add_succ, ih]
-- s6: an induction inside an alternative, both naming their hypothesis ih
-- (tests/front/04-nested-ih.lf).
theorem s6 (n m : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    induction m with
    | zero => rw [Nat.add_succ, ih]
    | succ j ih => exact ih
