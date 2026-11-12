-- Lean source of tests/author/wrong/20-zero-add.lf: pinned Lean refuses it
-- (the base case proves 1 = 1, not 0 + 0 = 0), as LeanForth's check
-- rejects the text.
theorem zero_add' (n : Nat) : 0 + n = n :=
  @Nat.rec (fun k => 0 + k = k) (@Eq.refl Nat 1)
    (fun k ih => @congrArg Nat Nat (0 + k) k Nat.succ ih) n
