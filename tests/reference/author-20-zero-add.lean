-- Lean source of tests/author/20-zero-add.lf (see author-01-identity.lean).
-- A proof by induction, written as the kernel term: the recursor Nat.rec
-- with its motive, the case for zero and the step.
theorem zero_add' (n : Nat) : 0 + n = n :=
  @Nat.rec (fun k => 0 + k = k) (@Eq.refl Nat 0)
    (fun k ih => @congrArg Nat Nat (0 + k) k Nat.succ ih) n

set_option pp.unicode.fun true
set_option pp.explicit true in
#print zero_add'
