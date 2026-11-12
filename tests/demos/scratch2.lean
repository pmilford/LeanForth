theorem even_of_sq (a : Nat) (h : (a*a) % 2 = 0) : a % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
  · exact h0
  · exfalso
    have : (a*a) % 2 = 1 := by rw [Nat.mul_mod, h1]
    omega

theorem no_sqrt2 : ∀ b : Nat, ∀ a : Nat, 0 < b → a ^ 2 ≠ 2 * b ^ 2 := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro a hb h
    rw [Nat.pow_two, Nat.pow_two] at h
    obtain ⟨c, hc⟩ : ∃ c, a = 2 * c := ⟨a / 2, by have := even_of_sq a (by omega); omega⟩
    subst hc
    have e : 2 * 2 * (c * c) = 2 * (b * b) := by rw [← Nat.mul_mul_mul_comm]; exact h
    obtain ⟨d, hd⟩ : ∃ d, b = 2 * d := ⟨b / 2, by have := even_of_sq b (by omega); omega⟩
    subst hd
    have e2 : 2 * 2 * (d * d) * 2 = 2 * 2 * (c * c) := by
      rw [e, ← Nat.mul_mul_mul_comm]; omega
    have e3 : c * c = 2 * (d * d) := by omega
    exact ih d (by omega) c (by omega) (by rw [Nat.pow_two, Nat.pow_two]; exact e3)
#check @no_sqrt2
