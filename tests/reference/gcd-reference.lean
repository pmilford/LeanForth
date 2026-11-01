import Lean

/- Mathematical Euclidean algorithm only; no Forth semantics are modeled. -/
namespace GcdReference

def euclid (a b : Nat) : Nat :=
  if _h : b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

theorem euclid_correct (a b : Nat) : euclid a b = Nat.gcd a b := by
  fun_induction euclid a b with
  | case1 a => simp
  | case2 a b _ ih =>
    rw [ih, Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a,
      Nat.gcd_comm]

def checked (a b : Int) : Option Nat :=
  if a < 0 ∨ b < 0 then none else some (euclid a.toNat b.toNat)

theorem negative_rejected (a b : Int) (h : a < 0 ∨ b < 0) :
    checked a b = none := by simp [checked, h]

theorem nonnegative_exact (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    checked a b = some (Nat.gcd a.toNat b.toNat) := by
  simp [checked, Int.not_lt.mpr ha, Int.not_lt.mpr hb, euclid_correct]

theorem divides_both (a b : Nat) : euclid a b ∣ a ∧ euclid a b ∣ b := by
  rw [euclid_correct]
  exact Nat.gcd_dvd a b

theorem greatest (a b d : Nat) (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ euclid a b := by
  rw [euclid_correct]
  exact Nat.dvd_gcd ha hb

example : checked 0 0 = some 0 := by simp [checked, euclid.eq_def]
example : checked 0 17 = some 17 := by simp [checked, euclid.eq_def]
example : checked 17 0 = some 17 := by simp [checked, euclid.eq_def]
example : checked 48 18 = some 6 := by simp [checked, euclid.eq_def]
example : checked 18 48 = some 6 := by simp [checked, euclid.eq_def]
example : checked 35 64 = some 1 := by simp [checked, euclid.eq_def]
example : checked (-1) 2 = none := by decide
example : checked 2 (-1) = none := by decide

#print axioms euclid_correct
#print axioms negative_rejected
#print axioms nonnegative_exact
#print axioms divides_both
#print axioms greatest

end GcdReference
