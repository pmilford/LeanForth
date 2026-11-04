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

-- The contract of lf-gcd, in the style of `ClampContract` (clamp.lean).
-- `GcdSpec a b r`: `r` is a right answer for the inputs `a b`, namely no
-- result if either is negative, and otherwise a common divisor of both that
-- every common divisor divides (so the answer for 0 and 0 is 0). It does not
-- mention Euclid's algorithm. tests/reference/program-ir.lean copies this
-- block and proves that the word's IR meets the same clauses.
def GcdSpec (a b : Int) (r : Option Nat) : Prop :=
  (a < 0 ∨ b < 0 → r = none) ∧
  (0 ≤ a → 0 ≤ b → ∃ g : Nat, r = some g ∧ (g : Int) ∣ a ∧ (g : Int) ∣ b ∧
    ∀ d : Int, d ∣ a → d ∣ b → d ∣ (g : Int))

def GcdContract (f : Int → Int → Option Nat) : Prop :=
  ∀ a b : Int, GcdSpec a b (f a b)

-- Lean's `Nat.gcd` of the inputs, rejecting negative ones, meets the clauses.
theorem natGcd_spec (a b : Int) :
    GcdSpec a b (if a < 0 ∨ b < 0 then none else some (Nat.gcd a.toNat b.toNat)) := by
  by_cases negative : a < 0 ∨ b < 0
  · exact ⟨fun _ => by simp [negative], fun ha hb => by omega⟩
  · refine ⟨fun h => absurd h negative,
      fun ha hb => ⟨Nat.gcd a.toNat b.toNat, by simp [negative], ?_⟩⟩
    obtain ⟨x, rfl⟩ : ∃ x : Nat, a = x := ⟨a.toNat, (Int.toNat_of_nonneg ha).symm⟩
    obtain ⟨y, rfl⟩ : ∃ y : Nat, b = y := ⟨b.toNat, (Int.toNat_of_nonneg hb).symm⟩
    simp only [Int.toNat_natCast]
    refine ⟨Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left x y),
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right x y), fun d hx hy => ?_⟩
    have both := Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hx) (Int.natAbs_dvd_natAbs.mpr hy)
    exact Int.natAbs_dvd_natAbs.mp (by simpa using both)

theorem checked_contract : GcdContract checked := by
  intro a b
  have same : checked a b =
      if a < 0 ∨ b < 0 then none else some (Nat.gcd a.toNat b.toNat) := by
    simp only [checked, euclid_correct]
  rw [same]
  exact natGcd_spec a b

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

-- Deliberately wrong variants. A guard that rejects only when both inputs
-- are negative fails the rejection clause at (-1, 2). An answer of 1 is a
-- common divisor of any two numbers, so only the clause that every common
-- divisor divides the answer rejects it: 2 divides 2 and 2 but not 1.
def checkedBothNegative (a b : Int) : Option Nat :=
  if a < 0 ∧ b < 0 then none else some (euclid a.toNat b.toNat)

def checkedOne (a b : Int) : Option Nat :=
  if a < 0 ∨ b < 0 then none else some 1

theorem checkedBothNegative_violates : ¬ GcdContract checkedBothNegative := by
  intro h
  have bad := (h (-1) 2).1 (by decide)
  simp [checkedBothNegative] at bad

theorem checkedOne_violates : ¬ GcdContract checkedOne := by
  intro h
  obtain ⟨g, same, _, _, greatest⟩ := (h 2 2).2 (by decide) (by decide)
  simp only [checkedOne, show ¬((2 : Int) < 0 ∨ (2 : Int) < 0) by decide, ↓reduceIte,
    Option.some.injEq] at same
  subst same
  have bad := greatest 2 (Int.dvd_refl 2) (Int.dvd_refl 2)
  omega

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
#print axioms checked_contract
#print axioms checkedBothNegative_violates
#print axioms checkedOne_violates

end GcdReference
