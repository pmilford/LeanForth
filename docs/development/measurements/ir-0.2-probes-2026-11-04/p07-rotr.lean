/-
IR 0.2 probe 7 (ADR 0019 Amendment 1): is the planned proof of `sha-rotr`
feasible? A throwaway check, not the model: it copies IR 0.1's cell
arithmetic (Cells, wrap, unsigned, signed and bitwise from
tests/reference/program-ir.lean), adds LSHIFT as IR 0.2 would define it,
and computes what the instructions of

  : sha-rotr ( u n -- u' ) 2dup rshift -rot 32 swap - lshift or sha-w32 ;
  : sha-w32 ( x -- u ) sha-mask and ;   $10000 dup * 1- constant sha-mask

leave for a word x (a cell holding x.toNat) and a count n < 32. Theorem
`rotr_masked` is the arithmetic heart, for every cell width of at least
32 bits; theorem `rotr_cells64` the whole computation on 64-bit cells
(the real proof would cover every width of at least 33 bits, as IR 0.1's
theorems cover every width). ROTR is copied from
tests/reference/sha256-spec.lean. The stack shuffling (2dup, -rot, swap)
is left to the real model's `simp`, as in IR 0.1's proofs.
Run: lean -DwarningAsError=true p07-rotr.lean
-/

abbrev Word := BitVec 32

/-- Copied from tests/reference/sha256-spec.lean. -/
def ROTR (n : Nat) (x : Word) : Word := (x >>> n) ||| (x <<< (32 - n))

theorem ROTR_toNat (n : Nat) (x : Word) :
    (ROTR n x).toNat = (x.toNat >>> n ||| x.toNat <<< (32 - n)) % 2 ^ 32 := by
  have small : x.toNat >>> n < 2 ^ 32 := by
    have := (x >>> n).isLt
    simpa using this
  simp only [ROTR, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt small]

/-- The heart of 32-bit masking on a wide cell: on any width w ≥ 32, the
right shift or'ed with the left shift cut to w bits, then and'ed with
2^32 - 1, is ROTR. -/
theorem rotr_masked (w n : Nat) (x : Word) (wide : 32 ≤ w) :
    (x.toNat >>> n ||| (x.toNat <<< (32 - n)) % 2 ^ w) &&& (2 ^ 32 - 1) = (ROTR n x).toNat := by
  rw [ROTR_toNat, Nat.and_two_pow_sub_one_eq_mod, Nat.or_mod_two_pow, Nat.or_mod_two_pow,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 wide)]

/-- Copied from tests/reference/program-ir.lean (IR 0.1). -/
structure Cells where
  bits : Nat
  two_le : 2 ≤ bits

namespace Cells
variable (c : Cells)
def half : Int := ((2 ^ (c.bits - 1) : Nat) : Int)
def max : Int := c.half - 1
def min : Int := -c.half
def modulus : Int := 2 * c.half
def wrap (x : Int) : Int := (x - c.min) % c.modulus + c.min
def unsigned (x : Int) : Nat := (if x < 0 then x + c.modulus else x).toNat
def signed (u : Nat) : Int := if (u : Int) > c.max then (u : Int) - c.modulus else u
end Cells

def bitwise (c : Cells) (op : Nat → Nat → Nat) (a b : Int) : Int :=
  c.signed (op (c.unsigned a) (c.unsigned b))

/-- IR 0.1's RSHIFT, for a count below the cell width. -/
def rshiftCell (c : Cells) (a : Int) (n : Nat) : Int := c.signed (c.unsigned a >>> n)

/-- LSHIFT as IR 0.2 would define it, for a count below the cell width:
the bit pattern shifted left, the bits above the cell dropped. -/
def lshiftCell (c : Cells) (a : Int) (n : Nat) : Int :=
  c.signed ((c.unsigned a <<< n) % 2 ^ c.bits)

/-- sha-mask: `65536 dup * 1-`, wrapping as IR 0.1's `*` and `1-` do. -/
def mask (c : Cells) : Int := c.wrap (c.wrap (65536 * 65536) - 1)

/-- What sha-rotr leaves for x and n: rshift, the count 32 - n, lshift,
or, then sha-w32's and with the mask. -/
def rotrCells (c : Cells) (x : Int) (n : Nat) : Int :=
  bitwise c (· &&& ·)
    (bitwise c (· ||| ·) (rshiftCell c x n) (lshiftCell c x (c.wrap (32 - n)).toNat))
    (mask c)

def cells64 : Cells := ⟨64, by decide⟩

theorem mask64 : mask cells64 = 4294967295 := by decide
theorem max64 : cells64.max = 9223372036854775807 := by decide
theorem modulus64 : cells64.modulus = 18446744073709551616 := by decide

theorem unsigned64_nat (u : Nat) : cells64.unsigned (u : Int) = u := by
  simp only [Cells.unsigned, modulus64]
  split <;> omega

theorem unsigned64_signed {u : Nat} (h : u < 2 ^ 64) :
    cells64.unsigned (cells64.signed u) = u := by
  simp only [Cells.unsigned, Cells.signed, max64, modulus64]
  split <;> split <;> omega

theorem signed64_small {u : Nat} (h : u < 2 ^ 63) : cells64.signed u = u := by
  simp only [Cells.signed, max64]
  split <;> omega

/-- sha-rotr on 64-bit cells, for a word x and a count n < 32, leaves
ROTR^n(x), as the cell holding its value. -/
theorem rotr_cells64 (x : Word) (n : Nat) (hn : n < 32) :
    rotrCells cells64 (x.toNat : Int) n = ((ROTR n x).toNat : Int) := by
  have hx := x.isLt
  have count : (cells64.wrap (32 - (n : Int))).toNat = 32 - n := by
    simp only [Cells.wrap, Cells.min, Cells.modulus, Cells.half, cells64]
    omega
  have right : x.toNat >>> n < 2 ^ 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have left : (x.toNat <<< (32 - n)) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have both : x.toNat >>> n ||| (x.toNat <<< (32 - n)) % 2 ^ 64 < 2 ^ 64 :=
    Nat.or_lt_two_pow (by omega) left
  have result : (ROTR n x).toNat < 2 ^ 63 := by
    have := (ROTR n x).isLt
    omega
  -- rshift, lshift, or, and: one step each.
  have shifted_right : rshiftCell cells64 (x.toNat : Int) n = ((x.toNat >>> n : Nat) : Int) := by
    rw [rshiftCell, unsigned64_nat, signed64_small (by omega)]
  have shifted_left : lshiftCell cells64 (x.toNat : Int) (32 - n) =
      cells64.signed ((x.toNat <<< (32 - n)) % 2 ^ 64) := by
    rw [lshiftCell, unsigned64_nat]
    rfl
  have ored : bitwise cells64 (· ||| ·) (rshiftCell cells64 (x.toNat : Int) n)
      (lshiftCell cells64 (x.toNat : Int) (32 - n)) =
      cells64.signed (x.toNat >>> n ||| (x.toNat <<< (32 - n)) % 2 ^ 64) := by
    rw [bitwise, shifted_right, shifted_left, unsigned64_nat, unsigned64_signed left]
  have mask_bits : cells64.unsigned (mask cells64) = 2 ^ 32 - 1 := by
    rw [mask64]
    decide
  rw [rotrCells, count, ored, bitwise, unsigned64_signed both, mask_bits,
    rotr_masked 64 n x (by decide), signed64_small result]

/-- A wrong variant refuted: without sha-w32's mask, the left shift's
bits above bit 31 stay in the cell (x = 2^31, n = 1). -/
theorem unmasked_rotr_wrong :
    bitwise cells64 (· ||| ·) (rshiftCell cells64 2147483648 1) (lshiftCell cells64 2147483648 31)
      ≠ ((ROTR 1 (2147483648 : Word)).toNat : Int) := by decide

#print axioms rotr_masked
#print axioms rotr_cells64
#print axioms unmasked_rotr_wrong
