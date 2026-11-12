-- Lean source of tests/author/08-monoid.lf (see author-01-identity.lean).
-- The fixture writes the class's constants as import stubs with these types.
universe u
class MyMonoid (M : Type u) where
  mul : M → M → M
  one : M
  mul_one : ∀ a : M, mul a one = a

namespace MyMonoid
theorem mul_one' {M : Type u} [inst : MyMonoid M] (a : M) : mul a one = a :=
  mul_one a
end MyMonoid

set_option pp.unicode.fun true
set_option pp.explicit true
set_option pp.notation false in
#print MyMonoid.mul_one'
