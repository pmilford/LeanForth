-- Lean source of tests/author/06-universes.lf (see author-01-identity.lean).
-- The unused arguments keep Lean's universe check satisfied.
universe u v
def Big : Type (u + 1) := Type u
def PairSort (_A : Sort u) (_B : Sort v) : Type (max u v) := Sort (max u v)
def ImaxSort (_A : Sort u) (_B : Sort v) : Type (imax u v) := Sort (imax u v)
def PairOf (A : Sort u) (B : Sort v) : Type (max u v) := PairSort.{v, u} B A

set_option pp.unicode.fun true
#print Big
#print PairSort
#print ImaxSort
#print PairOf
