-- Lean source of tests/author/02-composition.lf (see author-01-identity.lean).
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)

set_option pp.unicode.fun true
#print composition
