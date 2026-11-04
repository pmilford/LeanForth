-- Lean source of tests/author/04-poly-identity.lf (see author-01-identity.lean).
universe u
theorem poly_identity {A : Sort u} {P : A → Prop} {x : A} (proof : P x) : P x := proof

set_option pp.unicode.fun true
#print poly_identity
