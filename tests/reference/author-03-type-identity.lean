-- Lean source of tests/author/03-type-identity.lf (see author-01-identity.lean).
theorem type_identity {A : Type} {P : A → Prop} {x : A} (proof : P x) : P x := proof

set_option pp.unicode.fun true
#print type_identity
