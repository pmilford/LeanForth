-- Lean source of tests/author/11-strict.lf (see author-01-identity.lean).
theorem strict_example {A : Type} {P : A → Prop} (h : ∀ ⦃x : A⦄, P x) (y : A) : P y := @h y

set_option pp.unicode.fun true
#print strict_example
