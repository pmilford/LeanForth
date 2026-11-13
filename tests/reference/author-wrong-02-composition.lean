-- Lean source of tests/author/wrong/02-composition.lf: pinned Lean refuses
-- it (g needs a proof of B, value is one of A), as LeanForth's check
-- rejects the text.
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g value
