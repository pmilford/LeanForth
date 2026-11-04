-- Lean source of tests/author/12-hygienic-used.lf (see author-01-identity.lean).
-- Lean source cannot write the hygienic binder name of the fixture; Lean
-- prints it as P, as the term printer does. Q is used only in q's type.
set_option linter.unusedVariables false in
theorem hyg_used : ∀ (P : Prop), P → P := fun Q q => q

set_option pp.unicode.fun true
#print hyg_used
