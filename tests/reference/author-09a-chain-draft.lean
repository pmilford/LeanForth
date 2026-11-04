-- Lean source of tests/author/09a-chain-draft.lf (see author-01-identity.lean).
theorem chain {A B C D : Prop} (f : A → B) (g : B → C) (h : C → D) : A → D :=
  fun a => h (g (f a))

set_option pp.unicode.fun true
#print chain
