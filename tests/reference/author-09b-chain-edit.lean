-- Lean source of tests/author/09b-chain-edit.lf (see author-01-identity.lean).
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
theorem chain {A B C D : Prop} (f : A → B) (g : B → C) (h : C → D) : A → D :=
  fun a => h (composition f g a)

set_option pp.unicode.fun true
#print composition
#print chain
