theorem composition_invalid {A B C : Prop} (f : A → B) (g : C → C) : A → C :=
  fun value => g (f value)
