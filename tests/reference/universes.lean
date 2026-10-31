def sort_zero_in_one : Sort 1 := Sort 0

def impredicative_identity : Prop := ∀ P : Prop, P → P

theorem beta_conversion (P : Prop) (proof : P) : (fun Q : Prop => Q) P := proof
