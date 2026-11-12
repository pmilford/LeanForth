/-- Cantor's theorem: no function from `α` to the predicates on `α` is onto.
    The diagonal predicate `fun x => ¬ f x x` is not any `f a`. Demo 4 of docs/user/DEMOS.md. -/
theorem cantor (α : Type) : ¬ ∃ f : α → α → Prop, ∀ g : α → Prop, ∃ a, f a = g :=
  fun ⟨f, h⟩ =>
    let ⟨a, ha⟩ := h (fun x => ¬ f x x)
    have e : f a a = ¬ f a a := congrFun ha a
    have n : ¬ f a a := fun p => (e ▸ p) p
    n (e ▸ n)
