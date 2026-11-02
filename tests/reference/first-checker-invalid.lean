/- Broken copies of the five pinned fixtures, written as ordinary Lean source.
   Lean must reject every line marked `-- expect <case>: <message>`, with that
   message on that line, and report no error anywhere else:
   tests/reference/first-checker-check.sh checks this. Case names match
   first-checker-expected.lean, which checks the same mistakes directly in
   Lean's kernel; here Lean's front end usually finds them first, so the
   messages differ. Kernel-only cases (a loose bound variable, a non-recursive
   self-reference, a missing universe argument) cannot be written in source.
   Unmarked declarations are correct helpers and must be accepted. -/
set_option autoImplicit false

universe u

-- composition
theorem composition_invalid {A B C : Prop} (f : A → B) (g : C → C) : A → C := fun value => g (f value) -- expect composition.wrong-intermediate: Application type mismatch
theorem composition_wrong_argument {A B C : Prop} (_f : A → B) (g : B → C) : A → C := fun value => g value -- expect composition.wrong-argument: Application type mismatch
theorem composition_wrong_type {A B C : Prop} (f : A → B) (g : B → C) : A → B := fun value => g (f value) -- expect composition.wrong-declared-type: Type mismatch
theorem composition_types {A B C : Type} (f : A → B) (g : B → C) : A → C := fun value => g (f value) -- expect composition.theorem-over-types: is not a proposition
theorem composition_non_function {A B C : Prop} (_f : A → B) (g : B → C) : A → C := fun value => g (value value) -- expect composition.applies-a-non-function: Function expected

-- identity
theorem identity_wrong_binder {P Q : Prop} (first : P) (_second : Q) : Q := first -- expect identity.wrong-binder: Type mismatch
theorem identity_returns_prop {P : Prop} (_proof : P) : P := P -- expect identity.returns-the-proposition: Type mismatch
theorem identity_non_type : fun (P : Prop) => P := fun (P : Prop) => P -- expect identity.type-is-not-a-type: type expected
theorem identity_types {P : Type} (proof : P) : P := proof -- expect identity.theorem-over-types: is not a proposition
theorem identity_unknown {P : Prop} (proof : P) : P := LeanForthMissing proof -- expect identity.unknown-constant: Unknown identifier

-- type-identity
theorem type_identity_wrong_universe : ∀ {A : Type} {P : A → Prop} {x : A}, P x → P x := fun {A : Prop} {_P} {_x} proof => proof -- expect type-identity.wrong-universe: Type mismatch
theorem type_identity_wrong_argument {A : Type} {P : A → Prop} {x y : A} (proof : P x) : P y := proof -- expect type-identity.wrong-argument: Type mismatch
theorem type_identity_non_type {A : Type} {P : A → Prop} {x : A} (proof : x) : P x := proof -- expect type-identity.binder-is-not-a-type: type expected
theorem type_identity_non_function {A : Type} {P : A} {x : A} (proof : P x) : P x := proof -- expect type-identity.applies-a-non-function: Function expected
theorem type_identity_types {A : Type} {P : A → Type} {x : A} (proof : P x) : P x := proof -- expect type-identity.theorem-over-types: is not a proposition

-- poly-identity
theorem poly_identity_undeclared {A : Sort v} {P : A → Prop} {x : A} (proof : P x) : P x := proof -- expect poly-identity.undeclared-universe: unknown universe level
theorem poly_identity_repeated.{w, w} {A : Sort w} {P : A → Prop} {x : A} (proof : P x) : P x := proof -- expect poly-identity.repeated-universe: already been declared
theorem poly_identity_wrong_universe.{w} : ∀ {A : Sort w} {P : A → Prop} {x : A}, P x → P x := fun {A : Sort (w + 1)} {_P} {_x} proof => proof -- expect poly-identity.wrong-universe: Type mismatch
theorem poly_identity_swapped.{w, z} {_B : Sort z} : ∀ {A : Sort w} {P : A → Prop} {x : A}, P x → P x := fun {A : Sort z} {_P} {_x} proof => proof -- expect poly-identity.swapped-universe: Type mismatch
theorem poly_identity_sort_u.{w} {A : Sort w} {P : A → Sort w} {x : A} (proof : P x) : P x := proof -- expect poly-identity.theorem-over-sort-u: is not a proposition

-- constant fixture (helpers fixtureIdCopy and fixtureUseCopy are correct)
def fixturePolyEarly {α : Sort u} (x : α) : α := fixtureIdLater x -- expect constant.forward-reference: Unknown identifier
def fixtureIdLater {α : Sort u} (x : α) : α := x
def fixtureIdCopy {α : Sort u} (x : α) : α := x
def fixtureIdCopy {α : Sort u} (x : α) : α := x -- expect constant.duplicate-name: has already been declared
theorem fixtureUseCopy {P : Prop} (h : P) : P := fixtureIdCopy h
def fixturePolyTooMany {α : Sort u} (x : α) : α := fixtureIdCopy.{u, u} x -- expect constant.too-many-universes: too many explicit universe levels
theorem fixtureUseWrongUniverse {P : Prop} (h : P) : P := @fixtureIdCopy.{1} P h -- expect constant.wrong-universe-argument: Application type mismatch
theorem fixtureUseWrongArgument {P : Prop} (_h : P) : P := @fixtureIdCopy.{0} P P -- expect constant.wrong-argument: Application type mismatch
theorem fixtureUnfoldWrong {P Q : Prop} (h : P) : @fixtureIdCopy.{1} Prop Q := h -- expect constant.needs-unfolding-wrong: Type mismatch
theorem fixtureOverApplied {P : Prop} (h : P) : P := @fixtureUseCopy P h h -- expect constant.over-application: Function expected
