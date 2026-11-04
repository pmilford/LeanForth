-- Lean source of tests/author/05-constant-fixture.lf (see author-01-identity.lean).
universe u
def fixtureId {α : Sort u} (x : α) : α := x
def fixturePoly {α : Sort u} (x : α) : α := fixtureId x
theorem fixtureUse {P : Prop} (h : P) : P := fixtureId h

set_option pp.unicode.fun true
#print fixtureId
#print fixturePoly
#print fixtureUse
