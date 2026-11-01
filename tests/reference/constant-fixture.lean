universe u

def fixtureId {α : Sort u} (x : α) : α := x

def fixturePoly {α : Sort u} (x : α) : α := fixtureId x

theorem fixtureUse {P : Prop} (h : P) : P := fixtureId h
