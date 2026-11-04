-- Lean source of tests/author/18-protected.lf (see author-01-identity.lean):
-- which constant a name means when some are protected.
def bar : Type := Prop
protected def N.bar : Type := Prop
def N.baz : Type := Prop
def A.x : Type := Prop
protected def A.B.x : Type := Prop
protected axiom P.q : Type
def q : Type := Prop

namespace N
def t1 : Type := bar
def t2 : Type := N.bar
def t3 : Type := baz
end N
def N.t4 : Type := bar
namespace M
open N
def t5 : Type := baz
def t6 : Type := bar
end M
namespace A.B
def t7 : Type := x
end B
end A
namespace P
def t8 : Type := q
end P

#print bar
#print N.bar
#print N.baz
#print A.x
#print A.B.x
#print P.q
#print q
#print N.t1
#print N.t2
#print N.t3
#print N.t4
#print M.t5
#print M.t6
#print A.B.t7
#print P.t8
