-- Lean source of tests/author/16-namespaces.lf (see author-01-identity.lean):
-- which constant a name means.
def c : Type := Prop
def A.c : Type := Prop
def A.B.c : Type := Prop
def X.c : Type := Prop
def X.d : Type := Prop
def Y.Z.h : Type := Prop

namespace A
def t1 : Type := c
end A
def A.t2 : Type := c
namespace A
def B.t3 : Type := c
def B.t4 : Type := B.c
end A
namespace A.B
def t5 : Type := c
end B
def t6 : Type := c
end A
namespace A
open X
def t7 : Type := c
def t8 : Type := d
end A
namespace W
open Y
open Z
def t9 : Type := h
end W

#print c
#print A.c
#print A.B.c
#print X.c
#print X.d
#print Y.Z.h
#print A.t1
#print A.t2
#print A.B.t3
#print A.B.t4
#print A.B.t5
#print A.t6
#print A.t7
#print A.t8
#print W.t9
