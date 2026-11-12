-- Lean source of tests/author/14-case.lf (see author-01-identity.lean).
def caseVar {X : Type} (x : X) : X := x
def bothIds (f : Id Nat) : Id Nat := id f
def propVar (prop : Prop) : Prop := prop

set_option pp.unicode.fun true
set_option pp.explicit true
#print caseVar
#print bothIds
#print propVar
