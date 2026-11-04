-- Lean source of tests/author/15-case-variables.lf (see author-01-identity.lean).
def caseVar {X : Type} (x : X) : X := x

set_option pp.unicode.fun true
#print caseVar
