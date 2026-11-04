-- Lean source of tests/author/01-identity.lf; its #print output must equal the
-- lean: lines of that fixture's report (tests/author/check_author.py --lean).
theorem identity {P : Prop} (proof : P) : P := proof

set_option pp.unicode.fun true
#print identity
