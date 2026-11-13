-- Lean source of tests/author/21-numeric-name.lf (see author-01-identity.lean).
-- Lean names the private theorem
-- _private.tests.reference.author-21-numeric-name.0.twice: the module is this
-- file's path, as check_author.py compiles it from the repository root, and 0
-- is a numeric part (Name.num).
private theorem twice (p : Prop) (h : p) : p := h
theorem useTwice (p : Prop) (h : p) : p := twice p h

set_option pp.unicode.fun true
#print twice
#print useTwice
