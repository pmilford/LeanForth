\ Check structural term storage, field ordering, failure behavior and reset.
\ These are storage tests, not well-scopedness, type checking or proof tests.
include ../support/tester.fs
include ../../src/core/terms.fs

lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 1 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-app -> 2 true }T
T{ 0 1 lf-term-lam -> 3 true }T
T{ 0 1 lf-term-pi -> 4 true }T
T{ 0 lf-term-read -> lf-tag-sort 0 0 true }T
T{ 1 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 2 lf-term-read -> lf-tag-app 0 1 true }T
T{ 3 lf-term-read -> lf-tag-lam 0 1 true }T
T{ 4 lf-term-read -> lf-tag-pi 0 1 true }T
T{ -1 lf-term-sort -> false }T
T{ -1 lf-term-bvar -> false }T
T{ -1 0 lf-term-app -> false }T
T{ 0 -1 lf-term-lam -> false }T
T{ 5 0 lf-term-pi -> false }T
T{ 0 5 lf-term-app -> false }T
T{ 0 1 0 lf-term-binary -> false }T
T{ 0 1 lf-tag-sort lf-term-binary -> false }T
T{ -1 lf-term-read -> false }T
T{ 5 lf-term-read -> false }T
T{ 100000 lf-term-read -> false }T
T{ lf-term-count @ -> 5 }T
T{ 2 lf-term-read -> lf-tag-app 0 1 true }T

\ Fill all remaining slots to exercise failure at the allocation boundary.
: fill-terms ( -- )
  begin lf-term-count @ lf-term-capacity < while
    0 lf-term-sort 0= if -1 throw then drop
  repeat ;
fill-terms
T{ 0 lf-term-sort -> false }T
T{ 0 lf-term-bvar -> false }T
T{ 0 1 lf-term-app -> false }T
T{ 0 1 lf-term-lam -> false }T
T{ 0 1 lf-term-pi -> false }T
T{ lf-term-count @ -> lf-term-capacity }T
T{ 2 lf-term-read -> lf-tag-app 0 1 true }T
lf-term-reset
T{ 0 lf-term-read -> false }T
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-read -> lf-tag-sort 0 0 true }T

\ Build the structure of polymorphic identity over propositions. These tests
\ only inspect its nodes; they do not claim the term is scoped or well typed.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-pi -> 3 true }T
T{ 0 3 lf-term-pi -> 4 true }T
T{ 1 1 lf-term-lam -> 5 true }T
T{ 0 5 lf-term-lam -> 6 true }T
T{ 4 lf-term-read -> lf-tag-pi 0 3 true }T
T{ 6 lf-term-read -> lf-tag-lam 0 5 true }T

\ Corrupt counts must never permit reads or allocations outside storage.
-1 lf-term-count !
T{ 0 lf-term-read -> false }T
T{ 0 lf-term-sort -> false }T
T{ 0 lf-term-bvar -> false }T
T{ 0 0 lf-term-app -> false }T
T{ lf-term-count @ -> -1 }T
lf-term-capacity 1+ lf-term-count !
T{ 0 lf-term-read -> false }T
T{ 0 lf-term-sort -> false }T
T{ 0 lf-term-bvar -> false }T
T{ 0 0 lf-term-pi -> false }T
T{ lf-term-count @ -> lf-term-capacity 1+ }T
lf-term-reset
bye
