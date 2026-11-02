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

\ Identities are fresh for each allocation and never reused after a reset;
\ each reset advances the generation by one. Handles rely on both.
lf-term-reset
lf-term-serial @ constant term-serial0
lf-term-generation @ constant term-generation0
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-identity -> term-serial0 1+ true }T
T{ 1 lf-term-identity -> false }T
T{ -1 lf-term-identity -> false }T
lf-term-reset
T{ lf-term-generation @ -> term-generation0 1+ }T
T{ 0 lf-term-identity -> false }T
T{ 0 lf-term-bvar -> 0 true }T
T{ 0 lf-term-identity -> term-serial0 2 + true }T

\ A spent identity serial refuses every constructor and changes nothing.
max-n lf-term-serial !
T{ 0 lf-term-sort -> false }T
T{ 0 0 lf-term-app -> false }T
T{ lf-term-count @ lf-term-serial @ -> 1 max-n }T
T{ 0 lf-term-read -> lf-tag-bvar 0 0 true }T

\ A saturated generation poisons the store: nothing is readable or allocated,
\ and further resets do not revive it.
0 lf-term-serial !
max-n lf-term-generation !
lf-term-reset
T{ lf-term-generation @ lf-term-count-valid? -> -1 false }T
T{ 0 lf-term-sort -> false }T
lf-term-reset
T{ lf-term-generation @ -> -1 }T
T{ 0 lf-term-read -> false }T
0 lf-term-generation !
lf-term-reset

\ The leaf constructor refuses non-leaf tags, so it cannot create a node
\ with a dangling child.
T{ 999 lf-tag-app lf-term-leaf -> false }T
T{ 0 99 lf-term-leaf -> false }T
T{ 0 lf-tag-bvar lf-term-leaf -> 0 true }T

\ Failed constructors leave the serial and count unchanged.
lf-term-serial @ constant term-serial1
T{ 0 0 99 lf-term-binary -> false }T
T{ 0 5 lf-term-app -> false }T
T{ 5 0 99 lf-term-binary -> false }T
T{ -1 lf-term-sort -> false }T
T{ lf-term-serial @ lf-term-count @ -> term-serial1 1 }T

\ Identities are unreadable under a corrupted count.
-1 lf-term-count !
T{ 0 lf-term-identity -> false }T
lf-term-capacity 1+ lf-term-count !
T{ 0 lf-term-identity -> false }T
1 lf-term-count !
T{ 0 lf-term-identity -> term-serial1 true }T
lf-term-reset
bye
