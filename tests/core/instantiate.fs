\ Regression tests for the untrusted instantiation experiment. No result from
\ this module authorizes a proof, declaration or theorem.
include ../support/tester.fs
include ../../src/experimental/instantiate.fs

\ Substituting loose variable one beneath a lambda must shift the replacement
\ to variable two, while the lambda's locally bound variable remains zero.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 1 lf-term-bvar -> 1 true }T
T{ 0 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-app -> 3 true }T
T{ 0 3 lf-term-lam -> 4 true }T
T{ 4 1 100 lf-instantiate -> 7 lf-inst-ok }T
T{ 5 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 6 lf-term-read -> lf-tag-app 5 2 true }T
T{ 7 lf-term-read -> lf-tag-lam 0 6 true }T

\ Variables beyond the removed binder move down by one under a lambda.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 2 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-app -> 3 true }T
T{ 0 3 lf-term-lam -> 4 true }T
T{ 4 1 100 lf-instantiate -> 7 lf-inst-ok }T
T{ 5 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 6 lf-term-read -> lf-tag-app 1 5 true }T
T{ 7 lf-term-read -> lf-tag-lam 0 6 true }T

\ Resource exhaustion, invalid inputs and malformed replacement nodes must not
\ retain allocations. Repeating a valid call after failure must still work.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 0 0 lf-instantiate -> -1 lf-inst-exhausted }T
T{ 1 0 1 lf-instantiate -> -1 lf-inst-exhausted }T
T{ -1 0 10 lf-instantiate -> -1 lf-inst-invalid }T
T{ 1 -1 10 lf-instantiate -> -1 lf-inst-invalid }T
T{ 1 0 -1 lf-instantiate -> -1 lf-inst-invalid }T
99 0 lf-term-slot !
T{ 1 0 10 lf-instantiate -> -1 lf-inst-invalid }T
lf-tag-sort 0 lf-term-slot !
T{ lf-term-count @ -> 2 }T
T{ 1 0 10 lf-instantiate -> 0 lf-inst-ok }T
T{ lf-term-count @ -> 2 }T

\ A malformed replacement must be rejected even when no variable is replaced.
99 0 lf-term-slot !
T{ 1 lf-term-sort -> 2 true }T
T{ 2 0 10 lf-instantiate -> -1 lf-inst-invalid }T
T{ lf-term-count @ -> 3 }T

\ Exhaustion after a transformed child was allocated must roll back the whole
\ operation. A sufficient budget must then produce the expected application.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 1 lf-term-bvar -> 1 true }T
T{ 1 0 lf-term-app -> 2 true }T
T{ 2 0 3 lf-instantiate -> -1 lf-inst-exhausted }T
T{ lf-term-count @ -> 3 }T
T{ 2 0 4 lf-instantiate -> 4 lf-inst-ok }T
T{ 3 lf-term-read -> lf-tag-bvar 0 0 true }T
T{ 4 lf-term-read -> lf-tag-app 3 0 true }T

\ A corrupted source root is invalid even when its replacement is sound.
99 2 lf-term-slot !
T{ 2 0 20 lf-instantiate -> -1 lf-inst-invalid }T
lf-tag-app 2 lf-term-slot !
T{ lf-term-count @ -> 5 }T

\ Exhausted allocation capacity cannot overwrite the existing input nodes.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 1 lf-term-bvar -> 1 true }T
: fill-inst-arena ( -- )
  begin lf-term-count @ lf-term-capacity < while
    0 lf-term-sort 0= if -1 throw then drop
  repeat ;
fill-inst-arena
T{ 1 0 10 lf-instantiate -> -1 lf-inst-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
T{ 1 lf-term-read -> lf-tag-bvar 1 0 true }T
lf-term-reset
bye
