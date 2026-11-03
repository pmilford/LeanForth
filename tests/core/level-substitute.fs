include ../support/tester.fs
require ../../src/lib/lib.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/kernel/level-substitute.fs

create formals 2 cells allot
create actuals 2 cells allot
lf-level-reset lf-lscope-context-reset
11 formals ! 22 formals cell+ !
11 lf-lscope-context-add drop 22 lf-lscope-context-add drop
11 lf-level-param drop constant p
22 lf-level-param drop constant q
p q lf-level-max drop constant pq
pq p lf-level-imax drop constant tree
q actuals ! p actuals cell+ !
T{ tree formals actuals 2 10 lf-lsubst -> 6 outcome-ok }T
T{ 5 lf-level-read -> lf-level-tag-max q p true }T
T{ 6 lf-level-read -> lf-level-tag-imax 5 q true }T
\ Replacement q is not itself substituted to p, even with colliding names.
T{ p formals actuals 2 3 lf-lsubst -> q outcome-ok }T
T{ tree formals actuals 2 6 lf-lsubst -> outcome-exhausted }T
T{ lf-level-count @ -> 7 }T
T{ tree formals actuals 2 -1 lf-lsubst -> outcome-invalid }T
T{ tree formals actuals -1 10 lf-lsubst -> outcome-invalid }T
T{ tree formals actuals 65 10 lf-lsubst -> outcome-invalid }T
T{ 0 0 0 0 1 lf-lsubst -> 0 outcome-ok }T
T{ p 0 0 0 1 lf-lsubst -> outcome-invalid }T
22 formals !
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
11 formals !
lf-lscope-context-reset
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
11 lf-lscope-context-add drop 22 lf-lscope-context-add drop
99 tree lf-level-slot !
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
lf-level-tag-imax tree lf-level-slot !
tree tree lf-level-slot cell+ !
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
pq tree lf-level-slot cell+ !
1 0 lf-level-slot cell+ !
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
0 0 lf-level-slot cell+ !
T{ lf-level-count @ -> 7 }T

\ Actuals are validated even when their formal is unused.
99 q lf-level-slot !
T{ p formals actuals 2 20 lf-lsubst -> outcome-invalid }T
lf-level-tag-param q lf-level-slot !
T{ lf-level-count @ -> 7 }T
\ Identity substitution reuses nodes and leaves the allocation identity intact.
p actuals ! q actuals cell+ !
tree lf-level-identity drop constant tree-id
T{ tree formals actuals 2 20 lf-lsubst -> tree outcome-ok }T
T{ tree lf-level-identity -> tree-id true }T
T{ lf-level-count @ -> 7 }T
\ Shared occurrences consume fuel independently, but rebuilt DAGs share nodes.
q actuals ! p actuals cell+ !
pq pq lf-level-max drop constant shared
T{ shared formals actuals 2 8 lf-lsubst -> outcome-exhausted }T
T{ lf-level-count @ -> 8 }T
T{ shared formals actuals 2 9 lf-lsubst -> 9 outcome-ok }T
T{ 9 lf-level-read -> lf-level-tag-max 8 8 true }T
T{ 8 lf-level-read -> lf-level-tag-max q p true }T
\ Running out of allocation identities or storage (full, not exhausted)
\ cannot append partial results.
lf-level-serial @ constant saved-serial
-1 1 rshift lf-level-serial !
T{ tree formals actuals 2 20 lf-lsubst -> outcome-full }T
T{ lf-level-count @ -> 10 }T
saved-serial lf-level-serial !
\ A commit that fails part way appends nothing. The plan stages two nodes;
\ then, as if the store changed during the call (which callers must
\ exclude), only one identity is left: the first node is added and the
\ second refused, and the count goes back. White-box: the passes of lf-lsubst.
20 lf-lsubst-walker walk-budget drop formals actuals 2 lf-lsubst-use
T{ tree lf-lsubst-prepare lf-lsubst-new-count @ -> tree outcome-ok 2 }T
-1 1 rshift 1- lf-level-serial !
T{ tree lf-lsubst-finish lf-level-count @ -> outcome-invalid 10 }T
saved-serial lf-level-serial !
: fill-arena ( -- )
  begin lf-level-count @ lf-level-capacity < while
    0 lf-level-succ 0= if -1 throw then drop
  repeat ;
fill-arena
T{ tree formals actuals 2 20 lf-lsubst -> outcome-full }T
T{ lf-level-count @ -> lf-level-capacity }T
T{ tree lf-level-identity -> tree-id true }T
\ Identity transformations can succeed even when no more slots are free.
p actuals ! q actuals cell+ !
T{ tree formals actuals 2 20 lf-lsubst -> tree outcome-ok }T
bye
