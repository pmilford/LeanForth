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
\ Shared occurrences consume fuel independently, but rebuilt DAGs share
\ nodes: max (max p q) (max p q) becomes mk_max of two equal images, the
\ image itself (level.cpp 84-85), as Lean builds it.
q actuals ! p actuals cell+ !
pq pq lf-level-max drop constant shared
T{ shared formals actuals 2 8 lf-lsubst -> outcome-exhausted }T
T{ lf-level-count @ -> 8 }T
T{ shared formals actuals 2 9 lf-lsubst -> 8 outcome-ok }T
T{ 8 lf-level-read -> lf-level-tag-max q p true }T
T{ lf-level-count @ -> 9 }T
\ Running out of allocation identities or storage (full, not exhausted)
\ cannot append partial results.
lf-level-serial @ constant saved-serial
-1 1 rshift lf-level-serial !
T{ tree formals actuals 2 20 lf-lsubst -> outcome-full }T
T{ lf-level-count @ -> 9 }T
saved-serial lf-level-serial !
\ A build that fails part way appends nothing: tree needs two new nodes
\ (max q p, then imax over it); with one identity left the first is added,
\ the second refused, and the store is rolled back.
-1 1 rshift 1- lf-level-serial !
T{ tree formals actuals 2 20 lf-lsubst lf-level-count @ -> outcome-full 9 }T
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

\ Lean's instantiate (ADR 0011, Amendment 1). Fresh store: p, q and w,
\ with 1, succ w and imax p q.
require ../../src/core/diagnostics.fs
: must ( flag -- ) 0= if -1 throw then ;
lf-level-reset lf-lscope-context-reset
11 lf-lscope-context-add must 22 lf-lscope-context-add must 33 lf-lscope-context-add must
11 lf-level-param must constant p     22 lf-level-param must constant q
33 lf-level-param must constant w     0 lf-level-succ must constant one
w lf-level-succ must constant w+1     p q lf-level-imax must constant ipq
: sub ( root a b -- result status ) actuals cell+ ! actuals ! formals actuals 2 100 lf-lsubst ;
\ T.{1, w+1}: imax 1 (w+1) is rebuilt by mk_imax into max 1 (w+1), the
\ review's case d.
T{ ipq one w+1 sub -> lf-level-count @ 1- outcome-ok }T
T{ lf-level-count @ 1- lf-level-read -> lf-level-tag-max one w+1 true }T
\ A zero right side gives zero; a zero or one left side the right side;
\ equal sides one of them; otherwise a new imax.
T{ ipq w 0 sub ipq 0 w sub ipq one w sub ipq w w sub -> 0 outcome-ok w outcome-ok
  w outcome-ok w outcome-ok }T
T{ ipq w+1 w sub -> lf-level-count @ 1- outcome-ok }T
T{ lf-level-count @ 1- lf-level-read -> lf-level-tag-imax w+1 w true }T
\ A node without a parameter stays even when mk_max would change it
\ (replace keeps it, level.cpp 320-321).
0 one lf-level-max must constant max01
T{ max01 w w sub -> max01 outcome-ok }T
\ K6: imax 1 (p+1) whose images are its own children. Lean keeps it only
\ when the arguments are the objects its type holds; LeanForth cannot know:
\ unknown, recorded with the node, nothing appended. The same for an
\ actual that is another node of the same parameter.
p lf-level-succ must constant p+1   one p+1 lf-level-imax must constant shared-imax
lf-level-count @ constant before-k6
lf-diag-clear
T{ shared-imax p q sub -> outcome-unknown }T
T{ lf-diag@ nip -> shared-imax 0 lf-diag-shared-level }T
T{ lf-level-count @ -> before-k6 }T
11 lf-level-param must constant p'
T{ shared-imax p' q sub -> outcome-unknown }T
\ One that mk_imax leaves alone is kept: imax q p under p:=p, q:=q.
q p lf-level-imax must constant iqp
T{ iqp p q sub -> iqp outcome-ok }T
\ A changed child rebuilds it: imax 1 (q+1) becomes max 1 (q+1).
T{ shared-imax q p sub -> lf-level-count @ 1- outcome-ok }T
T{ lf-level-count @ 1- lf-level-read nip nip -> lf-level-tag-max true }T
bye
