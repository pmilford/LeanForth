include ../support/tester.fs
require ../../src/lib/lib.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/kernel/level-substitute.fs
require ../support/store-faults.fs

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
99 tree level-tag!
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
lf-level-tag-imax tree level-tag!
tree tree level-first!
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
pq tree level-first!
1 0 level-first!
T{ tree formals actuals 2 20 lf-lsubst -> outcome-invalid }T
0 0 level-first!
T{ lf-level-count @ -> 7 }T

\ Actuals are validated even when their formal is unused.
99 q level-tag!
T{ p formals actuals 2 20 lf-lsubst -> outcome-invalid }T
lf-level-tag-param q level-tag!
T{ lf-level-count @ -> 7 }T
\ Identity substitution reuses nodes and leaves the allocation identity intact.
p actuals ! q actuals cell+ !
tree lf-level-identity drop constant tree-id
T{ tree formals actuals 2 20 lf-lsubst -> tree outcome-ok }T
T{ tree lf-level-identity -> tree-id true }T
T{ lf-level-count @ -> 7 }T
\ A shared node is checked once, a repeat costing only its unit, and
\ rebuilt DAGs share nodes: max (max p q) (max p q) costs the actuals q
\ and p, then shared, pq, p, q and pq again, 7 units, and becomes mk_max
\ of two equal images, the image itself (level.cpp 84-85), as Lean builds it.
q actuals ! p actuals cell+ !
pq pq lf-level-max drop constant shared
T{ shared formals actuals 2 6 lf-lsubst -> outcome-exhausted }T
T{ lf-level-count @ -> 8 }T
T{ shared formals actuals 2 7 lf-lsubst -> 8 outcome-ok }T
T{ 8 lf-level-read -> lf-level-tag-max q p true }T
T{ lf-level-count @ -> 9 }T
\ Running out of allocation identities or storage (full, not exhausted)
\ cannot append partial results.
level-serial constant saved-serial
-1 1 rshift level-serial!
T{ tree formals actuals 2 20 lf-lsubst -> outcome-full }T
T{ lf-level-count @ -> 9 }T
saved-serial level-serial!
\ A build that fails part way appends nothing: tree needs two new nodes
\ (max q p, then imax over it); with one identity left the first is added,
\ the second refused, and the store is rolled back.
-1 1 rshift 1- level-serial!
T{ tree formals actuals 2 20 lf-lsubst lf-level-count @ -> outcome-full 9 }T
saved-serial level-serial!
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

\ Lean's instantiate (ADR 0011, Amendment 1). Fresh store: the parameters
\ pp (ID 11), qq (22) and w (33), with 1, succ w and imax pp qq.
require ../../src/core/diagnostics.fs
: must ( flag -- ) 0= if -1 throw then ;
lf-level-reset lf-lscope-context-reset
11 lf-lscope-context-add must 22 lf-lscope-context-add must 33 lf-lscope-context-add must
11 lf-level-param must constant pp     22 lf-level-param must constant qq
33 lf-level-param must constant w     0 lf-level-succ must constant one
w lf-level-succ must constant w+1     pp qq lf-level-imax must constant ipq
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
\ K6: imax 1 (pp+1) whose images are its own children. Lean keeps it only
\ when the arguments are the objects its type holds; LeanForth cannot know:
\ unknown, recorded with the node, nothing appended. The same for an
\ actual that is another node of the same parameter.
pp lf-level-succ must constant pp+1   one pp+1 lf-level-imax must constant shared-imax
lf-level-count @ constant before-k6
lf-diag-clear
T{ shared-imax pp qq sub -> outcome-unknown }T
T{ lf-diag@ nip -> shared-imax 0 lf-diag-shared-level }T
T{ lf-level-count @ -> before-k6 }T
11 lf-level-param must constant pp'
T{ shared-imax pp' qq sub -> outcome-unknown }T
\ One that mk_imax leaves alone is kept: imax qq pp under pp:=pp, qq:=qq.
qq pp lf-level-imax must constant iqp
T{ iqp pp qq sub -> iqp outcome-ok }T
\ A changed child rebuilds it: imax 1 (qq+1) becomes max 1 (qq+1).
T{ shared-imax qq pp sub -> lf-level-count @ 1- outcome-ok }T
T{ lf-level-count @ 1- lf-level-read nip nip -> lf-level-tag-max true }T

\ Stamps (plan task 6.5.5): a source walk marks the nodes it reaches with
\ a new stamp and erases nothing, except when the stamps run out: then the
\ column is erased and they restart at 1, so no earlier walk's mark counts
\ as this one's. imax pp qq under pp:=w, qq:=0 is 0; then every node holds
\ stamp 1, as if an earlier walk had reached it, the stamps run out, and
\ under pp:=1, qq:=w+1 the node is still rebuilt, not given its earlier
\ image 0. The walk listed its three nodes once each.
T{ ipq w 0 sub -> 0 outcome-ok }T
: stale-stamps ( -- )
  lf-level-count @ 0 ?do 1 i lf-lsubst-seen ! loop max-n lf-lsubst-stamp ! ;
stale-stamps
T{ ipq one w+1 sub -> lf-level-count @ 1- outcome-ok }T
T{ lf-level-count @ 1- lf-level-read -> lf-level-tag-max one w+1 true }T
T{ lf-lsubst-stamp @ lf-lsubst-reached @ -> 1 3 }T

\ lf-cells-sort: every arrangement of up to six cells, with repeats, comes
\ out in ascending order and as the same cells (their sum and xor).
create sort-cells 6 cells allot
: sort-cell ( i -- addr ) cells sort-cells + ;
: arrangement! ( code n -- ) 0 ?do dup 3 mod i sort-cell ! 3 / loop drop ;
: ascending? ( n -- flag )
  true swap 1 max 1 ?do i sort-cell @ i 1- sort-cell @ < if drop false then loop ;
: sum-xor ( n -- sum xor ) 0 0 rot 0 ?do i sort-cell @ tuck xor >r + r> loop ;
: arrangement-sorted? ( code n -- flag )
  tuck arrangement! dup sum-xor 2>r sort-cells over lf-cells-sort
  dup ascending? swap sum-xor 2r> d= and ;
: arrangements-sorted? ( -- flag )
  true 7 0 do 729 0 do i j arrangement-sorted? and loop loop ;
T{ arrangements-sorted? -> true }T
bye
