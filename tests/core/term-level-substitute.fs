include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/kernel/level-substitute.fs
include ../../src/legacy/term-level-substitute.fs

create formals 2 cells allot
create actual-handles 4 cells allot
T{ lf-repr-ok lf-tls-repr-status -> lf-tlsubst-ok }T
T{ lf-repr-invalid lf-tls-repr-status -> lf-tlsubst-invalid }T
T{ lf-repr-exhausted lf-tls-repr-status -> lf-tlsubst-exhausted }T
T{ 3 lf-tls-repr-status -> lf-tlsubst-invalid }T
T{ 99 lf-tls-repr-status -> lf-tlsubst-invalid }T
T{ lf-lsubst-ok lf-tls-level-status -> lf-tlsubst-ok }T
T{ lf-lsubst-invalid lf-tls-level-status -> lf-tlsubst-invalid }T
T{ lf-lsubst-exhausted lf-tls-level-status -> lf-tlsubst-exhausted }T
T{ 3 lf-tls-level-status -> lf-tlsubst-invalid }T
T{ 99 lf-tls-level-status -> lf-tlsubst-invalid }T
: actual! ( index position -- )
  2 * cells actual-handles + >r dup r@ ! lf-level-identity drop r> cell+ ! ;
lf-term-reset lf-level-reset lf-lscope-context-reset
33 lf-lscope-context-add drop 44 lf-lscope-context-add drop
11 formals ! 22 formals cell+ !
11 lf-level-param drop constant p
22 lf-level-param drop constant q
33 lf-level-param drop constant x
44 lf-level-param drop constant y
p q lf-level-max drop constant pq
x 0 actual! y 1 actual!
lf-ssession-begin drop
pq dup lf-level-identity drop lf-hterm-sort drop constant sid constant s
0 lf-hterm-bvar drop constant bid constant b
s sid b bid lf-hterm-app drop constant aid constant a
s sid a aid lf-hterm-lam drop constant lid constant l
l lid s sid lf-hterm-pi drop constant rid constant root
T{ root rid formals actual-handles 2 200 lf-tlsubst -> 8 lf-term-serial @ 0 }T
T{ 8 lf-term-read -> lf-tag-pi 7 5 true }T
T{ 7 lf-term-read -> lf-tag-lam 5 6 true }T
T{ 6 lf-term-read -> lf-tag-app 5 b true }T
T{ 5 lf-term-read -> lf-tag-symbolic-sort 6 0 true }T
T{ 6 lf-level-read -> lf-level-tag-max x y true }T
T{ 8 lf-term-serial @ 100 lf-hterm-check -> lf-repr-ok }T
T{ root rid formals actual-handles 2 0 lf-tlsubst -> lf-tlsubst-exhausted }T
T{ root rid 1+ formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
T{ lf-term-count @ -> 9 }T
T{ lf-level-count @ -> 7 }T
\ A stale actual is rejected even when its formal is unused.
actual-handles cell+ @ constant xid
xid 1+ actual-handles cell+ !
T{ b bid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
xid actual-handles cell+ !
\ Duplicate formals, unsupported nodes, and stale Sort stamps fail closed.
11 formals cell+ !
T{ root rid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
22 formals cell+ !
s cells lf-hsort-level-identities + @ constant sort-level-id
sort-level-id 1+ s cells lf-hsort-level-identities + !
T{ root rid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
sort-level-id s cells lf-hsort-level-identities + !
99 root lf-term-slot !
T{ root rid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
lf-tag-pi root lf-term-slot !
T{ lf-term-count @ -> 9 }T
T{ lf-level-count @ -> 7 }T
\ Reject malformed source levels, actual levels and a missing source formal.
99 pq lf-level-slot !
T{ root rid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
lf-level-tag-max pq lf-level-slot !
99 x lf-level-slot !
T{ b bid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
lf-level-tag-param x lf-level-slot !
T{ root rid formals actual-handles 1 200 lf-tlsubst -> lf-tlsubst-invalid }T
T{ root rid formals actual-handles -1 200 lf-tlsubst -> lf-tlsubst-invalid }T
T{ root rid formals actual-handles 2 -1 lf-tlsubst -> lf-tlsubst-invalid }T
T{ lf-term-count @ -> 9 }T
T{ lf-level-count @ -> 7 }T
\ Overlapping formal and caller IDs remain simultaneous, not recursive.
lf-term-reset lf-level-reset lf-lscope-context-reset
11 lf-lscope-context-add drop 22 lf-lscope-context-add drop
11 lf-level-param drop constant cp
22 lf-level-param drop constant cq
cp cq lf-level-max drop constant cpq
cq 0 actual! cp 1 actual!
lf-ssession-begin drop
cpq dup lf-level-identity drop lf-hterm-sort drop constant csid constant cs
T{ cs csid formals actual-handles 2 100 lf-tlsubst -> 1 lf-term-serial @ 0 }T
T{ 1 lf-term-read -> lf-tag-symbolic-sort 4 0 true }T
T{ 4 lf-level-read -> lf-level-tag-max cq cp true }T
\ A real rollback followed by reusing the same level index cannot revive the
\ old actual handle, even though its bare index is now valid again.
lf-level-count @ constant ephemeral-slot
11 lf-level-param drop constant ephemeral
ephemeral 0 actual!
ephemeral-slot lf-level-count !
22 lf-level-param drop constant replacement
T{ replacement -> ephemeral }T
T{ cs csid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-invalid }T
cq 0 actual!
\ Force term identity exhaustion after allocating a replacement level and Sort.
cs csid cs csid lf-hterm-app drop constant caid constant ca
lf-level-count @ constant before-levels
lf-term-count @ constant before-terms
-1 1 rshift 1- lf-term-serial !
T{ ca caid formals actual-handles 2 200 lf-tlsubst -> lf-tlsubst-exhausted }T
T{ lf-term-count @ -> before-terms }T
T{ lf-level-count @ -> before-levels }T
T{ lf-term-serial @ -> -1 1 rshift }T
bye
