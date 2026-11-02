include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/legacy/raw-declaration-index.fs
include ../../src/kernel/level-substitute.fs
include ../../src/legacy/term-level-substitute.fs
include ../../src/legacy/raw-signature-specialize.fs
include ../../src/legacy/constant-signature-probe.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/legacy/constant-term-type-probe.fs

create formals 2 cells allot
create actuals 4 cells allot
: actual! ( index position -- )
  2 * cells actuals + >r dup r@ ! lf-level-identity drop r> cell+ ! ;
: ref ( name addr count -- index identity )
  >r >r lf-name-generation @ r> r> lf-cref-new 0= abort" ref" ;
lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset lf-cref-reset
0 s" candidate" lf-name-str drop constant candidate
0 s" zero" lf-name-str drop constant zero-name
0 s" missing" lf-name-str drop constant missing-name
11 lf-lscope-context-add drop 22 lf-lscope-context-add drop
33 lf-lscope-context-add drop 44 lf-lscope-context-add drop
11 formals ! 22 formals cell+ !
11 lf-level-param drop constant p
22 lf-level-param drop constant q
33 lf-level-param drop constant x
44 lf-level-param drop constant y
p q lf-level-max drop constant pq
x 0 actual! y 1 actual!
lf-ssession-begin drop lf-rawdecl-begin drop
pq dup lf-level-identity drop lf-hterm-sort drop constant sid constant s
s sid s sid lf-hterm-app drop constant aid constant a
0 lf-hterm-bvar drop constant bid constant bare
T{ candidate a aid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ zero-name bare bid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ lf-rspec-begin -> true }T
lf-rawdecl-token drop constant tok
T{ tok candidate a aid formals 2 1000 lf-rspec-put -> lf-rspec-ok }T
T{ tok zero-name bare bid formals 0 1000 lf-rspec-put -> lf-rspec-ok }T
candidate actuals 2 ref constant rid constant ri
zero-name 0 0 ref constant zid constant zi
missing-name 0 0 ref constant mid constant mi
y 0 actual! x 1 actual!
candidate actuals 2 ref constant reversed-id constant reversed-ref
x 0 actual! y 1 actual!
candidate actuals 1 ref constant short-id constant short-ref
candidate 0 0 ref constant empty-id constant empty-ref

: node ( ref identity -- root identity )
  lf-cterm-new 0= abort" constant node" ;
ri rid node constant nid constant root-node
zi zid node constant nzid constant nz
mi mid node constant nmid constant nm
reversed-ref reversed-id node constant nrid constant nr
short-ref short-id node constant nsid constant short-node
empty-ref empty-id node constant neid constant ne
T{ tok nz nzid 1 1000 lf-cttype-probe -> bare bid lf-rspec-ok }T
T{ tok root-node nid 3 1000 lf-cttype-probe -> 10 lf-term-serial @ lf-rspec-ok }T
T{ 10 lf-term-read -> lf-tag-app 9 9 true }T
T{ 9 lf-term-read -> lf-tag-symbolic-sort 6 0 true }T
T{ 6 lf-level-read -> lf-level-tag-max x y true }T
T{ tok nr nrid 3 1000 lf-cttype-probe -> 12 lf-term-serial @ lf-rspec-ok }T
T{ 12 lf-term-read -> lf-tag-app 11 11 true }T
T{ 11 lf-term-read -> lf-tag-symbolic-sort 7 0 true }T
T{ 7 lf-level-read -> lf-level-tag-max y x true }T
T{ tok short-node nsid 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
T{ tok ne neid 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
T{ tok nm nmid 1 1000 lf-cttype-probe -> lf-rspec-unknown }T
T{ tok bare bid 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
T{ tok a aid 1000 1000 lf-cttype-probe -> lf-rspec-invalid }T
T{ tok root-node nid -1 1000 lf-cttype-probe -> lf-rspec-invalid }T
T{ tok root-node nid 1000 -1 lf-cttype-probe -> lf-rspec-invalid }T
T{ 123 tok root-node nid 0 1000 lf-cttype-probe -> 123 lf-rspec-exhausted }T
T{ tok root-node nid 2 1000 lf-cttype-probe -> lf-rspec-exhausted }T
T{ tok root-node nid 3 0 lf-cttype-probe -> lf-rspec-exhausted }T
T{ tok root-node nid 1+ 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
T{ tok -1 nid 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
T{ tok 1+ root-node nid 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
\ Scope is checked even for a name with no candidate metadata.
55 lf-level-param drop constant out-of-scope
out-of-scope 0 actual!
missing-name actuals 1 ref node constant out-id constant scoped-node
T{ tok scoped-node out-id 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
x 0 actual! y 1 actual!
\ An unknown name with a scoped live argument is unknown, but the same
\ node becomes invalid when that argument is malformed or its slot is reused.
33 lf-level-param drop constant unknown-level
unknown-level 0 actual!
missing-name actuals 1 ref node constant unknown-id constant unknown-node
T{ tok unknown-node unknown-id 10 1000 lf-cttype-probe -> lf-rspec-unknown }T
unknown-level lf-level-slot 2 cells + 1 swap !
T{ tok unknown-node unknown-id 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
0 unknown-level lf-level-slot 2 cells + !
T{ tok unknown-node unknown-id 10 1000 lf-cttype-probe -> lf-rspec-unknown }T
unknown-level lf-level-count !
: reuse-level ( -- ) 33 lf-hlevel-param 0= abort" reuse level" 2drop ;
reuse-level
T{ tok unknown-node unknown-id 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
x 0 actual! y 1 actual!
\ A stale root identity is rejected before any reference can be used.
T{ tok root-node nid 1+ 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
\ A rolled-back reference slot reused with a new identity stays stale.
lf-cref-count @ constant spare-slot
zero-name 0 0 ref node constant spare-id constant spare-node
spare-slot lf-cref-count !
zero-name 0 0 ref 2drop
T{ tok spare-node spare-id 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
\ Allocation failure after partial substitution rolls both arenas back.
: framed ( token root id b s -- result marker | status marker )
  777 >r lf-cttype-probe r> ;
lf-term-count @ constant terms-before
lf-level-count @ constant levels-before
-1 1 rshift 1- lf-term-serial !
lf-term-serial @ constant terms-serial-before
lf-level-serial @ constant levels-serial-before
T{ 123 tok root-node nid 10 1000 framed -> 123 lf-rspec-exhausted 777 }T
T{ lf-term-count @ -> terms-before }T
T{ lf-level-count @ -> levels-before }T
T{ lf-term-serial @ terms-serial-before > -> true }T
T{ lf-level-serial @ levels-serial-before > -> true }T
\ Restarting the index invalidates an otherwise live token and root.
T{ lf-rawdecl-begin -> true }T
T{ tok root-node nid 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
\ A new index and token are live before a context reset invalidates the
\ session. The index necessarily becomes stale as well: it captures session.
T{ lf-rspec-begin -> true }T
lf-rawdecl-token drop constant session-token
T{ session-token lf-rspec-current? -> true }T
T{ root-node nid 10 lf-cterm-check -> lf-repr-ok }T
T{ session-token root-node nid 10 1000 lf-cttype-probe -> lf-rspec-unknown }T
lf-lscope-context-reset
T{ lf-ssession-current? -> false }T
T{ root-node nid 10 lf-cterm-check -> lf-repr-invalid }T
T{ session-token root-node nid 10 1000 lf-cttype-probe -> lf-rspec-invalid }T
bye
