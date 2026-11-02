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
T{ tok zi zid 1000 lf-csig-probe -> bare bid lf-rspec-ok }T
T{ tok ri rid 1000 lf-csig-probe -> 4 lf-term-serial @ lf-rspec-ok }T
T{ 4 lf-term-read -> lf-tag-app 3 3 true }T
T{ 3 lf-term-read -> lf-tag-symbolic-sort 6 0 true }T
T{ 6 lf-level-read -> lf-level-tag-max x y true }T
T{ tok reversed-ref reversed-id 1000 lf-csig-probe -> 6 lf-term-serial @ lf-rspec-ok }T
T{ 6 lf-term-read -> lf-tag-app 5 5 true }T
T{ 5 lf-term-read -> lf-tag-symbolic-sort 7 0 true }T
T{ 7 lf-level-read -> lf-level-tag-max y x true }T
T{ tok short-ref short-id 1000 lf-csig-probe -> lf-rspec-invalid }T
T{ tok empty-ref empty-id 1000 lf-csig-probe -> lf-rspec-invalid }T
T{ tok mi mid 1000 lf-csig-probe -> lf-rspec-unknown }T
T{ 123 tok ri rid 0 lf-csig-probe -> 123 lf-rspec-exhausted }T
T{ tok ri rid -1 lf-csig-probe -> lf-rspec-invalid }T
T{ tok 1+ ri rid 1000 lf-csig-probe -> lf-rspec-invalid }T
T{ tok ri rid 1+ 1000 lf-csig-probe -> lf-rspec-invalid }T
T{ tok -1 rid 1000 lf-csig-probe -> lf-rspec-invalid }T
\ An index restart invalidates the old token even if references remain live.
T{ lf-rawdecl-begin -> true }T
T{ tok ri rid 1000 lf-csig-probe -> lf-rspec-invalid }T
T{ lf-rspec-begin -> true }T
lf-rawdecl-token drop constant tok2
T{ tok2 ri rid 1000 lf-csig-probe -> lf-rspec-unknown }T
T{ candidate a aid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ tok2 candidate a aid formals 2 1000 lf-rspec-put -> lf-rspec-ok }T
\ Exhaust after one allocated term; preserve arena counts and caller stacks.
: framed-probe ( token index identity fuel -- result marker | status marker )
  777 >r lf-csig-probe r> ;
lf-term-count @ constant terms-before
lf-level-count @ constant levels-before
-1 1 rshift 1- lf-term-serial !
T{ 123 tok2 ri rid 1000 framed-probe -> 123 lf-rspec-exhausted 777 }T
T{ lf-term-serial @ -> -1 1 rshift }T
T{ lf-term-count @ -> terms-before }T
T{ lf-level-count @ -> levels-before }T
\ Reset and reuse a reference slot: old identity stays stale.
lf-cref-reset
candidate actuals 2 ref constant new-id constant new-ref
T{ tok2 ri rid 1000 lf-csig-probe -> lf-rspec-invalid }T
T{ tok2 new-ref new-id 0 lf-csig-probe -> lf-rspec-exhausted }T
\ Reuse a level slot without resetting the index lifetime; stale pair fails
\ before lookup, even though a new level occupies the same numeric index.
4 lf-level-count !
: reuse-level ( -- ) 0 lf-level-identities @ lf-hlevel-succ 0= abort" reuse" 2drop ;
reuse-level
T{ tok2 lf-rspec-current? -> true }T
T{ tok2 new-ref new-id 1000 lf-csig-probe -> lf-rspec-invalid }T
\ A new name-table and index lifetime cannot revive an old name handle.
zero-name 0 0 ref constant stale-name-id constant stale-name-ref
lf-name-reset
0 s" candidate" lf-name-str 2drop
0 s" zero" lf-name-str 2drop
T{ lf-rawdecl-begin -> true }T
T{ lf-rspec-begin -> true }T
lf-rawdecl-token drop constant tok3
T{ tok3 lf-rspec-current? -> true }T
T{ tok3 stale-name-ref stale-name-id 1000 lf-csig-probe -> lf-rspec-invalid }T
bye
