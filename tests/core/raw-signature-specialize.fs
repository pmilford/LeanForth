include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/legacy/raw-declaration-index.fs
include ../../src/core/level-substitute.fs
include ../../src/legacy/term-level-substitute.fs
include ../../src/legacy/raw-signature-specialize.fs

create formals 2 cells allot
create actuals 4 cells allot
: actual! ( index position -- )
  2 * cells actuals + >r dup r@ ! lf-level-identity drop r> cell+ ! ;
lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset
0 s" candidate" lf-name-str 2drop
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
T{ 1 a aid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ lf-rspec-begin -> true }T
lf-rawdecl-token drop constant tok
\ An unavailable zero level returns only false; preserve the caller stack.
lf-level-count @ constant saved-level-count
0 lf-level-count !
T{ 12345 lf-rspec-coverage -> 12345 lf-rspec-invalid }T
saved-level-count lf-level-count !
T{ tok 1 a aid 1+ formals 2 1000 lf-rspec-put -> lf-rspec-invalid }T
T{ tok 1 a aid formals 2 0 lf-rspec-put -> lf-rspec-exhausted }T
11 formals cell+ !
T{ tok 1 a aid formals 2 1000 lf-rspec-put -> lf-rspec-invalid }T
22 formals cell+ !
\ Missing source formal must fail without committing or retaining allocations.
lf-term-count @ constant put-terms
lf-level-count @ constant put-levels
T{ tok 1 a aid formals 1 1000 lf-rspec-put -> lf-rspec-invalid }T
T{ lf-rspec-count @ -> 0 }T
T{ 1 15 lf-rawdecl-find -> a aid lf-rawdecl-ok }T
T{ tok 1 a aid formals 2 15 lf-rspec-put -> lf-rspec-exhausted }T
T{ lf-rspec-count @ -> 0 }T
T{ lf-term-count @ -> put-terms }T
T{ lf-level-count @ -> put-levels }T
T{ tok 1 a aid formals 2 1000 lf-rspec-put -> lf-rspec-ok }T
T{ lf-term-count @ -> put-terms }T
T{ lf-level-count @ -> put-levels }T
T{ tok 1 a aid formals 2 1000 lf-rspec-put -> lf-rspec-invalid }T
T{ lf-rspec-begin -> false }T
T{ lf-rspec-count @ -> 1 }T
99 formals ! 99 formals cell+ ! \ copied, not borrowed
T{ tok 1 actuals 2 1000 lf-rspec-specialize -> 3 lf-term-serial @ lf-rspec-ok }T
T{ 3 lf-term-read -> lf-tag-app 2 2 true }T
T{ 2 lf-term-read -> lf-tag-symbolic-sort 6 0 true }T
T{ 6 lf-level-read -> lf-level-tag-max x y true }T
T{ tok 1 actuals 1 1000 lf-rspec-specialize -> lf-rspec-invalid }T
T{ tok 1 actuals 3 1000 lf-rspec-specialize -> lf-rspec-invalid }T
T{ tok 1 actuals 2 0 lf-rspec-specialize -> lf-rspec-exhausted }T
T{ tok 1 actuals 2 -1 lf-rspec-specialize -> lf-rspec-invalid }T
T{ tok 2 actuals 2 1000 lf-rspec-specialize -> lf-rspec-unknown }T
T{ tok 1+ 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
actuals cell+ @ constant xid
xid 1+ actuals cell+ !
T{ tok 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
xid actuals cell+ !
\ A changed stored handle must never use metadata for another candidate.
aid 1+ lf-rawdecl-identities !
T{ tok 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
aid lf-rawdecl-identities !
s lf-rawdecl-types ! sid lf-rawdecl-identities !
T{ tok 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
a lf-rawdecl-types ! aid lf-rawdecl-identities !
\ A parameter-free term accepts zero arity and a separately named record
\ with an unused formal; exact arity still applies to that record.
0 s" zero" lf-name-str 2drop
0 s" unused" lf-name-str 2drop
0 lf-hterm-bvar drop constant bid constant bare-term
T{ 2 bare-term bid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ 3 bare-term bid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ tok 2 bare-term bid formals 0 1000 lf-rspec-put -> lf-rspec-ok }T
11 formals !
T{ tok 3 bare-term bid formals 1 1000 lf-rspec-put -> lf-rspec-ok }T
T{ tok 2 actuals 0 1000 lf-rspec-specialize -> bare-term bid lf-rspec-ok }T
T{ tok 3 actuals 1 1000 lf-rspec-specialize -> bare-term bid lf-rspec-ok }T
T{ tok 3 actuals 0 1000 lf-rspec-specialize -> lf-rspec-invalid }T
\ New index lifetime, even with identical contents, invalidates metadata.
T{ lf-rawdecl-begin -> true }T
T{ 1 a aid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ tok 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
T{ lf-rspec-begin -> true }T
lf-rawdecl-token drop constant tok2
11 formals ! 22 formals cell+ !
T{ tok2 1 a aid formals 2 1000 lf-rspec-put -> lf-rspec-ok }T
lf-name-reset
0 s" other" lf-name-str 2drop
T{ tok2 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
T{ lf-rawdecl-begin -> true }T
T{ tok2 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
\ Rebind metadata, then isolate term reset while names remain current.
T{ 1 a aid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ lf-rspec-begin -> true }T
lf-rawdecl-token drop constant tok3
T{ tok3 1 a aid formals 2 1000 lf-rspec-put -> lf-rspec-ok }T
\ A second candidate lets us exercise coverage allocation exhaustion before
\ metadata is committed. The term serial is deliberately near saturation.
0 s" exhaustion" lf-name-str 2drop
T{ 2 a aid 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
\ Coverage allocates one term, then exhausts the final term identity. Both
\ arena counts roll back while the serial proves that allocation occurred.
lf-term-count @ constant before-terms
lf-level-count @ constant before-levels
-1 1 rshift 1- lf-term-serial !
T{ tok3 2 a aid formals 2 1000 lf-rspec-put -> lf-rspec-exhausted }T
T{ lf-term-serial @ -> -1 1 rshift }T
T{ lf-rspec-count @ -> 1 }T
T{ lf-term-count @ -> before-terms }T
T{ lf-level-count @ -> before-levels }T
T{ tok3 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-exhausted }T
T{ lf-term-count @ -> before-terms }T
T{ lf-level-count @ -> before-levels }T
lf-term-reset
T{ tok3 1 actuals 2 1000 lf-rspec-specialize -> lf-rspec-invalid }T
T{ lf-rspec-begin -> false }T
\ Helper statuses keep their meaning; other codes are invalid, never ok.
T{ lf-rawdecl-ok lf-rspec-decl-status -> lf-rspec-ok }T
T{ lf-rawdecl-invalid lf-rspec-decl-status -> lf-rspec-invalid }T
T{ lf-rawdecl-exhausted lf-rspec-decl-status -> lf-rspec-exhausted }T
T{ lf-rawdecl-unknown lf-rspec-decl-status -> lf-rspec-unknown }T
T{ 99 lf-rspec-decl-status -> lf-rspec-invalid }T
T{ lf-tlsubst-ok lf-rspec-subst-status -> lf-rspec-ok }T
T{ lf-tlsubst-invalid lf-rspec-subst-status -> lf-rspec-invalid }T
T{ lf-tlsubst-exhausted lf-rspec-subst-status -> lf-rspec-exhausted }T
T{ 3 lf-rspec-subst-status -> lf-rspec-invalid }T
T{ 99 lf-rspec-subst-status -> lf-rspec-invalid }T
bye
