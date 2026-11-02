include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/core/level-substitute.fs
include ../../src/core/mixed-level-substitute.fs
include ../../src/core/mixed-signature-probe.fs
include ../../src/core/constant-term-scope.fs
include ../../src/core/mixed-signature-audit.fs

create formals 2 cells allot
create actuals 4 cells allot
create args 4 cells allot
variable fixture-root variable root-id variable cref-id
variable result variable result-id variable constant-id
: pair! ( index addr -- ) >r dup r@ ! lf-level-identity 0= abort" identity" r> cell+ ! ;
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  11 lf-lscope-context-add 0= abort" context"
  22 lf-lscope-context-add 0= abort" context"
  33 lf-lscope-context-add 0= abort" context"
  lf-ssession-begin 0= abort" session"
  0 s" C" lf-name-str 0= abort" name" drop
  11 lf-level-param 0= abort" p" drop
  22 lf-level-param 0= abort" q" drop
  33 lf-level-param 0= abort" x" drop
  1 2 lf-level-max 0= abort" max" drop
  11 formals ! 22 formals cell+ !
  2 actuals pair! 3 actuals 2 cells + pair!
  4 args pair! 2 args 2 cells + pair!
  0 lf-name-generation @ args 2 lf-cref-new 0= abort" cref" cref-id ! drop
  0 cref-id @ lf-cterm-new 0= abort" const" constant-id ! drop
  1 dup lf-level-identity 0= abort" level" lf-hterm-sort 0= abort" sort"
  result-id ! result !
  0 constant-id @ 0 constant-id @ lf-hterm-app 0= abort" inner"
  result @ result-id @ lf-hterm-app 0= abort" app" root-id ! fixture-root ! ;

setup
: new-name ( addr len -- id ) 0 -rot lf-name-str 0= abort" name" ;
s" first" new-name constant first
s" second" new-name constant second
T{ lf-msp-begin -> true }T
lf-msp-token drop constant token
: put ( name root id -- ) >r >r token swap r> r> formals 2 500 lf-msp-put 0<> abort" put" ;
first fixture-root @ root-id @ put
second result @ result-id @ put
0 lf-hterm-bvar drop constant open-id constant open-root
variable lam-root variable lam-id variable pi-root variable pi-id
variable bad-domain-root variable bad-domain-id
: make-binders ( -- )
  result @ result-id @ open-root open-id lf-hterm-lam 0= abort" lambda"
  lam-id ! lam-root !
  result @ result-id @ open-root open-id lf-hterm-pi 0= abort" pi"
  pi-id ! pi-root !
  open-root open-id result @ result-id @ lf-hterm-lam 0= abort" bad domain"
  bad-domain-id ! bad-domain-root ! ;
make-binders
variable tc variable lc variable cc variable ts variable ls variable cs
variable saved-value
: snapshot ( -- ) lf-term-count @ tc ! lf-level-count @ lc ! lf-cref-count @ cc !
  lf-term-serial @ ts ! lf-level-serial @ ls ! lf-cref-serial @ cs ! ;
: unchanged? ( -- flag )
  lf-term-count @ tc @ = lf-level-count @ lc @ = and lf-cref-count @ cc @ = and
  lf-term-serial @ ts @ = and lf-level-serial @ ls @ = and lf-cref-serial @ cs @ = and ;
snapshot
T{ token 1000 lf-mixed-signature-audit -> lf-msp-ok }T
T{ unchanged? -> true }T
T{ token 0 lf-mixed-signature-audit -> lf-msp-exhausted }T
T{ token -1 lf-mixed-signature-audit -> lf-msp-invalid }T
T{ token 1+ 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
T{ unchanged? -> true }T
\ The shared budget covers both records and repeated constant DAG edges.
variable saw-exhausted variable saw-success
: budget-sweep ( -- )
  false saw-exhausted ! false saw-success !
  500 0 do
    token i lf-mixed-signature-audit
    dup lf-msp-exhausted = if drop true saw-exhausted ! else
      lf-msp-ok <> abort" unexpected audit status" true saw-success !
    then
    unchanged? 0= abort" audit mutated arenas"
  loop
  saw-exhausted @ 0= saw-success @ 0= or abort" incomplete budget sweep" ;
budget-sweep
\ Bodies acquire a binder, domains do not.
lam-root @ 1 cells lf-msp-roots + ! lam-id @ 1 cells lf-msp-ids + !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-ok }T
pi-root @ 1 cells lf-msp-roots + ! pi-id @ 1 cells lf-msp-ids + !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-ok }T
bad-domain-root @ 1 cells lf-msp-roots + ! bad-domain-id @ 1 cells lf-msp-ids + !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
result @ 1 cells lf-msp-roots + ! result-id @ 1 cells lf-msp-ids + !
T{ unchanged? -> true }T
\ An otherwise live root with an unbound variable fails at depth zero.
open-root 1 cells lf-msp-roots + ! open-id 1 cells lf-msp-ids + !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
result @ 1 cells lf-msp-roots + ! result-id @ 1 cells lf-msp-ids + !
T{ unchanged? -> true }T
\ Corrupt the later record; restore it after each check.
1 cells lf-msp-ids + dup @ 1+ swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
1 cells lf-msp-ids + dup @ 1- swap !
1 lf-msp-formals-at cell+ dup @ saved-value ! 11 swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
saved-value @ 1 lf-msp-formals-at cell+ !
1 lf-msp-formals-at dup @ saved-value ! 33 swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
saved-value @ 1 lf-msp-formals-at !
1 cells lf-msp-arities + dup @ saved-value ! -1 swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
saved-value @ 1 cells lf-msp-arities + !
1 cells lf-msp-names + dup @ saved-value ! 0 swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
saved-value @ 1 cells lf-msp-names + !
lf-lscope-context dup @ saved-value ! 0 swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
saved-value @ lf-lscope-context !
\ A valid context that omits a used parameter also fails.
lf-lscope-context dup @ saved-value ! 44 swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
saved-value @ lf-lscope-context !
\ Malformed nested reference metadata is rejected.
0 lf-cref-slot 3 cells + dup @ saved-value ! -1 swap !
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
saved-value @ 0 lf-cref-slot 3 cells + !
T{ unchanged? -> true }T
\ A stale nested reference is detected although the index token is current.
lf-cref-reset
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
T{ unchanged? -> false }T
\ Reset changed the reference count itself; audit changed neither count nor serial.
snapshot
T{ token 1000 lf-mixed-signature-audit -> lf-msp-invalid }T
T{ unchanged? -> true }T
bye
