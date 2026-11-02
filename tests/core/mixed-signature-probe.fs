include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/level-substitute.fs
include ../../src/experimental/mixed-level-substitute.fs
include ../../src/experimental/mixed-signature-probe.fs

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
s" candidate" new-name constant candidate
s" second" new-name constant second
T{ lf-msp-begin -> true }T
lf-msp-token drop constant token
lf-term-count @ constant initial-terms
lf-level-count @ constant initial-levels
lf-cref-count @ constant initial-crefs
: put-candidate ( count fuel -- status )
  >r >r token candidate fixture-root @ root-id @ formals r> r> lf-msp-put ;
: specialize ( count fuel -- index id 0 | status )
  >r >r token candidate actuals r> r> lf-msp-specialize ;
\ Unerased serials demonstrate that a missing later formal is caught before
\ allocation, even though an earlier constant could require rebuilding.
lf-term-serial @ constant pre-term-serial
lf-level-serial @ constant pre-level-serial
lf-cref-serial @ constant pre-cref-serial
T{ 1 500 put-candidate -> lf-msp-invalid }T
T{ lf-term-serial @ lf-level-serial @ lf-cref-serial @ -> pre-term-serial pre-level-serial pre-cref-serial }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> initial-terms initial-levels initial-crefs }T
T{ 2 0 put-candidate -> lf-msp-exhausted }T
T{ 2 500 put-candidate -> lf-msp-ok }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> initial-terms initial-levels initial-crefs }T
T{ 2 500 put-candidate -> lf-msp-invalid }T
T{ 1 500 specialize -> lf-msp-invalid }T
T{ 3 500 specialize -> lf-msp-invalid }T
T{ 2 0 specialize -> lf-msp-exhausted }T
T{ token second actuals 2 500 lf-msp-specialize -> lf-msp-unknown }T
T{ token 1+ candidate actuals 2 500 lf-msp-specialize -> lf-msp-invalid }T
\ Formal IDs are copied. The nested repeated constants and sort all specialize.
99 formals ! 99 formals cell+ !
T{ 2 500 specialize -> 7 lf-term-serial @ lf-msp-ok }T
T{ 7 lf-term-read -> lf-tag-app 6 5 true }T
T{ 6 lf-term-read -> lf-tag-app 4 4 true }T
T{ 4 lf-term-read -> lf-tag-constant 1 lf-cref-serial @ true }T
T{ 1 lf-cref-serial @ 0 lf-cref-level -> 5 lf-level-serial @ true }T
T{ 5 lf-level-read -> lf-level-tag-max 2 3 true }T
actuals cell+ @ constant good-id
good-id 1+ actuals cell+ !
T{ 2 500 specialize -> lf-msp-invalid }T
good-id actuals cell+ !
\ Repeated low budgets cover preaudit and partial allocation; every failed
\ result must restore all three counts while serials may advance.
variable saw-allocation variable sfuel
: sweep ( -- flag )
  false saw-allocation !
  500 0 do
    i sfuel ! lf-term-count @ >r lf-level-count @ >r lf-cref-count @ >r
    lf-level-serial @ >r
    2 sfuel @ specialize dup lf-msp-exhausted = if
      drop lf-level-serial @ r> > if true saw-allocation ! then
      lf-cref-count @ r> <> lf-level-count @ r> <> or
      lf-term-count @ r> <> or if false unloop exit then
    else
      lf-msp-ok <> if r> drop r> drop r> drop r> drop false unloop exit then
      2drop r> drop r> drop r> drop r> drop
      saw-allocation @ unloop exit
    then
  loop false ;
T{ sweep -> true }T
\ This source uses only parameter 11, so the second formal would be unused;
\ rejection must come from the malformed formal, not missing coverage.
11 formals ! 11 formals cell+ !
T{ token second result @ result-id @ formals 2 500 lf-msp-put -> lf-msp-invalid }T
0 formals cell+ !
T{ token second result @ result-id @ formals 2 500 lf-msp-put -> lf-msp-invalid }T
T{ lf-msp-count @ -> 1 }T
22 formals cell+ !
s" control" new-name constant control
T{ token control result @ result-id @ formals 2 500 lf-msp-put -> lf-msp-ok }T
T{ lf-msp-count @ -> 2 }T
\ Force insertion coverage to fail after allocating a level and a cref.
11 formals ! 22 formals cell+ !
lf-term-count @ constant cover-terms
lf-level-count @ constant cover-levels
lf-cref-count @ constant cover-crefs
lf-level-serial @ constant cover-level-serial
lf-cref-serial @ constant cover-cref-serial
-1 1 rshift 1- lf-term-serial !
T{ token second fixture-root @ root-id @ formals 2 500 lf-msp-put -> lf-msp-exhausted }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> cover-terms cover-levels cover-crefs }T
T{ lf-level-serial @ cover-level-serial > lf-cref-serial @ cover-cref-serial > and -> true }T
T{ lf-msp-count @ -> 2 }T
\ A reset invalidates captured reference identities, even if its slot is reused.
lf-cref-reset
: reuse-ref 0 lf-name-generation @ 0 0 lf-cref-new 0= abort" cref" 2drop ;
reuse-ref
T{ 2 500 specialize -> lf-msp-invalid }T
T{ lf-msp-begin -> true }T
T{ 2 500 specialize -> lf-msp-invalid }T
lf-msp-token drop constant token2
lf-name-reset
T{ token2 second actuals 2 500 lf-msp-specialize -> lf-msp-invalid }T
\ Substitution statuses keep their meaning; an unknown or other code is invalid.
T{ lf-mlsubst-ok lf-msp-status -> lf-msp-ok }T
T{ lf-mlsubst-invalid lf-msp-status -> lf-msp-invalid }T
T{ lf-mlsubst-exhausted lf-msp-status -> lf-msp-exhausted }T
T{ 3 lf-msp-status -> lf-msp-invalid }T
T{ 99 lf-msp-status -> lf-msp-invalid }T
bye
