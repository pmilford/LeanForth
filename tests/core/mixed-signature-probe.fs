include ../support/tester.fs
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-level-substitute.fs
require ../../src/kernel/mixed-signature-probe.fs

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
T{ 1 500 put-candidate -> outcome-invalid }T
T{ lf-term-serial @ lf-level-serial @ lf-cref-serial @ -> pre-term-serial pre-level-serial pre-cref-serial }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> initial-terms initial-levels initial-crefs }T
T{ 2 0 put-candidate -> outcome-exhausted }T
T{ 2 500 put-candidate -> outcome-ok }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> initial-terms initial-levels initial-crefs }T
T{ 2 500 put-candidate -> outcome-invalid }T
T{ 1 500 specialize -> outcome-invalid }T
T{ 3 500 specialize -> outcome-invalid }T
T{ 2 0 specialize -> outcome-exhausted }T
T{ token second actuals 2 500 lf-msp-specialize -> outcome-unknown }T
T{ token 1+ candidate actuals 2 500 lf-msp-specialize -> outcome-invalid }T
\ Formal IDs are copied. The nested repeated constants and sort all specialize.
99 formals ! 99 formals cell+ !
T{ 2 500 specialize -> 7 lf-term-serial @ outcome-ok }T
T{ 7 lf-term-read -> lf-tag-app 6 5 true }T
T{ 6 lf-term-read -> lf-tag-app 4 4 true }T
T{ 4 lf-term-read -> lf-tag-constant 1 lf-cref-serial @ true }T
T{ 1 lf-cref-serial @ 0 lf-cref-level -> 5 lf-level-serial @ true }T
T{ 5 lf-level-read -> lf-level-tag-max 2 3 true }T
actuals cell+ @ constant good-id
good-id 1+ actuals cell+ !
T{ 2 500 specialize -> outcome-invalid }T
good-id actuals cell+ !
\ lf-msp-specialize-fuel gives the same result and status, and on success
\ also the fuel the substitution left, which mixed-infer continues with.
lf-term-count @ constant spec-terms
T{ token candidate actuals 2 500 lf-msp-specialize-fuel rot drop
   -> spec-terms 3 + 459 outcome-ok }T
T{ token candidate actuals 2 500 lf-msp-specialize-fuel 2swap 2drop
   -> lf-mls-fuel @ outcome-ok }T
T{ token second actuals 2 500 lf-msp-specialize-fuel -> outcome-unknown }T
T{ token candidate actuals 2 0 lf-msp-specialize-fuel -> outcome-exhausted }T
T{ token candidate actuals 2 -1 lf-msp-specialize-fuel -> outcome-invalid }T
\ Repeated low budgets cover preaudit and partial allocation; every failed
\ result must restore all three counts while serials may advance.
variable saw-allocation variable sfuel
: sweep ( -- flag )
  false saw-allocation !
  500 0 do
    i sfuel ! lf-term-count @ >r lf-level-count @ >r lf-cref-count @ >r
    lf-level-serial @ >r
    2 sfuel @ specialize dup outcome-exhausted = if
      drop lf-level-serial @ r> > if true saw-allocation ! then
      lf-cref-count @ r> <> lf-level-count @ r> <> or
      lf-term-count @ r> <> or if false unloop exit then
    else
      outcome-ok <> if r> drop r> drop r> drop r> drop false unloop exit then
      2drop r> drop r> drop r> drop r> drop
      saw-allocation @ unloop exit
    then
  loop false ;
T{ sweep -> true }T
\ This source uses only parameter 11, so the second formal would be unused;
\ rejection must come from the malformed formal, not missing coverage.
11 formals ! 11 formals cell+ !
T{ token second result @ result-id @ formals 2 500 lf-msp-put -> outcome-invalid }T
0 formals cell+ !
T{ token second result @ result-id @ formals 2 500 lf-msp-put -> outcome-invalid }T
T{ lf-msp-count @ -> 1 }T
22 formals cell+ !
s" control" new-name constant control
T{ token control result @ result-id @ formals 2 500 lf-msp-put -> outcome-ok }T
T{ lf-msp-count @ -> 2 }T
\ Force insertion coverage to fail after allocating a cref: the term serial
\ runs out, which is full, not exhausted.
11 formals ! 22 formals cell+ !
lf-term-count @ constant cover-terms
lf-level-count @ constant cover-levels
lf-cref-count @ constant cover-crefs
lf-level-serial @ constant cover-level-serial
lf-cref-serial @ constant cover-cref-serial
-1 1 rshift 1- lf-term-serial !
T{ token second fixture-root @ root-id @ formals 2 500 lf-msp-put -> outcome-full }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> cover-terms cover-levels cover-crefs }T
\ Coverage substitutes zero for p and q: C.{max p q, q} becomes C.{0, 0},
\ since Lean's mk_max gives 0 for max 0 0 (ADR 0011, Amendment 1), so no
\ level is allocated, only the reference.
T{ lf-level-serial @ cover-level-serial = lf-cref-serial @ cover-cref-serial > and -> true }T
T{ lf-msp-count @ -> 2 }T
\ A reset invalidates captured reference identities, even if its slot is reused.
lf-cref-reset
: reuse-ref 0 lf-name-generation @ 0 0 lf-cref-new 0= abort" cref" 2drop ;
reuse-ref
T{ 2 500 specialize -> outcome-invalid }T
T{ lf-msp-begin -> true }T
T{ 2 500 specialize -> outcome-invalid }T
lf-msp-token drop constant token2
lf-name-reset
T{ token2 second actuals 2 500 lf-msp-specialize -> outcome-invalid }T
\ The statuses are the shared outcomes, with their established values.
T{ outcome-ok outcome-invalid outcome-exhausted outcome-unknown -> 0 1 2 3 }T
T{ outcome-ok outcome-invalid outcome-exhausted outcome-unknown
   -> outcome-ok outcome-invalid outcome-exhausted outcome-unknown }T
\ The lifetime generation saturates: the last begin before the limit
\ succeeds, the next poisons the generation to -1, and it stays there.
max-n 1- lf-msp-generation !
T{ lf-msp-begin lf-msp-generation @ -> true max-n }T
T{ lf-msp-begin lf-msp-generation @ lf-msp-active @ -> false -1 0 }T
T{ lf-msp-begin lf-msp-generation @ -> false -1 }T
bye
