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
: run-substitution ( fuel -- index id 0 | status )
  >r fixture-root @ root-id @ formals actuals 2 r> lf-mixed-level-substitute ;
T{ 500 run-substitution -> 7 lf-term-serial @ lf-mlsubst-ok }T
T{ 7 lf-term-serial @ 500 lf-cterm-check -> lf-repr-ok }T
T{ 7 lf-term-read -> lf-tag-app 6 5 true }T
T{ 6 lf-term-read -> lf-tag-app 4 4 true }T
T{ 4 lf-term-read -> lf-tag-constant 1 lf-cref-serial @ true }T
T{ 1 lf-cref-serial @ 0 lf-cref-level -> 5 lf-level-serial @ true }T
T{ 5 lf-level-read -> lf-level-tag-max 2 3 true }T
T{ 1 lf-cref-serial @ 1 lf-cref-level -> 3 3 lf-level-identity drop true }T
\ Source must be audited in its real session context, not merely formals.
33 formals cell+ !
T{ 500 run-substitution -> lf-mlsubst-invalid }T
22 formals cell+ !
\ Even unused replacements are audited, including identities and scope.
actuals cell+ @ 1+ actuals cell+ !
T{ 500 run-substitution -> lf-mlsubst-invalid }T
2 actuals pair!
44 lf-level-param drop constant out-of-scope
out-of-scope actuals pair!
T{ 500 run-substitution -> lf-mlsubst-invalid }T
2 actuals pair!
T{ 0 run-substitution -> lf-mlsubst-exhausted }T
T{ -1 run-substitution -> lf-mlsubst-invalid }T
11 formals cell+ !
T{ 500 run-substitution -> lf-mlsubst-invalid }T
22 formals cell+ !
\ Unchanged replacements preserve the original graph and allocate nothing.
1 actuals pair! 2 actuals 2 cells + pair!
lf-term-count @ variable unchanged-terms unchanged-terms !
lf-level-count @ variable unchanged-levels unchanged-levels !
lf-cref-count @ variable unchanged-crefs unchanged-crefs !
T{ 500 run-substitution -> fixture-root @ root-id @ lf-mlsubst-ok }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> unchanged-terms @ unchanged-levels @ unchanged-crefs @ }T
2 actuals pair! 3 actuals 2 cells + pair!
\ Formal membership alone must not bless an out-of-context input level.
44 formals !
out-of-scope dup lf-level-identity drop lf-hterm-sort drop
variable bad-id variable bad-root bad-id ! bad-root !
T{ bad-root @ bad-id @ formals actuals 2 500 lf-mixed-level-substitute -> lf-mlsubst-invalid }T
11 formals !
\ Invalid source references are rejected before any arena allocation.
lf-term-count @ variable audit-terms audit-terms !
lf-level-count @ variable audit-levels audit-levels !
lf-cref-count @ variable audit-crefs audit-crefs !
0 cells lf-cterm-stamps + @ variable saved-stamp saved-stamp !
0 0 cells lf-cterm-stamps + !
T{ 500 run-substitution -> lf-mlsubst-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> audit-terms @ audit-levels @ audit-crefs @ }T
saved-stamp @ 0 cells lf-cterm-stamps + !
\ A later constant uses session parameter 33, absent from the formal list.
\ An earlier sibling would allocate if building began before the full audit.
variable bad-constant-root variable bad-constant-id
variable before-term-serial variable before-level-serial variable before-cref-serial
: make-bad-constant-fixture ( -- )
  3 args pair!
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref"
  lf-cterm-new 0= abort" const"
  0 constant-id @ 2swap lf-hterm-app 0= abort" app"
  bad-constant-id ! bad-constant-root ! ;
make-bad-constant-fixture
lf-term-count @ audit-terms ! lf-level-count @ audit-levels ! lf-cref-count @ audit-crefs !
lf-term-serial @ before-term-serial ! lf-level-serial @ before-level-serial !
lf-cref-serial @ before-cref-serial !
T{ bad-constant-root @ bad-constant-id @ formals actuals 2 500 lf-mixed-level-substitute -> lf-mlsubst-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> audit-terms @ audit-levels @ audit-crefs @ }T
T{ lf-term-serial @ lf-level-serial @ lf-cref-serial @ -> before-term-serial @ before-level-serial @ before-cref-serial @ }T
\ Sweep the shared fuel budget across audit and build. Every exhausted call
\ restores all counts, including when it consumed allocation identities.
variable saw-partial variable sweep-fuel
: fuel-sweep ( -- flag )
  false saw-partial !
  500 0 do
    i sweep-fuel !
    lf-term-count @ >r lf-level-count @ >r lf-cref-count @ >r
    lf-level-serial @ >r
    sweep-fuel @ run-substitution dup lf-mlsubst-exhausted = if
      drop lf-level-serial @ r> > if true saw-partial ! then
      lf-cref-count @ r> <> lf-level-count @ r> <> or
      lf-term-count @ r> <> or if false unloop exit then
    else
      lf-mlsubst-ok <> if r> drop r> drop r> drop r> drop false unloop exit then
      2drop r> drop r> drop r> drop r> drop
      saw-partial @ unloop exit
    then
  loop false ;
T{ fuel-sweep -> true }T
setup
\ Failure after a newly allocated level and reference restores all counts.
lf-term-count @ constant before-term
lf-level-count @ constant before-level
lf-cref-count @ constant before-cref
-1 1 rshift 2 - lf-term-serial !
T{ 500 run-substitution -> lf-mlsubst-exhausted }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> before-term before-level before-cref }T
T{ lf-term-serial @ -> -1 1 rshift }T
T{ lf-level-serial @ before-level > -> true }T
T{ lf-cref-serial @ before-cref > -> true }T
\ Rolled-back identities cannot be revived by slot reuse.
lf-level-identities before-level cells + @ constant discarded-level-id
T{ before-level lf-level-count @ = -> true }T
: reuse-level 33 lf-level-param 0= abort" reuse" drop ;
reuse-level
T{ before-level discarded-level-id lf-hlevel-valid? -> false }T
\ Reuse a rolled-back cref slot; its discarded identity remains stale.
lf-cref-storage before-cref lf-cref-slot-cells * cells + @ constant discarded-cref-id
: reuse-discarded-cref 0 lf-name-generation @ 0 0 lf-cref-new 0= abort" reuse discarded cref" 2drop ;
reuse-discarded-cref
T{ before-cref discarded-cref-id lf-cref-valid? -> false }T
\ Reusing a captured original reference invalidates the original input.
lf-cref-reset
: reuse-cref 0 lf-name-generation @ 0 0 lf-cref-new 0= abort" reuse cref" 2drop ;
reuse-cref
T{ 500 run-substitution -> lf-mlsubst-invalid }T
bye
