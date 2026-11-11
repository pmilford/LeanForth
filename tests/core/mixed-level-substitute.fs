include ../support/tester.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-level-substitute.fs
require ../support/store-faults.fs

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
T{ 500 run-substitution -> 7 term-serial outcome-ok }T
T{ 7 term-serial 500 lf-cterm-check -> outcome-ok }T
T{ 7 lf-term-read -> lf-tag-app 6 5 true }T
T{ 6 lf-term-read -> lf-tag-app 4 4 true }T
T{ 4 lf-term-read -> lf-tag-constant 1 lf-cref-serial @ true }T
T{ 1 lf-cref-serial @ 0 lf-cref-level -> 5 level-serial true }T
T{ 5 lf-level-read -> lf-level-tag-max 2 3 true }T
T{ 1 lf-cref-serial @ 1 lf-cref-level -> 3 3 lf-level-identity drop true }T
\ The source audit alone, as mixed-signature-audit runs it, against the
\ formals 11 and 22. Term 3 = app (app C C) (Sort 1): terms 3, 1, 2, 0, 0
\ cost five units, level 1 one unit, and each C's levels 4 = max 1 2 and
\ 2 four units: 14 in all. With only formal 11 the audit stops at level 2,
\ the second child of level 4, after eight units. Nothing is allocated.
lf-term-count @ constant source-terms
lf-level-count @ lf-cref-count @ 2constant source-counts
T{ 3 formals 2 100 lf-mls-audit-formals -> 86 outcome-ok }T
T{ 3 formals 2 14 lf-mls-audit-formals -> 0 outcome-ok }T
T{ 3 formals 2 13 lf-mls-audit-formals -> 0 outcome-exhausted }T
T{ 3 formals 1 100 lf-mls-audit-formals -> 92 outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> source-terms source-counts }T
\ Negative fuel and a negative count spend nothing. There is no other
\ limit on the count (plan task 6.2.0): 1,000 formals, the two above and
\ 998 more, give the same audit.
T{ 3 formals 2 -1 lf-mls-audit-formals -> -1 outcome-invalid }T
T{ 3 formals -1 100 lf-mls-audit-formals -> 100 outcome-invalid }T
create many-formals 1000 cells allot
: many-formals! ( -- )
  formals many-formals 2 cells move
  1000 2 do i 1000 + i cells many-formals + ! loop ;
many-formals!
T{ 3 many-formals 1000 100 lf-mls-audit-formals -> 86 outcome-ok }T
\ Source must be audited in its real session context, not merely formals.
33 formals cell+ !
T{ 500 run-substitution -> outcome-invalid }T
22 formals cell+ !
\ Even unused replacements are audited, including identities and scope.
actuals cell+ @ 1+ actuals cell+ !
T{ 500 run-substitution -> outcome-invalid }T
2 actuals pair!
44 lf-level-param drop constant out-of-scope
out-of-scope actuals pair!
T{ 500 run-substitution -> outcome-invalid }T
2 actuals pair!
T{ 0 run-substitution -> outcome-exhausted }T
T{ -1 run-substitution -> outcome-invalid }T
11 formals cell+ !
T{ 500 run-substitution -> outcome-invalid }T
22 formals cell+ !
\ Unchanged replacements preserve the original graph and allocate nothing.
1 actuals pair! 2 actuals 2 cells + pair!
lf-term-count @ variable unchanged-terms unchanged-terms !
lf-level-count @ variable unchanged-levels unchanged-levels !
lf-cref-count @ variable unchanged-crefs unchanged-crefs !
T{ 500 run-substitution -> fixture-root @ root-id @ outcome-ok }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> unchanged-terms @ unchanged-levels @ unchanged-crefs @ }T
\ Every level pair of a reference is compared: a constant over levels 1, 2
\ whose first level stays and whose second becomes 3 is rebuilt.
: kept-first-fixture ( -- index id )
  1 args pair! 2 args 2 cells + pair!
  0 lf-name-generation @ args 2 lf-cref-new 0= abort" cref"
  lf-cterm-new 0= abort" const" ;
kept-first-fixture 2constant kept-first
1 actuals pair! 3 actuals 2 cells + pair!
lf-term-count @ constant kept-index
T{ kept-first formals actuals 2 500 lf-mixed-level-substitute
   -> kept-index term-serial outcome-ok }T
T{ kept-index lf-term-read -> lf-tag-constant 3 lf-cref-serial @ true }T
T{ 3 lf-cref-serial @ 1 lf-cref-level -> 3 3 lf-level-identity drop true }T
2 actuals pair! 3 actuals 2 cells + pair!
\ Formal membership alone must not bless an out-of-context input level.
44 formals !
out-of-scope dup lf-level-identity drop lf-hterm-sort drop
variable bad-id variable bad-root bad-id ! bad-root !
T{ bad-root @ bad-id @ formals actuals 2 500 lf-mixed-level-substitute -> outcome-invalid }T
11 formals !
\ Invalid source references are rejected before any arena allocation.
lf-term-count @ variable audit-terms audit-terms !
lf-level-count @ variable audit-levels audit-levels !
lf-cref-count @ variable audit-crefs audit-crefs !
0 lf-cterm-stamp-cell @ variable saved-stamp saved-stamp !
0 0 lf-cterm-stamp-cell !
T{ 500 run-substitution -> outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> audit-terms @ audit-levels @ audit-crefs @ }T
saved-stamp @ 0 lf-cterm-stamp-cell !
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
term-serial before-term-serial ! level-serial before-level-serial !
lf-cref-serial @ before-cref-serial !
T{ bad-constant-root @ bad-constant-id @ formals actuals 2 500 lf-mixed-level-substitute -> outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> audit-terms @ audit-levels @ audit-crefs @ }T
T{ term-serial level-serial lf-cref-serial @ -> before-term-serial @ before-level-serial @ before-cref-serial @ }T
\ Sweep the shared fuel budget across audit and build. Every exhausted call
\ restores all counts, including when it consumed allocation identities.
variable saw-partial variable sweep-fuel
: fuel-sweep ( -- flag )
  false saw-partial !
  500 0 do
    i sweep-fuel !
    lf-term-count @ >r lf-level-count @ >r lf-cref-count @ >r
    level-serial >r
    sweep-fuel @ run-substitution dup outcome-exhausted = if
      drop level-serial r> > if true saw-partial ! then
      lf-cref-count @ r> <> lf-level-count @ r> <> or
      lf-term-count @ r> <> or if false unloop exit then
    else
      outcome-ok <> if r> drop r> drop r> drop r> drop false unloop exit then
      2drop r> drop r> drop r> drop r> drop
      saw-partial @ unloop exit
    then
  loop false ;
T{ fuel-sweep -> true }T
\ Stamps (plan task 6.5.5): an audit marks the terms it reaches with a new
\ stamp and erases nothing, except when the stamps run out: then the
\ column is erased and they restart at 1, so no earlier audit's mark
\ counts as this one's. An unchanged substitution leaves the root as its
\ own image; then every term holds stamp 1, as if an earlier audit had
\ reached it, the stamps run out, and the changing substitution still
\ rebuilds the term (term 7, as above), not the root's earlier image.
setup
1 actuals pair! 2 actuals 2 cells + pair!
T{ 500 run-substitution -> fixture-root @ root-id @ outcome-ok }T
2 actuals pair! 3 actuals 2 cells + pair!
: stale-stamps ( -- ) lf-term-count @ 0 ?do 1 i lf-mls-seen ! loop max-n lf-mls-stamp ! ;
stale-stamps
T{ 500 run-substitution -> 7 term-serial outcome-ok }T
T{ lf-mls-stamp @ lf-mls-reached @ -> 1 4 }T
\ The audit alone lists each reached term once (term 3, then 2, 1 and 0;
\ the repeated edges to term 0 add nothing), with a new stamp.
T{ 3 formals 2 100 lf-mls-audit-formals -> 86 outcome-ok }T
T{ lf-mls-stamp @ lf-mls-reached @ -> 2 4 }T
\ A count below zero is invalid before any allocation, and so is a stale or out-of-range actual, even when the source
\ is a bare variable that has no level to substitute.
: counts@ ( -- terms levels crefs ) lf-term-count @ lf-level-count @ lf-cref-count @ ;
: substitute-count ( count -- index id 0 | status )
  >r fixture-root @ root-id @ formals actuals r> 500 lf-mixed-level-substitute ;
setup
T{ -1 substitute-count -> outcome-invalid }T
T{ counts@ -> 4 5 1 }T
: bare-variable ( -- ) 0 lf-hterm-bvar 0= abort" bvar" root-id ! fixture-root ! ;
bare-variable
T{ fixture-root @ root-id @ -> 4 term-serial }T
actuals cell+ @ 1+ actuals cell+ !
T{ 2 substitute-count -> outcome-invalid }T
2 actuals pair! lf-level-capacity actuals !
T{ 2 substitute-count -> outcome-invalid }T
T{ counts@ -> 5 5 1 }T
2 actuals pair!
T{ 2 substitute-count -> 4 root-id @ outcome-ok }T
\ A full reference store: the constant, whose levels change, needs a new
\ reference, and there is no room for it. That is full, and every count
\ is restored.
setup
: fill-crefs ( -- )
  begin lf-cref-count @ lf-cref-capacity < while
    0 lf-name-generation @ 0 0 lf-cref-new 0= abort" fill" 2drop repeat ;
fill-crefs
counts@ 2constant full-counts constant full-terms
T{ 500 run-substitution counts@ -> outcome-full full-terms full-counts }T
setup
\ Failure after a newly allocated level and reference restores all counts:
\ the term serial runs out, which is full (out of room), not exhausted.
lf-term-count @ constant before-term
lf-level-count @ constant before-level
lf-cref-count @ constant before-cref
-1 1 rshift 2 - term-serial!
T{ 500 run-substitution -> outcome-full }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> before-term before-level before-cref }T
T{ term-serial -> -1 1 rshift }T
T{ level-serial before-level > -> true }T
T{ lf-cref-serial @ before-cref > -> true }T
\ Rolled-back identities cannot be revived by slot reuse.
before-level level-identity@ constant discarded-level-id
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
T{ 500 run-substitution -> outcome-invalid }T
bye
