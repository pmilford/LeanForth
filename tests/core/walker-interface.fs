\ Interface tests of the four lowest walkers (level scope, Sort
\ representation, session, handle audit): the fuel each check leaves,
\ which other modules read back, and the work stacks other modules borrow.
\ Expected fuel is counted by hand from the visit order: each node visit
\ costs one unit before the node is read, children are pushed first then
\ second and popped in reverse, and shared nodes are visited once per path.
include ../support/tester.fs
include ../support/checks.fs
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs

\ Level scope. Levels: 1 = param 1, 2 = succ 1, 3 = max 2 1, 4 = param 2.
\ Root 3 visits 3, 1, 2, 1: four units. Parameter 2 is not in the context.
lf-level-reset lf-lscope-context-reset
1 lf-lscope-context-add drop
1 lf-level-param 2drop  1 lf-level-succ 2drop  2 1 lf-level-max 2drop  2 lf-level-param 2drop
T{ 3 10 lf-lscope-check lf-lscope-fuel @ -> outcome-ok 6 }T
T{ 3 4 lf-lscope-check lf-lscope-fuel @ -> outcome-ok 0 }T
T{ 3 3 lf-lscope-check lf-lscope-fuel @ -> outcome-exhausted 0 }T
T{ 4 10 lf-lscope-check lf-lscope-fuel @ -> outcome-invalid 9 }T
T{ 99 7 lf-lscope-check lf-lscope-fuel @ -> outcome-invalid 7 }T
5 lf-lscope-fuel !
T{ 3 -1 lf-lscope-check lf-lscope-fuel @ -> outcome-invalid 5 }T
T{ 3 10 ' lf-lscope-check rs-checked -> outcome-ok }T

\ Sort representation. Terms: 0 = Sort 0, 1 = bvar 0, 2 = app 0 1,
\ 3 = pi 0 2. Root 3 visits 3, 2, 1, 0, 0: five units; root 2 three.
lf-term-reset
0 lf-term-sort 2drop  0 lf-term-bvar 2drop  0 1 lf-term-app 2drop  0 2 lf-term-pi 2drop
T{ 3 lf-repr-concrete 10 lf-repr-check lf-repr-fuel @ -> outcome-ok 5 }T
T{ 3 lf-repr-symbolic 10 lf-repr-check lf-repr-fuel @ -> outcome-invalid 6 }T
T{ 3 lf-repr-concrete 4 lf-repr-check lf-repr-fuel @ -> outcome-exhausted 0 }T
T{ 3 7 10 lf-repr-check lf-repr-fuel @ -> outcome-invalid 10 }T
T{ 2 3 lf-repr-concrete 10 lf-repr-check-pair lf-repr-fuel @ -> outcome-ok 2 }T
T{ 2 3 lf-repr-concrete 7 lf-repr-check-pair lf-repr-fuel @ -> outcome-exhausted 0 }T
6 lf-repr-fuel !
T{ 3 lf-repr-concrete -1 lf-repr-check lf-repr-fuel @ -> outcome-invalid 6 }T

\ Session: the representation pass and the level pass share one budget, and
\ each symbolic Sort's level check continues with it. Terms: 0 = symbolic
\ Sort of level 2, 1 = bvar 0, 2 = app 0 1. Fuel 20: representation 3 units,
\ then terms 2, 1, 0 three units, then levels 2, 1 two units: 12 left.
lf-term-reset lf-level-reset lf-lscope-context-reset
1 lf-lscope-context-add drop
1 lf-level-param 2drop  1 lf-level-succ 2drop
lf-ssession-begin drop
2 lf-term-symbolic-sort 2drop  0 lf-term-bvar 2drop  0 1 lf-term-app 2drop
T{ 2 20 lf-ssession-check lf-ssession-fuel @ -> outcome-ok 12 }T
T{ 2 8 lf-ssession-check lf-ssession-fuel @ -> outcome-ok 0 }T
T{ 2 7 lf-ssession-check lf-ssession-fuel @ -> outcome-exhausted 0 }T
T{ 2 5 lf-ssession-check lf-ssession-fuel @ -> outcome-exhausted 0 }T
T{ 2 2 lf-ssession-check lf-ssession-fuel @ -> outcome-exhausted 0 }T
9 lf-ssession-fuel !
T{ 2 -1 lf-ssession-check lf-ssession-fuel @ -> outcome-invalid 9 }T
lf-lscope-context-reset
T{ 2 20 lf-ssession-check lf-ssession-fuel @ -> outcome-invalid 20 }T

\ Handles: lf-hterm-check runs the session check, then the stamp audit
\ with the fuel it leaves. Fuel 30: session 3 + 3 + 2 units, audit 3 units.
variable term-sort-id  variable term-var-id  variable term-app-id
lf-term-reset lf-level-reset lf-lscope-context-reset
1 lf-lscope-context-add drop
lf-ssession-begin drop
1 lf-hlevel-param drop lf-hlevel-succ drop
lf-hterm-sort drop term-sort-id ! drop
0 lf-hterm-bvar drop term-var-id ! drop
0 term-sort-id @ 1 term-var-id @ lf-hterm-app drop term-app-id ! drop
T{ 2 term-app-id @ 30 lf-hterm-check lf-href-fuel @ -> outcome-ok 19 }T
T{ 2 term-app-id @ 30 ' lf-hterm-check rs-checked -> outcome-ok }T
\ A broken level stamp fails at the Sort, after three audit visits.
0 lf-hsort-level-stamp @ constant saved-level-stamp
-7 0 lf-hsort-level-stamp !
T{ 2 term-app-id @ 30 lf-hterm-check lf-href-fuel @ -> outcome-invalid 19 }T
saved-level-stamp 0 lf-hsort-level-stamp !
T{ 2 term-app-id @ 30 lf-hterm-check -> outcome-ok }T
T{ 2 -1 lf-href-check -> outcome-invalid }T
T{ 2 term-app-id 1+ 30 lf-hterm-check -> outcome-invalid }T

\ Borrowed work stacks keep their layout: pending cells, pushed at
\ pending cells from the work address, refused when full; a check started
\ afterwards resets the stack and works.
0 lf-lscope-pending !
T{ 5 lf-lscope-push lf-lscope-work @ lf-lscope-pending @ -> true 5 1 }T
lf-level-capacity lf-lscope-pending !
T{ 6 lf-lscope-push lf-lscope-pending @ -> false lf-level-capacity }T
0 lf-href-pending !
T{ 7 lf-href-push lf-href-work @ lf-href-pending @ -> true 7 1 }T
lf-term-capacity lf-href-pending !
T{ 8 lf-href-push lf-href-pending @ -> false lf-term-capacity }T
T{ 2 term-app-id @ 30 lf-hterm-check -> outcome-ok }T
bye
