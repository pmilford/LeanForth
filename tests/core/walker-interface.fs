\ Interface tests of the four lowest walkers (level scope, Sort
\ representation, session, handle audit) and the two substitution passes
\ built on walk records: the fuel each check leaves, which other modules
\ read back, and that no pass disturbs another module's work stack.
\ Expected fuel is counted by hand from the visit order: each node visit
\ costs one unit before the node is read, children are pushed first then
\ second and popped in reverse, and shared nodes are visited once per path.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/level-substitute.fs
require ../../src/kernel/mixed-level-substitute.fs
require ../support/store-faults.fs

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

\ Mixed substitution of parameter 1 by zero in term 2 (app of the Sort
\ over level 2 = succ 1, and bvar 0), all passes sharing one budget: the
\ actual's scope 1 unit, the graph check 3 term and 2 level visits, the
\ source audit 4 (the app, the Sort and its 2 levels: bvar 0 has no
\ universe parameter, so it is neither visited nor rebuilt, Lean's
\ has_param_univ test, plan step S4; 5 before), then the Sort's level
\ substitution 3 (actual 1, source 2): 13 units. mixed-signature-audit
\ runs the audit alone: 4 units.
create mls-formals 1 ,
create mls-actuals 0 , 0 lf-level-identity drop ,
T{ 2 term-app-id @ mls-formals mls-actuals 1 30 lf-mixed-level-substitute
   rot drop lf-mls-fuel @ -> term-serial outcome-ok 17 }T
T{ 2 term-app-id @ mls-formals mls-actuals 1 13 lf-mixed-level-substitute
   rot drop lf-mls-fuel @ -> term-serial outcome-ok 0 }T
T{ 2 term-app-id @ mls-formals mls-actuals 1 12 lf-mixed-level-substitute
   lf-mls-fuel @ -> outcome-exhausted 0 }T
T{ 2 term-app-id @ mls-formals mls-actuals 1 30 ' lf-mixed-level-substitute rs-checked
   rot drop -> term-serial outcome-ok }T
T{ 2 mls-formals 1 30 lf-mls-audit-formals -> 26 outcome-ok }T
\ The substitution walks its own record, not the handle audit's stack.
0 lf-href-walker walk-pending !  9 lf-href-walker walk-push drop
T{ 2 term-app-id @ mls-formals mls-actuals 1 30 lf-mixed-level-substitute
   nip nip lf-href-walker walk-pending @ lf-href-walker walk-stack @
   -> outcome-ok 1 9 }T

\ Level substitution: inputs (one visit per actual), then the source walk,
\ first child first. Levels 3 = max 1 2, 4 = param 3 (in the context but
\ not a formal), 5 = max 4 3. Swapping parameters 1 and 2 in level 3 costs
\ 2 + 3 units. In level 5 the source walk stops at its first child, level
\ 4, after 2 visits; visiting level 3 first would cost 3 more.
lf-level-reset lf-lscope-context-reset
1 lf-lscope-context-add drop 2 lf-lscope-context-add drop 3 lf-lscope-context-add drop
1 lf-level-param 2drop  2 lf-level-param 2drop  1 2 lf-level-max 2drop
3 lf-level-param 2drop  4 3 lf-level-max 2drop
create subst-formals 1 , 2 ,
create subst-actuals 2 , 1 ,
T{ 3 subst-formals subst-actuals 2 20 lf-lsubst lf-lsubst-fuel @ -> 6 outcome-ok 15 }T
T{ 3 subst-formals subst-actuals 2 4 lf-lsubst lf-lsubst-fuel @ -> outcome-exhausted 0 }T
T{ 5 subst-formals subst-actuals 2 20 lf-lsubst lf-lsubst-fuel @ -> outcome-invalid 16 }T
\ The same substitution again gives the same level (hash-consed levels).
T{ 3 subst-formals subst-actuals 2 20 ' lf-lsubst rs-checked -> 6 outcome-ok }T

\ A handle audit starts from an empty work stack, even when the last walk
\ left it full. A checker's walk grows past its first room (plan task
\ 6.2.0): the push moves the stack to the heap, keeping its items.
lf-term-capacity lf-href-walker walk-pending !
7 lf-href-walker walk-stack !
T{ 8 lf-href-walker walk-push lf-href-walker walk-pending @ -> true lf-term-capacity 1+ }T
T{ lf-href-walker walk-stack @ lf-href-walker walk-capacity @ lf-term-capacity > -> 7 true }T
lf-term-reset lf-level-reset lf-lscope-context-reset
1 lf-lscope-context-add drop
lf-ssession-begin drop
1 lf-hlevel-param drop lf-hlevel-succ drop
lf-hterm-sort drop term-sort-id ! drop
0 lf-hterm-bvar drop term-var-id ! drop
0 term-sort-id @ 1 term-var-id @ lf-hterm-app drop term-app-id ! drop
T{ 2 term-app-id @ 30 lf-hterm-check -> outcome-ok }T
bye
