include ../support/tester.fs
include ../support/checks.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-compare.fs
require ../../src/kernel/mixed-convert.fs
require ../support/store-faults.fs
create ids 32 cells allot
create args 4 cells allot
variable name-x variable name-y variable num-root variable num-child
: save ( index identity true | false -- ) 0= abort" setup" swap cells ids + ! ;
: h ( index -- index identity ) dup cells ids + @ ;
: ref-term ( name count -- )
  >r lf-name-generation @ args r> lf-cref-new 0= abort" ref"
  lf-cterm-new save ;
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
T{ 42 lf-lscope-context-add -> true }T
T{ lf-ssession-begin -> true }T
: setup ( -- )
0 s" x" lf-name-str 0= abort" name" name-x !
0 s" y" lf-name-str 0= abort" name" name-y !
0 lf-level-identity 0= abort" zero" args cell+ ! 0 args !
name-x @ 1 ref-term
name-x @ 1 ref-term
name-y @ 1 ref-term
name-x @ 0 ref-term
0 dup lf-level-identity 0= abort" zero" lf-hlevel-succ 0= abort" succ" 2drop
0 dup lf-level-identity 0= abort" zero" lf-hlevel-succ 0= abort" succ" 2drop
1 args ! 1 lf-level-identity drop args cell+ ! name-x @ 1 ref-term
2 args ! 2 lf-level-identity drop args cell+ ! name-x @ 1 ref-term
1 dup lf-level-identity 0= abort" level" lf-hterm-sort save
2 dup lf-level-identity 0= abort" level" lf-hterm-sort save
0 lf-hterm-bvar save
1 lf-hterm-bvar save
0 h 8 h lf-hterm-app save
1 h 8 h lf-hterm-app save
0 h 8 h lf-hterm-lam save
1 h 8 h lf-hterm-lam save
0 h 8 h lf-hterm-pi save
1 h 9 h lf-hterm-pi save ;
setup

\ Fuel left, pinned. Since plan task 4.2.2b conversion is Lean's
\ is_def_eq (src/kernel/defeq.fs): the audits, then Lean's == first (one
\ unit per node, on mixed-compare's walk, whose fuel it leaves in
\ lf-mcompare-fuel), each visit one unit; the keeping variant keeps what an
\ unknown comparison left (lf-mixed-convert leaves none). Before, the
\ walk of beta-reduced pairs left 985, 979, 993, 991 and 993 here. Since
\ plan task 5.2.2's step 9 (whnf_core of both sides, two visits) an
\ undecided pair leaves 2 units less (990 and 991 before).
: convert-fuel ( a aid b bid -- status fuel )
  1000 ['] lf-mixed-convert-keeping rs-checked lf-mconvert-fuel @ ;
T{ 0 h 1 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 0 h 1 h convert-fuel -> outcome-ok 990 }T
T{ 4 h 5 h convert-fuel -> outcome-ok 987 }T
T{ 8 h 8 h convert-fuel -> outcome-ok 996 }T
T{ 0 h 3 h convert-fuel -> outcome-unknown 988 }T
T{ 8 h 9 h convert-fuel -> outcome-unknown 989 }T
T{ lf-mcompare-fuel @ -> 995 }T
T{ 0 h 3 h 1000 lf-mixed-convert lf-mconvert-fuel @ -> outcome-unknown 0 }T

T{ 0 h 1 h 10000 lf-mixed-convert -> outcome-ok }T
T{ 0 h 2 h 10000 lf-mixed-convert -> outcome-unknown }T
T{ 4 h 5 h 10000 lf-mixed-convert -> outcome-ok }T
T{ 0 h 4 h 10000 lf-mixed-convert -> outcome-unknown }T
T{ 6 h 7 h 10000 lf-mixed-convert -> outcome-ok }T
T{ 8 h 9 h 10000 lf-mixed-convert -> outcome-unknown }T
\ Universe arity is part of a constant: x.{0} and x.{} are never equal, in
\ either order, even though their names and shared arguments agree.
T{ 0 h 3 h 10000 ' lf-mixed-convert rs-checked -> outcome-unknown }T
T{ 3 h 0 h 10000 ' lf-mixed-convert rs-checked -> outcome-unknown }T
\ Nested reduction: ((fun x => x) (fun x => x)) constant.
: more ( -- )
  0 h 8 h lf-hterm-lam save
  16 h 16 h lf-hterm-app save
  17 h 0 h lf-hterm-app save
  0 h 18 h lf-hterm-pi save
  1 h 1 h lf-hterm-pi save ;
more
T{ 18 h 0 h 10000 lf-mixed-convert -> outcome-ok }T
T{ 19 h 20 h 10000 lf-mixed-convert -> outcome-ok }T
T{ 18 h 0 h convert-fuel -> outcome-ok 972 }T
T{ 19 h 20 h convert-fuel -> outcome-ok 939 }T
variable term-start variable level-start variable serial-start variable saw-allocated
: sweep ( -- )
  lf-term-count @ term-start ! lf-level-count @ level-start !
  0 saw-allocated !
  700 0 do
    term-serial serial-start !
    19 h 20 h i lf-mixed-convert
    dup outcome-exhausted = if
      term-serial serial-start @ > if true saw-allocated ! then
    else dup outcome-ok <> abort" unexpected sweep result" then drop
    lf-term-count @ term-start @ <> abort" term leak"
    lf-level-count @ level-start @ <> abort" level leak"
  loop
  saw-allocated @ 0= abort" no exhaustion after allocation" ;
sweep
T{ 18 h 0 h -1 lf-mixed-convert -> outcome-invalid }T
T{ 18 h 0 h 0 lf-mixed-convert -> outcome-exhausted }T
\ Later stale input must be caught before the reducible first input allocates.
term-serial serial-start !
T{ 18 h 0 0 10000 lf-mixed-convert -> outcome-invalid }T
T{ term-serial -> serial-start @ }T
\ Capture avoidance under a binder: (fun x => fun y => x) z.
: capture-fixtures ( -- )
  0 h 9 h lf-hterm-lam save
  0 h 21 h lf-hterm-lam save
  22 h 8 h lf-hterm-app save
  0 h 23 h lf-hterm-lam save
  0 h 21 h lf-hterm-lam save
  0 h 8 h lf-hterm-lam save
  0 h 26 h lf-hterm-lam save ;
capture-fixtures
T{ 24 h 25 h 20000 lf-mixed-convert -> outcome-ok }T
T{ 24 h 27 h 20000 lf-mixed-convert -> outcome-unknown }T
\ Equivalent but differently represented universe arguments.
 : universe-fixtures ( -- )
42 lf-hlevel-param 0= abort" parameter" 2drop
3 0 lf-level-max 0= abort" max" drop
3 args ! 3 lf-level-identity 0= abort" level" args cell+ !
name-x @ 1 ref-term
4 args ! 4 lf-level-identity 0= abort" level" args cell+ !
name-x @ 1 ref-term ;
universe-fixtures
T{ 28 h 29 h 20000 lf-mixed-convert -> outcome-ok }T
\ Lean's no (Sort 0 against Sort 1, quick_is_def_eq on their levels) is
\ rejected since plan task 4.2.2d; the caller records its step.
: sort-zero ( -- node identity ) 0 dup lf-level-identity 0= abort" zero" lf-hterm-sort 0= abort" sort" ;
T{ sort-zero 6 h 20000 lf-mixed-convert -> outcome-rejected }T
T{ 6 h 7 h 20000 lf-mixed-convert -> outcome-ok }T
\ A bad discarded argument is audited even below a redex on either side.
 : malformed-fixture ( -- )
0 lf-term-symbolic-sort 0= abort" malformed sort" drop
16 30 lf-term-app 0= abort" application" drop ;
malformed-fixture
term-serial serial-start !
T{ 31 dup lf-term-identity drop 18 h 20000 lf-mixed-convert -> outcome-invalid }T
T{ 18 h 31 dup lf-term-identity drop 20000 lf-mixed-convert -> outcome-invalid }T
T{ term-serial -> serial-start @ }T
\ Visit order. app(bvar 0, P) against app(bvar 1, P), with P a nested Pi
\ shared by both sides: the first children differ (unknown), so a
\ pre-order walk stops before the shared second children. Both conversion
\ and comparison pin the fuel this leaves (values from the code before the
\ paired-walk refactor; visiting second children first gives 643 and 925;
\ conversion left 890 before Lean's is_def_eq, plan task 4.2.2b, whose
\ is_def_eq_app compares the functions first and stops there; 933 before
\ plan task 5.2.2's step 9, two whnf_core visits in each of the three
\ comparisons that reach it).
: order-setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  42 lf-lscope-context-add 0= abort" ctx" 42 lf-level-param 0= abort" level" drop
  lf-ssession-begin 0= abort" session"
  1 dup lf-level-identity 0= abort" lid" lf-hterm-sort save
  0 lf-hterm-bvar save 1 lf-hterm-bvar save
  0 h 0 h lf-hterm-pi save 3 h 3 h lf-hterm-pi save 4 h 4 h lf-hterm-pi save
  1 h 5 h lf-hterm-app save 2 h 5 h lf-hterm-app save ;
order-setup
T{ 6 h 7 h 1000 lf-mixed-convert-keeping lf-mconvert-fuel @ -> outcome-unknown 927 }T
T{ 6 h 7 h 1000 lf-mixed-compare lf-mcompare-fuel @ -> outcome-unknown 948 }T
bye
