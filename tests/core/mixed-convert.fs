include ../support/tester.fs
include ../support/checks.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/mixed-compare.fs
include ../../src/experimental/mixed-shift.fs
include ../../src/experimental/mixed-instantiate.fs
include ../../src/experimental/mixed-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/mixed-convert.fs
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

\ Dependency statuses keep their meaning; unrecognized values are never equal.
T{ lf-mbeta-ok lf-mconvert-beta-status -> lf-mconvert-equal }T
T{ lf-mbeta-invalid lf-mconvert-beta-status -> lf-mconvert-invalid }T
T{ lf-mbeta-exhausted lf-mconvert-beta-status -> lf-mconvert-exhausted }T
T{ 3 lf-mconvert-beta-status -> lf-mconvert-invalid }T
T{ 99 lf-mconvert-beta-status -> lf-mconvert-invalid }T
T{ lf-mcompare-equal lf-mconvert-compare-status -> lf-mconvert-equal }T
T{ lf-mcompare-invalid lf-mconvert-compare-status -> lf-mconvert-invalid }T
T{ lf-mcompare-exhausted lf-mconvert-compare-status -> lf-mconvert-exhausted }T
T{ lf-mcompare-unknown lf-mconvert-compare-status -> lf-mconvert-unknown }T
T{ 99 lf-mconvert-compare-status -> lf-mconvert-invalid }T

T{ 0 h 1 h 10000 lf-mixed-convert -> lf-mconvert-equal }T
T{ 0 h 2 h 10000 lf-mixed-convert -> lf-mconvert-unknown }T
T{ 4 h 5 h 10000 lf-mixed-convert -> lf-mconvert-equal }T
T{ 0 h 4 h 10000 lf-mixed-convert -> lf-mconvert-unknown }T
T{ 6 h 7 h 10000 lf-mixed-convert -> lf-mconvert-equal }T
T{ 8 h 9 h 10000 lf-mixed-convert -> lf-mconvert-unknown }T
\ Universe arity is part of a constant: x.{0} and x.{} are never equal, in
\ either order, even though their names and shared arguments agree.
T{ 0 h 3 h 10000 ' lf-mixed-convert rs-checked -> lf-mconvert-unknown }T
T{ 3 h 0 h 10000 ' lf-mixed-convert rs-checked -> lf-mconvert-unknown }T
\ Nested reduction: ((fun x => x) (fun x => x)) constant.
: more ( -- )
  0 h 8 h lf-hterm-lam save
  16 h 16 h lf-hterm-app save
  17 h 0 h lf-hterm-app save
  0 h 18 h lf-hterm-pi save
  1 h 1 h lf-hterm-pi save ;
more
T{ 18 h 0 h 10000 lf-mixed-convert -> lf-mconvert-equal }T
T{ 19 h 20 h 10000 lf-mixed-convert -> lf-mconvert-equal }T
variable term-start variable level-start variable serial-start variable saw-allocated
: sweep ( -- )
  lf-term-count @ term-start ! lf-level-count @ level-start !
  0 saw-allocated !
  700 0 do
    lf-term-serial @ serial-start !
    19 h 20 h i lf-mixed-convert
    dup lf-mconvert-exhausted = if
      lf-term-serial @ serial-start @ > if true saw-allocated ! then
    else dup lf-mconvert-equal <> abort" unexpected sweep result" then drop
    lf-term-count @ term-start @ <> abort" term leak"
    lf-level-count @ level-start @ <> abort" level leak"
  loop
  saw-allocated @ 0= abort" no exhaustion after allocation" ;
sweep
T{ 18 h 0 h -1 lf-mixed-convert -> lf-mconvert-invalid }T
T{ 18 h 0 h 0 lf-mixed-convert -> lf-mconvert-exhausted }T
\ Later stale input must be caught before the reducible first input allocates.
lf-term-serial @ serial-start !
T{ 18 h 0 0 10000 lf-mixed-convert -> lf-mconvert-invalid }T
T{ lf-term-serial @ -> serial-start @ }T
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
T{ 24 h 25 h 20000 lf-mixed-convert -> lf-mconvert-equal }T
T{ 24 h 27 h 20000 lf-mixed-convert -> lf-mconvert-unknown }T
\ Equivalent but differently represented universe arguments.
 : universe-fixtures ( -- )
42 lf-hlevel-param 0= abort" parameter" 2drop
3 0 lf-level-max 0= abort" max" drop
3 args ! 3 lf-level-identity 0= abort" level" args cell+ !
name-x @ 1 ref-term
4 args ! 4 lf-level-identity 0= abort" level" args cell+ !
name-x @ 1 ref-term ;
universe-fixtures
T{ 28 h 29 h 20000 lf-mixed-convert -> lf-mconvert-equal }T
\ A bad discarded argument is audited even below a redex on either side.
 : malformed-fixture ( -- )
0 lf-term-symbolic-sort 0= abort" malformed sort" drop
16 30 lf-term-app 0= abort" application" drop ;
malformed-fixture
lf-term-serial @ serial-start !
T{ 31 dup lf-term-identity drop 18 h 20000 lf-mixed-convert -> lf-mconvert-invalid }T
T{ 18 h 31 dup lf-term-identity drop 20000 lf-mixed-convert -> lf-mconvert-invalid }T
T{ lf-term-serial @ -> serial-start @ }T
bye
