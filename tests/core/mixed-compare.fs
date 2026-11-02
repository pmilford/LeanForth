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
include ../../src/kernel/mixed-compare.fs
create ids 32 cells allot
create args 4 cells allot
variable name-x variable name-y variable num-root variable num-child
: save ( index identity true | false -- ) 0= abort" setup" swap cells ids + ! ;
: h ( index -- index identity ) dup cells ids + @ ;
: ref-term ( name count -- )
  >r lf-name-generation @ args r> lf-cref-new 0= abort" ref"
  lf-cterm-new save ;
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
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
T{ 0 h 1 h 1000 lf-mixed-compare -> lf-mcompare-equal }T
T{ 0 h 2 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
T{ 0 h 3 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
T{ 4 h 5 h 1000 lf-mixed-compare -> lf-mcompare-equal }T
T{ 0 h 4 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
T{ 6 h 7 h 1000 lf-mixed-compare -> lf-mcompare-equal }T
T{ 8 h 9 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
T{ 10 h 11 h 1000 lf-mixed-compare -> lf-mcompare-equal }T
T{ 12 h 13 h 1000 lf-mixed-compare -> lf-mcompare-equal }T
T{ 14 h 15 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
T{ 10 h 12 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
\ Same numeric component is equal only when the structured prefix agrees.
: numeric-fixtures ( -- )
  0 10 lf-name-num 0= abort" numeric name" num-root !
  name-x @ 10 lf-name-num 0= abort" numeric child" num-child !
  num-root @ 0 ref-term num-root @ 0 ref-term num-child @ 0 ref-term ;
numeric-fixtures
T{ 16 h 17 h 1000 lf-mixed-compare -> lf-mcompare-equal }T
T{ 16 h 18 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
\ Ordered universe arguments are part of a constant's syntax.
: ordered-fixtures ( -- )
  0 args ! 0 lf-level-identity 0= abort" zero" args cell+ !
  1 args 2 cells + ! 1 lf-level-identity 0= abort" level" args 3 cells + !
  name-x @ 2 ref-term name-x @ 2 ref-term
  1 args ! 1 lf-level-identity 0= abort" level" args cell+ !
  0 args 2 cells + ! 0 lf-level-identity 0= abort" zero" args 3 cells + !
  name-x @ 2 ref-term ;
ordered-fixtures
T{ 19 h 20 h 1000 lf-mixed-compare -> lf-mcompare-equal }T
T{ 19 h 21 h 1000 lf-mixed-compare -> lf-mcompare-unknown }T
\ Two variable audits and one comparison visit require exactly three units.
T{ 8 h 8 h 2 lf-mixed-compare -> lf-mcompare-exhausted }T
T{ 8 h 8 h 3 lf-mixed-compare -> lf-mcompare-equal }T
T{ lf-mcompare-fuel @ -> 0 }T
T{ 0 h 0 h -1 lf-mixed-compare -> lf-mcompare-invalid }T
T{ 0 h 0 h 0 lf-mixed-compare -> lf-mcompare-exhausted }T
T{ 0 h 1 0 1000 lf-mixed-compare -> lf-mcompare-invalid }T
\ Corruption beneath a mismatched root must still be audited on either side.
0 0 cells lf-cterm-stamps + !
T{ 8 h 10 h 1000 lf-mixed-compare -> lf-mcompare-invalid }T
T{ 10 h 8 h 1000 lf-mixed-compare -> lf-mcompare-invalid }T
\ Audit statuses keep their meaning; an unknown or other code is invalid.
T{ lf-repr-ok lf-mcompare-audit-status -> lf-mcompare-equal }T
T{ lf-repr-invalid lf-mcompare-audit-status -> lf-mcompare-invalid }T
T{ lf-repr-exhausted lf-mcompare-audit-status -> lf-mcompare-exhausted }T
T{ 3 lf-mcompare-audit-status -> lf-mcompare-invalid }T
T{ 99 lf-mcompare-audit-status -> lf-mcompare-invalid }T
bye
