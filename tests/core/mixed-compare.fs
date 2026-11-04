include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-compare.fs
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
T{ 0 h 1 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 0 h 2 h 1000 lf-mixed-compare -> outcome-unknown }T
T{ 0 h 3 h 1000 lf-mixed-compare -> outcome-unknown }T
T{ 4 h 5 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 0 h 4 h 1000 lf-mixed-compare -> outcome-unknown }T
T{ 6 h 7 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 8 h 9 h 1000 lf-mixed-compare -> outcome-unknown }T
T{ 10 h 11 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 12 h 13 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 14 h 15 h 1000 lf-mixed-compare -> outcome-unknown }T
T{ 10 h 12 h 1000 lf-mixed-compare -> outcome-unknown }T
\ Fuel left, pinned against the previous implementation: each audit visit
\ and each term, level and name-component comparison costs one unit; the
\ arity check costs nothing.
: compare-fuel ( a aid b bid -- status fuel )
  1000 ['] lf-mixed-compare rs-checked lf-mcompare-fuel @ ;
T{ 0 h 1 h compare-fuel -> outcome-ok 992 }T
T{ 4 h 5 h compare-fuel -> outcome-ok 989 }T
T{ 12 h 13 h compare-fuel -> outcome-ok 986 }T
T{ 14 h 15 h compare-fuel -> outcome-unknown 986 }T
T{ 0 h 2 h compare-fuel -> outcome-unknown 994 }T
T{ 0 h 3 h compare-fuel -> outcome-unknown 996 }T
\ Same numeric component is equal only when the structured prefix agrees.
: numeric-fixtures ( -- )
  0 10 lf-name-num 0= abort" numeric name" num-root !
  name-x @ 10 lf-name-num 0= abort" numeric child" num-child !
  num-root @ 0 ref-term num-root @ 0 ref-term num-child @ 0 ref-term ;
numeric-fixtures
T{ 16 h 17 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 16 h 18 h 1000 lf-mixed-compare -> outcome-unknown }T
\ Ordered universe arguments are part of a constant's syntax.
: ordered-fixtures ( -- )
  0 args ! 0 lf-level-identity 0= abort" zero" args cell+ !
  1 args 2 cells + ! 1 lf-level-identity 0= abort" level" args 3 cells + !
  name-x @ 2 ref-term name-x @ 2 ref-term
  1 args ! 1 lf-level-identity 0= abort" level" args cell+ !
  0 args 2 cells + ! 0 lf-level-identity 0= abort" zero" args 3 cells + !
  name-x @ 2 ref-term ;
ordered-fixtures
T{ 19 h 20 h 1000 lf-mixed-compare -> outcome-ok }T
T{ 19 h 21 h 1000 lf-mixed-compare -> outcome-unknown }T
\ Two variable audits and one comparison visit require exactly three units.
T{ 8 h 8 h 2 lf-mixed-compare -> outcome-exhausted }T
T{ 8 h 8 h 3 lf-mixed-compare -> outcome-ok }T
T{ lf-mcompare-fuel @ -> 0 }T
T{ 0 h 0 h -1 lf-mixed-compare -> outcome-invalid }T
T{ 0 h 0 h 0 lf-mixed-compare -> outcome-exhausted }T
T{ 0 h 1 0 1000 lf-mixed-compare -> outcome-invalid }T
\ Corruption beneath a mismatched root must still be audited on either side.
0 0 lf-cterm-stamp-cell !
T{ 8 h 10 h 1000 lf-mixed-compare -> outcome-invalid }T
T{ 10 h 8 h 1000 lf-mixed-compare -> outcome-invalid }T
\ Names compare one component per unit of the given walk's fuel, down to the
\ anonymous root; the walk's work stack is not used.
4 walk2: name-walk
: names ( a b fuel -- outcome fuel' )
  name-walk walk-fuel ! name-walk ['] lf-mcompare-names rs-checked name-walk walk-fuel @ ;
T{ name-x @ name-x @ 5 names -> outcome-ok 3 }T
T{ 0 0 5 names -> outcome-ok 4 }T
T{ name-x @ name-y @ 5 names -> outcome-unknown 4 }T
T{ name-x @ 0 5 names -> outcome-unknown 4 }T
T{ num-root @ num-child @ 5 names -> outcome-unknown 3 }T
\ Names that differ only in a numeric component differ, as Lean's x.10
\ and x.11 (Name.num with 10 and 11) do; the last component decides.
variable num-sibling
: sibling-fixture ( -- ) name-x @ 11 lf-name-num 0= abort" numeric sibling" num-sibling ! ;
sibling-fixture
T{ num-child @ num-sibling @ 5 names -> outcome-unknown 4 }T
T{ num-sibling @ num-child @ 5 names -> outcome-unknown 4 }T
T{ num-child @ num-child @ 3 names -> outcome-ok 0 }T
T{ num-child @ num-child @ 2 names -> outcome-exhausted 0 }T
T{ 0 0 0 names -> outcome-exhausted 0 }T
T{ name-walk walk-pending @ -> 0 }T
\ Guard paths that the audits make unreachable from lf-mixed-compare: a
\ full work stack is full (with one pair of room left, the second push is
\ refused), an unallocated node and an unknown tag are invalid.
2 walk2: tiny
T{ tiny walk-capacity @ tiny walk-pending ! 0 lf-term-slot dup tiny lf-mcompare-children -> outcome-full }T
T{ 2 tiny walk-pending ! 0 lf-term-slot dup tiny lf-mcompare-children
  tiny walk-pending @ -> outcome-full 4 }T
T{ lf-term-count @ tiny walk-node ! 0 tiny walk-context ! tiny lf-mcompare-visit -> outcome-invalid }T
T{ 0 lf-term-slot dup tiny lf-tag-sort lf-mcompare-dispatch -> outcome-invalid }T
bye
