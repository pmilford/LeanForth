\ Universe substitution when the heap cannot grow a list or set: each case
\ refuses one allocation of a level substitution and expects what the
\ words' stack comments promise: the documented cells, outcome full,
\ nothing thrown, and the diagnostic record naming the list's count and
\ room. Regression pins for five stack faults on these paths (found by
\ the coverage tests COV2, 2026-11-12; fixed the same day):
\ B1 lf-mls-audit-from dropped the cell below the outcome when the set of
\    reached terms could not be made (lf-mixed-level-substitute and
\    lf-mls-audit-formals each lost a cell of their caller).
\ B2 lf-mls-crowded, B4 lf-lsubst-crowded ( n -- n ) left n twice: a
\    reached list the heap could not grow gave an extra cell.
\ B3 lf-mls-image-room left the reached count, which the build then
\    reported as its status.
\ B5 lf-mls-substituted dropped a cell of its caller when the new level
\    pairs of a constant could not be held.
\ Test-only; nothing here accepts a theorem.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/diagnostics.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-level-substitute.fs
decimal

false lf-term-sharing!
: must ( flag -- ) 0= abort" crowded: refused" ;
\ Parameters p, q, x (IDs 11, 22, 33); p := q and q := x.
create formals 11 , 22 ,
create actuals 4 cells allot
create levels 2 cells allot
create cargs 4 cells allot
: level-pair! ( level addr -- ) >r dup r@ ! lf-level-identity must r> cell+ ! ;
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
11 lf-lscope-context-add must  22 lf-lscope-context-add must  33 lf-lscope-context-add must
lf-ssession-begin must
11 lf-level-param must constant p   22 lf-level-param must constant q
33 lf-level-param must constant x
p q lf-level-max must constant p-or-q
q actuals level-pair!  x actuals 2 cells + level-pair!  q levels !  x levels cell+ !
p cargs level-pair!  q cargs 2 cells + level-pair!
\ app (Sort p) (bvar U), U past the data word's range: three terms reached.
: sort-p ( -- index id ) p dup lf-level-identity must lf-hterm-sort must ;
: var-u ( -- index id ) lf-data-unknown lf-hterm-bvar must ;
sort-p var-u lf-hterm-app must 2constant app-u
\ The constant C.{p, q}: one term reached, two level pairs rebuilt.
0 s" C" lf-name-str must drop
0 lf-name-generation @ cargs 2 lf-cref-new must lf-cterm-new must 2constant c-pq
: subst-run ( index id -- index id 0 | status ) formals actuals 2 500 lf-mixed-level-substitute ;
: substituted ( -- index id 0 | status ) app-u subst-run ;

\ A run under CATCH gives its outcome, CATCH's code and the change in
\ depth (k taken, the outcome and the code left): ( outcome 0 1 ) when it
\ keeps its stack effect. A first run sizes every array, so that only the
\ one a case trims or frees grows again. Each case starts with a clear
\ diagnostic record.
: outcome-of ( index id 0 | status -- outcome ) dup ok? if nip nip then ;
: one-run ( k -- outcome ) lf-diag-clear heap-refusals ! substituted outcome-of ;
: refused ( k -- outcome code cells )
  depth >r ['] one-run catch 0 heap-refusals ! depth r> - ;
\ The record a full list or set leaves: its count and room, and the code.
: noted ( -- count room code ) lf-diag@ nip ;
\ After each case, a run with nothing refused grows the array again.
: sized ( -- outcome ) substituted outcome-of ;
: c-sized ( -- outcome ) c-pq subst-run outcome-of ;
T{ sized -> outcome-ok }T
T{ c-sized -> outcome-ok }T
\ B2: the reached list trimmed to one cell; listing the second term is
\ refused (one listed, room for one).
T{ lf-mls-reached-cells slab-trim drop 1 refused -> outcome-full 0 1 }T
T{ noted -> 1 1 lf-diag-work-stack-full }T
T{ sized -> outcome-ok }T
\ B3: the images trimmed to one cell; room for the three is refused
\ before the build makes anything.
lf-term-count @ constant terms-before
T{ lf-mls-image-cells slab-trim drop 1 refused -> outcome-full 0 1 }T
T{ noted -> 3 1 lf-diag-work-stack-full }T
T{ lf-term-count @ -> terms-before }T
T{ sized -> outcome-ok }T
\ B4: level substitution of max p q, its reached list trimmed; listing
\ the second node is refused (one listed, room for one).
: level-run ( -- outcome )
  lf-diag-clear 1 heap-refusals ! p-or-q formals levels 2 500 lf-lsubst
  dup ok? if nip then ;
: level-refused ( -- outcome code cells )
  lf-lsubst-reached-cells slab-trim drop
  depth >r ['] level-run catch 0 heap-refusals ! depth r> - ;
T{ level-refused -> outcome-full 0 2 }T
T{ noted -> 1 1 lf-diag-work-stack-full }T
T{ sized -> outcome-ok }T
\ B5: the constant's new level pairs trimmed to one pair; holding its two
\ is refused, and the caller keeps its cells.
: c-run ( k -- outcome ) lf-diag-clear heap-refusals ! c-pq subst-run outcome-of ;
: c-refused ( k -- outcome code cells )
  depth >r ['] c-run catch 0 heap-refusals ! depth r> - ;
lf-term-count @ constant c-terms-before
T{ lf-mls-arg-pairs slab-trim drop 1 c-refused -> outcome-full 0 1 }T
T{ lf-term-count @ -> c-terms-before }T
T{ c-sized -> outcome-ok }T
T{ sized -> outcome-ok }T
\ B5 after a rebuilt child: app (Sort p) C.{p, q}, its Sort p made
\ before C, so the build makes Sort q first; then the pairs are refused
\ and the stores roll back: the term made is given back (the count as
\ before), its identity is not (the serial has moved). Two runs first
\ grow the stores (one growth the second run makes, refused, is not a
\ failure), so that the one refused is the pairs' (still one pair).
: early-sort-p ( -- index id ) app-u drop lf-term-first@ dup lf-term-identity must ;
early-sort-p c-pq lf-hterm-app must 2constant app-c
: ac-run ( k -- outcome ) lf-diag-clear heap-refusals ! app-c subst-run outcome-of ;
: ac-refused ( k -- outcome code cells )
  depth >r ['] ac-run catch 0 heap-refusals ! depth r> - ;
T{ app-c subst-run outcome-of -> outcome-ok }T
T{ app-c subst-run outcome-of -> outcome-ok }T
lf-term-count @ constant ac-terms-before
lf-term-serial @ constant ac-serial-before
T{ lf-mls-arg-pairs slab-trim drop 1 ac-refused -> outcome-full 0 1 }T
T{ lf-mls-arg-pairs slab-capacity -> 1 }T
T{ lf-term-count @ -> ac-terms-before }T
T{ lf-term-serial @ ac-serial-before - -> 1 }T
T{ app-c subst-run outcome-of -> outcome-ok }T
T{ sized -> outcome-ok }T
\ B1: the set freed, its making refused: full, with nothing reached and
\ no slots; then the set is made again.
T{ lf-mls-set htab-free 1 refused -> outcome-full 0 1 }T
T{ noted -> 0 0 lf-diag-work-stack-full }T
T{ sized -> outcome-ok }T
\ B1 through the audit alone: the caller's cell below is kept, and the
\ fuel is given back unspent.
: audit-run ( -- mark fuel' status )
  lf-diag-clear 1 heap-refusals ! 7 app-u drop formals 2 500 lf-mls-audit-formals ;
: audit-refused ( -- mark fuel' status code cells )
  lf-mls-set htab-free depth >r ['] audit-run catch 0 heap-refusals ! depth r> - ;
T{ audit-refused -> 7 500 outcome-full 0 4 }T
T{ noted -> 0 0 lf-diag-work-stack-full }T
T{ app-u drop formals 2 500 lf-mls-audit-formals nip -> outcome-ok }T
T{ sized -> outcome-ok }T
bye
