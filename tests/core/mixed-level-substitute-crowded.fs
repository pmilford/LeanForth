\ KNOWN BUGS, NOT RUN BY make test: this file fails until they are fixed
\ (found by the coverage tests COV2, 2026-11-12; no source change was
\ allowed there). Run it with: gforth tests/core/mixed-level-substitute-crowded.fs
\ Each case refuses one allocation of a level substitution and expects
\ what the words' stack comments promise: one cell left, outcome full,
\ nothing thrown. Today each leaves the stack wrong:
\ B1 src/kernel/mixed-level-substitute.fs:205, lf-mls-audit-from: when
\    the set of reached terms cannot be made (lf-mls-set-ready full),
\    `ok-then? 0= if nip exit then` drops a cell more than it should
\    (ok-then? has already put the outcome in the root's place); the
\    caller lf-mls-run then underflows the stack (lf-mls-audit-formals
\    loses its caller's cell the same way).
\ B2 src/kernel/mixed-level-substitute.fs:127-129, lf-mls-crowded
\    ( n -- n ): `dup dup` leaves n twice, so a reached list the heap
\    cannot grow gives an extra cell (lf-mls-list, then lf-mls-mark).
\ B3 src/kernel/mixed-level-substitute.fs:304-307, lf-mls-image-room:
\    the same extra `dup` leaves the reached count on the stack, and the
\    build reports that count as its status.
\ B4 src/kernel/level-substitute.fs:136-138, lf-lsubst-crowded: as B2,
\    for the reached list of a level substitution.
\ Test-only; nothing here accepts a theorem.
include ../support/tester.fs
include ../support/heap-watch.fs
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
decimal

false lf-term-sharing!
: must ( flag -- ) 0= abort" crowded: refused" ;
\ Every case runs and reports; the file fails at its end when any did.
variable bugs  0 bugs !
: bug-seen ( c-addr u -- ) type source type cr 1 bugs +! ;
' bug-seen error-xt !
\ Parameters p, q, x (IDs 11, 22, 33); p := q and q := x.
create formals 11 , 22 ,
create actuals 4 cells allot
create levels 2 cells allot
: pair! ( level addr -- ) >r dup r@ ! lf-level-identity must r> cell+ ! ;
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
11 lf-lscope-context-add must  22 lf-lscope-context-add must  33 lf-lscope-context-add must
lf-ssession-begin must
11 lf-level-param must constant p   22 lf-level-param must constant q
33 lf-level-param must constant x
p q lf-level-max must constant p-or-q
q actuals pair!  x actuals 2 cells + pair!  q levels !  x levels cell+ !
\ app (Sort p) (bvar U), U past the data word's range: three terms reached.
: sort-p ( -- index id ) p dup lf-level-identity must lf-hterm-sort must ;
: var-u ( -- index id ) lf-data-unknown lf-hterm-bvar must ;
sort-p var-u lf-hterm-app must 2constant app-u
: substituted ( -- index id 0 | status ) app-u formals actuals 2 500 lf-mixed-level-substitute ;

\ The cells a run leaves and its outcome, under CATCH: ( outcome 0 1 )
\ when it keeps its stack effect. A first run sizes every array, so that
\ only the one a case trims or frees grows again.
: outcome-of ( index id 0 | status -- outcome ) dup ok? if nip nip then ;
: one-run ( k -- outcome ) heap-refusals ! substituted outcome-of ;
: refused ( k -- outcome code cells )
  depth >r ['] one-run catch 0 heap-refusals ! depth r> - ;
\ After each case, a run with nothing refused grows the array again.
: sized ( -- outcome ) substituted outcome-of ;
T{ sized -> outcome-ok }T
\ B2: the reached list trimmed to one cell, its growth refused.
T{ lf-mls-reached-cells slab-trim drop 1 refused -> outcome-full 0 1 }T
T{ sized -> outcome-ok }T
\ B3: the images trimmed to one cell, their growth refused.
T{ lf-mls-image-cells slab-trim drop 1 refused -> outcome-full 0 1 }T
T{ sized -> outcome-ok }T
\ B4: level substitution of max p q, its reached list trimmed, refused.
: level-run ( -- outcome )
  1 heap-refusals ! p-or-q formals levels 2 500 lf-lsubst dup ok? if nip then ;
T{ lf-lsubst-reached-cells slab-trim drop depth >r ' level-run catch 0 heap-refusals !
   depth r> - -> outcome-full 0 2 }T
T{ sized -> outcome-ok }T
\ B1, last (it throws): the set freed, its making refused.
T{ lf-mls-set htab-free 1 refused -> outcome-full 0 1 }T
bugs @ . .( of 4 cases failed) cr
bugs @ [if] 1 throw [then]
bye
