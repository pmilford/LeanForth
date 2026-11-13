\ Structural transformation tests; these do not establish theorem validity.
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
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/core/literals.fs
require ../../src/core/string-literals.fs
require ../../src/kernel/mixed-shift.fs
require ../support/store-faults.fs

\ These cases number their nodes and identity serials: the term store's
\ hash-consing (compact-store plan step S3) is off here, so that each
\ constructor and each rebuilt node is a new node, as the cases count.
false lf-term-sharing!

variable rid variable cid variable sid variable rootid variable outid variable serial-before
create args 2 cells allot
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-ssession-begin 0= abort" session"
  0 s" x" lf-name-str 0= abort" name" drop
  0 args ! 0 lf-level-identity 0= abort" level" args cell+ !
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref" rid ! drop
  0 rid @ lf-cterm-new 0= abort" constant" cid ! drop
  0 args cell+ @ lf-hterm-sort 0= abort" sort" sid ! drop
  0 lf-hterm-bvar 0= abort" bound" 2drop
  1 lf-hterm-bvar 0= abort" free" 2drop
  0 3 lf-term-app 0= abort" app" drop
  2 4 lf-term-app 0= abort" app" drop
  1 5 lf-term-lam 0= abort" lam" drop
  term-serial rootid ! ;
setup
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> 10 term-serial outcome-ok }T
term-serial outid !
T{ 7 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 8 lf-term-read -> lf-tag-app 0 7 true }T
T{ 9 lf-term-read -> lf-tag-app 2 8 true }T
T{ 10 lf-term-read -> lf-tag-lam 1 9 true }T
T{ 10 outid @ 100 lf-cterm-check -> outcome-ok }T
T{ 0 cid @ 0 3 3 lf-mixed-shift -> 0 cid @ outcome-ok }T
T{ 0 cid @ 0 0 3 lf-mixed-shift -> 0 cid @ outcome-ok }T
T{ lf-mshift-fuel @ -> 1 }T
T{ 1 sid @ 0 3 3 lf-mixed-shift -> 1 sid @ outcome-ok }T
T{ 0 cid @ 0 0 1 lf-mixed-shift -> -1 0 outcome-exhausted }T
T{ 6 rootid @ -1 0 100 lf-mixed-shift -> -1 0 outcome-invalid }T
T{ 6 rootid @ 0 -1 100 lf-mixed-shift -> -1 0 outcome-invalid }T
T{ 6 rootid @ 0 0 -1 lf-mixed-shift -> -1 0 outcome-invalid }T
\ Lean's lift_loose_bvars gives a term with no loose bound variable at or
\ above the cutoff back at once (expr.cpp 455; its data word's range, plan
\ task 6.5.5): at the largest cutoff the root itself, for the audit's 9
\ and the root's visit. With fuel 9 the audit takes it all and the root's
\ visit is exhausted.
T{ 6 rootid @ lf-mshift-max 1 100 lf-mixed-shift lf-mshift-fuel @ ->
  6 rootid @ outcome-ok 90 }T
T{ 6 rootid @ lf-mshift-max 1 10 lf-mixed-shift lf-mshift-fuel @ ->
  6 rootid @ outcome-ok 0 }T
T{ 6 rootid @ lf-mshift-max 1 9 lf-mixed-shift lf-mshift-fuel @ ->
  -1 0 outcome-exhausted 0 }T
T{ lf-term-count @ -> 11 }T
\ A node without data (a bound variable past the data word's ranges,
\ core/terms.fs) is visited: a lambda at the largest cutoff cannot put its
\ body one binder deeper; it is full (out of room, not fuel) before its
\ first child is visited. That binder check is independent of fuel (ADR
\ 0008): when the root's visit takes the last unit the lambda is still
\ full, with no fuel left.
T{ lf-data-unknown lf-term-bvar -> 11 true }T
T{ 1 11 lf-term-lam -> 12 true }T
T{ 12 dup lf-term-data@ -> 12 false }T
T{ 12 term-serial lf-mshift-max 1 100 lf-mixed-shift lf-mshift-fuel @ ->
  -1 0 outcome-full 95 }T
T{ 12 term-serial lf-mshift-max 1 5 lf-mixed-shift lf-mshift-fuel @ ->
  -1 0 outcome-full 0 }T
T{ lf-term-count @ -> 13 }T
setup
\ A failed audit leaves no fuel.
T{ 6 0 0 1 100 lf-mixed-shift lf-mshift-fuel @ -> -1 0 outcome-invalid 0 }T
\ Force failure after the first child has allocated a shifted variable.
setup
T{ 2 3 lf-term-app -> 7 true }T
term-serial serial-before !
T{ 7 term-serial 0 1 5 lf-mixed-shift -> -1 0 outcome-exhausted }T
T{ lf-term-count @ -> 8 }T
T{ term-serial -> serial-before @ 1+ }T
\ A rolled-back identity cannot resurrect when its slot is reused.
term-serial outid !
T{ 0 lf-term-bvar -> 8 true }T
T{ 8 outid @ lf-hterm-valid? -> false }T
T{ 8 term-serial lf-hterm-valid? -> true }T
\ Overflow and stale references fail without retaining output: an index
\ past lf-mshift-max has no room in a cell, which is full.
T{ 3 term-serial 0 lf-mshift-max 100 lf-mixed-shift -> -1 0 outcome-invalid }T
T{ 7 7 term-identity@ 0 lf-mshift-max 100 lf-mixed-shift -> -1 0 outcome-full }T
T{ lf-term-count @ -> 9 }T
\ Shared constant occurrences each consume audit fuel; the audit checks
\ the constant's level once (constant-term-boundary's marks). The shift
\ then gives the closed node back at once, for its root's visit (Lean's
\ lift_loose_bvars, expr.cpp 449: no loose bound variable at or above the
\ cutoff).
setup
T{ 0 0 lf-term-pi -> 7 true }T
term-serial outid !
T{ 7 outid @ 0 1 4 lf-mixed-shift -> -1 0 outcome-exhausted }T
T{ 7 outid @ 0 1 5 lf-mixed-shift -> 7 outid @ outcome-ok }T
T{ lf-term-count @ -> 8 }T
\ A malformed leaf fails before allocation.
1 3 term-second!
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> -1 0 outcome-invalid }T
0 3 term-second!
\ Full arena: a variable requiring reconstruction is full, without mutation.
: fill-arena ( -- ) begin lf-term-count @ lf-term-capacity < while
  0 lf-term-bvar 0= abort" fill" drop repeat ;
fill-arena
T{ 3 3 term-identity@ 0 0 100 lf-mixed-shift ->
  3 3 term-identity@ outcome-ok }T
T{ 3 3 term-identity@ 0 1 100 lf-mixed-shift -> -1 0 outcome-full }T
T{ lf-term-count @ -> lf-term-capacity }T
setup
lf-cref-reset
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> -1 0 outcome-invalid }T
setup
lf-level-reset
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> -1 0 outcome-invalid }T
\ Interface: the fuel a shift leaves, which mixed-infer continues with
\ (audit 9 visits, shift 7), and a balanced return stack.
setup
T{ 6 rootid @ 0 1 100 lf-mixed-shift lf-mshift-fuel @ -> 10 term-serial outcome-ok 84 }T
setup
T{ 6 rootid @ 0 1 100 ' lf-mixed-shift rs-checked -> 10 term-serial outcome-ok }T
T{ 6 rootid @ 0 1 -1 ' lf-mixed-shift rs-checked -> -1 0 outcome-invalid }T
\ lf-mshift-inside shifts on fuel lent by another pass's frames record and
\ gives back what is left; nothing is rolled back.
1 0 frames: lender
setup 50 lender frame-budget drop
T{ 3 2 lender lf-mshift-inside lender frame-fuel @ -> 7 outcome-ok 49 }T
T{ 7 lf-term-read -> lf-tag-bvar 3 0 true }T
\ A shift record already in use (left busy by a THROW out of a pass, or
\ asked again from inside its own pass) refuses both entries, changing
\ nothing; frame-reset makes it idle again.
1 lf-mshift-frames frame-depth !
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> -1 0 outcome-invalid }T
T{ 3 5 lender ' lf-mshift-inside rs-checked lender frame-fuel @ ->
  -1 outcome-invalid 49 }T
T{ lf-mshift-fuel @ lf-mshift-amount @ lf-term-count @ -> 49 2 8 }T
lf-mshift-frames frame-reset
T{ 6 rootid @ 0 1 100 lf-mixed-shift -> 11 term-serial outcome-ok }T
\ The frame limit equals the store capacity, so a chain that fills the store
\ is visited all the way down: node 0 is bvar 0 and node k is lam(k-1, 0).
\ The audit costs 127 visits and the shift 64 more, reaching node 0 at the
\ 64th frame, whose shifted variable cannot be made in the full store.
: chain ( -- root identity )
  lf-term-reset lf-ssession-begin 0= abort" session" 0 lf-term-bvar 2drop
  63 0 do i 0 lf-term-lam 0= abort" chain" drop loop 63 dup lf-term-identity drop ;
T{ chain 0 1 1000 lf-mixed-shift lf-mshift-fuel @ lf-term-count @ ->
  -1 0 outcome-full 809 64 }T
\ With cutoff 1 no node has a loose bound variable at or above it (each
\ node's range is 1): the root comes back at once (Lean's
\ lift_loose_bvars, expr.cpp 449), for its visit after the audit.
T{ chain 1 1 1000 lf-mixed-shift lf-mshift-fuel @ -> 63 63 term-identity@ outcome-ok 872 }T
\ An audit failure (stale root) or negative fuel leaves zero fuel, and a raw
\ concrete Sort, which the current passes do not accept (ADR 0007), is
\ invalid for the audit and for the shift.
setup
T{ 6 rootid @ 1+ 0 1 100 lf-mixed-shift lf-mshift-fuel @ -> -1 0 outcome-invalid 0 }T
T{ 6 rootid @ 0 1 -5 lf-mixed-shift lf-mshift-fuel @ -> -1 0 outcome-invalid 0 }T
T{ 0 lf-term-sort -> 7 true }T
T{ 7 7 lf-term-identity drop 100 lf-cterm-check -> outcome-invalid }T
T{ 7 7 lf-term-identity drop 0 1 100 lf-mixed-shift -> -1 0 outcome-invalid }T
T{ lf-term-count @ -> 8 }T
\ The shift keeps its results by node and cutoff (kernel/replace-memo.fs,
\ plan task 6.5.5): N = #0 #1 outside a binder becomes #1 #2 (nodes 10 to
\ 12), under one #0 #2 (13, 14), in N (fun _ : Sort => N) shifted by 1.
setup
T{ 2 3 lf-term-app -> 7 true }T
T{ 1 7 lf-term-lam -> 8 true }T
T{ 7 8 lf-term-app -> 9 true }T
T{ 9 term-serial 0 1 100 lf-mixed-shift -> 16 term-serial outcome-ok }T
T{ 12 lf-term-read 14 lf-term-read -> lf-tag-app 10 11 true lf-tag-app 2 13 true }T
T{ 11 lf-term-read 13 lf-term-read -> lf-tag-bvar 2 0 true lf-tag-bvar 2 0 true }T
\ Literal leaves are kept as they are (coverage COV2): #0 5 "ab" shifted
\ by one is #1 5 "ab", over the same literal nodes.
setup
variable lit-node  variable str-node
: lit-leaf ( -- node ) 5 lf-hterm-cell 0= abort" lit" drop dup lit-node ! ;
: str-leaf ( -- node ) s" ab" lf-str-new ok? 0= abort" str" drop dup str-node ! ;
: app ( f a -- node ) lf-term-app 0= abort" app" ;
: lit-root ( -- node identity ) 2 lit-leaf app str-leaf app dup lf-term-identity drop ;
: parts ( node -- var-index lit str )
  dup lf-term-first@ dup lf-term-first@ lf-term-first@ swap lf-term-second@
  rot lf-term-second@ ;
T{ lit-root 0 1 100 lf-mixed-shift nip swap parts -> outcome-ok 1 lit-node @ str-node @ }T
bye
