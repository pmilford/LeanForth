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

variable rid variable rindex variable cid variable sid variable bid variable aid variable lid variable pid
create args 2 cells allot
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
T{ lf-ssession-begin -> true }T
: setup ( -- )
0 s" x" lf-name-str 0= abort" name" drop
0 args ! 0 lf-level-identity 0= abort" level" args cell+ !
0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref" rid ! drop
0 rid @ lf-cterm-new 0= abort" constant" cid ! drop
0 args cell+ @ lf-hterm-sort 0= abort" sort" sid ! drop
0 lf-hterm-bvar 0= abort" bvar" bid ! drop
0 cid @ 2 bid @ lf-hterm-app 0= abort" app" aid ! drop
1 sid @ 3 aid @ lf-hterm-lam 0= abort" lam" lid ! drop
1 sid @ 4 lid @ lf-hterm-pi 0= abort" pi" pid ! drop ;
setup
T{ 5 pid @ 100 lf-cterm-check -> outcome-ok }T
T{ 5 pid @ -1 lf-cterm-check -> outcome-invalid }T
T{ 5 pid @ 0 lf-cterm-check -> outcome-exhausted }T
T{ 5 pid @ 1 lf-cterm-check -> outcome-exhausted }T
T{ 0 rid @ 1+ lf-cterm-new -> false }T
\ Malformed child, payload, tag and unstamped raw constant fail closed.
variable saved-child
5 lf-term-slot cell+ @ saved-child ! 5 5 lf-term-slot cell+ !
T{ 5 pid @ 100 lf-cterm-check -> outcome-invalid }T
saved-child @ 5 lf-term-slot cell+ !
2 lf-term-slot 2 cells + 1 swap !
T{ 5 pid @ 100 lf-cterm-check -> outcome-invalid }T
0 2 lf-term-slot 2 cells + !
99 2 lf-term-slot !
T{ 5 pid @ 100 lf-cterm-check -> outcome-invalid }T
lf-tag-bvar 2 lf-term-slot !
: raw-constant ( -- ) lf-tag-constant 0 rid @ lf-term-add 0= abort" raw" drop ;
raw-constant
T{ 6 lf-term-identities 6 cells + @ 10 lf-cterm-check -> outcome-invalid }T
\ Reusing a reference slot never revives the captured reference.
lf-cref-reset
: reuse-cref ( -- ) 0 lf-name-generation @ 0 0 lf-cref-new 0= abort" reuse cref" 2drop ;
reuse-cref
T{ 0 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ Old term handles fail across reset and slot reuse, even in a new session.
lf-term-reset
T{ lf-ssession-begin -> true }T
: reuse-term ( -- ) 0 lf-hterm-bvar 0= abort" reuse term" 2drop ;
reuse-term
T{ 0 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ Construct at the final slot after prior allocations made identity exceed
\ capacity. This catches indexing the stamp array by identity instead of slot.
: fill-terms ( -- ) begin lf-term-count @ 63 < while
  0 lf-hterm-bvar 0= abort" fill" 2drop
repeat ;
fill-terms
0 lf-name-generation @ 0 0 lf-cref-new drop rid ! rindex !
63 lf-cterm-stamp-cell @ saved-child !
rindex @ rid @ lf-cterm-new drop cid ! drop
T{ 63 cid @ 10 lf-cterm-check -> outcome-ok }T
T{ cid @ lf-term-capacity > -> true }T
T{ 63 lf-cterm-stamp-cell @ -> cid @ }T
T{ 62 lf-cterm-stamp-cell @ -> 0 }T
T{ rindex @ rid @ lf-cterm-new -> false }T
lf-level-reset
T{ 63 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ Where a fixture's terms and levels begin, as store marks (lib/store.fs):
\ slots are given back through them, never by setting a count.
create term-start /store-mark allot   create level-start /store-mark allot
: fresh-marked ( -- )
  term-start lf-terms store-mark ok? 0= abort" term mark"
  level-start lf-levels store-mark ok? 0= abort" level mark" ;
: terms-back ( -- outcome ) term-start lf-terms store-rollback ;
: levels-back ( -- outcome ) level-start lf-levels store-rollback ;
\ A shared constant is visited twice but checked once, with its level:
\ the second visit costs its own unit only (the marks).
: fresh ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  fresh-marked lf-ssession-begin 0= abort" session"
  0 s" y" lf-name-str 0= abort" name" drop
  0 args ! 0 lf-level-identity 0= abort" zero" args cell+ !
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref" rid ! drop
  0 rid @ lf-cterm-new 0= abort" const" cid ! drop ;
fresh
0 cid @ 0 cid @ lf-hterm-app drop aid ! drop
T{ 1 aid @ 3 lf-cterm-check -> outcome-exhausted }T
T{ 1 aid @ 4 lf-cterm-check -> outcome-ok }T
\ Unscoped parameter rejected whether it occurs in a Sort or a cref.
: param-fixture ( -- )
  42 lf-hlevel-param 0= abort" param" args cell+ ! 1 args !
  1 args cell+ @ lf-hterm-sort 0= abort" sort" sid ! drop
  0 lf-name-generation @ args 1 lf-cref-new 0= abort" cref" rid ! rindex !
  rindex @ rid @ lf-cterm-new 0= abort" const" cid ! drop ;
param-fixture
T{ 2 sid @ 10 lf-cterm-check -> outcome-invalid }T
T{ 3 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ A malformed level is rejected through both paths, even if in scope.
\ Reset and establish the parameter context before beginning a session.
lf-term-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ lf-ssession-begin -> true }T
1 args cell+ @ lf-hterm-sort drop sid ! drop
rindex @ rid @ lf-cterm-new drop cid ! drop
T{ 0 sid @ 2 lf-cterm-check -> outcome-ok }T
T{ 1 cid @ 2 lf-cterm-check -> outcome-ok }T
1 lf-level-slot 2 cells + 1 swap !
T{ 0 sid @ 10 lf-cterm-check -> outcome-invalid }T
T{ 1 cid @ 10 lf-cterm-check -> outcome-invalid }T
0 1 lf-level-slot 2 cells + !
\ Reusing the level slot invalidates both captured identities without a reset.
T{ levels-back lf-level-count @ -> outcome-ok 1 }T
: reuse-level ( -- ) 42 lf-hlevel-param 0= abort" reuse level" 2drop ;
reuse-level
T{ 0 sid @ 10 lf-cterm-check -> outcome-invalid }T
T{ 1 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ A context reset invalidates the session even when all other data is live.
fresh
lf-lscope-context-reset
T{ 0 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ Rollback and reuse cannot inherit a constant stamp from the old allocation.
fresh
T{ terms-back lf-term-count @ -> outcome-ok 0 }T
: raw-reuse ( -- ) lf-tag-constant 0 rid @ lf-term-add 0= abort" raw reuse" drop ;
raw-reuse
T{ 0 lf-term-identities @ 10 lf-cterm-check -> outcome-invalid }T
T{ 0 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ The fuel a check leaves, which seven kernel callers continue with:
\ what remains on success, zero on exhaustion, the given fuel for an
\ invalid root, and unchanged for negative fuel.
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
T{ lf-ssession-begin -> true }T
setup
\ (The Sort shared by the Pi's and the lambda's domain is checked once:
\ its second visit costs one unit, its level none.)
T{ 5 pid @ 100 lf-cterm-check lf-cterm-fuel @ -> outcome-ok 91 }T
T{ 5 pid @ 9 lf-cterm-check lf-cterm-fuel @ -> outcome-ok 0 }T
T{ 5 pid @ 8 lf-cterm-check lf-cterm-fuel @ -> outcome-exhausted 0 }T
T{ 5 pid @ 1+ 7 lf-cterm-check lf-cterm-fuel @ -> outcome-invalid 7 }T
T{ 5 pid @ -1 lf-cterm-check lf-cterm-fuel @ -> outcome-invalid 7 }T
T{ 5 pid @ 100 ' lf-cterm-check rs-checked -> outcome-ok }T
-3 0 lf-cterm-stamp-cell !
T{ 5 pid @ 100 lf-cterm-check lf-cterm-fuel @ -> outcome-invalid 95 }T
\ The contract's outcome set: only ok, invalid, exhausted or full, which
\ the rebuilding passes pass on unnarrowed. Every index from -1 to 64 with
\ its own identity and a wrong one, at every fuel from -1 to 12, on the
\ store above, after corrupting a tag and a child, and after resetting the
\ references and the levels. Full is in the set but never reached: with
\ children earlier, the 64-item work stacks cannot overflow (counted below).
variable stray  variable oks  variable fulls
: cterm-outcome? ( outcome -- flag )
  dup outcome-invalid outcome-exhausted 1+ within over outcome-full = or swap ok? or ;
: cterm-note ( outcome -- )
  dup outcome-full = if 1 fulls +! then
  dup ok? if 1 oks +! then cterm-outcome? 0= if 1 stray +! then ;
: cterm-try ( index identity fuel -- ) lf-cterm-check cterm-note ;
: cterm-identity ( index -- index identity ) dup lf-term-identity 0= if 0 then ;
: cterm-sweep ( -- )
  65 -1 do 13 -1 do j cterm-identity i cterm-try j 77 i cterm-try loop loop ;
0 stray !  0 oks !  0 fulls !  0 dup lf-term-identity drop lf-cterm-stamp  cterm-sweep
T{ stray @ oks @ 0> -> 0 true }T
99 3 lf-term-slot !  -5 4 lf-term-slot cell+ !  cterm-sweep
lf-cref-reset cterm-sweep  lf-level-reset cterm-sweep
T{ stray @ fulls @ -> 0 0 }T
\ The predicate itself: those four pass, nothing else.
: cterm-set ( -- n ) 0 9 -2 do i cterm-outcome? 1 and + loop ;
T{ outcome-full cterm-outcome? outcome-unknown cterm-outcome? cterm-set -> true false 4 }T
bye
