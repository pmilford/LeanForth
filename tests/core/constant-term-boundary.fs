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
require ../support/store-faults.fs

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
5 lf-term-first@ saved-child ! 5 5 term-first!
T{ 5 pid @ 100 lf-cterm-check -> outcome-invalid }T
saved-child @ 5 term-first!
1 2 term-second!
T{ 5 pid @ 100 lf-cterm-check -> outcome-invalid }T
0 2 term-second!
99 2 term-tag!
T{ 5 pid @ 100 lf-cterm-check -> outcome-invalid }T
lf-tag-bvar 2 term-tag!
\ A raw node with a constant's fields is a forgery only while sharing is
\ off: with it on, the term table gives the stamped constant back
\ (compact-store plan step S4), which is that constant.
T{ lf-tag-constant 0 0 lf-term-add -> 0 true }T
\ A constant's fields are its reference's index and 0; the reference's
\ identity is stamped beside it, a full cell (step S4).
T{ 0 lf-term-read 0 lf-cterm-ref -> lf-tag-constant 0 0 true 0 rid @ }T
\ lf-term-const?: a constant node, not a node of another kind.
T{ 0 lf-term-const? lf-tag-bvar 0 term-tag! 0 lf-term-const? -> true false }T
lf-tag-constant 0 term-tag!
T{ 0 lf-term-const? -> true }T
: raw-constant ( -- )
  false lf-term-sharing! lf-tag-constant 0 rid @ lf-term-add 0= abort" raw" drop
  true lf-term-sharing! ;
raw-constant
T{ 6 6 term-identity@ 10 lf-cterm-check -> outcome-invalid }T
\ An unstamped node in the table is never given out as a constant: for a
\ new reference, a raw node with its fields is entered while sharing, and
\ lf-cterm-new then makes and stamps a node of its own.
: forged-make ( -- ref rid node )
  0 lf-name-generation @ args 0 lf-cref-new 0= abort" cref"
  over lf-tag-constant swap 0 lf-term-add 0= abort" forged" ;
forged-make constant forged 2constant forged-ref
T{ forged forged term-identity@ 10 lf-cterm-check -> outcome-invalid }T
T{ forged-ref lf-cterm-new rot forged - -> term-serial true 1 }T
T{ forged 1+ dup term-identity@ 10 lf-cterm-check -> outcome-ok }T
T{ forged-ref lf-cterm-new -> forged 1+ term-serial true }T
\ No 32-bit identity on constants (review rvS36 L1): a reference whose
\ identity is past 2^32 - 1 makes a constant that is not full and passes
\ the audit (before step S4 its identity filled a 32-bit field, and every
\ constant after the 2^32 - 1st reference was full). Run where a cell is
\ wider than 32 bits; the serial is then put back.
lf-cref-serial @ constant saved-cref-serial
: wide-ref ( -- ref rid )
  u32-mask lf-cref-serial !  0 s" wide" lf-name-str 0= abort" wide name"
  lf-name-generation @ args 1 lf-cref-new 0= abort" wide cref" ;
u32-mask max-n u< [if]
wide-ref 2constant wide
T{ wide nip u32-mask u> wide lf-cterm-new -> true lf-term-count @ 1- term-serial true }T
T{ lf-term-count @ 1- dup term-identity@ 10 lf-cterm-check -> outcome-ok }T
T{ lf-term-count @ 1- lf-term-read lf-term-count @ 1- lf-cterm-ref
  -> lf-tag-constant wide drop 0 true wide }T
[then]
saved-cref-serial lf-cref-serial !
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
: fill-terms ( -- ) false lf-term-sharing! begin lf-term-count @ 63 < while
  0 lf-hterm-bvar 0= abort" fill" 2drop
repeat true lf-term-sharing! ;
fill-terms
0 lf-name-generation @ 0 0 lf-cref-new drop rid ! rindex !
63 lf-term-own-stamp @ saved-child !
rindex @ rid @ lf-cterm-new drop cid ! drop
T{ 63 cid @ 10 lf-cterm-check -> outcome-ok }T
T{ cid @ lf-term-capacity > -> true }T
T{ 63 lf-term-own-stamp @ -> cid @ }T
T{ 62 lf-term-own-stamp @ -> 0 }T
T{ rindex @ rid @ lf-cterm-new -> false }T
lf-level-reset
T{ 63 cid @ 10 lf-cterm-check -> outcome-invalid }T
\ Where a fixture's terms and levels begin, as store marks (lib/store.fs):
\ slots are given back through them, never by setting a count.
create term-start /store-mark allot   create level-start /store-mark allot
: fresh-marked ( -- )
  term-start lf-terms store-mark ok? 0= abort" term mark"
  level-start lf-levels store-mark ok? 0= abort" level mark" ;
: terms-back ( -- outcome ) term-start lf-term-rollback ;
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
1 1 level-second!
T{ 0 sid @ 10 lf-cterm-check -> outcome-invalid }T
T{ 1 cid @ 10 lf-cterm-check -> outcome-invalid }T
0 1 level-second!
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
T{ 0 0 term-identity@ 10 lf-cterm-check -> outcome-invalid }T
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
-3 0 lf-term-own-stamp !
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
99 3 term-tag!  -5 4 term-first!  cterm-sweep
lf-cref-reset cterm-sweep  lf-level-reset cterm-sweep
T{ stray @ fulls @ -> 0 0 }T
\ The predicate itself: those four pass, nothing else.
: cterm-set ( -- n ) 0 9 -2 do i cterm-outcome? 1 and + loop ;
T{ outcome-full cterm-outcome? outcome-unknown cterm-outcome? cterm-set -> true false 4 }T

\ ---------------------------------------------------------------------------
\ The audit memo (compact-store plan step S6 (c); ADR 0014 Amendment 4).
\ On, a node a run checked is not visited again in its epoch and a checked
\ root costs no fuel; off, and outside a check (lf-memo-auto: this file
\ loads no checker), every audit runs in full.
: cterm-fuel ( index identity -- outcome fuel ) 100 lf-cterm-check lf-cterm-fuel @ ;
variable xid  variable fid
: app! ( left lid right rid -- ) lf-hterm-app 0= abort" app" xid ! drop ;
: local! ( -- ) 0 lf-lctx-local outcome-ok <> abort" local" term-identity@ fid ! ;
lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
T{ lf-ssession-begin -> true }T
setup
T{ 5 pid @ cterm-fuel 5 pid @ cterm-fuel -> outcome-ok 91 outcome-ok 91 }T
lf-memo-on lf-audit-memo!
T{ 5 pid @ cterm-fuel 5 pid @ cterm-fuel -> outcome-ok 91 outcome-ok 100 }T
\ A new node over checked ones: only it is visited.
1 sid @ 5 pid @ app!
T{ 6 xid @ cterm-fuel -> outcome-ok 99 }T
lf-memo-off lf-audit-memo!
T{ 5 pid @ cterm-fuel -> outcome-ok 91 }T
lf-memo-auto lf-audit-memo!
T{ 5 pid @ cterm-fuel -> outcome-ok 91 }T
\ Turned on again, the memo starts a new epoch: nothing kept before counts.
lf-memo-on lf-audit-memo!
T{ 5 pid @ cterm-fuel 5 pid @ cterm-fuel -> outcome-ok 91 outcome-ok 100 }T
\ Planted-fault rows. A rolled-back index made again is a new node with a
\ new identity: kept units name the old one, so the new node is checked,
\ as a root and as a child (a memo without identities would pass both).
fresh
T{ 0 cid @ cterm-fuel drop 0 cid @ cterm-fuel -> outcome-ok outcome-ok 100 }T
T{ terms-back lf-term-count @ -> outcome-ok 0 }T
raw-reuse
T{ 0 0 term-identity@ 10 lf-cterm-check -> outcome-invalid }T
0 0 term-identity@ 0 0 term-identity@ app!
T{ 1 xid @ 10 lf-cterm-check -> outcome-invalid }T
\ A run that does not end ok keeps nothing: the root a run out of fuel
\ reached is checked in full by the next run (here an unstamped constant
\ below it is found).
fresh
raw-constant
0 cid @ 1 1 term-identity@ app!
T{ 2 xid @ 1 lf-cterm-check -> outcome-exhausted }T
T{ 2 xid @ 10 lf-cterm-check -> outcome-invalid }T
\ A node with a free variable is kept in the open epoch, which ends when
\ the local context is emptied (a new inference job); a node without one
\ stays kept (a memo without the open epoch would pass the dead variable).
fresh
local!
1 fid @ 0 cid @ app!
T{ 0 cid @ cterm-fuel drop 2 xid @ cterm-fuel drop -> outcome-ok outcome-ok }T
T{ 2 xid @ cterm-fuel 0 cid @ cterm-fuel -> outcome-ok 100 outcome-ok 100 }T
lf-lctx-reset
T{ 2 xid @ 10 lf-cterm-check -> outcome-invalid }T
T{ 0 cid @ cterm-fuel -> outcome-ok 100 }T
\ A reset of the reference store (a generation the closed epoch keeps)
\ starts a new epoch: the constant whose reference went is checked again
\ (a memo blind to that generation would pass it).
fresh
T{ 0 cid @ cterm-fuel drop 0 cid @ cterm-fuel -> outcome-ok outcome-ok 100 }T
lf-cref-reset
T{ 0 cid @ 10 lf-cterm-check -> outcome-invalid }T
lf-memo-auto lf-audit-memo!

\ A constant or Sort the term table finds is given again only while its
\ stamps hold (plan step S4): for a reference made again at the index of
\ a reset one, lf-cterm-new makes a node of its own; and a Sort whose
\ level index was reset is not given again (a session begins
\ only on an empty term store, so the reset is a raw one here).
fresh
: fresh-sort ( -- node ) 0 dup lf-level-identity drop lf-hterm-sort 0= abort" sort" drop ;
fresh-sort constant fsort
T{ 0 lf-term-reusable? fsort lf-term-reusable? -> true true }T
lf-cref-reset reuse-cref
T{ 0 lf-term-reusable? 0 dup lf-cref-current lf-cterm-new nip swap 0= -> false true false }T
lf-level-reset
T{ fsort lf-term-reusable? -> false }T

\ Marks at a depth, on the node fsort in a paired walk. lf-walk-seen?: a
\ node a run reached at depth 2 is seen at any depth no smaller (3), not
\ at a smaller one (1, then marked there). lf-walk-seen-at? (C1's, as
\ Lean's for_each with an offset): seen only at a depth the run reached
\ it at, every such depth kept -- the first in the unit, the others in
\ the pair set -- so a node met at alternating depths is not walked again
\ (review rvKN 1: a unit keeping only the latest depth gave 3 2 -> true
\ false); a new run has seen nothing.
4 walk2: mark-walk
: at-depth ( depth -- walk ) mark-walk walk-context ! fsort mark-walk walk-node ! mark-walk ;
mark-walk lf-walk-marking
T{ 2 at-depth lf-walk-seen? 3 at-depth lf-walk-seen? 1 at-depth lf-walk-seen?
   -> false true false }T
mark-walk lf-walk-pairing
T{ 2 at-depth lf-walk-seen-at? 2 at-depth lf-walk-seen-at? 3 at-depth lf-walk-seen-at?
   -> false true false }T
T{ 3 at-depth lf-walk-seen-at? 2 at-depth lf-walk-seen-at? 1 at-depth lf-walk-seen-at?
   -> true true false }T
T{ 1 at-depth lf-walk-seen-at? 3 at-depth lf-walk-seen-at? 2 at-depth lf-walk-seen-at?
   -> true true true }T
mark-walk lf-walk-pairing
T{ 2 at-depth lf-walk-seen-at? 3 at-depth lf-walk-seen-at? -> false false }T
\ A walk run inside another's visit (lf-walk-once-aside's test) keeps its
\ pairs in the set alone: the outer walk's unit stays, so the outer walk
\ still skips the node (review rvKN 2: an inner run that marked the unit
\ made the outer walk visit it again). A run that does not own the set (a
\ walk started inside the set's run took it), or any run after the
\ counter wrapped (lf-marks-erase), skips nothing and keeps nothing.
4 walk2: aside-walk
: aside-at ( depth -- walk ) aside-walk walk-context ! fsort aside-walk walk-node ! aside-walk ;
mark-walk lf-walk-marking
T{ 2 at-depth lf-walk-seen? -> false }T
aside-walk lf-walk-pairing
T{ 2 aside-at lf-walk-seen-aside? 2 aside-at lf-walk-seen-aside? 3 aside-at lf-walk-seen-aside?
   -> false true false }T
T{ 2 at-depth lf-walk-seen? -> true }T
mark-walk lf-walk-pairing
T{ 2 aside-at lf-walk-seen-aside? 2 aside-at lf-walk-seen-aside? -> false false }T
aside-walk lf-walk-pairing
T{ 2 aside-at lf-walk-seen-aside? -> false }T
lf-marks-erase
T{ 2 aside-at lf-walk-seen-aside? 2 aside-at lf-walk-seen-aside? -> false false }T
bye
