\ Allocation-failure injection for tests (plan task 1.4.6). Loading this
\ file before anything else turns on src/lib/store.fs's test-only hook,
\ store-refuse?, and makes it fail the k-th allocation that would
\ otherwise go ahead, counted across every store the program allocates
\ in (each context's term, level, name, reference and input stores, and
\ the checked environment's dependency pool) from the moment af-arm runs:
\ the store refuses as if it were full, or, in THROW mode, the
\ allocation throws af-thrown. Only the k-th fails; the ones after it go
\ ahead. af-hit tells whether the k-th was reached, and in which store.
\
\ Test-only and single-threaded: the state below is global, outside every
\ context, and counts the allocations of whatever task runs. Production
\ code never loads this file (src/main.fs does not define
\ store-fault-hooks), so there store-open? has no hook at all.

: store-fault-hooks ( -- ) ;
require ../../src/lib/store.fs
[undefined] store-refuse? [if]
  .( alloc-fail.fs: src/lib/store.fs was loaded before the hook was defined) cr
  1 throw
[then]

\ The THROW code of an injected failure in THROW mode: outside
\ Forth-2012's reserved range and LeanForth's codes (-4096 to -4101 the
\ job pool's, -4110 the environment's, -4129 the authoring words').
-4150 constant af-thrown

begin-structure /af
  field: af-at       \ the allocation that fails: 1, 2, ...; 0 for none
  field: af-seen     \ allocations seen since af-arm
  field: af-store    \ the store whose allocation failed, or 0
  field: af-throws   \ true: throw af-thrown instead of refusing
end-structure
create af-state /af allot  af-state /af erase

\ Fail the k-th allocation from now on (0: none), by refusing or throwing.
: af-arm ( k -- ) af-state /af erase af-state af-at ! ;
: af-arm-throw ( k -- ) af-arm true af-state af-throws ! ;
: af-off ( -- ) 0 af-arm ;
\ Allocations seen since af-arm, and the store that failed (0: none yet).
: af-seen@ ( -- n ) af-state af-seen @ ;
: af-hit ( -- store|0 ) af-state af-store @ ;

: af-due? ( -- flag ) 1 af-state af-seen +! af-seen@ af-state af-at @ = ;
: af-fail ( store -- true )
  af-state af-store ! af-state af-throws @ if af-thrown throw then true ;
: af-refuse ( store -- flag ) af-due? if af-fail else drop false then ;
' af-refuse is store-refuse?
