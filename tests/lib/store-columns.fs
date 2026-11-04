\ Side columns of a growable store (src/lib/store-columns.fs), outside the
\ checker: a heap store of two-cell "things" as a context member, a group
\ of two columns beside it, their units kept and the new ones zeroed as
\ the store grows, the cheap columns-ready, a growth the test hook of
\ src/lib/store.fs refuses (full, no column changed), columns-each, and
\ a new context's columns made by its setup and freed by its teardown,
\ with no heap block left. Test-only.

: store-fault-hooks ( -- ) ;   \ the test hook of src/lib/store.fs
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/lib/lib.fs
require ../../src/lib/store-columns.fs

variable refusing
:noname ( store -- flag ) drop refusing @ ; is store-refuse?

store-header context-record: things
: things-make ( -- ) 4 2 cells 0 things store-heap-init drop 64 things store-limit! drop ;
' things-make context-setup
:noname ( -- ) things store-heap-free ; context-teardown
' things column-group: thing-columns
:noname ( -- ) thing-columns columns-setup ; context-setup
:noname ( -- ) thing-columns columns-free ; context-teardown
/slab context-record: marks
1 cells ' marks thing-columns column-add
/slab context-record: pairs
2 cells ' pairs thing-columns column-add
1 cells context-record: covered

: claim ( -- index ) things store-ready drop things store-new 0= abort" claim" ;
: claims ( n -- ) 0 ?do claim drop loop ;
: covers? ( n -- flag ) dup marks slab-capacity > 0= swap pairs slab-capacity > 0= and ;

\ The columns cover the store as it was made.
T{ thing-columns group-capacity dup covers? -> 4 true }T
\ A unit written is kept when the store grows (4 + 16 records); the new
\ units are zero.
4 claims
7 3 marks column-at !
T{ claim things store-capacity @ -> 4 20 }T
T{ thing-columns columns-cover 20 covers? -> outcome-ok true }T
T{ 3 marks column-at @ 19 marks column-at @ 19 pairs column-at 2@ -> 7 0 0 0 }T
\ columns-ready covers again only for a capacity other than the mark's.
T{ 0 covered ! covered thing-columns columns-ready covered @ -> true 20 }T
T{ covered thing-columns columns-ready -> true }T
\ A growth the hook refuses: full, and no column grows.
15 claims
T{ claim things store-capacity @ -> 20 40 }T
true refusing !
T{ thing-columns columns-cover 40 covers? -> outcome-full false }T
T{ covered thing-columns columns-ready covered @ -> false 20 }T
false refusing !
T{ covered thing-columns columns-ready covered @ 40 covers? -> true 40 true }T
\ columns-each visits every column (newest first), with the stack below.
: units ( sum column -- sum' ) column-slab slab-unit + ;
T{ 0 ' units thing-columns columns-each -> 3 cells }T
\ A new context gets its own store and columns, zeroed; freeing it gives
\ every heap block back.
live-blocks @ constant blocks-before
: in-new ( -- capacity unit ior )
  context-new throw >r r@ context-use thing-columns group-capacity 2 marks column-at @
  context-main context-use r> context-free ;
T{ in-new live-blocks @ blocks-before - -> 4 0 0 0 }T

\ A store whose capacity was corrupted by a raw write is found invalid before
\ any column grows (review rvKC, R2-L1): columns-ready is false, no column
\ changes size, and the repaired store covers again.
things store-capacity @ constant cap0
: column-units ( -- n ) marks slab-capacity pairs slab-capacity + ;
column-units constant units0
1000000 things store-capacity !
T{ things store-count-valid? -> false }T
T{ 0 covered ! covered thing-columns columns-ready column-units -> false units0 }T
cap0 things store-capacity !
T{ 0 covered ! covered thing-columns columns-ready column-units -> true units0 }T

cases-done
bye
