\ Unit tests of src/lib/blocks.fs, heap blocks held in a cell, outside
\ the checker, in the classes of docs/development/TEST_COVERAGE_REVIEW.md.
\ Interfaces: the words, the header's example, stack effects and the
\ return stack. Results: blocks of 0, 1 and many units, zeroed over dirty
\ memory; a resize keeping the old units, from an empty cell and from a
\ block. Resources and rollback: the heap refusing each (full, the cell
\ and its block unchanged, nothing leaked), releasing twice, blocks
\ counted by tests/support/heap-watch.fs. T{ }T checks results and depth.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/lib/blocks.fs
require ../../src/lib/portability.fs   \ max-n, for a block the heap refuses

: blocks ( -- n ) live-blocks @ ;
variable cell-a  0 cell-a !
variable cell-b  0 cell-b !

\ ---- heap-claim and heap-release (moved from bytes.fs).
T{ 16 heap-claim swap cell-a ! blocks -> true 1 }T
T{ cell-a heap-release cell-a @ blocks cell-a heap-release cell-a @ blocks -> 0 0 0 0 }T
T{ 1 heap-refusals ! 16 heap-claim blocks -> false 0 }T

\ ---- block-zeroed: u units (at least one), erased, stored; full leaves
\ the cell as it was.
: dirty ( u -- ) dup allocate drop tuck swap -1 fill free drop ;
: all-zero? ( a-addr u -- flag ) true -rot 0 ?do dup i + c@ 0= rot and swap loop drop ;
T{ 4000 dirty 4000 cell-a block-zeroed cell-a @ 4000 all-zero? blocks -> outcome-ok true 1 }T
cell-a heap-release
T{ 0 cell-a block-zeroed cell-a @ 0<> cell-a @ c@ blocks -> outcome-ok true 0 1 }T
cell-a heap-release
T{ 7 cell-b ! 1 heap-refusals ! 10 cell-b block-zeroed cell-b @ blocks -> outcome-full 7 0 }T
0 cell-b !
T{ max-n cell-a block-zeroed cell-a @ blocks -> outcome-full 0 0 }T
T{ 8 cell-a ' block-zeroed rs-checked blocks -> outcome-ok 1 }T
cell-a heap-release

\ ---- block-resize: from an empty cell (a new block), then larger with
\ the old units kept; full keeps the cell and its block.
T{ 10 cell-a block-resize cell-a @ 0<> blocks -> outcome-ok true 1 }T
: tag ( -- ) 10 0 do i cell-a @ i + c! loop ;
: tagged? ( -- flag ) true 10 0 do cell-a @ i + c@ i = and loop ;
tag
T{ 5000 cell-a block-resize tagged? blocks -> outcome-ok true 1 }T
cell-a @ cell-b !
T{ 1 heap-refusals ! 9000 cell-a block-resize cell-a @ cell-b @ = tagged? blocks
   -> outcome-full true true 1 }T
T{ 0 cell-a block-resize cell-a @ c@ -> outcome-ok 0 }T
T{ 2 cell-a ' block-resize rs-checked -> outcome-ok }T
cell-a heap-release  0 cell-b !
T{ 1 heap-refusals ! 4 cell-a block-resize cell-a @ blocks -> outcome-full 0 0 }T
T{ heap-refusals @ -> 0 }T

\ ---- block-reused (reuse-out-2): a new zeroed block for an empty cell,
\ the same block erased when the cell holds one; false when the heap
\ refuses, the cell kept. block-free: 0 and a zeroed cell, 0 again for an
\ empty cell.
T{ 64 cell-a block-reused cell-a @ 64 all-zero? blocks -> true true 1 }T
cell-a @ cell-b !  cell-a @ 64 -1 fill
T{ 64 cell-a block-reused cell-a @ cell-b @ = cell-a @ 64 all-zero? blocks -> true true true 1 }T
T{ 64 cell-a ' block-reused rs-checked blocks -> true 1 }T
T{ cell-a block-free cell-a @ blocks cell-a block-free -> 0 0 0 0 }T
T{ cell-a ' block-free rs-checked -> 0 }T
0 cell-b !
T{ 1 heap-refusals ! 8 cell-a block-reused cell-a @ blocks -> false 0 0 }T

\ ---- The header's example.
variable buf  0 buf !
T{ 100 buf block-zeroed buf @ 99 + c@ 200 buf block-resize -> outcome-ok 0 outcome-ok }T
T{ buf heap-release buf @ buf heap-release buf @ blocks -> 0 0 0 }T
bye
