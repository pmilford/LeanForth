\ Unit tests of src/lib/pqueue.fs, priority queues of cells, outside the
\ checker, in the classes of docs/development/TEST_COVERAGE_REVIEW.md.
\ Interfaces: the public words and hidden helpers, the header's example,
\ stack effects with the return stack checked. Results and refusals: an
\ order of 0, a queue never made or freed (invalid), smallest first by
\ sort-signed and unsigned values with the top bit set by sort-unsigned,
\ an order with ties (every cell out, in order of the order). Resources:
\ the heap refusing growth (full, nothing changed), comparisons within
\ about 2 log2 n a step, blocks freed. State: clears; 3,000 random pushes
\ and pops against a model, and the same operations against a copy of the
\ scheduler's former heap (src/kernel/env-schedule.fs before 2026-11-13):
\ the same cells out and the same heap, cell for cell, after every step.
\ Loaded under HEX: the module must not depend on BASE. T{ }T checks
\ results and data-stack depth.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/lib/pqueue.fs base @ decimal constant base-after-load
require ../../src/lib/sort.fs

T{ base-after-load -> 16 }T
: blocks ( -- n ) live-blocks @ ;

\ ---- The interface (ADR 0010).
T{ [defined] /pqueue [defined] pq-init [defined] pq-free [defined] pq-count
   -> true true true true }T
T{ [defined] pq-push [defined] pq-pop [defined] pq-min [defined] pq-clear
   -> true true true true }T
T{ [defined] pq-cells [defined] pq-order [defined] pq-up [defined] pq-down [defined] pq-after?
   -> false false false false false }T

\ ---- The header's example.
create ready /pqueue allot   ' sort-signed ready pq-init drop
7 ready pq-push drop  3 ready pq-push drop  5 ready pq-push drop
T{ ready pq-pop ready pq-pop ready pq-count -> 3 5 1 }T
ready pq-free
T{ blocks ready pq-count -> 0 0 }T

\ ---- Refusals: an order of 0; a queue never made, or freed.
create q /pqueue allot   q /pqueue erase
T{ q pq-count 5 q pq-push -> 0 outcome-invalid }T
T{ 0 q pq-init 5 q pq-push q pq-count -> outcome-invalid outcome-invalid 0 }T
q pq-free
T{ ' sort-signed q pq-init 5 q pq-push q pq-count -> outcome-ok outcome-ok 1 }T
q pq-free
T{ q pq-count 5 q pq-push blocks -> 0 outcome-invalid 0 }T

\ ---- Orders: signed values smallest first, duplicates kept; unsigned
\ values with the top bit set after the others.
: pops ( n pq -- x1 .. xn ) swap 0 ?do dup pq-pop swap loop drop ;
: pushes ( x1 .. xn n pq -- ) swap 0 ?do tuck pq-push drop loop drop ;
' sort-signed q pq-init drop
T{ 4 -2 9 4 0 -7 6 q pushes q pq-count q pq-min -> 6 -7 }T
T{ 6 q pops q pq-count -> -7 -2 0 4 4 9 0 }T
q pq-free
' sort-unsigned q pq-init drop
T{ -1 3 max-n 0 4 q pushes 4 q pops -> 0 3 max-n -1 }T
q pq-free
\ An order with ties: by tens; a heap is not stable, but every cell comes
\ out, tens in order.
: by-tens ( x1 x2 -- n ) 10 / swap 10 / swap sort-signed ;
' by-tens q pq-init drop
T{ 31 12 35 17 33 15 6 q pushes 6 q pops + + >r + + r> -> 44 99 }T
q pq-free

\ ---- Clearing, and stack effects with the return stack checked.
' sort-signed q pq-init drop
T{ 3 2 1 3 q pushes q pq-clear q pq-count 8 q pq-push q pq-pop -> 0 outcome-ok 8 }T
T{ 5 q ' pq-push rs-checked q ' pq-min rs-checked q ' pq-pop rs-checked -> outcome-ok 5 5 }T
q pq-free

\ ---- The heap refusing growth: the 17th cell needs a larger block (16
\ cells first). Full, the queue as it was.
' sort-signed q pq-init drop
: down ( n pq -- ) swap 0 ?do 100 i - over pq-push drop loop drop ;
T{ 16 q down q pq-count blocks -> 16 1 }T
T{ 1 heap-refusals ! 7 q pq-push q pq-count q pq-min -> outcome-full 16 85 }T
T{ 7 q pq-push q pq-count q pq-pop q pq-pop -> outcome-ok 17 7 85 }T
q pq-free
T{ blocks -> 0 }T

\ ---- Comparisons: 1,000 pushes and pops, at most about 2 log2 n each.
variable compares
: counted ( x1 x2 -- n ) 1 compares +! sort-signed ;
variable test-seed  2463534242 test-seed !
: rand-below ( n -- u )
  test-seed @ dup 13 lshift xor dup 7 rshift xor dup 17 lshift xor dup test-seed !
  1 rshift swap mod ;
' counted q pq-init drop
max-n negate 1- constant min-n
: fill-queue ( n -- ) 0 ?do 100000 rand-below q pq-push drop loop ;
: sorted-out? ( n -- flag )
  true min-n rot 0 ?do q pq-pop tuck > if nip false swap then loop drop ;
T{ 0 compares ! 1000 fill-queue compares @ 1000 10 * < -> true }T
T{ 0 compares ! 1000 sorted-out? compares @ 1000 20 * < q pq-count -> true true 0 }T
q pq-free

\ ---- 3,000 random pushes and pops against a model (a count per value)
\ and against the scheduler's former heap, copied: the same cell out at
\ every pop and the same heap, cell for cell, after every step.
create old-heap /slab allot  1 cells dup slab-limit-max old-heap slab-init drop
: lf-sch-cell@ ( i slab -- x ) slab-at @ ;
: lf-sch-push ( x slab -- outcome )
  1 over slab-claim ok-then? if swap slab-at ! outcome-ok else nip nip then ;
: lf-sch-pop ( slab -- x ) dup slab-count 1- over slab-at @ swap -1 swap slab-commit ;
: lf-sch-heap-swap ( i j heap -- )
  tuck slab-at >r slab-at dup @ r@ @ rot ! r> ! ;
: lf-sch-heap-less? ( i j heap -- flag ) tuck lf-sch-cell@ >r lf-sch-cell@ r> < ;
: lf-sch-heap-parent ( i -- j ) 1- 2/ ;
: lf-sch-heap-up ( i heap -- )
  >r begin dup 0> while
    dup dup lf-sch-heap-parent r@ lf-sch-heap-less? 0= if r> 2drop exit then
    dup dup lf-sch-heap-parent r@ lf-sch-heap-swap lf-sch-heap-parent
  repeat r> 2drop ;
: lf-sch-heap-child ( i heap -- j )
  >r 2* 1+ dup r@ slab-count < 0= if r> 2drop -1 exit then
  dup 1+ dup r@ slab-count < 0= if drop r> drop exit then
  2dup r@ lf-sch-heap-less? if drop else nip then r> drop ;
: lf-sch-heap-down ( i heap -- )
  >r begin dup r@ lf-sch-heap-child dup 0< 0= while
    2dup swap r@ lf-sch-heap-less? 0= if 2drop r> drop exit then
    tuck r@ lf-sch-heap-swap
  repeat 2drop r> drop ;
: lf-sch-heap-push ( x heap -- outcome )
  tuck lf-sch-push ok-then? 0= if exit then
  dup slab-count 1- swap lf-sch-heap-up outcome-ok ;
: lf-sch-heap-min ( heap -- x ) 0 swap lf-sch-cell@ ;
: lf-sch-heap-pop ( heap -- x )
  dup lf-sch-heap-min swap dup lf-sch-pop over slab-count if
    over 0 swap slab-at ! 0 swap lf-sch-heap-down else 2drop then ;

64 constant value-span
create model value-span cells allot   model value-span cells erase
variable model-n   0 model-n !
variable mismatches   0 mismatches !
: differs ( -- ) 1 mismatches +! ;
: model-min ( -- x ) 0 begin dup cells model + @ 0= while 1+ repeat ;
: model-push ( x -- ) cells model + 1 swap +! 1 model-n +! ;
: model-pop ( -- x ) model-min dup cells model + -1 swap +! -1 model-n +! ;
lf-lib-private order+
: same-heap? ( -- flag )
  q pq-cells slab-count old-heap slab-count <> if false exit then
  true old-heap slab-count 0 ?do i q pq@ i old-heap lf-sch-cell@ = and loop ;
order-
' sort-signed q pq-init drop
: op-push ( -- ) value-span rand-below dup model-push dup old-heap lf-sch-heap-push drop
  q pq-push ok? 0= if differs then ;
: op-pop ( -- ) model-n @ 0= if exit then
  model-pop old-heap lf-sch-heap-pop q pq-pop over <> if differs then <> if differs then ;
: op ( -- ) 5 rand-below 3 < if op-push else op-pop then
  same-heap? 0= if differs then q pq-count model-n @ <> if differs then ;
: run-ops ( n -- ) 0 ?do op loop ;
T{ 3000 run-ops mismatches @ -> 0 }T
q pq-free  old-heap slab-free
T{ blocks -> 0 }T
bye
