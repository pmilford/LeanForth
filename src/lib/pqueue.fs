\ Priority queues of cells: a binary min-heap on a growable array, the
\ caller's order deciding which cell comes out first. A general tool with
\ no Lean knowledge; untrusted. Written for the parallel scheduler's ready
\ queues (src/kernel/env-schedule.fs; library audit 2026-11-13, action 11).
\
\ The order. order ( x1 x2 -- n ), the convention of sort.fs: n > 0 means
\ x1 comes out after x2; zero or negative, not after. So sort.fs's
\ sort-signed gives the smallest value first and sort-unsigned the
\ smallest unsigned one. Cells the order ties come out in an order the
\ heap's shape decides (a heap is not stable): give distinct values, or
\ an order that breaks ties, when that matters. The order must take two
\ cells and give one, and must not use the queue.
\
\ The method. The cells are a heap in a slab (slab.fs) from unit 0: no
\ cell comes out after its parent, unit i's children being 2i+1 and 2i+2.
\ pq-push moves the new cell up from the last place past each parent that
\ comes out after it; pq-pop takes the root and moves the last cell down
\ from the root past the child that comes out first while that one comes
\ out before it (the right child on a tie, as in the scheduler's heap it
\ replaced, so that its queues stay the same cell for cell). A cell moves
\ through a hole (each cell it passes moves into the hole, it is stored
\ once at the end), which makes the comparisons and the result those of
\ swapping. At most about log2 n comparisons a step each way, no
\ recursion, and memory one cell per cell queued (the slab doubles as it
\ fills, from 16). Why so: the
\ checker's queues hold declaration numbers, up to one per declaration of
\ an input (some 60,000 for Init, 300,000 for Mathlib), pushed and popped
\ in any order; a heap is the simplest structure with logarithmic steps.
\
\ Outcomes (lib/outcome.fs): pq-init ok, or invalid for an order of 0 (the
\ queue then refuses every push); pq-push ok, full when the slab cannot
\ grow (nothing changed), invalid for a queue that is not live. pq-pop
\ and pq-min are unchecked: the queue holds a cell (pq-count > 0).
\
\ Example: declaration numbers, smallest first.
\   create ready /pqueue allot   ' sort-signed ready pq-init drop
\   7 ready pq-push drop  3 ready pq-push drop  5 ready pq-push drop
\   ready pq-pop . ready pq-pop . ready pq-count .   \ 3 5 1
\   ready pq-free
\
\ Interface: /pqueue pq-init pq-free pq-count pq-push pq-pop pq-min
\ pq-clear. State: none of its own; every word takes a queue record made
\ by the caller (in the dictionary or inside a larger record), which owns
\ its heap block until pq-free. One queue is single-threaded; separate
\ queues are independent. Requires portability.fs, outcome.fs, slab.fs
\ and module.fs; helpers are private in lf-lib-private (ADR 0010). Loads
\ in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./outcome.fs
require ./slab.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
begin-structure /pqueue
lf-lib-private set-current
  /slab +field pq-cells         \ the heap, from unit 0
  field: pq-order               \ xt ( x1 x2 -- n ), or 0 in a queue not accepted
  field: pq-hole                \ while a cell moves: the place it would take
  field: pq-held                \ and its value
end-structure

\ ---- The heap's cells, and the order: whether one comes out after another.
: pq-at ( i pq -- a-addr ) pq-cells slab-at ;
: pq-x ( i pq -- x ) pq-at @ ;
: pq-compare ( pq x1 x2 -- n ) rot pq-order @ execute ;
: pq-cells-after? ( i j pq -- flag ) tuck pq-x >r tuck pq-x r> pq-compare 0> ;
\ Cell i against the value moving: whether it comes out after, or before.
: pq-cell-after? ( i pq -- flag ) tuck pq-x over pq-held @ pq-compare 0> ;
: pq-held-after? ( i pq -- flag ) tuck pq-x over pq-held @ swap pq-compare 0> ;
\ Cell i moved into the hole, which goes to i; the value moving put in the
\ hole at last.
: pq-fill ( i pq -- ) 2dup pq-x over dup pq-hole @ swap pq-at ! pq-hole ! ;
: pq-settle ( pq -- ) dup pq-held @ swap dup pq-hole @ swap pq-at ! ;

\ ---- Moving the value up: past each parent that comes out after it.
: pq-parent ( pq -- j ) pq-hole @ 1- 2/ ;
: pq-rises? ( pq -- flag )
  dup pq-hole @ 0> if dup pq-parent swap pq-cell-after? else drop false then ;
: pq-up ( pq -- ) begin dup pq-rises? while dup pq-parent over pq-fill repeat pq-settle ;
\ Moving it down: past the hole's child that comes out first (the right
\ one unless the left comes out before it) while it comes out after that.
: pq-in? ( i pq -- flag ) pq-cells slab-count < ;
: pq-right? ( c pq -- flag )
  over 1+ over pq-in? if >r dup 1+ swap r> pq-cells-after? 0= else 2drop false then ;
: pq-child ( pq -- c ) dup pq-hole @ 2* 1+ tuck swap pq-right? if 1+ then ;
: pq-sinks? ( c pq -- flag ) 2dup pq-in? if pq-held-after? else 2drop false then ;
: pq-down ( pq -- )
  begin dup pq-child over 2dup pq-sinks? while pq-fill repeat 2drop pq-settle ;
: pq-slab ( pq -- ) pq-cells >r 1 cells dup slab-limit-max r> slab-init drop ;

lf-lib set-current
\ A queue ordered by order: ok, or invalid for an order of 0. It must not
\ be given a queue that holds memory: pq-free first.
: pq-init ( order pq -- outcome ) 2dup pq-order ! pq-slab 0<> flag>outcome ;
: pq-free ( pq -- ) dup pq-cells slab-free /pqueue erase ;
\ Cells queued (0 for a queue that is not live).
: pq-count ( pq -- n ) pq-cells dup slab-live? if slab-count else drop 0 then ;
: pq-clear ( pq -- ) pq-cells slab-clear ;
\ Queue x: ok; full when the heap cannot grow (nothing changed); invalid
\ for a queue not accepted or not live.
: pq-push ( x pq -- outcome )
  dup pq-order @ 0= if 2drop outcome-invalid exit then
  1 over pq-cells slab-claim ok-then? 0= if nip nip exit then
  over pq-hole ! tuck pq-held ! pq-up outcome-ok ;
\ The cell that comes out first, staying, and taken out (unchecked: the
\ queue holds a cell): the last cell then moves down from the root.
: pq-min ( pq -- x ) 0 swap pq-x ;
: pq-pop ( pq -- x )
  dup pq-min swap -1 over pq-cells slab-commit dup pq-count 0= if drop exit then
  dup pq-cells slab-top @ over pq-held ! 0 over pq-hole ! pq-down ;

module-close
base !   \ the BASE this file was loaded with
