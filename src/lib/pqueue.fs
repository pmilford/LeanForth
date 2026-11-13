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
\ pq-push puts the new cell last and moves it up past each parent that
\ comes out after it; pq-pop takes the root, puts the last cell there and
\ moves it down past the child that comes out first while that one comes
\ out before it (the right child on a tie, as in the scheduler's heap it
\ replaced, so that its queues stay the same cell for cell). At most about
\ log2 n comparisons a step each way, no recursion, and memory one cell
\ per cell queued (the slab doubles as it fills, from 16). Why so: the
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
end-structure

\ ---- The heap's cells.
: pq-at ( i pq -- a-addr ) pq-cells slab-at ;
: pq@ ( i pq -- x ) pq-at @ ;
: pq-parent ( i -- j ) 1- 2/ ;
\ Whether cell i comes out after cell j.
: pq-after? ( i j pq -- flag ) dup >r tuck pq@ >r pq@ r> r> pq-order @ execute 0> ;
: pq-swap ( i j pq -- ) tuck pq-at >r pq-at dup @ r@ @ rot ! r> ! ;

\ ---- Moving a cell up: past each parent that comes out after it.
: pq-rises? ( i pq -- flag )
  over 0> if >r dup pq-parent swap r> pq-after? else 2drop false then ;
: pq-up ( i pq -- )
  >r begin dup r@ pq-rises? while dup dup pq-parent r@ pq-swap pq-parent repeat
  drop r> drop ;
\ Moving a cell down: past its child that comes out first (the right one
\ on a tie) while that comes out before it.
: pq-in? ( i pq -- flag ) pq-cells slab-count < ;
: pq-right? ( c pq -- flag )
  over 1+ over pq-in? if >r dup 1+ swap r> pq-after? 0= else 2drop false then ;
: pq-child ( i pq -- c ) swap 2* 1+ tuck swap pq-right? if 1+ then ;
: pq-sinks? ( i c pq -- flag ) 2dup pq-in? if pq-after? else drop 2drop false then ;
: pq-next ( i pq -- c flag ) 2dup pq-child dup >r swap pq-sinks? r> swap ;
: pq-down ( i pq -- )
  >r begin dup r@ pq-next while 2dup r@ pq-swap nip repeat 2drop r> drop ;
\ The last cell, taken out of the slab (its memory stays as it was).
: pq-last ( pq -- x ) -1 over pq-cells slab-commit pq-cells slab-top @ ;
: pq-root! ( x pq -- ) 0 swap pq-at ! ;

lf-lib set-current
\ A queue ordered by order: ok, or invalid for an order of 0. It must not
\ be given a queue that holds memory: pq-free first.
: pq-init ( order pq -- outcome )
  2dup pq-order ! 1 cells dup slab-limit-max rot pq-cells slab-init drop
  0<> flag>outcome ;
: pq-free ( pq -- ) dup pq-cells slab-free 0 swap pq-order ! ;
\ Cells queued (0 for a queue that is not live).
: pq-count ( pq -- n ) pq-cells dup slab-live? if slab-count else drop 0 then ;
: pq-clear ( pq -- ) pq-cells slab-clear ;
\ Queue x: ok; full when the heap cannot grow (nothing changed); invalid
\ for a queue not accepted or not live.
: pq-push ( x pq -- outcome )
  dup pq-order @ 0= if 2drop outcome-invalid exit then
  1 over pq-cells slab-claim ok-then? 0= if nip nip exit then
  >r tuck r@ swap pq-at ! r> swap pq-up outcome-ok ;
\ The cell that comes out first, staying, and taken out (unchecked: the
\ queue holds a cell).
: pq-min ( pq -- x ) 0 swap pq@ ;
: pq-pop ( pq -- x )
  dup pq-min swap dup pq-last over pq-count
  if over pq-root! 0 swap pq-down else 2drop then ;

module-close
base !   \ the BASE this file was loaded with
