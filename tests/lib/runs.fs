\ Tests of the runs library (src/lib/runs.fs), outside the checker: its
\ header's example; each word's results and refusals (invalid handles and
\ counts); sharing (a push in place, a copy, a join in place) and that a
\ run never changes; every refusal of the heap inside an operation (full,
\ no run, the other runs unchanged), with the slabs filled to the room
\ that makes each allocation the refused one; a reset; and 400 random
\ operations compared with a simple model, every run checked again at the
\ end. Every T{ }T checks the data stack's depth.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/lib/runs.fs

: made ( x outcome -- x ) ok? 0= abort" runs: not made" ;
: cells. ( run -- x1 .. xn ) dup run-count 0 ?do dup i run@ swap loop drop ;

\ The header's example.
T{ 0 7 run-push drop  dup 8 run-push drop  over 9 run-push drop  rot drop  run-cat drop
   dup run-count swap 2 run-after drop 0 run@ -> 4 7 }T
runs-reset

\ Sharing, parts, joins; a run never changes.
0 7 run-push made constant r7
r7 8 run-push made constant r78
r7 9 run-push made constant r79
T{ r78 cells. r79 cells. r7 cells. -> 7 8 7 9 7 }T
\ [7 8] was made in place (r7 ended at the top), [7 9] by a copy of [7].
T{ runs-cells -> 4 }T
T{ 0 run-count 0 run-valid? r79 run-valid? 99 run-valid? -5 run-valid? -> 0 true true false false }T
T{ r78 1 run-take made cells. r78 1 run-after made cells. -> 7 8 }T
T{ r78 2 run-take made r78 = r78 0 run-after made r78 = -> true true }T
T{ r78 0 run-take made r78 2 run-after made -> 0 0 }T
T{ r78 3 run-take r78 -1 run-after 99 0 run-take -> -1 outcome-invalid -1 outcome-invalid
   -1 outcome-invalid }T
T{ -5 1 run-push 99 1 run-push -> -1 outcome-invalid -1 outcome-invalid }T
T{ r78 r79 run-cat made cells. -> 7 8 7 9 }T
\ A part and the part after it join in place; the empty run is neutral.
runs-cells constant cells-before
T{ r78 1 run-take made r78 1 run-after made run-cat made cells. -> 7 8 }T
T{ runs-cells cells-before = -> true }T
T{ 0 r79 run-cat made r79 = r79 0 run-cat made r79 = -> true true }T
T{ r79 99 run-cat 99 r79 run-cat -> -1 outcome-invalid -1 outcome-invalid }T
T{ r78 cells. r79 cells. r7 cells. -> 7 8 7 9 7 }T

\ ---- The heap refusing. room ( n slab -- ) leaves exactly n free units
\ in a slab (claiming the rest, which no run names), so the operation's
\ next allocation in that slab is the first, refused one: full, no run.
lf-lib-private order+
: free# ( slab -- n ) dup slab-capacity swap slab-count - ;
: reserve! ( n slab -- ) slab-reserve ok? 0= abort" runs: no room" ;
: grow-to ( n slab -- ) 2dup free# > if tuck slab-count + swap reserve! else 2drop then ;
: room ( n slab -- ) 2dup grow-to dup free# rot - swap slab-claim made drop ;
: refused ( -- ) 1 heap-refusals ! ;
: refusal-done? ( -- flag ) heap-refusals @ 0= ;
\ A new run's record: the cells fit, the record does not.
T{ 4 rn-cells room 0 rn-recs room refused 0 7 run-push refusal-done? -> -1 outcome-full true }T
T{ 4 rn-cells room 0 rn-recs room refused r78 1 run-take refusal-done? -> -1 outcome-full true }T
T{ 4 rn-cells room 0 rn-recs room refused r78 1 run-after refusal-done? -> -1 outcome-full true }T
\ A push in place: no room for x.
0 7 run-push made constant s7
T{ 0 rn-cells room 4 rn-recs room refused s7 8 run-push refusal-done? -> -1 outcome-full true }T
\ A push with a copy: no room for the copy; room for it but not for x.
T{ 0 rn-cells room 4 rn-recs room refused r78 5 run-push refusal-done? -> -1 outcome-full true }T
T{ 2 rn-cells room 4 rn-recs room refused r78 5 run-push refusal-done? -> -1 outcome-full true }T
\ A join with copies: no room for run1's copy; room for it, not run2's.
T{ 0 rn-cells room 4 rn-recs room refused r79 r78 run-cat refusal-done? -> -1 outcome-full true }T
T{ 2 rn-cells room 4 rn-recs room refused r79 r78 run-cat refusal-done? -> -1 outcome-full true }T
\ Nothing changed; with the heap giving room the same operations work.
T{ r78 cells. r79 cells. s7 cells. -> 7 8 7 9 7 }T
T{ r78 5 run-push made cells. r79 r78 run-cat made cells. s7 8 run-push made cells.
   -> 7 8 5 7 9 7 8 7 8 }T
order-

\ A reset empties every run; the epoch changes.
runs-epoch constant epoch0
T{ runs-reset r7 run-valid? runs-epoch epoch0 = runs-cells -> false false 0 }T


\ ---- 400 random operations against a model: each run's cells kept in a
\ plain row of cells when it is made; push, take, after and join of runs
\ chosen at random (a push or join only while the result has at most 64
\ cells); each new run checked against its row when made, and every run
\ made checked again at the end (a run never changes).
variable rs-seed  4242 rs-seed !
: rs-rnd ( n -- r ) rs-seed @ 1103515245 * 12345 + dup rs-seed ! 16 rshift 32767 and swap mod ;
400 constant ops
64 constant longest
create handles ops 1+ cells allot
create lens ops 1+ cells allot
create models ops 1+ longest * cells allot
variable made#  variable ka  variable kb  variable kn
: row ( k -- addr ) longest * cells models + ;
: handle ( k -- run ) cells handles + @ ;
: len ( k -- n ) cells lens + @ ;
: new-row ( -- addr ) made# @ row ;
: record ( run n -- ) made# @ cells lens + ! made# @ cells handles + ! 1 made# +! ;
: a-row ( -- addr ) ka @ row ;  : a-len ( -- n ) ka @ len ;  : a-run ( -- run ) ka @ handle ;
: b-row ( -- addr ) kb @ row ;  : b-len ( -- n ) kb @ len ;  : b-run ( -- run ) kb @ handle ;
: op-push ( -- )
  a-len longest = if exit then  1000 rs-rnd kn !
  a-row new-row a-len cells move  kn @ new-row a-len cells + !
  a-run kn @ run-push made a-len 1+ record ;
: op-take ( -- )
  a-len 1+ rs-rnd kn !  a-row new-row kn @ cells move  a-run kn @ run-take made kn @ record ;
: op-after ( -- )
  a-len 1+ rs-rnd kn !  a-row kn @ cells + new-row a-len kn @ - cells move
  a-run kn @ run-after made a-len kn @ - record ;
: op-cat ( -- )
  a-len b-len + longest > if exit then
  a-row new-row a-len cells move  b-row new-row a-len cells + b-len cells move
  a-run b-run run-cat made a-len b-len + record ;
: op ( -- )
  made# @ rs-rnd ka !  made# @ rs-rnd kb !
  4 rs-rnd case 0 of op-push endof 1 of op-take endof 2 of op-after endof op-cat endcase ;
: same-cell? ( k i -- flag ) 2dup swap handle swap run@ -rot cells swap row + @ = ;
: matches? ( k -- flag )
  dup handle run-count over len <> if drop false exit then
  true swap dup len 0 ?do dup i same-cell? rot and swap loop drop ;
variable mismatches
: check ( k -- ) matches? 0= if 1 mismatches +! then ;
: run-ops ( -- ) ops 0 do op made# @ 1- check loop ;
: check-all ( -- ) made# @ 0 do i check loop ;
0 made# !  0 0 record
T{ run-ops check-all mismatches @ made# @ 200 > -> 0 true }T

T{ depth -> 0 }T
cr .( runs.fs: all tests passed) cr
bye
