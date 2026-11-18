\ perf-scan: does sort-records stay inside its records? n cells between guard cells.
decimal
create sk /sorter allot
create arr 80 cells allot
variable sd  7 sd !
: rn ( -- u ) sd @ 1103515245 * 12345 + $7fffffff and dup sd ! ;
: guard ( -- ) arr 80 cells $55 fill ;
: fill-n ( n -- ) 0 ?do rn arr 8 cells + i cells + ! loop ;
: guards-ok? ( n -- flag )
  true 8 0 do arr i cells + @ $5555555555555555 = and loop
  swap 8 + 80 swap ?do arr i cells + @ $5555555555555555 = and loop ;
: sorted? ( n -- flag )
  true swap 1 ?do arr 8 cells + i cells + dup cell- @ swap @ u> 0= and loop ;
: try ( n -- )
  guard dup fill-n
  ['] sort-unsigned sk sorter-cells drop
  arr 8 cells + over sk sort-records ." n=" over . ." outcome " .
  dup guards-ok? ." guards " . sorted? ." sorted " . cr ;
2 try 5 try 16 try 31 try 32 try 33 try 40 try 64 try
: again ( n reps -- ) ['] sort-unsigned sk sorter-cells drop
  0 ?do guard dup fill-n arr 8 cells + over sk sort-records drop
    dup guards-ok? 0= if ." guard broken at rep " i . cr leave then loop drop ." again done" cr ;
32 1000 again 33 1000 again 16 1000 again
