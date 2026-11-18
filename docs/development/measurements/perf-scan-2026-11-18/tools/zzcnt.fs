\ perf-scan counters (scratch copy only, never in src/)
[undefined] cnts [if]
create cnts 64 cells allot  cnts 64 cells erase
: cnt+ ( i -- ) cells cnts + 1 swap +! ;
: cnt-add ( n i -- ) cells cnts + +! ;
: cnt-max ( n i -- ) cells cnts + dup @ rot max swap ! ;
: cnt-dump ( -- ) 64 0 do cnts i cells + @ ?dup if
  ." CNT " i . . cr then loop ;
: allocate ( u -- a ior ) 40 cnt+ dup 43 cnt-add allocate ;
: free ( a -- ior ) 41 cnt+ free ;
: resize ( a u -- a ior ) 42 cnt+ resize ;
[then]
