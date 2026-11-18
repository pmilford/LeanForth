\ perf-scan: sort-records timing, cells by sort-unsigned, pseudo-random; ns per element (fill excluded)
decimal
create sk2 /sorter allot
variable sd2  7 sd2 !  variable buf2  2variable tsum
: rn2 ( -- u ) sd2 @ 1103515245 * 12345 + $7fffffff and dup sd2 ! ;
: fill2 ( n -- ) 0 ?do rn2 buf2 @ i cells + ! loop ;
: one-sort ( n -- ) utime rot buf2 @ swap sk2 sort-records drop utime 2swap d- tsum 2@ d+ tsum 2! ;
: sort-time ( n reps -- )
  over cells allocate throw buf2 !  ['] sort-unsigned sk2 sorter-cells drop  0. tsum 2!
  dup 0 ?do over fill2 over one-sort loop
  ." sort n=" over . tsum 2@ drop 1000 * -rot * / . ." ns/element" cr buf2 @ free throw ;
16 100000 sort-time 32 50000 sort-time 33 50000 sort-time 1000 1000 sort-time 100000 10 sort-time 1000000 2 sort-time
