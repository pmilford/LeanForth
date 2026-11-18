\ Library call counters (lib-profiles 2026-11-18; a scratch copy only, never in src/).
\ lcnt+ ( i -- ) counts a call of counter i; lcnt-size ( n i -- ) counts a call that
\ passes size n: calls, total, largest, and a histogram by floor(log2 n). Globals, so
\ run the patched checker with --jobs 1. lcnt-dump prints every counter used.
[undefined] lcnt-calls [if]
create lcnt-calls 64 cells allot  lcnt-calls 64 cells erase
create lcnt-total 64 cells allot  lcnt-total 64 cells erase
create lcnt-max 64 cells allot    lcnt-max 64 cells erase
create lcnt-hist 64 64 * cells allot  lcnt-hist 64 64 * cells erase
: lcnt-at ( i table -- a-addr ) swap cells + ;
: lcnt+ ( i -- ) lcnt-calls lcnt-at 1 swap +! ;
: lcnt-log2 ( n -- k ) 0 swap begin dup 1 > while 2/ swap 1+ swap repeat drop ;
: lcnt-bucket ( n i -- a-addr ) 64 * swap 0 max lcnt-log2 + cells lcnt-hist + ;
: lcnt-size ( n i -- )
  dup lcnt+ 2dup lcnt-total lcnt-at +!
  2dup lcnt-max lcnt-at dup @ rot max swap !  lcnt-bucket 1 swap +! ;
: lcnt-hist. ( i -- ) 64 0 do dup 64 * i + cells lcnt-hist + @ ?dup if
  space i 0 .r ." :" 0 .r then loop drop ;
: lcnt-dump ( -- ) base @ decimal 64 0 do lcnt-calls i cells + @ ?dup if
  ." LCNT " i . . lcnt-total i cells + @ . lcnt-max i cells + @ . ." |" i lcnt-hist. cr
  then loop base ! ;
[then]
