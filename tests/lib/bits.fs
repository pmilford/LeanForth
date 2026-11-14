\ Unit tests of src/lib/bits.fs, bits of cells, bit sets and binary
\ search, outside the checker, in the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md. Interfaces: the public words
\ and hidden helpers, the header's example, stack effects and the return
\ stack. Results: cell-bits against the host; log2-ceiling at every power
\ of two and one past it; bits in the first, a middle and the last cell
\ of a set, set without touching their neighbours; searches of empty,
\ one-element, all-below and none-below ranges, duplicates, ranges not
\ starting at 0, a test carrying two values below k, ranges wider than
\ max-n (review reuse-out L1), and 2,000 random sorted arrays against a
\ linear search. Loaded under HEX: the
\ module must not depend on BASE. T{ }T checks results and stack depth.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/bits.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T

\ ---- The interface (ADR 0010).
T{ [defined] cell-bits [defined] log2-ceiling [defined] bits>cells [defined] bit@
   [defined] bit-on [defined] lower-bound -> true true true true true true }T
T{ [defined] count-cell-bits [defined] bit-cell [defined] lb-mid [defined] lb-half
   [defined] bit-off -> false false false false false }T

\ ---- cell-bits: a cell's bits, whatever an address unit holds.
T{ 1 cell-bits 1- lshift 0< 1 cell-bits 1- lshift 2* -> true 0 }T
T{ cell-bits 8 mod cell-bits 32 < -> 0 false }T

\ ---- log2-ceiling: the smallest k with 2^k >= u.
T{ 1 log2-ceiling 2 log2-ceiling 3 log2-ceiling 4 log2-ceiling 5 log2-ceiling -> 0 1 2 2 3 }T
: power-ok? ( k -- flag )
  1 over lshift dup log2-ceiling swap 1+ log2-ceiling rot tuck 1+ = -rot = and ;
: powers-ok? ( -- flag ) true cell-bits 1- 1 ?do i power-ok? and loop ;
T{ powers-ok? 1 cell-bits 1- lshift log2-ceiling max-n log2-ceiling -> true cell-bits 1- cell-bits 1- }T
T{ 1000 log2-ceiling 1024 log2-ceiling 1025 log2-ceiling -> 10 10 11 }T

\ ---- bits>cells: the cells n bits take.
T{ 0 bits>cells 1 bits>cells cell-bits bits>cells cell-bits 1+ bits>cells -> 0 1 1 2 }T
T{ cell-bits 3 * bits>cells cell-bits 3 * 1- bits>cells -> 3 3 }T

\ ---- Bit sets: set and read bits in the first, a middle and the last
\ cell; the cells around are left alone.
create guard-lo -1 ,  create set 3 cells allot  create guard-hi -1 ,
set 3 cells erase
: last-bit ( -- i ) cell-bits 3 * 1- ;
T{ 0 set bit@ last-bit set bit@ -> false false }T
0 set bit-on  cell-bits 1+ set bit-on  last-bit set bit-on
T{ 0 set bit@ 1 set bit@ cell-bits set bit@ cell-bits 1+ set bit@ last-bit set bit@
   -> true false false true true }T
T{ set @ set cell+ @ set 2 cells + @ 0< -> 1 2 true }T
T{ guard-lo @ guard-hi @ -> -1 -1 }T
set 3 cells erase
5 set bit-on 5 set bit-on
T{ 5 set bit@ set @ 7 set ' bit@ rs-checked -> true 32 false }T

\ ---- lower-bound: the first index in lo..hi-1 whose element is not
\ below the sought one, or hi.
create sorted 2 , 3 , 5 , 7 , 11 ,
: below? ( x k -- x flag ) cells sorted + @ over < ;
T{ 5 0 5 ' below? lower-bound 6 0 5 ' below? lower-bound -> 5 2 6 3 }T
T{ 1 0 5 ' below? lower-bound 2 0 5 ' below? lower-bound 12 0 5 ' below? lower-bound
   -> 1 0 2 0 12 5 }T
T{ 11 0 5 ' below? lower-bound 7 2 4 ' below? lower-bound 7 4 5 ' below? lower-bound
   -> 11 4 7 3 7 4 }T
\ Empty ranges give lo; one element.
T{ 9 3 3 ' below? lower-bound 9 4 2 ' below? lower-bound 9 4 5 ' below? lower-bound
   -> 9 3 9 4 9 4 }T
\ Duplicates: the first of the equal ones.
create dups 1 , 4 , 4 , 4 , 9 ,
: dup-below? ( x k -- x flag ) cells dups + @ over < ;
T{ 4 0 5 ' dup-below? lower-bound 5 0 5 ' dup-below? lower-bound -> 4 1 5 4 }T
\ A test with two values below k (a key and a table), as a record's search
\ would; the return stack is the caller's again afterwards.
: in-table? ( x table k -- x table flag ) cells over + @ 2 pick < ;
T{ 7 sorted 0 5 ' in-table? lower-bound 7 sorted 0 5 ' in-table? ' lower-bound rs-checked
   -> 7 sorted 3 7 sorted 3 }T
\ The test is asked about log2 (hi - lo) + 1 times at most.
variable asked
: counted? ( x k -- x flag ) 1 asked +! below? ;
T{ 0 asked ! 12 0 5 ' counted? lower-bound asked @ 4 < -> 12 5 true }T
\ Ranges wider than max-n: hi - lo does not fit a signed cell, yet each
\ search halves to its answer in at most cell-bits + 1 tests (element k
\ is k; the test gives up, false, after 200, so a search that cannot
\ halve ends with a wrong answer instead of running on).
: k-below? ( x k -- x flag )
  1 asked +! asked @ 200 < if over < else drop false then ;
: wide ( x -- x k asked ) 0 asked ! max-n invert 2 + max-n 1- ['] k-below? lower-bound asked @ ;
: wide-ok? ( x -- flag ) dup wide cell-bits 2 + < >r nip = r> and ;
T{ 0 wide-ok? -1 wide-ok? 1 wide-ok? max-n 2 - wide-ok? max-n invert 3 + wide-ok?
   -> true true true true true }T
T{ max-n wide drop nip max-n invert wide drop nip -> max-n 1- max-n invert 2 + }T

\ ---- Random sorted arrays against a linear search.
variable bits-seed  20261113 bits-seed !
: next-random ( -- u ) bits-seed @ 1103515245 * 12345 + $7fffffff and dup bits-seed ! ;
create arr 64 cells allot
variable arr#
: arr-fill ( -- ) next-random 64 mod arr# !  0 arr# @ 0 ?do next-random 4 mod + dup i cells arr + ! loop drop ;
: arr-below? ( x k -- x flag ) cells arr + @ over < ;
: linear ( x -- k ) arr# @ 0 ?do i cells arr + @ over < 0= if drop i unloop exit then loop drop arr# @ ;
variable misses
: one-search ( -- )
  arr-fill next-random 200 mod dup 0 arr# @ ['] arr-below? lower-bound nip swap linear <> if 1 misses +! then ;
: searches ( n -- ) 0 ?do one-search loop ;
T{ 0 misses ! 2000 searches misses @ -> 0 }T

\ ---- The header's example.
create seen 100 bits>cells cells allot  seen 100 bits>cells cells erase
5 seen bit-on
T{ 5 seen bit@ 6 seen bit@ 1000 log2-ceiling -> true false 10 }T
bye
