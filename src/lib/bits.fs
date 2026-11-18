\ Bits of cells, bit sets and binary search. A general tool with no Lean
\ knowledge; untrusted. Written for the copies the 2026-11-13 library
\ audit found (action 9, plan 9.4.8d): the cell's width counted by hand
\ in five modules (two of them assuming 8-bit address units), log2 by
\ hand in three, bit sets in the feed, the axiom rows and the reach
\ tables, and three hand-written binary searches.
\
\ The method. cell-bits counts a cell's bits once, when the file loads,
\ by shifting max-n right until it is zero (never `1 cells 8 *`, which
\ assumes 8-bit address units). log2-ceiling shifts u-1 right until it
\ is zero: the smallest k with 2^k >= u. A bit set is a run of cells,
\ bit i in cell i / cell-bits at i mod cell-bits; bits>cells gives the
\ cells n bits take. lower-bound halves the range lo..hi (Knuth's
\ Algorithm B, TAOCP 6.2.1, in its "first not below" form): it asks the
\ caller's test of index k whether element k lies below the sought one,
\ about log2 (hi - lo) + 1 times, and gives the first k of lo..hi whose
\ element does not, hi when every one does.
\
\ Genericity. Bit indices from 0, unchecked (the caller keeps i below
\ the set's size); any cell width. lower-bound knows nothing of the
\ elements: the test xt ( i*x k -- i*x flag ) reads them, with the
\ values below k its own (as lib/outcome.fs's all? gives them), so a
\ search may carry the sought key and a record; the elements from lo to
\ hi-1 must be ordered so that the test is true for a prefix of them.
\ Cost: bit words constant time; lower-bound O(log (hi - lo)) tests, no
\ memory, no recursion.
\
\ Example:
\   1000 log2-ceiling .  cell-bits 32 >= .  \ 10 -1 (cells of 32 bits or more)
\   create seen 100 bits>cells cells allot  seen 100 bits>cells cells erase
\   5 seen bit-on  5 seen bit@ .  6 seen bit@ .  \ -1 0
\   create sorted 2 , 3 , 5 , 7 , 11 ,
\   : below? ( x k -- x flag ) cells sorted + @ over < ;
\   5 0 5 ' below? lower-bound nip .        \ 2: sorted[2] = 5
\   6 0 5 ' below? lower-bound nip .        \ 3: the first above 6
\   \ prints: 10 -1 -1 0 2 3
\
\ Interface: cell-bits log2-ceiling bits>cells bit@ bit-on lower-bound.
\ State: none (cell-bits is a constant). Requires
\ portability.fs and module.fs; helpers private in lf-lib-private (ADR
\ 0010). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./module.fs

lf-lib-private module-open

: count-cell-bits ( -- n ) 0 max-n begin ?dup while 1 rshift swap 1+ swap repeat 1+ ;
lf-lib set-current
\ The bits of a cell.
count-cell-bits constant cell-bits
\ The smallest log2 with 2^log2 >= u, for u >= 1 (0 for u = 1).
: log2-ceiling ( u -- log2 ) 1- 0 swap begin ?dup while 1 rshift swap 1+ swap repeat ;
\ The cells that hold n bits, n >= 0.
: bits>cells ( n -- cells ) cell-bits 1- + cell-bits / ;
lf-lib-private set-current
\ Bit i's cell and its mask in it.
: bit-cell ( i a-addr -- a-addr' mask )
  over cell-bits / cells + swap cell-bits mod 1 swap lshift ;
lf-lib set-current
\ Bit i of the set at a-addr: read, set. (No caller clears a bit: the
\ sets are erased whole.)
: bit@ ( i a-addr -- flag ) bit-cell swap @ and 0<> ;
: bit-on ( i a-addr -- ) bit-cell over @ or swap ! ;
lf-lib-private set-current

\ One halving of lo..hi at mid: above mid when element mid is below.
\ hi - lo, for lo < hi, is taken unsigned: it fits a cell even when it
\ does not fit a signed one (lo near min-n, hi near max-n).
: lb-mid ( lo hi -- mid ) over - 1 rshift + ;
: lb-half ( lo hi mid below? -- lo' hi' ) if 1+ rot drop swap else nip then ;
lf-lib set-current
\ The first k in lo..hi-1 whose element is not below the sought one,
\ by the test xt ( i*x k -- i*x flag ), true when element k is below;
\ hi when every one is (and lo for an empty range, hi <= lo). The test
\ runs with xt, lo, hi and k on the return stack, the values below k its
\ own. Any signed lo and hi.
: lower-bound ( i*x lo hi xt -- i*x k )
  >r 2>r begin 2r@ < while
    2r@ lb-mid 2r> r@ -rot 2>r over >r execute r> 2r> 2swap swap lb-half 2>r
  repeat 2r> drop r> drop ;

module-close
base !   \ the BASE this file was loaded with
