\ Range and memory predicates used to validate input before forming
\ addresses: index and range tests compare signed, so no bound wraps
\ around; and cell-counted records, laid down and read back, whose
\ bounded writers compare a length unsigned, so a length with the top bit
\ set (a negative u) never fits. No state.
\ Interface: cell-pair@ cell-pair! cell-triple@ cell-triple! between? upto?
\ range-at in-ranges? cells-zero? cells= index? cells-index cells-has?
\ cell-at@ pair-at record-at first-nonzero first-or-second one-of2?
\ one-of3? cell-tally cell-spend? epoch+ cell-counted, cell-count cell-counted! cell-counted+!
\ cell-counted-left cell-counted+?. Requires portability.fs, outcome.fs
\ (any?, 2dup-under) and module.fs; helpers are private in lf-lib-private
\ (ADR 0010).
\ Example:
\   create primes 2 , 3 , 5 , 7 ,   create odds 3 , 5 , 7 ,
\   3 4 index? .  4 4 index? .  5 primes 4 cells-index . .
\   primes cell+ odds 3 cells= .
\   create buf 0 , 8 allot            \ a buffer of 8 bytes after its count
\   s" abc" buf 8 cell-counted+? .  buf 8 cell-counted-left .
\   s" defghi" buf 8 cell-counted+? .  buf cell-count type
\   \ prints: -1 0 -1 2 -1 -1 5 0 abc
\ More cases, with their results:
\   create primes 2 , 3 , 5 , 7 ,   create odds 3 , 5 , 7 ,
\   3 4 index?  4 4 index?  0 -1 index?    \ true false false
\   5 primes 4 cells-index                 \ 2 true
\   4 primes 4 cells-index  7 primes 4 cells-has?    \ false true
\   primes cell+ odds 3 cells=  primes odds 3 cells=   \ true false
\   create digits 48 , 57 ,  65 , 70 ,       \ 0-9 and A-F
\   char 7 digits 2 in-ranges?  char G digits 2 in-ranges?   \ true false
\   create two 0 , 0 ,   1 2 two cell-pair!  two @  two cell-pair@   \ 1 1 2
\   create three 0 , 0 , 0 ,   4 5 6 three cell-triple!  three cell-triple@
\                                                       \ 4 5 6
\   7 5 7 one-of2?  6 5 7 one-of2?  3 1 2 3 one-of3?    \ true false true

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./outcome.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
\ True when lo <= n <= hi; false whenever hi < lo.
: between? ( n lo hi -- flag ) rot tuck < 0= -rot swap < 0= and ;
\ True when 0 <= n <= limit; false for any negative limit.
: upto? ( n limit -- flag ) 0 swap between? ;
\ Two adjacent cells in the order they lie in memory, x1 at addr and x2 in
\ the next cell (2@ and 2! keep the top of the stack at addr instead): two
\ neighbouring fields of a record read or written together where each is
\ also used alone, or whose layout is fixed. Unchecked, as @ and !.
: cell-pair@ ( addr -- x1 x2 ) 2@ swap ;
: cell-pair! ( x1 x2 addr -- ) tuck cell+ ! ! ;
\ The same for three adjacent cells, x1 at addr: a record's three
\ neighbouring fields.
: cell-triple@ ( addr -- x1 x2 x3 ) dup @ swap cell+ cell-pair@ ;
: cell-triple! ( x1 x2 x3 addr -- ) tuck 2 cells + ! cell-pair! ;
\ Whether lo <= x <= hi for one of the n pairs (lo, hi) of cells from
\ a-addr (a table of ranges, such as a character class); n <= 0 holds
\ none. range-at gives pair k; in-range-at? is in-ranges?'s test of it.
: range-at ( a-addr k -- lo hi ) 2* cells + cell-pair@ ;
lf-lib-private set-current
: in-range-at? ( x a-addr k -- x a-addr flag ) 2dup-under range-at between? ;
lf-lib set-current
: in-ranges? ( x a-addr n -- flag ) ['] in-range-at? any? nip nip ;

\ True when the n cells starting at addr are all zero; n <= 0 reads nothing
\ and is true.
: cells-zero? ( addr n -- flag )
  0 max 0 ?do dup @ if drop false unloop exit then cell+ loop drop true ;
\ True when the n cells from a-addr1 equal the n cells from a-addr2, cell
\ by cell (never as bytes, so padding and host byte order do not matter);
\ n <= 0 reads nothing and is true.
: cells= ( a-addr1 a-addr2 n -- flag )
  0 max 0 ?do over i cells + @ over i cells + @ <> if 2drop false unloop exit then loop
  2drop true ;
\ True when 0 <= i < n, i an index into n items; false whenever n <= 0
\ (`0 n within` would take every i >= 0 for a negative n).
: index? ( i n -- flag ) over 0< if 2drop false else < then ;
\ The first index i < n whose cell, in the n cells from addr, holds x,
\ and true; or false. n <= 0 reads nothing.
: cells-index ( x addr n -- i true | false )
  0 max 0 ?do 2dup i cells + @ = if 2drop i true unloop exit then loop 2drop false ;
\ Whether one of the n cells from addr holds x.
: cells-has? ( x addr n -- flag ) cells-index dup if nip then ;
\ Element i of an array of cells at a-addr; the address of pair i of an
\ array of cell pairs (2@ and 2! read and write it); the address of
\ record i, of size bytes each, from a-addr. Unchecked: the caller keeps
\ i within the array (index? first).
: cell-at@ ( i a-addr -- x ) swap cells + @ ;
: pair-at ( i a-addr -- addr ) swap 2* cells + ;
: record-at ( i size a-addr -- addr ) >r * r> + ;
\ The first of two values that is not zero, else zero: the first failure
\ of two steps that give 0 for success (an ior, an image). The same code
\ as outcome.fs's outcome-and, whose ok is 0; that one names outcomes.
: first-nonzero ( x1 x2 -- x ) over if drop else nip then ;
\ x1 when n is 1, else x2: one of two values by its place from 1.
: first-or-second ( x1 x2 n -- x ) 1 = if drop else nip then ;
\ Whether x equals a or b (one-of2?), or one of a, b and c (one-of3?):
\ a kind, tag, mode or character tested against two or three values.
: one-of2? ( x a b -- flag ) >r over = swap r> = or ;
: one-of3? ( x a b c -- flag ) >r >r over = over r> = or swap r> = or ;
\ One more in cell i of an array of counts at a-addr (unchecked, as
\ cell-at@).
: cell-tally ( i a-addr -- ) swap cells + 1 swap +! ;
\ One unit spent from the count at a-addr when it is above zero: true;
\ else false and the count unchanged (a fuel or work budget).
: cell-spend? ( a-addr -- flag ) dup @ 0> if -1 swap +! true else drop false then ;
\ A generation counter one step on: 1+, saturating to -1 (poisoned)
\ instead of wrapping at max-n, and once negative it stays.
: epoch+ ( generation -- generation' )
  dup 0< if exit then dup max-n = if drop -1 else 1+ then ;
\ A cell-counted array or text: its count in the first cell, its cells
\ or bytes after it. cell-counted, compiles text of any length as one
\ (its length in a cell, then its bytes), then aligns: for tables of
\ names and messages built while loading. cell-count reads one back: the
\ address after the count and the count, as COUNT gives a counted
\ string's (unchecked: addr holds such a record).
: cell-counted, ( c-addr u -- ) dup , here swap dup allot move align ;
: cell-count ( addr -- addr' n ) dup cell+ swap @ ;
\ The same as a buffer of room bytes after its count cell (a record's
\ text field): cell-counted! puts the text c-addr u in it (true; false,
\ nothing changed, when u is more than room), cell-counted+! appends it
\ (unchecked: the caller made sure it fits). Lengths compare unsigned.
: cell-counted! ( c-addr u addr room -- flag )
  2 pick u< if drop 2drop false exit then 2dup ! cell+ swap move true ;
: cell-counted+! ( c-addr u addr -- ) 2dup +! cell-count + over - swap move ;
\ The same buffer, bounded: cell-counted-left gives the bytes still free
\ (room less the count), and cell-counted+? appends c-addr u only when it
\ fits (true; false, nothing changed, when it does not), so the caller
\ chooses to drop the text, clip it (`cell-counted-left min` first) or
\ fail.
: cell-counted-left ( addr room -- n ) swap @ - ;
: cell-counted+? ( c-addr u addr room -- flag )
  over swap cell-counted-left 0 max 2 pick u< if drop 2drop false exit then
  cell-counted+! true ;

module-close
base !   \ the BASE this file was loaded with
