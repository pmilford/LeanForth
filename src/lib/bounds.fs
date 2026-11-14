\ Range and memory predicates used to validate input before forming
\ addresses. Signed comparisons only, so no bound can wrap around. No state.
\ Interface: between? upto? cells-zero? cells= index? cells-index cells-has?.
\ Example:
\   create primes 2 , 3 , 5 , 7 ,   create odds 3 , 5 , 7 ,
\   3 4 index?  4 4 index?  0 -1 index?    \ true false false
\   5 primes 4 cells-index                 \ 2 true
\   4 primes 4 cells-index  7 primes 4 cells-has?    \ false true
\   primes cell+ odds 3 cells=  primes odds 3 cells=   \ true false

require ./portability.fs

\ True when lo <= n <= hi; false whenever hi < lo.
: between? ( n lo hi -- flag ) rot tuck < 0= -rot swap < 0= and ;
\ True when 0 <= n <= limit; false for any negative limit.
: upto? ( n limit -- flag ) 0 swap between? ;

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
