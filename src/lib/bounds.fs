\ Range and memory predicates used to validate input before forming
\ addresses. Signed comparisons only, so no bound can wrap around.
\ No state. Requires: portability.fs.

\ True when lo <= n <= hi; false whenever hi < lo.
: between? ( n lo hi -- flag ) rot tuck < 0= -rot swap < 0= and ;
\ True when 0 <= n <= limit; false for any negative limit.
: upto? ( n limit -- flag ) 0 swap between? ;

\ True when the n cells starting at addr are all zero; n <= 0 reads nothing
\ and is true.
: cells-zero? ( addr n -- flag )
  0 max 0 ?do dup @ if drop false unloop exit then cell+ loop drop true ;
