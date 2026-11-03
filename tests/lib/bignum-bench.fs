\ Timing of src/lib/bignum.fs for tests/lib/bignum_bench.py; report only,
\ Gforth only (utime). Each line of the bench file is
\   OP A B
\ with OP one of add sub mul div mod gcd pow parse print (parse reads A's
\ text, print writes A's digits; B is then ignored), and prints the
\ nanoseconds one operation took: the operation is repeated, doubling the
\ count, until the runs take at least 0.2 s. Every run gives its numbers
\ back. Usage, from the repository root:
\   gforth-fast tests/lib/bignum-bench.fs -e 's" FILE" run-bench bye'
\ Test-only; global variables are fine.
require ./bignum-cases.fs
decimal

variable bench-a  variable bench-b  variable bench-xt  2variable bench-text
: one-run ( -- )
  arena big-mark bench-a @ bench-b @ bench-xt @ execute arena big-release drop ;
: us-since ( d -- n ) utime 2swap d- drop ;
: time-runs ( reps -- us ) utime rot 0 ?do one-run loop us-since ;
: ns-per-op ( -- ns )
  1 begin dup time-runs dup 200000 < while drop 2* repeat 1000 rot */ ;

\ One run of each operation, ( a b -- ), its results left for one-run to give back.
wordlist constant timed-ops
get-current timed-ops set-current
: add ( a b -- ) arena big+ 2drop ;
: sub ( a b -- ) arena big- 2drop ;
: mul ( a b -- ) arena big* 2drop ;
: div ( a b -- ) arena big/ 2drop ;
: mod ( a b -- ) arena big-mod 2drop ;
: gcd ( a b -- ) arena big-gcd 2drop ;
: pow ( a b -- ) arena big-pow 2drop ;
: parse ( a b -- ) 2drop bench-text 2@ arena decimal>big 2drop ;
: print ( a b -- ) drop arena big>decimal 2drop drop ;
set-current

: bench-line ( addr u -- )
  arena big-mark >r token timed-ops search-wordlist 0= abort" unknown operation"
  bench-xt ! 2dup token bench-text 2! 2drop
  operands 0= abort" bad operands" bench-b ! bench-a !
  ns-per-op 0 .r cr r> arena big-release drop ;
: run-bench ( c-addr u -- )
  r/o open-file throw >r
  begin line line-max r@ read-line throw while line swap bench-line repeat drop
  r> close-file throw ;
