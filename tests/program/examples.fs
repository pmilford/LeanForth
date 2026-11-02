\ Run from the repository root: .tools/gforth/bin/gforth tests/program/examples.fs
\ Finite host-runtime tests only; these do not prove the words correct.
include ../support/tester.fs
include ../../src/program/examples.fs

T{ 0 0 lf-checked-add -> 0 true }T
T{ -5 3 lf-checked-add -> -2 true }T
T{ 5 -3 lf-checked-add -> 2 true }T
T{ lf-example-max 0 lf-checked-add -> lf-example-max true }T
T{ lf-example-min 0 lf-checked-add -> lf-example-min true }T
T{ lf-example-max 1 lf-checked-add -> false }T
T{ 1 lf-example-max lf-checked-add -> false }T
T{ lf-example-min -1 lf-checked-add -> false }T
T{ -1 lf-example-min lf-checked-add -> false }T
T{ lf-example-min lf-example-max lf-checked-add -> -1 true }T
T{ lf-example-max -1 lf-checked-add -> lf-example-max 1- true }T
T{ lf-example-min 1 lf-checked-add -> lf-example-min 1+ true }T
\ Sums exactly at either limit must be accepted, in both argument orders.
\ T{ also requires the canonical true flag, not merely a nonzero one.
T{ lf-example-max 1- 1 lf-checked-add -> lf-example-max true }T
T{ 1 lf-example-max 1- lf-checked-add -> lf-example-max true }T
T{ 0 lf-example-max lf-checked-add -> lf-example-max true }T
T{ 0 lf-example-min lf-checked-add -> lf-example-min true }T
T{ lf-example-min 1+ -1 lf-checked-add -> lf-example-min true }T
T{ -1 lf-example-min 1+ lf-checked-add -> lf-example-min true }T
\ Large operands from the host cell, not the 32-bit or near-zero values.
\ With h = max/2 + 1, h + (h - 1) is the maximum and h + h overflows; -h + -h
\ is the minimum and -h + -(h + 1) overflows. No arithmetic here can wrap.
lf-example-max 2/ 1+ constant test-half
T{ test-half test-half 1- lf-checked-add -> lf-example-max true }T
T{ test-half 1- test-half lf-checked-add -> lf-example-max true }T
T{ test-half test-half lf-checked-add -> false }T
T{ test-half negate test-half negate lf-checked-add -> lf-example-min true }T
T{ test-half negate test-half 1+ negate lf-checked-add -> false }T
T{ test-half 1+ negate test-half negate lf-checked-add -> false }T

T{ 0 lf-checked-abs -> 0 true }T
T{ -7 lf-checked-abs -> 7 true }T
T{ 7 lf-checked-abs -> 7 true }T
T{ lf-example-min lf-checked-abs -> false }T
T{ lf-example-min 1+ lf-checked-abs -> lf-example-max true }T
T{ lf-example-max lf-checked-abs -> lf-example-max true }T

T{ -1 lf-factorial -> false }T
T{ lf-example-min lf-factorial -> false }T
T{ 0 lf-factorial -> 1 true }T
T{ 1 lf-factorial -> 1 true }T
T{ 5 lf-factorial -> 120 true }T
T{ 10 lf-factorial -> 3628800 true }T
T{ 12 lf-factorial -> 479001600 true }T
T{ lf-example-max lf-factorial -> false }T
\ Independently known first overflowing inputs for 32- and 64-bit cells.
: check-known-factorial-limit ( -- )
  lf-example-max 2147483647 = if
    13 lf-factorial false <> if -1 throw then
  else
    1 cells 8 * 64 = if
      20 lf-factorial true <> if -1 throw then drop
      21 lf-factorial false <> if -1 throw then
    then
  then ;
check-known-factorial-limit
\ Independently find the last representable factorial, then check both sides
\ of the transition without assuming a particular host-cell width.
: check-factorial-boundary ( -- )
  1 1 begin
    2dup lf-example-max swap / <=
  while
    tuck * swap 1+
  repeat
  dup lf-factorial false <> if -1 throw then
  1- lf-factorial true <> if -1 throw then
  <> if -1 throw then ;
check-factorial-boundary

T{ 0 0 lf-gcd -> 0 true }T
T{ 0 17 lf-gcd -> 17 true }T
T{ 17 0 lf-gcd -> 17 true }T
T{ 48 18 lf-gcd -> 6 true }T
T{ 18 48 lf-gcd -> 6 true }T
T{ 35 64 lf-gcd -> 1 true }T
T{ -1 2 lf-gcd -> false }T
T{ 2 -1 lf-gcd -> false }T
T{ lf-example-min lf-example-min lf-gcd -> false }T
T{ lf-example-max 0 lf-gcd -> lf-example-max true }T
T{ lf-example-max lf-example-max lf-gcd -> lf-example-max true }T
T{ lf-example-max 1 lf-gcd -> 1 true }T
\ Either negative input is rejected, including the minimum cell beside zero.
T{ 0 lf-example-min lf-gcd -> false }T
T{ lf-example-min 0 lf-gcd -> false }T
T{ 0 -1 lf-gcd -> false }T
\ Consecutive integers are coprime, at the top of the host-cell range.
T{ lf-example-max lf-example-max 1- lf-gcd -> 1 true }T
T{ lf-example-max 1- lf-example-max lf-gcd -> 1 true }T
\ Euclid's worst case is a pair of consecutive Fibonacci numbers. F(46) and
\ F(45) fit a signed 32-bit cell and need over 40 remainder steps; F(30) and
\ F(29) scaled by 7 check that a common factor survives a long chain.
T{ 1836311903 1134903170 lf-gcd -> 1 true }T
T{ 1134903170 1836311903 lf-gcd -> 1 true }T
T{ 5824280 3599603 lf-gcd -> 7 true }T
\ Known answers independent of the Lean model, for 64-bit cells only (21!
\ fits a wider cell). [IF] skips the literals on 32-bit hosts, where they are
\ not single-cell numbers.
1 cells 8 = [IF]
\ F(92) and F(91): the largest consecutive Fibonacci pair in a signed 64-bit
\ cell, about 90 remainder steps.
T{ 7540113804746346429 4660046610375530309 lf-gcd -> 1 true }T
T{ 13 lf-factorial -> 6227020800 true }T
T{ 20 lf-factorial -> 2432902008176640000 true }T
T{ 21 lf-factorial -> false }T
[THEN]

T{ 5 0 10 lf-in-range -> true true }T
T{ 0 0 10 lf-in-range -> true true }T
T{ 10 0 10 lf-in-range -> true true }T
T{ -1 0 10 lf-in-range -> false true }T
T{ 11 0 10 lf-in-range -> false true }T
T{ 3 3 3 lf-in-range -> true true }T
T{ 2 3 3 lf-in-range -> false true }T
T{ 5 10 0 lf-in-range -> false }T
T{ lf-example-min lf-example-min lf-example-max lf-in-range -> true true }T
T{ lf-example-max lf-example-min lf-example-max lf-in-range -> true true }T
T{ 0 lf-example-max lf-example-min lf-in-range -> false }T

\ Preserve caller stack context on success and failure.
: example-frame ( n -- result true marker | false marker )
  987 >r lf-checked-abs r> ;
T{ 123 -4 example-frame -> 123 4 true 987 }T
T{ 123 lf-example-min example-frame -> 123 false 987 }T
T{ 123 4 5 lf-checked-add -> 123 9 true }T
T{ 123 lf-example-max 1 lf-checked-add -> 123 false }T
T{ 123 5 lf-factorial -> 123 120 true }T
T{ 123 lf-example-max lf-factorial -> 123 false }T
T{ 123 48 18 lf-gcd -> 123 6 true }T
T{ 123 -1 2 lf-gcd -> 123 false }T
T{ 123 5 0 10 lf-in-range -> 123 true true }T
T{ 123 5 10 0 lf-in-range -> 123 false }T

\ Exhaustively compare small signed additions with host arithmetic, where
\ the reference sum cannot overflow, and intervals with direct comparisons.
: check-small-additions ( -- )
  9 -8 do 9 -8 do
    i j lf-checked-add true <> if -1 throw then
    i j + <> if -1 throw then
  loop loop ;
check-small-additions

variable test-value
variable test-lower
variable test-upper
: check-small-intervals ( -- )
  4 -3 do i test-value !
    4 -3 do i test-lower !
      4 -3 do i test-upper !
        test-value @ test-lower @ test-upper @ lf-in-range
        test-lower @ test-upper @ > if
          false <> if -1 throw then
        else
          true <> if -1 throw then
          test-value @ test-lower @ >=
          test-value @ test-upper @ <= and <> if -1 throw then
        then
      loop
    loop
  loop ;
check-small-intervals

\ lf-in-range uses the return stack internally. Check that two caller
\ data-stack cells and two caller return-stack cells survive every small
\ triple, including reversed bounds, and that both flags are canonical.
: check-range-frame ( -- )
  101 202 303 >r 404 >r
  test-value @ test-lower @ test-upper @ lf-in-range
  test-lower @ test-upper @ > if
    false <> if -1 throw then
  else
    true <> if -1 throw then
    test-value @ test-lower @ >=
    test-value @ test-upper @ <= and <> if -1 throw then
  then
  r> 404 <> if -1 throw then
  r> 303 <> if -1 throw then
  202 <> if -1 throw then
  101 <> if -1 throw then ;

: check-range-frames ( -- )
  4 -3 do i test-value !
    4 -3 do i test-lower !
      4 -3 do i test-upper ! check-range-frame loop
    loop
  loop ;
check-range-frames

\ Host observation, not a LeanForth guarantee: on Gforth 1.0.0 and the
\ Ubuntu Gforth 0.7.3 package, each word run on an otherwise empty data stack
\ with one input missing throws -4 (stack underflow), which CATCH reports.
\ If the caller's own cells were present, a word would consume them silently
\ instead; no host check can detect that, so stack effects must be checked
\ statically. Other hosts or engines (e.g. gforth-fast) may behave otherwise.
: underflow-add ( -- ) 1 lf-checked-add ;
: underflow-abs ( -- ) lf-checked-abs ;
: underflow-factorial ( -- ) lf-factorial ;
: underflow-gcd ( -- ) 1 lf-gcd ;
: underflow-range ( -- ) 1 2 lf-in-range ;

\ ( xt -- ) Execute xt with nothing else on the data stack; expect -4.
: check-underflow
  depth 1 <> abort" underflow check needs an otherwise empty data stack"
  catch -4 <> abort" expected the host stack-underflow exception -4"
  depth 0<> abort" underflow check left data-stack items" ;
' underflow-add check-underflow
' underflow-abs check-underflow
' underflow-factorial check-underflow
' underflow-gcd check-underflow
' underflow-range check-underflow
bye
