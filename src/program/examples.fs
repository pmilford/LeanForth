\ Ordinary executable Forth examples, runtime-tested but not proved.
\ Assumes two's-complement signed cells, logical RSHIFT, standard Forth
\ signed comparisons and division, and sufficient data/return stack space.
\ Inputs and outputs are single host cells; no arithmetic wraps on success.

-1 1 rshift constant lf-example-max
lf-example-max invert constant lf-example-min

\ ( a b -- sum true | false ) Reject signed overflow before adding.
: lf-checked-add
  dup 0> if
    2dup lf-example-max swap - > if 2drop false exit then
  else
    dup 0< if
      2dup lf-example-min swap - < if 2drop false exit then
    then
  then
  + true ;

\ ( n -- magnitude true | false ) The minimum cell has no positive
\ single-cell magnitude; all other signed inputs are accepted.
: lf-checked-abs
  dup lf-example-min = if drop false exit then
  dup 0< if negate then true ;

\ ( n -- factorial true | false ) Reject negative inputs and any result
\ above lf-example-max. 0! is 1. Division is of nonnegative values.
: lf-factorial
  dup 0< if drop false exit then
  1 swap
  begin dup 1 > while
    2dup lf-example-max swap / > if 2drop false exit then
    tuck * swap 1-
  repeat
  drop true ;

\ ( a b -- gcd true | false ) Euclid's algorithm for nonnegative cells;
\ gcd(0,0) is defined here as 0. Negative inputs are rejected.
: lf-gcd
  2dup 0< swap 0< or if 2drop false exit then
  begin dup 0<> while tuck mod repeat
  drop true ;

\ ( value lower upper -- flag true | false ) Test membership in an
\ inclusive signed interval. Reversed bounds return false without a flag.
: lf-in-range
  2dup > if 2drop drop false exit then
  >r 2dup >= nip swap r> <= and true ;
