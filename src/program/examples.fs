\ Ordinary executable Forth examples, runtime-tested but not proved.
\ Assumes two's-complement signed cells, logical RSHIFT, standard Forth
\ signed comparisons and division, and sufficient data/return stack space.
\ Inputs and outputs are single host cells; no arithmetic wraps on success.
\ Standalone: no other module is needed. State: none.

-1 1 rshift constant lf-example-max
lf-example-max invert constant lf-example-min

\ Signed addition that rejects overflow before adding. The tests are those
\ of the Lean model (tests/reference/checked-add.lean), in its order: a
\ positive b overflows when max - b < a, a negative b when a < min - b.
\ Neither subtraction can wrap.
: lf-add-above? ( a b -- flag ) lf-example-max swap - > ;
: lf-add-below? ( a b -- flag ) lf-example-min swap - < ;
: lf-add-overflow? ( a b -- flag )
  dup 0> if lf-add-above? exit then dup 0< if lf-add-below? else 2drop false then ;
: lf-checked-add ( a b -- sum true | false )
  2dup lf-add-overflow? if 2drop false else + true then ;

\ The minimum cell has no positive single-cell magnitude; all other signed
\ inputs are accepted.
: lf-checked-abs ( n -- magnitude true | false )
  dup lf-example-min = if drop false else abs true then ;

\ Reject negative inputs and any result above lf-example-max; 0! is 1.
\ The product is built in descending factor order, and an overflow is
\ detected before it happens by a division of nonnegative values.
: lf-product-over? ( product n -- flag ) lf-example-max swap / > ;
: lf-factorial-from ( product n -- factorial true | false )
  begin dup 1 > while
    2dup lf-product-over? if 2drop false exit then tuck * swap 1-
  repeat drop true ;
: lf-factorial ( n -- factorial true | false )
  dup 0< if drop false else 1 swap lf-factorial-from then ;

\ Euclid's algorithm for nonnegative cells; gcd(0,0) is defined here as 0.
\ Negative inputs are rejected.
: lf-euclid ( a b -- gcd ) begin dup 0<> while tuck mod repeat drop ;
: lf-gcd ( a b -- gcd true | false )
  2dup 0< swap 0< or if 2drop false else lf-euclid true then ;

\ Membership in an inclusive signed interval. Reversed bounds return false
\ without a flag. Core comparisons only: not lower > value, not value > upper.
: lf-within-closed? ( value lower upper -- flag ) >r over > 0= swap r> > 0= and ;
: lf-in-range ( value lower upper -- flag true | false )
  2dup > if 2drop drop false else lf-within-closed? true then ;
