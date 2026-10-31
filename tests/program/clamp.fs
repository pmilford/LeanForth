\ Runtime examples for the ordinary host-cell clamp; not a formal proof.
\ Include normal, boundary, negative and invalid-precondition cases.
include ../support/tester.fs
include ../../src/program/clamp.fs

T{ -1 0 10 lf-clamp -> 0 true }T
T{ 0 0 10 lf-clamp -> 0 true }T
T{ 4 0 10 lf-clamp -> 4 true }T
T{ 10 0 10 lf-clamp -> 10 true }T
T{ 11 0 10 lf-clamp -> 10 true }T
T{ -20 -10 -5 lf-clamp -> -10 true }T
T{ -7 -10 -5 lf-clamp -> -7 true }T
T{ -1 -10 -5 lf-clamp -> -5 true }T
T{ -1 3 3 lf-clamp -> 3 true }T
T{ 3 3 3 lf-clamp -> 3 true }T
T{ 5 3 3 lf-clamp -> 3 true }T
T{ 5 10 0 lf-clamp -> false }T
\ Host regression: a data-stack prefix and a caller's return-stack value
\ survive both ordered and reversed-bound paths. This is not a runtime proof.
: clamp-return-stack-probe ( value lower upper -- result true marker | false marker )
  765 >r lf-clamp r> ;
T{ 123 4 0 10 lf-clamp -> 123 4 true }T
T{ 123 4 10 0 lf-clamp -> 123 false }T
T{ 123 4 0 10 clamp-return-stack-probe -> 123 4 true 765 }T
T{ 123 4 10 0 clamp-return-stack-probe -> 123 false 765 }T
\ Exercise host comparisons at signed 32-bit limits without arithmetic.
T{ -2147483648 -2147483648 2147483647 lf-clamp -> -2147483648 true }T
T{ 2147483647 -2147483648 2147483647 lf-clamp -> 2147483647 true }T
T{ -2147483648 2147483647 2147483647 lf-clamp -> 2147483647 true }T
T{ 2147483647 -2147483648 -2147483648 lf-clamp -> -2147483648 true }T
T{ 0 2147483647 -2147483648 lf-clamp -> false }T
\ Exercise the actual host-cell extrema, independent of the cell width.
-1 1 rshift constant test-cell-max
test-cell-max invert constant test-cell-min
T{ test-cell-min test-cell-min test-cell-max lf-clamp -> test-cell-min true }T
T{ test-cell-max test-cell-min test-cell-max lf-clamp -> test-cell-max true }T
T{ test-cell-min test-cell-max test-cell-max lf-clamp -> test-cell-max true }T
T{ test-cell-max test-cell-min test-cell-min lf-clamp -> test-cell-min true }T
T{ 0 test-cell-max test-cell-min lf-clamp -> false }T

\ Independently check every input and bound in [-3, 3], including reversed
\ intervals. This finite regression test does not replace a universal proof.
variable test-lower
variable test-upper
variable test-value

\ Check the current triple against a conditional reference specification.
: check-clamp-triple ( -- )
  test-value @ test-lower @ test-upper @ lf-clamp
  test-lower @ test-upper @ > if
    if -1 throw then
    exit
  then
  0= if -1 throw then
  test-value @ test-lower @ < if
    test-lower @
  else
    test-value @ test-upper @ > if test-upper @ else test-value @ then
  then
  <> if -1 throw then ;

\ Evaluate 343 triples; every result or invalid-input status must agree.
: check-clamp-small-domain ( -- )
  4 -3 do i test-lower !
    4 -3 do i test-upper !
      4 -3 do i test-value ! check-clamp-triple loop
    loop
  loop ;
check-clamp-small-domain

\ Check composition as well as single calls: clamping an already clamped
\ result to the same ordered interval must leave it unchanged. The flag is
\ checked on each call; no assertion is made about reversed intervals here.
variable test-first-result
: check-clamp-idempotence ( -- )
  test-value @ test-lower @ test-upper @ lf-clamp
  0= if -1 throw then
  test-first-result !
  test-first-result @ test-lower @ test-upper @ lf-clamp
  0= if -1 throw then
  test-first-result @ <> if -1 throw then ;

\ Run all 196 ordered triples from the same small domain.
: check-clamp-idempotence-domain ( -- )
  4 -3 do i test-lower !
    4 -3 do i test-upper !
      test-lower @ test-upper @ <= if
        4 -3 do i test-value !
          check-clamp-idempotence loop
      then
    loop
  loop ;
check-clamp-idempotence-domain

\ Mirror clampCode_nested on finite host inputs. The marker is a data-stack
\ prefix; the caller consumes each success flag before the next clamp.
variable test-outer-lower
variable test-outer-upper
variable test-inner-lower
variable test-inner-upper
variable test-nested-result
: check-clamp-nested ( -- )
  123456
  test-value @ test-outer-lower @ test-outer-upper @ lf-clamp
  0= if -1 throw then
  test-inner-lower @ test-inner-upper @ lf-clamp
  0= if -1 throw then
  test-nested-result !
  test-value @ test-inner-lower @ test-inner-upper @ lf-clamp
  0= if -1 throw then
  test-nested-result @ <> if -1 throw then
  123456 <> if -1 throw then ;

\ Seven values times 210 nondecreasing quadruples of bounds: 1470 cases.
: check-clamp-nested-domain ( -- )
  4 -3 do i test-outer-lower !
    4 -3 do i test-inner-lower !
      4 -3 do i test-inner-upper !
        4 -3 do i test-outer-upper !
          test-outer-lower @ test-inner-lower @ <=
          test-inner-lower @ test-inner-upper @ <= and
          test-inner-upper @ test-outer-upper @ <= and if
            4 -3 do i test-value ! check-clamp-nested loop
          then
        loop
      loop
    loop
  loop ;
check-clamp-nested-domain
bye
