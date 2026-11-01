\ Finite host observations, not a proof of Forth or its runtime.
\ Requires 64-bit two's-complement cells and examples.fs host assumptions.
include ../../src/program/examples.fs
decimal

: fr-check-cell ( -- )
  1 cells 8 <> abort" factorial-reference requires 64-bit cells"
  lf-example-max 9223372036854775807 <> abort" unexpected cell maximum"
  lf-example-min -9223372036854775808 <> abort" unexpected cell minimum" ;

\ ( n -- ) Print one result; reject a damaged sentinel or wrong stack shape.
: fr-row ( n -- )
  dup .
  12345 swap lf-factorial
  depth 2 < abort" factorial returned too few stack items"
  dup true = if
    depth 3 <> abort" factorial success has wrong stack shape"
    drop . ." ok"
  else
    depth 2 <> abort" factorial failure has wrong stack shape"
    false <> abort" factorial returned a noncanonical flag"
    ." invalid"
  then
  12345 <> abort" factorial damaged the stack sentinel"
  depth 0<> abort" factorial left extra stack items"
  cr ;

\ -128 through the first signed 64-bit overflow at 21, plus negative extremes.
: fr-table ( -- )
  22 -128 do i fr-row loop
  lf-example-min fr-row
  lf-example-min 1+ fr-row ;
fr-check-cell fr-table bye
