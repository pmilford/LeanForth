\ Actual Forth observations; the sentinel and depth check both result paths.
\ Requires 64-bit two's-complement cells and the assumptions in examples.fs.
require ../../src/program/examples.fs
decimal
: ar-check-cell ( -- )
  1 cells 8 <> abort" abs-reference requires 64-bit cells"
  lf-example-max 9223372036854775807 <> abort" unexpected signed cell maximum" ;
ar-check-cell
: ar-row ( n -- )
  dup .
  12345 swap lf-checked-abs
  dup true = if
    drop . ." ok"
  else
    false <> abort" lf-checked-abs returned a noncanonical flag"
    ." invalid"
  then
  12345 <> abort" lf-checked-abs damaged the stack sentinel"
  depth 0<> abort" lf-checked-abs left extra stack items"
  cr ;
: ar-small ( -- ) 129 -128 do i ar-row loop ;
: ar-extremes ( -- )
  lf-example-min ar-row
  lf-example-min 1+ ar-row
  lf-example-min 2 + ar-row
  lf-example-max 2 - ar-row
  lf-example-max 1- ar-row
  lf-example-max ar-row ;
ar-small ar-extremes bye
