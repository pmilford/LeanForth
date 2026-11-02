\ Compare actual host results with the independent Lean model; finite tests
\ are not a proof of Forth or its runtime. This table requires 64-bit cells.
require ../../src/lib/lib.fs
require ../../src/program/examples.fs
decimal
: gr-check ( -- ) 1 cells 8 <> abort" gcd reference requires 64-bit cells" ;
: gr-row ( a b -- )
  over . dup .
  12345 -rot lf-gcd
  dup true = if drop . ." ok" else
    false <> abort" gcd returned a noncanonical flag" ." invalid"
  then
  12345 <> abort" gcd damaged the stack sentinel"
  depth 0<> abort" gcd left extra stack items" cr ;
: gr-table ( -- )
  9 -3 do 9 -3 do j i gr-row loop loop
  lf-example-max 0 gr-row
  0 lf-example-max gr-row
  lf-example-max lf-example-max gr-row
  lf-example-max 1 gr-row
  lf-example-min 1 gr-row
  1 lf-example-min gr-row ;
gr-check gr-table bye
