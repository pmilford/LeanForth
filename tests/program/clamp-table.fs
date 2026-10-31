\ Emit a deterministic small-domain table for comparison with Lean's model.
\ Each row records lower bound, upper bound, value and result or invalid.
\ This is a finite test, not a proof that Forth executes the Lean definition.
include ../../src/program/clamp.fs
decimal
variable table-lower
variable table-upper
variable table-value

\ Print one row and consume the clamp's success flag and optional result.
: emit-clamp-row ( -- )
  table-lower @ . table-upper @ . table-value @ .
  table-value @ table-lower @ table-upper @ lf-clamp
  if . else ." invalid" then cr ;

\ Print every input triple in [-3, 3] in lower, upper, value order.
: emit-clamp-table ( -- )
  4 -3 do i table-lower !
    4 -3 do i table-upper !
      4 -3 do i table-value ! emit-clamp-row loop
    loop
  loop ;
emit-clamp-table
bye
