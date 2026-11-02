\ Emit a deterministic small-domain table for comparison with Lean's model.
\ Each row records lower bound, upper bound, value and result or invalid.
\ This is a finite test, not a proof that Forth executes the Lean definition.
require ../../src/program/clamp.fs
decimal
variable table-lower
variable table-upper
variable table-value
\ Signed 32-bit endpoints also fit the supported 64-bit development host.
create table-boundaries
  -2147483648 , -2147483647 , -1 , 0 , 1 , 2147483646 , 2147483647 ,

\ Fetch one boundary value by an index in [0, 7).
: table-boundary ( index -- value ) cells table-boundaries + @ ;

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
\ Print all triples drawn from signed 32-bit endpoint and near-zero values.
: emit-boundary-table ( -- )
  7 0 do i table-boundary table-lower !
    7 0 do i table-boundary table-upper !
      7 0 do i table-boundary table-value ! emit-clamp-row loop
    loop
  loop ;
emit-clamp-table
emit-boundary-table
bye
