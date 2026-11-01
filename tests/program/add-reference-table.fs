\ Finite host execution comparison; no proof of the runtime or Forth semantics.
include ../../src/program/examples.fs
decimal
: ar-check-cell ( -- )
  1 cells 8 <> abort" add-reference requires 64-bit cells" ;
ar-check-cell
variable ar-a
variable ar-b
create ar-boundaries
  lf-example-min , lf-example-min 1+ ,
  -2147483648 , -2147483647 , -1 , 0 , 1 , 2147483646 , 2147483647 ,
  lf-example-max 1- , lf-example-max ,
\ ( index -- n ) Fetch a selected boundary operand.
: ar-boundary cells ar-boundaries + @ ;
\ ( -- ) Emit one result, checking the stack shape and preserved sentinel.
: ar-row
  ar-a @ . ar-b @ .
  12345 ar-a @ ar-b @ lf-checked-add
  depth 2 < abort" checked-add returned too few stack items"
  if
    depth 2 <> abort" checked-add success stack depth"
    ." ok " 0 .r
  else
    depth 1 <> abort" checked-add failure stack depth"
    ." overflow"
  then
  12345 <> abort" checked-add damaged stack sentinel"
  depth 0<> abort" checked-add left extra stack items"
  cr ;
\ ( -- ) Cartesian product of all operands from -8 through 8.
: ar-small
  9 -8 do i ar-a !
    9 -8 do i ar-b ! ar-row loop
  loop ;
\ ( -- ) Cartesian product of 32-bit and host-cell boundary operands.
: ar-extremes
  11 0 do i ar-boundary ar-a !
    11 0 do i ar-boundary ar-b ! ar-row loop
  loop ;
ar-small ar-extremes bye
