\ Exhaustive triples from selected signed 64-bit boundaries. Check the
\ complete result shape, canonical flags and a sentinel below the arguments.
require ../../src/program/examples.fs
decimal
: xr-check-cell ( -- )
  1 cells 8 <> abort" extra range comparison requires 64-bit cells" ;
xr-check-cell
variable xr-lo
variable xr-hi
variable xr-value
create xr-boundaries
  lf-example-min , lf-example-min 1+ , -1 , 0 , 1 ,
  lf-example-max 1- , lf-example-max ,
: xr-boundary ( index -- n ) cells xr-boundaries + @ ;
: xr-row ( -- )
  xr-lo @ . xr-hi @ . xr-value @ .
  12345 xr-value @ xr-lo @ xr-hi @ lf-in-range
  depth 2 < abort" range returned too few stack items"
  dup true = if
    drop depth 2 <> abort" range success stack shape"
    dup true = if drop ." true" else
      false <> abort" range noncanonical membership flag" ." false"
    then
  else
    false <> abort" range noncanonical status flag"
    depth 1 <> abort" range failure stack shape" ." invalid"
  then
  12345 <> abort" range damaged stack sentinel"
  depth 0<> abort" range left extra stack items" cr ;
: xr-run ( -- )
  7 0 do i xr-boundary xr-lo !
    7 0 do i xr-boundary xr-hi !
      7 0 do i xr-boundary xr-value ! xr-row loop
    loop
  loop ;
xr-run bye
