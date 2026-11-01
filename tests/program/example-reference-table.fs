\ Finite differential of actual lf-in-range against ProgramExamplesReference.
\ Each row contains lower upper value and invalid/true/false. The sentinel
\ checks that the word preserves the stack below its arguments.
include ../../src/program/examples.fs
decimal
: er-check-cell ( -- )
  1 cells 8 < abort" example-reference requires cells of at least 64 bits" ;
er-check-cell
variable er-lower
variable er-upper
variable er-value
create er-boundaries
  -2147483648 , -2147483647 , -1 , 0 , 1 , 2147483646 , 2147483647 ,
: er-boundary ( index -- n ) cells er-boundaries + @ ;
: er-row ( -- )
  er-lower @ . er-upper @ . er-value @ .
  12345 er-value @ er-lower @ er-upper @ lf-in-range
  if if ." true" else ." false" then else ." invalid" then
  12345 <> abort" lf-in-range damaged the stack sentinel"
  depth 0<> abort" lf-in-range left extra stack items"
  cr ;
: er-small ( -- )
  4 -3 do i er-lower !
    4 -3 do i er-upper !
      4 -3 do i er-value ! er-row loop
    loop
  loop ;
: er-extremes ( -- )
  7 0 do i er-boundary er-lower !
    7 0 do i er-boundary er-upper !
      7 0 do i er-boundary er-value ! er-row loop
    loop
  loop ;
er-small er-extremes bye
