\ Test-only bounded memory; this is not a verified runtime.
decimal
create mr-cells 4 cells allot
variable mr-address
variable mr-value
variable mr-mode

: mr-init ( -- ) 4 0 do i 1+ 11 * mr-cells i cells + ! loop ;
\ Reject negative and out-of-range indices before forming an address.
: mr-in-bounds? ( index -- flag ) dup 0< 0= swap 4 < and ;
: mr-load ( index -- value flag )
  dup mr-in-bounds? if cells mr-cells + @ true else drop 0 false then ;
: mr-store ( value index -- flag )
  dup mr-in-bounds? if cells mr-cells + ! true else 2drop false then ;
: mr-run ( -- value flag )
  mr-mode @ if
    mr-value @ mr-address @ mr-store 0= if 0 false exit then
  then
  mr-address @ mr-load ;
: mr-row ( mode address value -- )
  mr-value ! mr-address ! mr-mode ! mr-init
  mr-mode @ . mr-address @ . mr-value @ .
  12345 mr-run
  if ." ok " . else ." invalid " . then
  12345 <> abort" memory operation damaged stack sentinel"
  depth 0<> abort" memory operation left extra stack items"
  4 0 do mr-cells i cells + @ . loop cr ;
: mr-table ( -- )
  6 -1 do
    0 i 0 mr-row
    1 i -9 mr-row  1 i 0 mr-row  1 i 57 mr-row
  loop ;
mr-table bye
