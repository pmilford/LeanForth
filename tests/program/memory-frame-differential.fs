\ Test-only bounded memory and copy-then-swap; not a verified runtime.
\ Single-threaded scratch variables; indices are signed, cells are host cells.
decimal
create mf-cells 4 cells allot
variable mf-source  variable mf-dest  variable mf-a  variable mf-b
variable mf-first   variable mf-second

: mf-init ( -- ) 4 0 do i 1+ 11 * mf-cells i cells + ! loop ;
: mf-valid? ( index -- flag ) dup 0< 0= swap 4 < and ;
\ Reject bad indices before address arithmetic. Failure leaves memory intact.
: mf-load ( index -- value flag )
  dup mf-valid? if cells mf-cells + @ true else drop 0 false then ;
: mf-store ( value index -- flag )
  dup mf-valid? if cells mf-cells + ! true else 2drop false then ;
\ Access number on failure; zero on success. Completed writes are retained.
: mf-run ( -- status )
  mf-source @ mf-load 0= if drop 1 exit then
  mf-dest @ mf-store 0= if 2 exit then
  mf-a @ mf-load 0= if drop 3 exit then mf-first !
  mf-b @ mf-load 0= if drop 4 exit then mf-second !
  mf-second @ mf-a @ mf-store 0= if 5 exit then
  mf-first @ mf-b @ mf-store 0= if 6 exit then
  0 ;
: mf-row ( source dest a b -- )
  mf-b ! mf-a ! mf-dest ! mf-source ! mf-init
  mf-source @ . mf-dest @ . mf-a @ . mf-b @ .
  12345 mf-run .
  12345 <> abort" sequence damaged stack sentinel"
  depth 0<> abort" sequence left extra stack items"
  4 0 do mf-cells i cells + @ . loop cr ;
variable mf-loop-source  variable mf-loop-dest  variable mf-loop-a
: mf-b-loop ( -- )
  5 -1 do mf-loop-source @ mf-loop-dest @ mf-loop-a @ i mf-row loop ;
: mf-a-loop ( -- ) 5 -1 do i mf-loop-a ! mf-b-loop loop ;
: mf-dest-loop ( -- ) 5 -1 do i mf-loop-dest ! mf-a-loop loop ;
: mf-table ( -- ) 5 -1 do i mf-loop-source ! mf-dest-loop loop ;
mf-table bye
