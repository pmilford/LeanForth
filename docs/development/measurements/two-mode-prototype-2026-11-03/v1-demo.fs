\ ADR 0019 demo source for a draft IR v1: counted loops, BEGIN ... UNTIL,
\ RECURSE, a user-written defining word, a data table and a variable.
\ Ordinary Forth: run mode loads it unchanged.
: sum-below ( n -- sum ) 0 swap 0 ?do i + loop ;
: pairs ( -- sum ) 0 3 0 do 2 0 do i j + + loop loop ;
: first-big ( limit -- i ) 0 swap 0 do i dup * 50 > if drop i leave then loop ;
: count-down ( n -- 0 ) begin 1- dup 0= until ;
: fact ( n -- n! ) dup 1 > if dup 1- recurse * then ;
: holder ( x "name" -- ) create , does> @ ;
7 holder seven
create squares 0 , 1 , 4 , 9 ,
variable total
: add-seven ( -- ) total @ seven + total ! ;
: square ( i -- n ) cells squares + @ ;
