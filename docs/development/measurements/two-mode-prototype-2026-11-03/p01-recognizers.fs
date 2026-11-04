\ What Forth's interpreter does with odd tokens when only our word list is
\ in the search order: depth change, fdepth change, THROW code.
wordlist constant my-wl
get-current my-wl set-current
: marker-word ( -- ) ;
set-current
variable saved-depth
create saved-order 20 cells allot
: save-order ( -- ) get-order dup saved-order ! 0 ?do saved-order i 1+ cells + ! loop ;
: restore-order ( -- ) saved-order @ dup 0 ?do saved-order over i - cells + @ swap loop set-order ;
[defined] fdepth [if] : fd ( -- n ) fdepth ; [else] : fd ( -- n ) 0 ; [then]
variable fd0
: try ( c-addr u -- )
  2dup type ."  => " depth 2 - saved-depth ! fd fd0 !
  save-order my-wl 1 set-order
  ['] evaluate catch restore-order
  dup if ." throw " . 2drop else drop ." ok" then
  ."  depth+" depth saved-depth @ - . ."  fdepth+" fd fd0 @ - .
  depth saved-depth @ - 0 ?do drop loop
  fd fd0 @ - 0 ?do [defined] fdrop [if] fdrop [then] loop cr ;
s" 5" try
s" -5" try
s" -0" try
s" 05" try
s" +5" try
s" --5" try
s" $10" try
s" #10" try
s" %10" try
s" &10" try
s" 0x10" try
s" 'a'" try
s" 1." try
s" 1.5" try
s" 1e" try
s" 1e0" try
s" 2p" try
s\" \"x\"" try
s\" \"x y\"" try
s" ->x" try
s" ->marker-word" try
s" +>marker-word" try
s" '>marker-word" try
s" `marker-word" try
s" ``marker-word" try
s" <marker-word>" try
s" ${HOME}" try
s" forth:dup" try
s" forth:bye" try
s" Forth:drop" try
s" float:1" try
s" num:1" try
s" forth:1" try
s" marker-word" try
s" MARKER-WORD" try
s" dup" try
s" bye" try
s" [" try
s" ]" try
s" 2147483648" try
s" 18446744073709551616" try
s" 99999999999999999999999999" try
s" 1,000" try
s" 1_000" try
s" 0b101" try
s" 1/2" try
s" 1:30" try
s" 1'000" try
s" 'ab'" try
s" ''" try
s" '" try
s" `" try
s" a" try
s" .5" try
s" 5." try
s" -" try
s" 1-" try
.s cr
bye
