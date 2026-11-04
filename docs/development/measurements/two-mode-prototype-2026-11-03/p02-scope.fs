\ Gforth 1.0's scope recognizer (voc:word) on words that are not
\ vocabularies, with only our word list in the search order. Does a token
\ like x:dup run anything?
wordlist constant my-wl
variable hits
get-current my-wl set-current
create x 0 , does> drop 1 hits +! ;
: ok-word ( -- ) 100 hits +! ;
create y my-wl ,
set-current
create saved-order 20 cells allot
: save-order ( -- ) get-order dup saved-order ! 0 ?do saved-order i 1+ cells + ! loop ;
: restore-order ( -- ) saved-order @ dup 0 ?do saved-order over i - cells + @ swap loop set-order ;
variable d0
: try ( c-addr u -- )
  2dup type ."  => " 0 hits ! depth 2 - d0 !
  save-order my-wl 1 set-order
  ['] evaluate catch restore-order
  dup if ." throw " . 2drop else drop ." ok" then
  ."  depth+" depth d0 @ - . ."  hits " hits @ .
  depth d0 @ - 0 ?do drop loop cr ;
s" x" try
s" x:ok-word" try
s" x:x" try
s" ok-word:x" try
s" y:ok-word" try
s" x:dup" try
s" X:OK-WORD" try
s" x:" try
s" :x" try
bye
