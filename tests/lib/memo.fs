\ Unit tests of src/lib/memo.fs, keyed memo tables, outside the checker, in
\ the classes of docs/development/TEST_COVERAGE_REVIEW.md. Interfaces: the
\ public words and hidden helpers, the header's example, stack effects.
\ Results and refusals: every shape refused; a memo never made, refused by
\ the heap, freed; keys of one, two and three cells, differing in any one
\ cell; values written over; the check hook (a stale value is a miss, a
\ put finds it again) and the admit hook (asked only for a new entry,
\ after the table is ready and before the entries grow). Resources: the
\ heap refusing the table, its growth and the entries' growth (full,
\ nothing changed), blocks given back by memo-empty and memo-free, keys
\ that differ only in their high bits spread over the table. State: cuts
\ (newest first, the rest found), clears, empties, a new entry's value
\ zero over reused memory; 4,000 random operations against a model.
\ Loaded under HEX: the module must not depend on BASE. T{ }T checks
\ results and data-stack depth.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/lib/memo.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T
: blocks ( -- n ) live-blocks @ ;
: made ( outcome -- ) ok? 0= abort" memo: not made" ;

\ ---- The interface (ADR 0010): the public words are found, the helpers
\ are not, until the test opens the private word list.
T{ [defined] /memo [defined] memo-init [defined] memo-free [defined] memo-live?
   [defined] memo-count [defined] memo-bytes -> true true true true true true }T
T{ [defined] memo-find [defined] memo-put [defined] memo-at [defined] memo-claim
   [defined] memo@ [defined] memo! -> true true true true true true }T
T{ [defined] memo-clear [defined] memo-empty [defined] memo-cut [defined] memo-check!
   [defined] memo-admit! [defined] memo-small -> true true true true true true }T
T{ [defined] memo-table [defined] memo-hash [defined] memo-add [defined] memo-probe
   [defined] memo-mix [defined] memo-hooks -> false false false false false false }T
T{ memo-small -> 1024 }T

\ ---- The header's example.
create sq /memo allot   2 1 sq memo-init made
T{ 49 7 0 sq memo! 7 0 sq memo@ -> outcome-ok 49 true }T
T{ 8 0 sq memo@ -> false }T
create m3 /memo allot   3 2 m3 memo-init made
create key3 1 , 2 , 3 ,
T{ key3 m3 memo-put nip -> outcome-ok }T
key3 m3 memo-put drop  10 over !  20 swap cell+ !
T{ key3 m3 memo-find @ -> 10 }T
T{ key3 m3 memo-find cell+ @ -> 20 }T
\ A memo of three key cells has no key of one or two cells on the stack:
\ found nowhere, a put refused (invalid), nothing read past the probe.
T{ 1 2 m3 memo-at 1 2 m3 memo@ 5 1 2 m3 memo! 1 2 m3 memo-claim m3 memo-count
   -> 0 false outcome-invalid 0 outcome-invalid 1 }T
sq memo-free  m3 memo-free
T{ blocks sq memo-live? m3 memo-live? -> 0 false false }T

\ ---- Shapes: a key of at least one cell, values of none or more, an
\ entry within a cell's count of address units; nothing is made else.
create m /memo allot
max-n cell / constant most-cells
T{ 0 1 m memo-init m memo-live? -> outcome-invalid false }T
T{ -1 1 m memo-init 1 -1 m memo-init -> outcome-invalid outcome-invalid }T
T{ most-cells 1+ 0 m memo-init most-cells 1 m memo-init -> outcome-invalid outcome-invalid }T
T{ 1 most-cells m memo-init max-n 0 m memo-init blocks -> outcome-invalid outcome-invalid 0 }T
T{ most-cells 0 m memo-init m memo-live? -> outcome-ok true }T
m memo-free
T{ 1 0 m memo-init m memo-live? m memo-count -> outcome-ok true 0 }T
m memo-free

\ ---- A memo that is not live: never made, refused by the heap, freed. It
\ finds nothing, holds nothing and refuses puts.
create z /memo allot   z /memo erase
: dead? ( memo -- flag count bytes ) dup memo-live? over memo-count rot memo-bytes ;
T{ z dead? 1 2 z memo-at 1 2 z memo@ key3 z memo-find -> false 0 0 0 false 0 }T
T{ 5 1 2 z memo! 1 2 z memo-claim key3 z memo-put
   -> outcome-invalid 0 outcome-invalid 0 outcome-invalid }T
z memo-clear  z memo-empty  0 z memo-cut  5 z memo-cut
T{ z dead? -> false 0 0 }T
\ The heap refuses the table: full, nothing held, the same as never made.
T{ 1 heap-refusals !  2 1 z memo-init z dead? blocks -> outcome-full false 0 0 0 }T
T{ heap-refusals @ -> 0 }T
T{ 5 1 2 z memo! 1 2 z memo@ -> outcome-invalid false }T
z memo-free
T{ z dead? blocks -> false 0 0 0 }T
\ The table is the one block memo-init takes: every memo shares one
\ read-only hooks record (review reuse-k1 M1), the entries wait for a put.
T{ 2 1 z memo-init blocks 2 heap-refusals ! 1 0 0 z memo! blocks heap-refusals @
   -> outcome-ok 1 outcome-ok 2 1 }T
0 heap-refusals !  z memo-free

\ ---- Keys of one cell (the second is not read), values written over.
1 1 m memo-init made
T{ 10 5 0 m memo! 20 6 99 m memo! m memo-count -> outcome-ok outcome-ok 2 }T
T{ 5 0 m memo@ 6 0 m memo@ 6 1 m memo@ 7 0 m memo@ -> 10 true 20 true 20 true false }T
T{ 11 5 7 m memo! m memo-count 5 0 m memo@ -> outcome-ok 2 11 true }T
T{ -1 -1 0 m memo! 0 0 0 m memo! -1 0 m memo@ 0 0 m memo@ -> outcome-ok outcome-ok -1 true 0 true }T
\ 16 slots of 32 bits and 16 entries of two cells.
T{ m memo-bytes -> 16 /htab-slot * 32 cells + }T
T{ blocks -> 2 }T
m memo-free

\ ---- Keys of two cells, differing in either.
create p /memo allot   2 1 p memo-init made
T{ 1 1 2 p memo! 2 1 3 p memo! 3 2 2 p memo! -> outcome-ok outcome-ok outcome-ok }T
T{ 1 2 p memo@ 1 3 p memo@ 2 2 p memo@ 2 3 p memo@ 3 2 p memo@ -> 1 true 2 true 3 true false false }T
T{ 1 2 p memo-at 1 2 p memo-at = 1 2 p memo-at 1 3 p memo-at = -> true false }T
p memo-free

\ ---- Keys of three cells by address, and values of none (a set).
create kbuf 3 cells allot
: k! ( a b c -- ) kbuf 2 cells + ! kbuf cell+ ! kbuf ! ;
3 2 m memo-init made
create s /memo allot   3 0 s memo-init made
: put3 ( a b c v1 v2 -- )
  2>r k! kbuf m memo-put made 2r> rot tuck cell+ ! ! kbuf s memo-put nip made ;
1 2 3 100 200 put3   1 2 4 101 201 put3   1 5 3 102 202 put3   6 2 3 103 203 put3
: get3 ( a b c -- v1 v2 | 0 ) k! kbuf m memo-find dup if dup @ swap cell+ @ then ;
: has3? ( a b c -- flag ) k! kbuf s memo-find 0<> ;
T{ 1 2 3 get3 1 2 4 get3 1 5 3 get3 6 2 3 get3 -> 100 200 101 201 102 202 103 203 }T
T{ 1 2 5 get3 1 6 3 get3 7 2 3 get3 -> 0 0 0 }T
T{ 1 2 3 has3? 6 2 3 has3? 6 2 4 has3? s memo-count -> true true false 4 }T
\ A value of no cells: memo-find gives the entry's end, never 0.
T{ 1 2 3 k! kbuf s memo-find 0= -> false }T
m memo-free  s memo-free

\ ---- Keys that differ only in their high bits (cells of more than 32
\ bits): distinct entries, spread over the table, not one probe run.
lf-lib-private order+
: high ( i -- x ) 16 lshift 16 lshift ;
: cells-wide? ( -- flag ) 1 high 0<> ;
: spread ( n memo -- ) swap 0 ?do i i high 7 + 0 3 pick memo! made loop drop ;
: compared ( memo -- n ) memo-table htab-stats drop nip ;
1 1 m memo-init made
cells-wide? [if]
T{ 500 m spread m memo-count -> 500 }T
T{ 7 0 m memo@ 9 high 7 + 0 m memo@ 500 high 7 + 0 m memo@ -> 0 true 9 true false }T
\ 500 finds of the puts plus 3: a few slots compared each, not hundreds.
T{ m compared 3000 < -> true }T
[then]
order-
m memo-free

\ ---- The check hook: a value that no longer holds is a miss; a put finds
\ the entry again and writes over it. Values: a number and its era.
variable era   1 era !
: holds? ( a-addr -- flag ) cell+ @ era @ = ;
: keep ( x key memo -- ) 0 swap memo-claim made tuck ! era @ swap cell+ ! ;
create c /memo allot   1 2 c memo-init made   ' holds? c memo-check!
T{ 5 9 c keep 9 0 c memo@ -> 5 true }T
2 era !
T{ 9 0 c memo@ 9 0 c memo-at -> false 0 }T
T{ 9 0 c memo-claim nip c memo-count -> outcome-ok 1 }T
T{ 9 0 c memo-claim drop dup @ swap cell+ @ -> 5 1 }T
T{ 6 9 c keep 9 0 c memo@ c memo-count -> 6 true 1 }T
0 c memo-check!   1 era !
T{ 9 0 c memo@ -> 6 true }T
c memo-free

\ ---- The admit hook: asked only before a new entry is added, after the
\ table is ready (and has grown) and before the entries grow; a refusal is
\ full with nothing changed.
variable admits   variable refusing
: admit? ( memo -- flag ) c <> abort" memo: admit given another memo"
  1 admits +! refusing @ 0= ;
1 1 c memo-init made   ' admit? c memo-admit!
: put ( i -- outcome ) dup 1000 + swap 0 c memo! ;
: puts ( n -- ) 0 ?do i put made loop ;
T{ 11 puts admits @ c memo-count -> 11 11 }T
T{ 3 put admits @ -> outcome-ok 11 }T
T{ 11 put admits @ c memo-count -> outcome-ok 12 12 }T
\ With 12 entries in 16 slots any put first makes the table grow (3/4
\ full), even of a key present: refused by the heap, admit not asked.
T{ 1 heap-refusals ! 3 put admits @ c memo-count heap-refusals @ -> outcome-full 12 12 0 }T
T{ 1 heap-refusals ! 12 put admits @ c memo-count heap-refusals @ -> outcome-full 12 12 0 }T
T{ 3 0 c memo@ -> 1003 true }T
true refusing !
T{ 12 put admits @ c memo-count 12 0 c memo@ -> outcome-full 13 12 false }T
false refusing !
T{ 12 put admits @ c memo-count -> outcome-ok 14 13 }T
T{ 13 put 14 put 15 put admits @ -> outcome-ok outcome-ok outcome-ok 17 }T
\ The 17th entry makes the entries grow (16 units): admit asked, then full.
T{ 1 heap-refusals ! 16 put admits @ c memo-count heap-refusals @ -> outcome-full 18 16 0 }T
T{ 16 0 c memo@ 15 0 c memo@ -> false 1015 true }T
T{ 16 put admits @ c memo-count 16 0 c memo@ -> outcome-ok 19 17 1016 true }T

\ ---- Cuts: the entries from the n-th on go, newest first; the others stay
\ found; the table is whole (they can be put again).
: found# ( n -- k ) 0 swap 0 ?do i 0 c memo@ if drop 1+ then loop ;
0 admits !
T{ 10 c memo-cut c memo-count 17 found# 9 0 c memo@ 10 0 c memo@ -> 10 10 1009 true false }T
T{ 20 c memo-cut c memo-count -> 10 }T
T{ 7 puts 17 puts c memo-count 17 found# admits @ -> 17 17 7 }T
T{ -3 c memo-cut c memo-count 17 found# -> 0 0 }T
\ A new entry's value cells are zero, also over the memory of a cut one.
2 2 p memo-init made
T{ 4 5 p memo-claim made dup 7 swap ! 8 swap cell+ ! -> }T
0 p memo-cut
T{ 4 5 p memo-claim made dup @ swap cell+ @ -> 0 0 }T
p memo-free

\ ---- Clear and empty: every entry out. memo-clear keeps the memory;
\ memo-empty does for a table of up to memo-small slots, and makes a
\ larger one small again, its blocks given back, the hooks kept.
0 c memo-cut   0 admits !
T{ 20 puts c memo-bytes c memo-clear c memo-bytes = c memo-count 5 0 c memo@ -> true 0 false }T
T{ 20 puts c memo-bytes c memo-empty c memo-bytes = c memo-count blocks -> true 0 2 }T
T{ 2000 puts c memo-count blocks -> 2000 2 }T
T{ c memo-empty c memo-count c memo-bytes c memo-live? blocks -> 0 16 /htab-slot * true 1 }T
T{ 0 admits !  3 put admits @ 3 0 c memo@ -> outcome-ok 1 1003 true }T
\ The heap refuses the new table: the memo is no longer live, holds nothing.
T{ 2000 puts 1 heap-refusals ! c memo-empty c dead? blocks -> false 0 0 0 }T
T{ 3 put -> outcome-invalid }T
1 1 c memo-init made
T{ 3 put c memo-count admits @ -> outcome-ok 1 2000 }T
c memo-free
T{ blocks -> 0 }T

\ ---- A memo record may move (a member of a checker context does while
\ modules load): a copy, the old record erased, finds and keeps as before.
create moved /memo allot
2 1 p memo-init made
T{ 5 1 2 p memo! -> outcome-ok }T
p moved /memo move   p /memo erase
T{ 1 2 moved memo@ 6 3 4 moved memo! 3 4 moved memo@ -> 5 true outcome-ok 6 true }T
: fill-moved ( n -- ) 0 ?do i i 9 moved memo! drop loop ;
T{ 40 fill-moved 39 9 moved memo@ 1 2 moved memo@ -> 39 true 5 true }T
moved memo-free

\ ---- Stack effects with the return stack checked.
2 1 p memo-init made
T{ 5 1 2 p ' memo! rs-checked 1 2 p ' memo@ rs-checked -> outcome-ok 5 true }T
T{ 1 2 p ' memo-at rs-checked @ 3 p ' memo-cut rs-checked p memo-count -> 5 1 }T
p memo-free

\ ---- 4,000 random operations against a model: keys of two cells (16
\ firsts by 4 seconds; with wide cells, some firsts with high bits), one
\ value; put, find, cut (to a random count), clear, empty. The model keeps
\ each key's value and the keys in the order they were first put.
variable test-seed  2463534242 test-seed !
: rand-below ( n -- u )
  test-seed @ dup 13 lshift xor dup 7 rshift xor dup 17 lshift xor dup test-seed !
  1 rshift swap mod ;
64 constant key-span
create model-values key-span cells allot
create model-in key-span cells allot     \ true when present
create model-order key-span cells allot  \ keys, oldest first
variable model-n
: model-clear ( -- ) model-in key-span cells erase 0 model-n ! ;
: key-parts ( k -- k1 k2 ) dup 4 / dup 3 and if 1 high + then swap 3 and ;
: model-put ( v k -- )
  dup cells model-in + @ 0= if dup model-n @ cells model-order + ! 1 model-n +!
  true over cells model-in + ! then cells model-values + ! ;
: model-cut ( n -- )
  begin dup model-n @ < while
    -1 model-n +! model-n @ cells model-order + @ cells model-in + 0 swap ! repeat drop ;
: model@ ( k -- x true | false )
  dup cells model-in + @ if cells model-values + @ true else drop false then ;
create rm /memo allot   2 1 rm memo-init made   model-clear
variable mismatches
: differs ( -- ) 1 mismatches +! ;
: model-pair ( k -- x flag ) model@ dup 0= if 0 swap then ;
: memo-pair ( k -- x flag ) key-parts rm memo@ dup 0= if 0 swap then ;
: check-key ( k -- ) dup model-pair rot memo-pair d= 0= if differs then ;
: check-all ( -- ) key-span 0 ?do i check-key loop
  rm memo-count model-n @ <> if differs then ;
: op-put ( -- ) 1000 rand-below key-span rand-below
  2dup model-put key-parts rm memo! ok? 0= if differs then ;
: op-cut ( -- ) model-n @ 1+ rand-below dup model-cut rm memo-cut ;
: op ( -- )
  100 rand-below dup 60 < if drop op-put exit then
  dup 90 < if drop key-span rand-below check-key exit then
  dup 97 < if drop op-cut exit then
  98 < if rm memo-clear else rm memo-empty then model-clear ;
: run-ops ( n -- ) 0 ?do op i 50 mod 0= if check-all then loop check-all ;
T{ 0 mismatches ! 4000 run-ops mismatches @ -> 0 }T
rm memo-free
T{ blocks -> 0 }T
bye
