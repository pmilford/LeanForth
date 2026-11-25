\ Unit tests of the general Forth library (src/lib): portability words,
\ range checks, bounded stores, tagged nodes, outcomes, walk and frame
\ records, and packed 32-bit fields. T{ }T checks results and data-stack
\ depth; rs-checked also checks the return stack around a call.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/lib/lib.fs
hex require ../../src/lib/find.fs base @ decimal constant find-base

\ Portability: comparisons and the largest cell.
T{ 2 1 >= -> true }T
T{ 1 2 >= -> false }T
T{ 1 1 <= -> true }T
T{ 0 0<= -> true }T
T{ 1 0<= -> false }T
T{ max-n 0> max-n 1+ 0< -> true true }T
\ ndrop: the n cells below n, none for 0.
T{ 1 2 3 4 3 ndrop -> 1 }T
T{ 5 0 ndrop 6 1 ndrop -> 5 }T
\ SYNONYM of an ordinary word, the host's or portability.fs's fallback
\ (Gforth 0.7.3).
synonym lib-dup dup
T{ 3 lib-dup -> 3 3 }T

\ The fallbacks, as a host without the words compiles them: portability.fs
\ included again with every [undefined] guard taken (fb-guards first in
\ the search order) into a word list of its own, each fallback then
\ compared with this host's word on the same inputs.
wordlist constant fb-guards
wordlist constant fallbacks
get-current fb-guards set-current
: [undefined] ( "name" -- true ) parse-name 2drop true ; immediate
set-current
get-order get-current
get-order fb-guards swap 1+ set-order fallbacks set-current
\ Loaded a second time on purpose (REQUIRE would skip it), so INCLUDED.
s" ../../src/lib/portability.fs" included
set-current set-order
: fb' ( "name" -- xt ) parse-name fallbacks search-wordlist 0= abort" no fallback" ;
T{ 100 5 fb' bounds execute -> 105 100 }T
T{ max-n 1 fb' bounds execute -> max-n 1 bounds }T
T{ 1 2 fb' u<= execute 2 1 fb' u<= execute 3 3 fb' u<= execute -> true false true }T
T{ -1 1 fb' u<= execute 1 -1 fb' u<= execute -> false true }T
T{ 2 1 fb' >= execute 1 2 fb' >= execute 1 2 fb' <= execute 2 1 fb' <= execute
   -> true false true false }T
T{ 0 fb' 0<= execute 1 fb' 0<= execute -1 fb' 0>= execute 0 fb' 0>= execute
   -> true false false true }T
T{ 1 2 3 fb' -rot execute -> 3 1 2 }T
T{ 1 2 3 4 3 fb' ndrop execute 5 0 fb' ndrop execute -> 1 5 }T
T{ fb' max-n execute fb' cell execute -> max-n cell }T
T{ s" " fb' stdout execute write-file s" " fb' stderr execute write-file -> 0 0 }T
T{ stdout fb' flush-file execute -> 0 }T
fb' begin-structure execute /fb-pair
  fb' field: execute fb-first
  1 chars fb' +field execute fb-char
  fb' field: execute fb-second
fb' end-structure execute
T{ /fb-pair 0 fb-first 0 fb-char 0 fb-second -> 1 chars aligned 2 cells + 0 cell 1 chars aligned cell + }T

\ between? and upto?: inclusive, signed, and never wrapping around.
T{ 3 1 5 between? -> true }T
T{ 1 1 5 between? 5 1 5 between? -> true true }T
T{ 0 1 5 between? 6 1 5 between? -> false false }T
T{ 3 5 1 between? -> false }T
T{ max-n 0 max-n between? -1 0 max-n between? -> true false }T
T{ 2 0 7 ' between? rs-checked -> true }T
T{ 0 0 upto? -> true }T
T{ 5 5 upto? -> true }T
T{ 6 5 upto? -> false }T
T{ -1 5 upto? -> false }T
T{ max-n max-n upto? -> true }T
T{ -1 max-n upto? -> false }T
T{ 0 -1 upto? -> false }T
T{ 3 -5 upto? max-n -5 upto? -> false false }T
T{ 3 7 ' upto? rs-checked -> true }T
\ index?: 0 <= i < n, signed; false for every i when n <= 0, where
\ `0 n within` would take any i >= 0 for a negative n.
T{ 0 1 index? 4 5 index? 5 5 index? -1 5 index? -> true true false false }T
T{ 0 0 index? 0 -1 index? 3 -1 index? max-n 1+ 0 index? -> false false false false }T
T{ 3 max-n 1+ index? max-n 1- max-n index? max-n max-n index? -> false true false }T
T{ 2 0 -1 within 2 -1 index? -> true false }T
T{ 2 3 ' index? rs-checked -> true }T
\ cells-index: the first cell equal to x, from 0 below n.
create some-cells 4 , -1 , 9 , -1 , 0 ,
T{ 4 some-cells 5 cells-index -1 some-cells 5 cells-index -> 0 true 1 true }T
T{ 0 some-cells 5 cells-index 0 some-cells 4 cells-index -> 4 true false }T
T{ 9 some-cells 2 cells-index 9 some-cells 3 cells-index -> false 2 true }T
T{ 4 some-cells 0 cells-index 4 some-cells -3 cells-index 7 some-cells 5 cells-index
   -> false false false }T
T{ 9 some-cells 5 ' cells-index rs-checked -> 2 true }T
\ cells-has?: cells-index's flag alone, the index dropped (review
\ reuse-1a L1); none in an empty or negative range.
T{ 9 some-cells 5 cells-has? 7 some-cells 5 cells-has? 4 some-cells 0 cells-has? -> true false false }T
T{ 0 some-cells 5 cells-has? 0 some-cells 4 cells-has? 4 some-cells -1 cells-has? -> true false false }T
\ cell-at@, pair-at, record-at (reuse-d): element i of an array of
\ cells, the address of pair i, of record i of a size; with the rs check.
T{ 0 some-cells cell-at@ 4 some-cells cell-at@ 2 some-cells ' cell-at@ rs-checked -> 4 0 9 }T
T{ 0 some-cells pair-at some-cells = 2 some-cells pair-at some-cells 4 cells + = -> true true }T
T{ 2 some-cells pair-at @ 1 some-cells pair-at 2@ -> 0 -1 9 }T
T{ 0 24 some-cells record-at some-cells = 3 24 some-cells record-at some-cells 72 + = -> true true }T
T{ 2 5 some-cells ' record-at rs-checked some-cells - -> 10 }T
\ cell-pair@, cell-pair! (cleanup-families-2): two adjacent cells in the
\ order they lie in memory, x1 at addr: the reverse of 2@'s and 2!'s.
create two-cells 0 , 0 ,
T{ 5 7 two-cells cell-pair! two-cells @ two-cells cell+ @ -> 5 7 }T
T{ two-cells cell-pair@ two-cells 2@ -> 5 7 7 5 }T
T{ 1 some-cells pair-at cell-pair@ 0 some-cells pair-at cell-pair@ -> 9 -1 4 -1 }T
T{ -1 0 two-cells ' cell-pair! rs-checked two-cells ' cell-pair@ rs-checked -> -1 0 }T
T{ two-cells @ two-cells cell+ @ -> -1 0 }T
\ cell-triple@, cell-triple! (cleanup-families-2): three adjacent cells in
\ memory order, x1 at addr.
create three-cells 0 , 0 , 0 , 0 ,
T{ 5 7 9 three-cells cell-triple! three-cells @ three-cells cell+ @ three-cells 2 cells + @
   three-cells 3 cells + @ -> 5 7 9 0 }T
T{ three-cells cell-triple@ -> 5 7 9 }T
T{ 0 some-cells pair-at cell-triple@ 1 some-cells pair-at cell-triple@ -> 4 -1 9 9 -1 0 }T
T{ -1 0 1 three-cells ' cell-triple! rs-checked three-cells ' cell-triple@ rs-checked -> -1 0 1 }T
\ cell-tally (reuse-d): one more in cell i of an array of counts.
create tallies 0 , 5 , 0 ,
T{ 1 tallies cell-tally 1 tallies cell-tally 2 tallies cell-tally -> }T
T{ 0 tallies cell-at@ 1 tallies cell-at@ 2 tallies cell-at@ -> 0 7 1 }T
\ cell-spend? (cleanup-families-3): a unit spent while the count is above
\ zero; at zero, or below (a corrupted budget), nothing spent and false.
variable budget  2 budget !
T{ budget cell-spend? budget cell-spend? budget cell-spend? budget @ -> true true false 0 }T
\ d+! and d-floor (review jobs-default finding 3): a double in memory
\ added to, the carry into the high cell and back; a difference of two
\ doubles, 0 when the second is larger, across the cell boundary too.
2variable dsum  0 0 dsum 2!
T{ 5 0 dsum d+! -1 0 dsum d+! dsum 2@ -> 4 1 }T
T{ -6 s>d dsum d+! dsum 2@ -> -2 0 }T
T{ 7 0 3 0 d-floor 3 0 7 0 d-floor 5 0 5 0 d-floor -> 4 0 0 0 0 0 }T
T{ 0 1 1 0 d-floor -2 s>d -5 s>d d-floor -> -1 0 3 0 }T
-3 budget !
T{ budget cell-spend? budget @ -> false -3 }T
1 budget !
T{ 5 budget ' cell-spend? rs-checked budget @ -> 5 true 0 }T
\ first-nonzero (reuse-d): the first of two that is not zero, else zero.
T{ 3 4 first-nonzero 0 4 first-nonzero -2 0 first-nonzero 0 0 first-nonzero -> 3 4 -2 0 }T
\ first-or-second (cleanup-families-1): x1 for place 1, x2 for any other.
T{ 3 4 1 first-or-second 3 4 2 first-or-second 3 4 0 first-or-second 3 4 -1 first-or-second
   -> 3 4 4 4 }T
\ one-of2? and one-of3? (cleanup-families-3), in place of `dup a = swap b
\ = or` and `dup a = over b = or swap c = or`: true at each place, false
\ when none matches, a well-formed flag either way; the values below kept.
T{ 5 5 7 one-of2? 7 5 7 one-of2? 6 5 7 one-of2? 5 5 5 one-of2? -> true true false true }T
T{ 1 1 2 3 one-of3? 2 1 2 3 one-of3? 3 1 2 3 one-of3? 4 1 2 3 one-of3? -1 0 1 -1 one-of3?
   -> true true true false true }T
T{ 9 7 5 7 ' one-of2? rs-checked 9 4 1 2 3 ' one-of3? rs-checked -> 9 true 9 false }T
\ epoch+ (reuse-d; was store.fs's and slab.fs's): one step on, max-n
\ saturates to -1, and a negative generation stays.
T{ 0 epoch+ 41 epoch+ max-n 1- epoch+ max-n epoch+ -1 epoch+ -7 epoch+ -> 1 42 max-n -1 -1 -7 }T
\ store-most (reuse-d; was author/form.fs's and front/mvars.fs's): the
\ most records of a width, each with its identity cell, that fit with the
\ header in max-n bytes; one more does not.
: most-fits? ( width -- flag1 flag2 )
  dup store-most over cell+ * store-header + max-n u> 0=
  swap dup store-most 1+ swap cell+ * store-header + max-n u> ;
T{ 1 cells most-fits? 8 cells most-fits? 3 most-fits? -> true true true true true true }T
\ cell-count (reuse-out-2): the cells after a count cell, and the count.
create counted-cells 3 , 7 , 8 , 9 ,
T{ counted-cells cell-count swap counted-cells cell+ = -> 3 true }T
T{ counted-cells cell-count drop 2 cells + @ counted-cells ' cell-count rs-checked nip -> 9 3 }T
\ cell-counted! and cell-counted+! (ROUT3): a text put into a buffer of
\ room bytes after its count cell, refused (nothing changed) when longer;
\ appended after what it holds.
create text-buf 1 cells 8 + allot
: buf-text ( -- c-addr u ) text-buf cell-count ;
T{ s" abc" text-buf 8 cell-counted! buf-text s" abc" compare -> true 0 }T
T{ s" 123456789" text-buf 8 cell-counted! buf-text s" abc" compare -> false 0 }T
T{ s" 12345678" text-buf 8 cell-counted! buf-text nip -> true 8 }T
T{ s" " text-buf 8 cell-counted! s" ab" text-buf cell-counted+! s" cd" text-buf cell-counted+!
   buf-text s" abcd" compare -> true 0 }T
T{ s" e" text-buf ' cell-counted+! rs-checked buf-text s" abcde" compare -> 0 }T
T{ s" xy" text-buf 8 ' cell-counted! rs-checked buf-text s" xy" compare -> true 0 }T
\ cell-counted-left and cell-counted+? (reuse-b): the room still free; an
\ append that fits, one to the last byte, one a byte too long (refused,
\ nothing changed), an empty one into a full buffer, and the rs check.
T{ text-buf 8 cell-counted-left s" abcdef" text-buf 8 cell-counted+? -> 6 true }T
T{ text-buf 8 cell-counted-left buf-text s" xyabcdef" compare -> 0 0 }T
T{ s" " text-buf 8 cell-counted! s" abcde" text-buf 8 cell-counted+? -> true true }T
T{ s" xyz" text-buf 8 cell-counted+? buf-text s" abcdexyz" compare -> true 0 }T
T{ s" !" text-buf 8 cell-counted+? buf-text s" abcdexyz" compare -> false 0 }T
T{ s" " text-buf 8 cell-counted+? text-buf 8 cell-counted-left -> true 0 }T
T{ s" ab" text-buf 4 cell-counted+? buf-text nip -> false 8 }T
\ A length with the top bit set (a negative u) never fits, in either
\ writer (review of reuse-b, 8): nothing is moved and nothing changes.
T{ s" " text-buf 8 cell-counted! pad -1 text-buf 8 cell-counted+? buf-text nip -> true false 0 }T
T{ pad -1 text-buf 8 cell-counted! pad max-n invert text-buf 8 cell-counted+? buf-text nip -> false false 0 }T
T{ s" " text-buf 8 cell-counted! drop s" q" text-buf 8 ' cell-counted+? rs-checked
   buf-text s" q" compare -> true 0 }T
T{ -1 some-cells 2 ' cells-has? rs-checked -> true }T
\ cells=: n cells compared cell by cell (review reuse-k1 B1); equal for
\ n <= 0; a difference in the first or the last cell, or in the sign.
create other-cells 4 , -1 , 9 , -1 , 1 ,
T{ some-cells other-cells 4 cells= some-cells other-cells 5 cells= -> true false }T
T{ some-cells some-cells 5 cells= some-cells other-cells 0 cells= -> true true }T
T{ some-cells other-cells -3 cells= some-cells 4 + other-cells 1 cells= -> true false }T
T{ some-cells cell+ some-cells 3 cells + 1 cells= some-cells some-cells cell+ 1 cells=
   -> true false }T
T{ some-cells other-cells 5 ' cells= rs-checked -> false }T
\ The header's example.
create primes 2 , 3 , 5 , 7 ,   create odds 3 , 5 , 7 ,
T{ primes cell+ odds 3 cells=  primes odds 3 cells= -> true false }T
\ in-ranges?: x within one of n (lo, hi) pairs, both ends included; none
\ for n <= 0; an empty pair (lo > hi) holds nothing; the header's example.
create digits 48 , 57 ,  65 , 70 ,
T{ char 7 digits 2 in-ranges?  char G digits 2 in-ranges?  char A digits 2 in-ranges? -> true false true }T
T{ 48 digits 2 in-ranges? 57 digits 2 in-ranges? 47 digits 2 in-ranges? 58 digits 2 in-ranges?
   -> true true false false }T
T{ 70 digits 2 in-ranges? 70 digits 1 in-ranges? 50 digits 0 in-ranges? 50 digits -2 in-ranges?
   -> true false false false }T
create odd-ranges 5 , 3 ,  -9 , -7 ,  max-n , max-n ,
T{ 4 odd-ranges 1 in-ranges? -8 odd-ranges 2 in-ranges? max-n odd-ranges 3 in-ranges? -> false true true }T
T{ digits 1 range-at char 5 digits 2 ' in-ranges? rs-checked -> 65 70 true }T

\ cells-zero?: any nonzero cell in range makes it false.
create zero-cells 3 cells allot
zero-cells 3 cells erase
T{ zero-cells 3 cells-zero? -> true }T
T{ zero-cells 0 cells-zero? -> true }T
T{ zero-cells -1 cells-zero? -> true }T
7 zero-cells 2 cells + !
T{ zero-cells 3 cells-zero? -> false }T
T{ zero-cells 2 cells-zero? -> true }T
T{ zero-cells 3 ' cells-zero? rs-checked -> false }T

\ epoch+: grows by one, saturates to -1, and a negative value stays.
T{ 0 epoch+ -> 1 }T
T{ max-n epoch+ -> -1 }T
T{ -1 epoch+ -> -1 }T
T{ -5 epoch+ -> -5 }T

\ Defining stores: shape fields set, counters zero, layout as documented.
T{ 3 /node 0 store: s0 -> }T
T{ 2 /node 1 store: s1 -> }T
T{ s0 store-capacity @ s0 store-width @ s0 store-base @ -> 3 /node 0 }T
T{ s0 store-count @ s0 store-generation @ s0 store-serial @ -> 0 0 0 }T
T{ s0 store-bytes -> 3 /node cell+ * }T
T{ s0 store-records s0 store-identities - -> 3 cells }T
T{ 1 s0 store-slot 0 s0 store-slot - -> /node }T
T{ 0 s0 store-slot s0 store-records = -> true }T
T{ s1 s0 store-records 3 /node * + u< -> false }T
T{ s0 store-count-valid? -> true }T
T{ s1 store-count-valid? -> false }T
T{ s1 store-new -> false }T
T{ s1 store-serial @ -> 0 }T

\ A bad shape aborts the definition: negative capacity, base above
\ capacity, a zero or unaligned width.
\ CATCH leaves the string only when the definition throws.
: bad-store? ( addr u -- flag ) ['] evaluate catch dup if nip nip then 0<> ;
T{ s" -1 /node 0 store: bad1" bad-store? -> true }T
T{ s" 2 /node 3 store: bad2" bad-store? -> true }T
T{ s" 2 0 0 store: bad3" bad-store? -> true }T
T{ s" 2 /node 1+ 0 store: bad4" bad-store? -> true }T
T{ s" 0 /node 0 store: empty0" bad-store? -> false }T

\ Allocation: indices in order, identities from the serial, nothing changes
\ when the store is full.
T{ s0 ' store-new rs-checked -> 0 true }T
T{ s0 store-new -> 1 true }T
T{ s0 store-new -> 2 true }T
T{ s0 store-new -> false }T
T{ s0 store-count @ s0 store-serial @ -> 3 3 }T
T{ 0 2 s0 store-pair-valid? 0 3 s0 store-pair-valid? 3 0 s0 store-pair-valid? -> true false false }T
T{ 0 s0 store-identity@ -> 1 true }T
T{ 2 s0 ' store-identity@ rs-checked -> 3 true }T
T{ 3 s0 store-identity@ -> false }T
T{ -1 s0 store-valid? -> false }T
T{ 2 s0 store-valid? -> true }T
T{ 3 s0 store-valid? -> false }T

\ A reset empties the store and advances the generation; identities are
\ never reused.
s0 store-clear
T{ s0 store-count @ s0 store-generation @ s0 store-serial @ -> 0 1 3 }T
T{ 0 s0 store-valid? -> false }T
T{ s0 store-new -> 0 true }T
T{ 0 s0 store-identity@ -> 4 true }T

\ A claim given back (store-drop): the newest record goes and its
\ identity is never reused; at the base nothing changes.
T{ s0 store-new -> 1 true }T
T{ s0 ' store-drop rs-checked s0 store-count @ 1 s0 store-valid? -> 1 false }T
T{ s0 store-new 1 s0 store-identity@ -> 1 true 6 true }T
T{ s0 store-drop s0 store-drop s0 store-drop s0 store-count @ -> 0 }T

\ A store with base 1 keeps record 0, and its identity, through a reset.
s1 ' store-clear rs-checked
T{ s1 store-count @ s1 store-count-valid? -> 1 true }T
0 s1 store-identity @ constant s1-identity0
s1 store-clear
T{ 0 s1 store-identity@ -> s1-identity0 true }T
T{ 0 s1 store-valid? -> true }T
T{ s1 store-new -> 1 true }T
T{ s1 store-new -> false }T

\ A spent serial refuses allocation and changes nothing.
s0 store-clear
max-n s0 store-serial !
T{ s0 store-spent? -> true }T
T{ s0 store-new -> false }T
T{ s0 store-count @ s0 store-serial @ -> 0 max-n }T

\ A saturated generation poisons the store, and it stays poisoned.
0 s0 store-serial !
max-n s0 store-generation !
s0 store-clear
T{ s0 store-generation @ -> -1 }T
T{ s0 store-count-valid? -> false }T
T{ s0 store-new -> false }T
T{ s0 store-serial @ -> 0 }T
s0 store-clear
T{ s0 store-generation @ -> -1 }T

\ Corrupted counts fail closed before any record is addressed.
0 s0 store-generation !
-1 s0 store-count !
T{ s0 store-count-valid? -> false }T
T{ 0 s0 store-valid? -> false }T
T{ s0 store-new -> false }T
T{ 0 s0 store-identity@ -> false }T
4 s0 store-count !
T{ s0 store-count-valid? -> false }T
T{ 3 s0 store-valid? -> false }T
T{ s0 store-new -> false }T
T{ s0 store-count @ -> 4 }T

\ A corrupted shape field breaks the seal: every check fails closed and
\ nothing is allocated, until the field is restored.
0 s0 store-count !
: shape-broken? ( store -- flag )
  dup store-count-valid? swap store-new if drop true else false then or 0= ;
1000 s0 store-capacity !
T{ s0 shape-broken? -> true }T
3 s0 store-capacity !
T{ s0 store-count-valid? -> true }T
2 s0 store-base !
T{ s0 shape-broken? -> true }T
0 s0 store-base !
/node 2* s0 store-width !
T{ s0 shape-broken? -> true }T
/node s0 store-width !
T{ s0 store-count-valid? -> true }T
T{ s0 store-count @ -> 0 }T
\ The block and the limit are shape fields too.
s0 store-limit @ 1+ s0 store-limit !
T{ s0 shape-broken? -> true }T
s0 store-limit @ 1- s0 store-limit !
1 s0 store-block !
T{ s0 shape-broken? -> true }T
0 s0 store-block !
T{ s0 store-count-valid? -> true }T
\ A store made in place never grows: full when every record is used.
T{ s0 store-heap? s0 store-grow -> false outcome-ok }T

\ Heap stores (plan task 1.1.5): a header in the caller's memory, a block
\ on the heap that grows by doubling up to the limit, records and
\ identities kept, marks valid across growth; then full at the limit.
create h0 store-header allot
T{ 2 /node 0 h0 store-heap-init -> outcome-ok }T
T{ h0 store-heap? h0 store-capacity @ h0 store-limit @ h0 store-count @ -> true 2 2 0 }T
T{ 1 2 3 h0 node-new 4 5 6 h0 node-new -> 0 true 1 true }T
T{ h0 store-grow 7 8 9 h0 node-new -> outcome-full false }T
T{ 1 h0 store-limit! -> outcome-invalid }T
T{ 40 h0 store-limit! h0 store-limit @ h0 store-capacity @ -> outcome-ok 40 2 }T
create hm /store-mark allot
T{ hm h0 store-mark -> outcome-ok }T
: h0-fill ( n -- ) 0 ?do h0 store-grow drop i dup dup h0 node-new 2drop loop ;
T{ 38 h0-fill h0 store-count @ h0 store-capacity @ -> 40 40 }T
T{ h0 store-grow 1 1 1 h0 node-new -> outcome-full false }T
T{ 0 h0 node-read 1 h0 node-read 39 h0 node-read -> 1 2 3 true 4 5 6 true 37 37 37 true }T
T{ 0 h0 store-identity@ 39 h0 store-identity@ -> 1 true 40 true }T
T{ hm h0 store-rollback h0 store-count @ h0 store-capacity @ -> outcome-ok 2 40 }T
\ A smaller limit shrinks the block, keeping the records in use.
T{ 2 h0 store-limit! h0 store-capacity @ 1 h0 node-read -> outcome-ok 2 4 5 6 true }T
T{ h0 ' store-grow rs-checked -> outcome-full }T
h0 store-heap-free
T{ h0 store-heap? h0 store-count-valid? h0 store-grow -> false false outcome-invalid }T
T{ 0 /node 3 h0 store-heap-init h0 store-heap? -> outcome-invalid false }T

\ store-poison: empty and permanently invalid.
s0 store-poison
T{ s0 store-count @ s0 store-generation @ -> 0 -1 }T
T{ 1 2 3 s0 node-new -> false }T

\ Tagged nodes: three named cells, whole-node store and fetch.
create n1 /node allot
T{ /node -> 3 cells }T
T{ 7 8 9 n1 node! n1 node@ -> 7 8 9 }T
T{ 1 2 3 n1 ' node! rs-checked n1 ' node@ rs-checked -> 1 2 3 }T
7 8 9 n1 node!
T{ n1 node-tag @ n1 node-first @ n1 node-second @ -> 7 8 9 }T

\ node-new and node-read on a store of nodes, including a full store and
\ invalid indices.
T{ 2 /node 0 store: s2 -> }T
T{ 1 2 3 s2 node-new -> 0 true }T
T{ 4 5 6 s2 ' node-new rs-checked -> 1 true }T
T{ 7 8 9 s2 node-new -> false }T
T{ s2 store-count @ s2 store-serial @ -> 2 2 }T
T{ 0 s2 node-read -> 1 2 3 true }T
T{ 1 s2 ' node-read rs-checked -> 4 5 6 true }T
T{ 2 s2 node-read -> false }T
T{ -1 s2 node-read -> false }T

\ Outcomes: the vocabulary, the sanitizer and the flag conversion.
T{ outcome-ok outcome-invalid outcome-exhausted -> 0 1 2 }T
T{ outcome-unknown outcome-rejected outcome-unsupported outcome-full -> 3 4 5 6 }T
T{ 0 outcome? 6 outcome? -1 outcome? 7 outcome? -> true true false false }T
T{ 3 outcome-sane 6 outcome-sane 7 outcome-sane -1 outcome-sane true outcome-sane ->
  3 6 1 1 1 }T
T{ outcome-full ok? outcome-exhausted ok? -> false false }T
T{ outcome-ok ok? outcome-unknown ok? -> true false }T
T{ true flag>outcome false flag>outcome -> outcome-ok outcome-invalid }T
\ room>outcome: only a true flag is room. visit-outcome: no fuel (zero or
\ negative) is exhausted whatever the room; with fuel, the room decides.
T{ true room>outcome false room>outcome 1 room>outcome -> outcome-ok outcome-full 6 }T
T{ 1 true visit-outcome 1 false visit-outcome max-n true visit-outcome ->
  outcome-ok outcome-full outcome-ok }T
T{ 0 true visit-outcome 0 false visit-outcome -1 false visit-outcome ->
  outcome-exhausted outcome-exhausted outcome-exhausted }T
T{ max-n 1+ true visit-outcome 1 2 visit-outcome 3 true ' visit-outcome rs-checked ->
  outcome-exhausted outcome-full outcome-ok }T
\ outcome-text: every outcome's name; anything else reads as invalid.
: named? ( outcome c-addr u -- flag ) rot outcome-text compare 0= ;
T{ outcome-ok s" ok" named? outcome-invalid s" invalid" named? -> true true }T
T{ outcome-exhausted s" exhausted" named? outcome-unknown s" unknown" named? -> true true }T
T{ outcome-rejected s" rejected" named? outcome-unsupported s" unsupported" named?
   -> true true }T
T{ outcome-full s" full" named? 7 s" invalid" named? -1 s" invalid" named? -> true true true }T
T{ outcome-full ' outcome-text rs-checked nip max-n outcome-text nip -> 4 7 }T

\ Walk records: definition, budget and the bounded work stack.
T{ 4 walk: w1 -> }T
T{ w1 walk-capacity @ w1 walk-pending @ w1 walk-fuel @ -> 4 0 0 }T
T{ -1 w1 walk-budget w1 walk-fuel @ -> false 0 }T
T{ 7 w1 walk-budget w1 walk-fuel @ -> true 7 }T
T{ 10 w1 walk-push 11 w1 walk-push 12 w1 walk-push 13 w1 walk-push -> true true true true }T
T{ 14 w1 walk-push w1 walk-pending @ -> false 4 }T
T{ w1 walk-pop w1 walk-pop -> 13 12 }T
-1 w1 walk-pending !
T{ 15 w1 ' walk-push rs-checked -> false }T
2 w1 walk-pending !

\ Children must come before the node being visited.
3 w1 walk-node !
T{ 0 w1 walk-child? 2 w1 walk-child? 3 w1 walk-child? -1 w1 walk-child? -> true true false false }T
0 w1 walk-pending !
T{ 2 w1 walk-child 3 w1 walk-child -> outcome-ok outcome-invalid }T
T{ 0 1 w1 walk-children 0 3 w1 walk-children 3 0 w1 walk-children -> outcome-ok outcome-invalid outcome-invalid }T
T{ w1 walk-pending @ -> 3 }T
\ With room for one item only the second push fails, and with none the
\ first: both are full.
T{ 0 1 w1 walk-push2 w1 walk-pending @ -> outcome-full 4 }T
T{ 0 1 w1 walk-push2 w1 walk-pending @ -> outcome-full 4 }T
T{ 1 2 w1 99 walk-bad-tag -> outcome-invalid 99 }T

\ walk-run over a DAG where node n >= 2 has children n-1 and n-2: shared
\ nodes are visited once per path, so root n costs V(n) = 1 + V(n-1) +
\ V(n-2) visits with V(0) = V(1) = 1, and V(5) = 15.
: fib-visit ( walk -- outcome )
  dup walk-node @ dup 2 < if 2drop outcome-ok else dup 1- swap 2 - rot walk-push2 then ;
T{ 8 walk: w2 -> }T
15 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-fuel @ -> outcome-ok 0 }T
14 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run -> outcome-exhausted }T
100 w2 walk-budget drop
T{ 5 ' fib-visit w2 ' walk-run rs-checked w2 walk-fuel @ -> outcome-ok 85 }T
T{ 0 w2 walk-budget drop 5 ' fib-visit w2 walk-run -> outcome-exhausted }T
\ Out of room rather than fuel: a work stack of two items cannot hold the
\ pending children, which is full, with fuel left.
T{ 2 walk: w3 -> }T
100 w3 walk-budget drop
T{ 5 ' fib-visit w3 walk-run w3 walk-fuel @ 0> -> outcome-full true }T
\ Room for a push is checked where it happens, independently of fuel (ADR
\ 0008): a visit that took the last unit and finds no room for its second
\ child is full, with no fuel left; with room for both it is exhausted at
\ the next step.
T{ 1 walk: w4 -> }T
1 w4 walk-budget drop
T{ 5 ' fib-visit w4 walk-run w4 walk-fuel @ -> outcome-full 0 }T
1 w3 walk-budget drop
T{ 5 ' fib-visit w3 walk-run w3 walk-fuel @ -> outcome-exhausted 0 }T

\ The first outcome that is not ok stops the walk.
: stop-at-3 ( walk -- outcome ) dup walk-node @ 3 = if drop outcome-unknown else fib-visit then ;
100 w2 walk-budget drop
T{ 5 ' stop-at-3 w2 walk-run -> outcome-unknown }T
\ A walk that ends before its first visit names no node (-1), not the node
\ of the walk before: here the root cannot be pushed (a corrupted
\ capacity, invalid), or no fuel is left (exhausted).
T{ w2 walk-node @ -> 3 }T
w2 walk-capacity @  0 w2 walk-capacity !
T{ 5 ' fib-visit w2 walk-run w2 walk-node @ -> outcome-invalid -1 }T
w2 walk-capacity !
T{ 5 ' stop-at-3 w2 walk-run w2 walk-node @ -> outcome-unknown 3 }T
0 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-node @ -> outcome-exhausted -1 }T
T{ 2 walk2: pz -> }T
3 pz walk-node !
T{ 5 6 ' fib-visit pz walk-run-pair pz walk-node @ -> outcome-exhausted -1 }T

\ Re-entrancy: a visitor may run a complete walk on another record, as the
\ session check runs a level-scope check inside its own walk.
: nested-visit ( walk -- outcome ) 2 ['] fib-visit w1 walk-run dup ok? if drop fib-visit else nip then ;
0 w1 walk-pending !
1000 w1 walk-budget drop
100 w2 walk-budget drop
T{ 4 ' nested-visit w2 walk-run w2 walk-fuel @ w1 walk-fuel @ -> outcome-ok 91 973 }T

\ Outcomes at the edges, the strict flag conversion and the helpers.
T{ 0 outcome-sane 4 outcome-sane 5 outcome-sane -> 0 4 5 }T
T{ max-n outcome-sane max-n 1+ outcome-sane -> 1 1 }T
T{ 1 flag>outcome 2 flag>outcome 3 flag>outcome -> 1 1 1 }T
T{ 7 outcome-ok ok-then? -> 7 true }T
T{ 7 outcome-unknown ok-then? -> outcome-unknown false }T
T{ 7 drop-invalid -> outcome-invalid }T
\ ok-keep? and ok-keep2? keep the values below a result only on ok; a
\ failure keeps the result and the outcome, whatever the result is.
T{ 7 8 outcome-ok ok-keep? -> 7 8 true }T
T{ 7 -1 outcome-exhausted ok-keep? -> -1 outcome-exhausted false }T
T{ 7 8 outcome-unknown ok-keep? -> 8 outcome-unknown false }T
T{ 6 7 8 outcome-ok ok-keep2? -> 6 7 8 true }T
T{ 6 7 -1 outcome-invalid ok-keep2? -> -1 outcome-invalid false }T
T{ 6 7 8 outcome-rejected ok-keep2? -> 8 outcome-rejected false }T
T{ 6 7 8 outcome-ok ' ok-keep2? rs-checked 7 8 outcome-unknown ' ok-keep? rs-checked ->
  6 7 8 true 8 outcome-unknown false }T
T{ outcome-exhausted no-result outcome-ok no-result ->
  -1 outcome-exhausted -1 outcome-ok }T
\ no-result-flag: -1 and false under the outcome, for every outcome and one
\ outside the vocabulary, the values below untouched (review ops-c1 B1:
\ in place of whnf.fs's wc-fail, kabstract.fs's kab-none, reduce-nat.fs's
\ rn-failed, synth.fs's sy-none and the inline `-1 false rot`).
T{ 7 outcome-full no-result-flag 7 outcome-unsupported no-result-flag ->
  7 -1 false outcome-full 7 -1 false outcome-unsupported }T
T{ outcome-ok no-result-flag outcome-rejected no-result-flag -> -1 false outcome-ok -1 false outcome-rejected }T
T{ outcome-exhausted no-result-flag outcome-invalid no-result-flag 99 no-result-flag ->
  -1 false outcome-exhausted -1 false outcome-invalid -1 false 99 }T
T{ 5 6 outcome-unknown ' no-result-flag rs-checked -> 5 6 -1 false outcome-unknown }T
\ ok-or-none: the result kept on ok, -1 in its place on every other
\ outcome, a value outside the vocabulary too.
T{ 7 outcome-ok ok-or-none 7 outcome-full ok-or-none 7 outcome-invalid ok-or-none
   -> 7 outcome-ok -1 outcome-full -1 outcome-invalid }T
T{ 7 outcome-exhausted ok-or-none 7 outcome-unknown ok-or-none 7 outcome-rejected ok-or-none
   -> -1 outcome-exhausted -1 outcome-unknown -1 outcome-rejected }T
T{ 7 outcome-unsupported ok-or-none 7 99 ok-or-none -1 outcome-ok ok-or-none
   -> -1 outcome-unsupported -1 99 -1 outcome-ok }T
T{ 5 6 outcome-ok ' ok-or-none rs-checked 5 6 outcome-full ' ok-or-none rs-checked
   -> 5 6 outcome-ok 5 -1 outcome-full }T
\ ok-and in place of the hand-written step `dup ok? if drop y then`
\ (reuse-d: seven sites, three in the kernel) and ok-apply in place of
\ `ok-then? if y else no-result then` (five sites, one in the kernel):
\ the old text, kept here as the model, and the word leave the same stack
\ for every outcome and one outside the vocabulary.
: rd-step ( x -- x' outcome ) 10 + outcome-unknown ;
: rd-old-and ( x outcome -- x' outcome' ) dup ok? if drop rd-step then ;
: rd-old-apply ( x outcome -- x' outcome' ) ok-then? if rd-step else no-result then ;
: rd-and-same? ( outcome -- flag )
  5 over rd-old-and rot 5 swap ['] rd-step ok-and d= ;
: rd-apply-same? ( outcome -- flag )
  5 over rd-old-apply rot 5 swap ['] rd-step ok-apply d= ;
: rd-all-same? ( xt -- flag )
  true outcome-full 2 + -1 do over i swap execute and loop nip ;
T{ ' rd-and-same? rd-all-same? ' rd-apply-same? rd-all-same? -> true true }T
\ The Forth review of reuse-d, findings 1 and 2: ok-then2? in place of
\ `dup ok? 0= if nip nip exit then drop` (kernel environment.fs's
\ lf-env-unheld-pass and the import files), and cell-at@ and pair-at in
\ place of `swap cells + @` and `swap 2* cells +` (kernel mixed-open.fs's
\ lf-open-s; import feed.fs, stage-records.fs, snapshot-tier.fs,
\ ndjson.fs): the old text, kept here as the model, gives the same for
\ every outcome and every index.
: rd-old-ch ( a b outcome -- x ) dup ok? 0= if nip nip exit then drop + ;
: rd-new-ch ( a b outcome -- x ) ok-then2? 0= if exit then + ;
: rd-new-ch2 ( a b outcome -- x ) ok-then2? if + then ;
: rd-ch-same? ( outcome -- flag )
  3 4 2 pick rd-old-ch 3 4 3 pick rd-new-ch 3 4 4 pick rd-new-ch2
  >r over = swap r> = and nip ;
T{ ' rd-ch-same? rd-all-same? 3 4 outcome-ok rd-new-ch2 -> true 7 }T
: rd-old-at ( i a-addr -- x ) swap cells + @ ;
: rd-old-pair ( i a-addr -- addr ) swap 2* cells + ;
: rd-at-same? ( -- flag )
  true 5 0 do i some-cells cell-at@ i some-cells rd-old-at = and loop ;
: rd-pair-same? ( -- flag )
  true 9 -2 do i some-cells pair-at i some-cells rd-old-pair = and loop ;
T{ rd-at-same? rd-pair-same? -> true true }T
T{ 5 outcome-ok ' rd-step ok-apply 5 outcome-rejected ' rd-step ok-apply
   -> 15 outcome-unknown -1 outcome-rejected }T
T{ 4 5 outcome-ok ' rd-step ' ok-apply rs-checked -> 4 15 outcome-unknown }T
\ ok-apply2 (cleanup-families-2) in place of `ok-then? if y else nip
\ no-result then`, a step of two values: the old text, kept as the
\ model, and the word leave the same stack for every outcome and one
\ outside the vocabulary; both values are dropped on a failure.
: rd-step2 ( x1 x2 -- x' outcome ) 10 * + outcome-unknown ;
: rd-old-apply2 ( x1 x2 outcome -- x' outcome' ) ok-then? if rd-step2 else nip no-result then ;
: rd-apply2-same? ( outcome -- flag )
  >r 3 5 r@ rd-old-apply2 3 5 r> ['] rd-step2 ok-apply2 d= ;
T{ ' rd-apply2-same? rd-all-same? -> true }T
T{ 3 5 outcome-ok ' rd-step2 ok-apply2 3 5 outcome-full ' rd-step2 ok-apply2
   -> 53 outcome-unknown -1 outcome-full }T
T{ 4 3 5 outcome-ok ' rd-step2 ' ok-apply2 rs-checked -> 4 53 outcome-unknown }T
\ ok-apply3 (cleanup-families-3) in place of `ok-then? 0= if nip nip
\ no-result exit then` before a step of three values: the old text, kept
\ as the model, and the word leave the same stack for every outcome and
\ one outside the vocabulary; all three values are dropped on a failure.
: rd-step3 ( x1 x2 x3 -- x' outcome ) 10 * + 10 * + outcome-unknown ;
: rd-old-apply3 ( x1 x2 x3 outcome -- x' outcome' )
  ok-then? 0= if nip nip no-result exit then rd-step3 ;
: rd-apply3-same? ( outcome -- flag )
  >r 2 3 5 r@ rd-old-apply3 2 3 5 r> ['] rd-step3 ok-apply3 d= ;
T{ ' rd-apply3-same? rd-all-same? -> true }T
T{ 2 3 5 outcome-ok ' rd-step3 ok-apply3 2 3 5 outcome-full ' rd-step3 ok-apply3
   -> 532 outcome-unknown -1 outcome-full }T
T{ 4 2 3 5 outcome-ok ' rd-step3 ' ok-apply3 rs-checked -> 4 532 outcome-unknown }T
T{ 4 2 3 5 outcome-rejected ' rd-step3 ' ok-apply3 rs-checked -> 4 -1 outcome-rejected }T
\ room-result: a store's x true is x and ok, its false is -1 and full;
\ any nonzero flag counts as true (IF's reading), the values below untouched.
T{ 5 7 true room-result 5 false room-result -> 5 7 outcome-ok 5 -1 outcome-full }T
T{ 0 true room-result 7 1 room-result -1 true room-result -> 0 outcome-ok 7 outcome-ok -1 outcome-ok }T
T{ 7 true ' room-result rs-checked false ' room-result rs-checked
   -> 7 outcome-ok -1 outcome-full }T
\ 2dup-under: the two values under the top copied above them, under it
\ (review reuse-out S1), and the header's example as a step of any?.
T{ 1 2 3 2dup-under 4 5 6 ' 2dup-under rs-checked -> 1 2 1 2 3 4 5 4 5 6 }T
: cell-is? ( x addr k -- x addr flag ) 2dup-under cells + @ = ;
create three-cells 4 , 7 , 9 ,
T{ 9 three-cells 3 ' cell-is? any? nip nip 8 three-cells 3 ' cell-is? any? nip nip -> true false }T
\ ok-then3? keeps three values only on ok (review FRI B6).
T{ 5 6 7 outcome-ok ok-then3? -> 5 6 7 true }T
T{ 5 6 7 outcome-full ok-then3? -> outcome-full false }T
T{ 5 6 7 outcome-ok ' ok-then3? rs-checked 5 6 7 outcome-rejected ' ok-then3? rs-checked ->
  5 6 7 true outcome-rejected false }T
\ outcome-and: two outcomes as one, the first that is not ok; ok only
\ when both are; any value outside the vocabulary passes through as the
\ first failure, never as ok.
T{ outcome-ok outcome-ok outcome-and outcome-ok outcome-full outcome-and -> 0 6 }T
T{ outcome-unknown outcome-ok outcome-and outcome-exhausted outcome-full outcome-and -> 3 2 }T
T{ outcome-rejected outcome-invalid outcome-and 99 outcome-ok outcome-and -> 4 99 }T
T{ outcome-ok outcome-unsupported ' outcome-and rs-checked -> 5 }T
\ outcome-steps: the steps ( x -- outcome ) of a 0-ended list in order,
\ to the first that is not ok; an empty list is ok and runs nothing.
variable step-trail
: step-a ( x -- outcome ) step-trail @ 10 * 1+ step-trail ! drop outcome-ok ;
: step-b ( x -- outcome ) step-trail @ 10 * 2 + step-trail ! ;
create steps-none 0 ,
create steps-ab ' step-a , ' step-b , ' step-a , 0 ,
: stepped ( x a -- outcome trail ) 0 step-trail ! outcome-steps step-trail @ ;
T{ 7 steps-none stepped -> outcome-ok 0 }T
T{ outcome-ok steps-ab stepped -> outcome-ok 121 }T
T{ outcome-unknown steps-ab stepped -> outcome-unknown 12 }T
T{ outcome-full steps-ab ' stepped rs-checked -> outcome-full 12 }T
\ ok-and: a step ( i*x -- j*x outcome ) run only while the outcome so far
\ is ok (review FRK A); a failure, or a value outside the vocabulary,
\ passes through with the values below it, the step not run.
: step-c ( x -- x' outcome ) 1+ step-trail @ 10 * 3 + step-trail ! outcome-ok ;
: step-u ( x -- x outcome ) step-trail @ 10 * 4 + step-trail ! outcome-unknown ;
: anded ( x outcome xt -- x' outcome trail ) 0 step-trail ! ok-and step-trail @ ;
T{ 7 outcome-ok ' step-c anded -> 8 outcome-ok 3 }T
T{ 7 outcome-ok ' step-u anded -> 7 outcome-unknown 4 }T
T{ 7 outcome-full ' step-c anded -> 7 outcome-full 0 }T
T{ 7 outcome-exhausted ' step-c anded 7 99 ' step-c anded -> 7 2 0 7 99 0 }T
T{ 0 step-trail ! 5 outcome-ok ' step-c ok-and ' step-u ok-and ' step-c ok-and step-trail @
  -> 6 outcome-unknown 34 }T
T{ 5 outcome-ok ' step-c ' anded rs-checked 5 outcome-rejected ' step-c ' anded rs-checked
  -> 6 outcome-ok 3 5 outcome-rejected 0 }T
\ ok-with: a step ( x -- outcome ) on x, which stays below, run only while
\ the outcome so far is ok; a failure passes through, the step not run.
: step-d ( x -- outcome ) step-trail @ 10 * + step-trail ! outcome-ok ;
: step-e ( x -- outcome ) step-trail @ 10 * + step-trail ! outcome-exhausted ;
: withed ( x outcome xt -- x outcome trail ) 0 step-trail ! ok-with step-trail @ ;
T{ 4 outcome-ok ' step-d withed -> 4 outcome-ok 4 }T
T{ 4 outcome-ok ' step-e withed -> 4 outcome-exhausted 4 }T
T{ 4 outcome-invalid ' step-d withed 4 -5 ' step-d withed -> 4 1 0 4 -5 0 }T
T{ 0 step-trail ! 3 outcome-ok ' step-d ok-with ' step-e ok-with ' step-d ok-with step-trail @
  -> 3 outcome-exhausted 33 }T
T{ 4 outcome-ok ' step-d ' withed rs-checked 4 outcome-full ' step-d ' withed rs-checked
  -> 4 outcome-ok 4 4 outcome-full 0 }T
\ drop-ok: a step ( x -- outcome ) that accepts any x, a failing outcome
\ or a value outside the vocabulary among them; as a step of a chain.
T{ 5 drop-ok 7 outcome-rejected drop-ok -1 drop-ok -> outcome-ok 7 outcome-ok outcome-ok }T
T{ 9 outcome-ok ' drop-ok ok-with 9 outcome-full ' drop-ok ok-with
  -> 9 outcome-ok 9 outcome-full }T
T{ 3 ' drop-ok rs-checked -> outcome-ok }T
\ ok-each: the step ( i*x k -- i*x outcome ) for k = 0 .. n-1 while ok;
\ it sees the values below k and may replace them (a fold); n <= 0 runs
\ nothing. step-k keeps a trail of the k it saw and fails at k = 3.
: step-k ( x k -- x outcome )
  dup step-trail @ 10 * + 1+ step-trail ! 3 = if outcome-unknown else outcome-ok then ;
: eached ( x n xt -- x outcome trail ) 0 step-trail ! ok-each step-trail @ ;
T{ 7 3 ' step-k eached -> 7 outcome-ok 123 }T
T{ 7 6 ' step-k eached -> 7 outcome-unknown 1234 }T
T{ 7 0 ' step-k eached 7 -5 ' step-k eached 7 max-n invert ' step-k eached
   -> 7 outcome-ok 0 7 outcome-ok 0 7 outcome-ok 0 }T
T{ 7 6 ' step-k ' eached rs-checked -> 7 outcome-unknown 1234 }T
\ A fold: the sum of k * k below n, and a step that uses the return stack.
: square+ ( sum k -- sum' outcome ) dup * + outcome-ok ;
: square+r ( sum k -- sum' outcome ) >r r@ r> * + outcome-ok ;
T{ 0 5 ' square+ ok-each 0 5 ' square+r ok-each -> 30 outcome-ok 30 outcome-ok }T
\ No value below k, and two; the failing step's values are kept.
: step-full ( k -- outcome ) 2 = if outcome-full else outcome-ok then ;
: pair-step ( a b k -- a' b' outcome ) + swap 1+ swap dup 10 > if outcome-full else outcome-ok then ;
T{ 9 ' step-full ok-each 2 ' step-full ok-each -> outcome-full outcome-ok }T
T{ 0 0 9 ' pair-step ok-each -> 6 15 outcome-full }T
\ Nested: each step runs a loop of its own.
: nested-squares ( sum k -- sum' outcome ) ['] square+ ok-each ;
T{ 0 4 ' nested-squares ok-each -> 6 outcome-ok }T
\ A step that leaves an outcome outside the vocabulary stops the loop.
: step-odd ( k -- outcome ) drop 99 ;
T{ 3 ' step-odd ok-each -> 99 }T
\ ok-fold: x := step ( x k y -- x' outcome ), y given to every step and
\ kept; the failing step's x' and outcome.
: fold-step ( x k y -- x' outcome )
  >r 10 * + r> + dup 100 > if drop -1 outcome-exhausted else outcome-ok then ;
T{ 0 3 5 ' fold-step ok-fold -> 45 outcome-ok }T
T{ 0 5 5 ' fold-step ok-fold -> -1 outcome-exhausted }T
T{ 4 0 5 ' fold-step ok-fold 4 -2 5 ' fold-step ok-fold -> 4 outcome-ok 4 outcome-ok }T
T{ 1 2 3 ' fold-step ' ok-fold rs-checked -> 17 outcome-ok }T
: fold-k ( x k y -- x' outcome ) drop step-k ;
T{ 0 step-trail ! 0 6 0 ' fold-k ok-fold step-trail @ -> 0 outcome-unknown 1234 }T
\ outcome-first!: the first failure stays; ok never overwrites one.
variable first-cell
T{ outcome-ok first-cell ! outcome-ok first-cell outcome-first! first-cell @ -> outcome-ok }T
T{ outcome-full first-cell outcome-first! first-cell @ -> outcome-full }T
T{ outcome-invalid first-cell outcome-first! outcome-ok first-cell outcome-first! first-cell @
   -> outcome-full }T
T{ outcome-unknown first-cell ' outcome-first! rs-checked first-cell @ -> outcome-full }T
\ ok-store: x stored only on ok; every other outcome, a value outside the
\ vocabulary too, is given back with x dropped and the cell as it was; the
\ values below untouched (review s2-unfold-a re-check L1).
variable kept-cell
T{ 5 kept-cell ! 7 kept-cell outcome-ok ok-store kept-cell @ -> outcome-ok 7 }T
T{ 8 kept-cell outcome-invalid ok-store 8 kept-cell outcome-exhausted ok-store kept-cell @
   -> outcome-invalid outcome-exhausted 7 }T
T{ 8 kept-cell outcome-unknown ok-store 8 kept-cell outcome-rejected ok-store kept-cell @
   -> outcome-unknown outcome-rejected 7 }T
T{ 8 kept-cell outcome-unsupported ok-store 8 kept-cell outcome-full ok-store 8 kept-cell 99
   ok-store kept-cell @ -> outcome-unsupported outcome-full 99 7 }T
T{ 1 -1 kept-cell outcome-ok ' ok-store rs-checked 2 0 kept-cell outcome-full ' ok-store
   rs-checked kept-cell @ -> 1 outcome-ok 2 outcome-full -1 }T
\ ok-true?: go on (true) only after true and ok; else false, the outcome
\ and false: a failure keeps its outcome whatever the flag.
T{ true outcome-ok ok-true? 1 outcome-ok ok-true? -> true true }T
T{ false outcome-ok ok-true? -> false outcome-ok false }T
T{ true outcome-full ok-true? false outcome-unknown ok-true? 7 99 ok-true?
   -> false outcome-full false false outcome-unknown false false 99 false }T
\ all?: the test ( i*x k -- i*x flag ) for k = 0 .. n-1 while true; n <=
\ 0 gives true. test-k keeps a trail of the k it saw and fails at k = 3;
\ cell-pos? reads a table kept below k.
: test-k ( x k -- x flag ) dup step-trail @ 10 * + 1+ step-trail ! 3 <> ;
: alled ( x n xt -- x flag trail ) 0 step-trail ! all? step-trail @ ;
T{ 7 3 ' test-k alled 7 6 ' test-k alled -> 7 true 123 7 false 1234 }T
T{ 7 0 ' test-k alled 7 -5 ' test-k alled 7 max-n invert ' test-k alled
   -> 7 true 0 7 true 0 7 true 0 }T
T{ 7 6 ' test-k ' alled rs-checked -> 7 false 1234 }T
: cell-pos? ( table k -- table flag ) cells over + @ 0> ;
create pos-cells 3 , 1 , 9 , -2 , 4 ,
T{ pos-cells 3 ' cell-pos? all? nip pos-cells 4 ' cell-pos? all? nip -> true false }T
\ A true flag other than -1 counts as true; the answer is a well-formed flag.
: test-one ( k -- flag ) drop 1 ;
T{ 4 ' test-one all? -> true }T
\ Nested: whether every k < n has every j < k below 3.
: below-3? ( j -- flag ) 3 < ;
: all-below? ( k -- flag ) ['] below-3? all? ;
T{ 4 ' all-below? all? 5 ' all-below? all? -> true false }T
\ A test that uses the return stack.
: test-r ( x k -- x flag ) >r dup r> > ;
T{ 5 5 ' test-r all? 5 6 ' test-r all? -> 5 true 5 false }T
\ any?: the test ( i*x k -- i*x flag ) for k = 0 .. n-1 until true; n <=
\ 0 gives false. test-k is true for every k but 3: it stops at k = 0;
\ test-3 holds only at k = 3.
: test-3 ( x k -- x flag ) dup step-trail @ 10 * + 1+ step-trail ! 3 = ;
: anyed ( x n xt -- x flag trail ) 0 step-trail ! any? step-trail @ ;
T{ 7 3 ' test-3 anyed 7 6 ' test-3 anyed 7 6 ' test-k anyed -> 7 false 123 7 true 1234 7 true 1 }T
T{ 7 0 ' test-3 anyed 7 -5 ' test-3 anyed 7 max-n invert ' test-3 anyed
   -> 7 false 0 7 false 0 7 false 0 }T
T{ 7 6 ' test-3 ' anyed rs-checked -> 7 true 1234 }T
create neg-cells 3 , 1 , 9 , -2 , 4 ,
: cell-neg? ( table k -- table flag ) cells over + @ 0< ;
T{ neg-cells 3 ' cell-neg? any? nip neg-cells 4 ' cell-neg? any? nip -> false true }T
\ any-in? (ROUT3): the same over lo .. hi-1, none when hi <= lo; the test
\ sees each k itself.
T{ neg-cells 0 3 ' cell-neg? any-in? nip neg-cells 3 5 ' cell-neg? any-in? nip -> false true }T
T{ neg-cells 4 5 ' cell-neg? any-in? nip neg-cells 3 3 ' cell-neg? any-in? nip -> false false }T
T{ neg-cells 4 2 ' cell-neg? any-in? nip neg-cells 2 4 ' cell-neg? ' any-in? rs-checked nip
   -> false true }T
T{ 7 2 6 ' test-3 ' any-in? rs-checked 0 step-trail ! 7 4 6 ' test-3 any-in? -> 7 true 7 false }T
\ find-index (find.fs, loaded under HEX with BASE kept; review F4 of
\ 2026-11-18): the first k whose test holds, x
\ dropped; none after it runs; false when none holds or n <= 0; the
\ return stack balanced (rs-checked); the header's example.
: found ( x n xt -- k true trail | false trail ) 0 step-trail ! find-index step-trail @ ;
T{ 7 6 ' test-3 found 7 3 ' test-3 found 7 6 ' test-k found -> 3 true 1234 false 123 0 true 1 }T
T{ 7 0 ' test-3 found 7 -5 ' test-3 found 7 max-n invert ' test-3 found
   -> false 0 false 0 false 0 }T
T{ 7 6 ' test-3 ' find-index rs-checked -> 3 true }T
T{ neg-cells 3 ' cell-neg? find-index neg-cells 5 ' cell-neg? find-index -> false 3 true }T
create neg-example 5 , -2 , -7 ,
T{ neg-example 3 ' cell-neg? find-index -> 1 true }T
T{ find-base [defined] find-index -> 16 true }T
\ find-last-index: the last k whose test holds, tried from n-1 down
\ (review tactic-a2ii B3b); the same refusals of n <= 0.
: found-last ( x n xt -- k true trail | false trail )
  0 step-trail ! find-last-index step-trail @ ;
T{ 7 6 ' test-3 found-last 7 3 ' test-3 found-last -> 3 true 654 false 321 }T
T{ 7 0 ' test-3 found-last 7 -5 ' test-3 found-last 7 max-n invert ' test-3 found-last
   -> false 0 false 0 false 0 }T
T{ 7 6 ' test-3 ' find-last-index rs-checked -> 3 true }T
T{ neg-cells 5 ' cell-neg? find-last-index neg-cells 3 ' cell-neg? find-last-index -> 3 true false }T
T{ neg-example 3 ' cell-neg? find-last-index neg-example 1 ' cell-neg? find-last-index
   -> 2 true false }T
T{ find-base [defined] find-last-index -> 16 true }T
\ count-index (review tactic-move-c4 B4 and re-check R1, find-index's
\ convention): how many k < n pass the test ( x k -- x flag ), every k
\ tried once in order, each test given x, x dropped; 0 for n <= 0; a
\ true answer other than -1 (1, a code 2) counts one; the return stack
\ balanced; a test ( k -- flag ) that reads no x; a test that counts in
\ turn (the inner loop's j its own); the header's example.
: odd-k ( x k -- x flag ) dup step-trail @ 10 * + 1+ step-trail ! 1 and ;
: counted ( x n xt -- m trail ) 0 step-trail ! count-index step-trail @ ;
T{ 7 5 ' odd-k counted 7 6 ' odd-k counted 7 6 ' test-3 counted
   -> 2 12345 3 123456 1 123456 }T
T{ 7 0 ' odd-k counted 7 -5 ' odd-k counted 7 max-n invert ' odd-k counted
   -> 0 0 0 0 0 0 }T
: divides? ( d k -- d flag ) over mod 0= ;
: even-code ( x k -- x code ) 1 and 0= 2 and ;
T{ 3 10 ' divides? count-index 4 10 ' divides? count-index 5 9 ' test-r count-index -> 4 3 5 }T
T{ 0 4 ' test-one count-index 0 5 ' even-code count-index -> 4 3 }T
T{ 0 3 ' below-3? count-index 0 6 ' below-3? count-index -> 3 3 }T
T{ 7 7 ' odd-k ' count-index rs-checked -> 3 }T
: odd? ( k -- flag ) 1 and ;
: two-odd-below? ( k -- flag ) 0 swap ['] odd? count-index 2 = ;
T{ 0 8 ' two-odd-below? count-index -> 2 }T
T{ neg-example 3 ' cell-neg? count-index neg-cells 5 ' cell-neg? count-index -> 2 1 }T
T{ find-base [defined] count-index -> 16 true }T
\ A true flag other than -1 counts as true; the answer is a well-formed flag.
T{ 4 ' test-one any? 0 ' test-one any? -> true false }T
\ Nested: whether some k < n has some j < k at 3 or above, and with all?.
: above-3? ( j -- flag ) 3 < 0= ;
: any-above? ( k -- flag ) ['] above-3? any? ;
T{ 4 ' any-above? any? 5 ' any-above? any? 5 ' any-above? all? -> false true false }T
T{ 5 5 ' test-r any? 5 6 ' test-r any? 5 0 ' test-r any? -> 5 true 5 true 5 false }T
\ ok-all?: the test ( i*x k -- i*x flag outcome ) while true and ok:
\ true and ok; false and ok at the first false; false and the outcome at
\ the first failure, true flag or not. n <= 0: true and ok.
: test-ko ( x k -- x flag outcome )
  dup step-trail @ 10 * + 1+ step-trail ! case
    2 of dup 0= outcome-ok endof  4 of true outcome-full endof  true outcome-ok rot
  endcase ;
: ok-alled ( x n xt -- x flag outcome trail ) 0 step-trail ! ok-all? step-trail @ ;
T{ 1 2 ' test-ko ok-alled 1 6 ' test-ko ok-alled -> 1 true outcome-ok 12 1 false outcome-ok 123 }T
T{ 0 6 ' test-ko ok-alled -> 0 false outcome-full 12345 }T
T{ 0 0 ' test-ko ok-alled 0 -3 ' test-ko ok-alled 0 max-n invert ' test-ko ok-alled
   -> 0 true outcome-ok 0 0 true outcome-ok 0 0 true outcome-ok 0 }T
T{ 0 6 ' test-ko ' ok-alled rs-checked -> 0 false outcome-full 12345 }T
\ A failing test's false flag keeps its outcome; an outcome outside the
\ vocabulary stops the loop as a failure.
: test-fail ( k -- flag outcome ) drop false outcome-exhausted ;
: test-odd ( k -- flag outcome ) drop true 99 ;
T{ 3 ' test-fail ok-all? 3 ' test-odd ok-all? -> false outcome-exhausted false 99 }T

\ ok-found?: stop at true and ok, or at any failure; go on after false and ok.
T{ true outcome-ok ok-found? 1 outcome-ok ok-found? false outcome-ok ok-found?
   -> true outcome-ok true true outcome-ok true false }T
T{ true outcome-full ok-found? false outcome-unknown ok-found? 7 99 ok-found?
   -> false outcome-full true false outcome-unknown true false 99 true }T
\ ok-any?: the test ( i*x k -- i*x flag outcome ) until a true and ok
\ answer or a failure: true and ok; false and the failure's outcome;
\ false and ok when none holds. test-ka is true at 3, fails at 4.
: test-ka ( x k -- x flag outcome )
  dup step-trail @ 10 * + 1+ step-trail ! case
    3 of true outcome-ok endof  4 of true outcome-full endof  false outcome-ok rot
  endcase ;
: ok-anyed ( x n xt -- x flag outcome trail ) 0 step-trail ! ok-any? step-trail @ ;
T{ 1 3 ' test-ka ok-anyed 1 6 ' test-ka ok-anyed -> 1 false outcome-ok 123 1 true outcome-ok 1234 }T
: test-k4 ( x k -- x flag outcome ) dup 3 = if drop false outcome-ok else test-ka then ;
T{ 0 6 ' test-k4 ok-anyed -> 0 false outcome-full 1235 }T
T{ 0 0 ' test-ka ok-anyed 0 -3 ' test-ka ok-anyed 0 max-n invert ' test-ka ok-anyed
   -> 0 false outcome-ok 0 0 false outcome-ok 0 0 false outcome-ok 0 }T
T{ 0 6 ' test-ka ' ok-anyed rs-checked -> 0 true outcome-ok 1234 }T
\ A failing test's true flag never reads as found; an outcome outside the
\ vocabulary stops the loop as a failure; a true other than -1 is true.
: test-full ( k -- flag outcome ) drop true outcome-full ;
: test-one-ok ( k -- flag outcome ) drop 1 outcome-ok ;
T{ 3 ' test-full ok-any? 3 ' test-odd ok-any? 3 ' test-one-ok ok-any?
   -> false outcome-full false 99 true outcome-ok }T
\ Nested in ok-all?: every k < n has some j < k at 2 or above.
: above-2? ( j -- flag outcome ) 2 > outcome-ok ;
: some-above-2? ( k -- flag outcome ) ['] above-2? ok-any? ;
T{ 3 ' some-above-2? ok-all? 5 ' some-above-2? ok-all? -> false outcome-ok false outcome-ok }T
T{ 5 ' some-above-2? ok-any? -> true outcome-ok }T

\ walk: refuses a capacity below 1.
: bad-walk? ( addr u -- flag ) ['] evaluate catch dup if nip nip then 0<> ;
T{ s" 0 walk: wbad0" bad-walk? s" -1 walk: wbad1" bad-walk? s" -100 walk: wbad2" bad-walk? -> true true true }T
T{ s" 1 walk: wone" bad-walk? -> false }T

\ A corrupted capacity or pending count refuses pushes. A root that cannot
\ be pushed can only mean a corrupted capacity, so walk-run reports invalid
\ without spending fuel, with fuel or without.
-1 w2 walk-capacity !
20 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-fuel @ -> outcome-invalid 20 }T
0 w2 walk-capacity !  0 w2 walk-budget drop
T{ 5 ' fib-visit w2 ' walk-run rs-checked w2 walk-fuel @ -> outcome-invalid 0 }T
8 w2 walk-capacity !
9 w2 walk-pending !
T{ 1 w2 walk-push w2 walk-pending @ -> false 9 }T
0 w2 walk-pending !

\ After exhaustion part way, fuel is 0 and work is left on the stack.
14 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-fuel @ w2 walk-pending @ -> outcome-exhausted 0 1 }T

\ Node 0 has no possible children.
0 w1 walk-node !
T{ 0 w1 walk-child? -1 w1 walk-child? -> false false }T

\ A visitor result outside the vocabulary counts as invalid.
: bad-visit ( walk -- outcome ) drop 7 ;
100 w2 walk-budget drop
T{ 3 ' bad-visit w2 walk-run -> outcome-invalid }T

\ The pushing helpers keep the return stack balanced.
0 w1 walk-pending !
3 w1 walk-node !
T{ 0 1 w1 ' walk-children rs-checked 0 1 w1 ' walk-push2 rs-checked -> outcome-ok outcome-ok }T

\ walk-visit reads the current node of a node store and dispatches on it.
: show-node ( first second walk tag -- outcome ) nip + + ;
T{ 2 /node 0 store: s3 -> }T
4 5 6 s3 node-new 2drop
0 w1 walk-node !
T{ w1 s3 ' show-node walk-visit -> 15 }T
1 w1 walk-node !
T{ w1 s3 ' show-node walk-visit -> outcome-invalid }T
\ Paired walks: each item is a node and a context cell, popped together.
T{ 3 walk2: p1 -> }T
T{ p1 walk-capacity @ p1 walk-width @ w1 walk-width @ p1 walk-pending @ -> 6 2 1 0 }T
T{ 10 100 p1 walk-push-pair 11 101 p1 walk-push-pair 12 102 p1 walk-push-pair -> true true true }T
T{ 13 103 p1 walk-push-pair p1 walk-pending @ -> false 6 }T
T{ p1 walk-pop-pair -> 12 102 }T
T{ p1 walk-take p1 walk-node @ p1 walk-context @ p1 walk-pending @ -> 11 101 2 }T
T{ 2 p1 walk-room-for? 4 p1 walk-room-for? 5 p1 walk-room-for? -> true true false }T
-1 p1 walk-pending !
T{ 1 2 p1 walk-push-pair p1 walk-pending @ -> false -1 }T
5 p1 walk-pending !
T{ 1 2 p1 walk-push-pair -> false }T

\ walk-children-at pushes the first child with the current context and the
\ second with the given one, so the second is visited first.
0 p1 walk-pending ! 7 p1 walk-context !
T{ 1 2 9 p1 walk-children-at p1 walk-pop-pair p1 walk-pop-pair -> outcome-ok 2 9 1 7 }T
4 p1 walk-pending !
T{ 1 2 9 p1 walk-children-at p1 walk-pending @ -> outcome-full 6 }T
T{ 1 2 9 p1 walk-children-at p1 walk-pending @ -> outcome-full 6 }T
T{ 1 2 p1 walk-pair-outcome p1 walk-pending @ -> outcome-full 6 }T
0 p1 walk-pending !
T{ 1 2 3 p1 ' walk-children-at rs-checked 4 5 p1 ' walk-pair-outcome rs-checked -> outcome-ok outcome-ok }T

\ walk-run-pair over the DAG above, where the second child (n-2) sits one
\ level deeper: 15 visits, and the deepest context is two below the root.
variable deepest
: depth-visit ( walk -- outcome )
  dup walk-context @ deepest @ max deepest !
  dup walk-node @ dup 2 < if 2drop outcome-ok exit then
  dup 1- swap 2 - rot dup walk-context @ 1+ swap walk-children-at ;
T{ 8 walk2: p2 -> }T
0 deepest ! 100 p2 walk-budget drop
T{ 5 10 ' depth-visit p2 walk-run-pair p2 walk-fuel @ deepest @ -> outcome-ok 85 12 }T
14 p2 walk-budget drop
T{ 5 10 ' depth-visit p2 walk-run-pair -> outcome-exhausted }T
T{ 2 walk2: p3 -> }T
100 p3 walk-budget drop
T{ 5 0 ' depth-visit p3 walk-run-pair -> outcome-full }T
\ As above, the last unit of fuel spent and no room for a child is full.
T{ 1 walk2: p4 -> }T
1 p4 walk-budget drop
T{ 5 0 ' depth-visit p4 walk-run-pair p4 walk-fuel @ -> outcome-full 0 }T
\ A corrupted capacity (-1, or one cell: less than an item) is invalid.
-1 p3 walk-capacity !
20 p3 walk-budget drop
T{ 5 0 ' depth-visit p3 walk-run-pair p3 walk-fuel @ -> outcome-invalid 20 }T
1 p3 walk-capacity !
T{ 5 0 ' depth-visit p3 ' walk-run-pair rs-checked p3 walk-fuel @ -> outcome-invalid 20 }T
\ walk-context? (reuse-out-2): a paired walk's context cell, 0 for a walk
\ that is not paired.
T{ 7 p4 walk-context ! p4 walk-context? 7 pz walk-context ! pz walk-context? -> 7 7 }T
T{ 2 walk: s9 -> }T
T{ 7 s9 walk-context ! s9 walk-context? s9 ' walk-context? rs-checked -> 0 0 }T
\ walk-children-unless (reuse-out-2): earlier children only, each pushed
\ unless the test says it needs no visit (here: odd ones), first then
\ second; a later child is invalid, a push without room full.
: odd-node? ( index -- flag ) 1 and 0<> ;
: s9-reset ( -- ) 10 s9 walk-node ! 0 s9 walk-pending ! ;
T{ s9-reset 3 4 s9 ' odd-node? walk-children-unless s9 walk-pending @ s9 walk-pop -> outcome-ok 1 4 }T
T{ s9-reset 4 6 s9 ' odd-node? walk-children-unless s9 walk-pop s9 walk-pop -> outcome-ok 6 4 }T
T{ s9-reset 3 5 s9 ' odd-node? walk-children-unless s9 walk-pending @ -> outcome-ok 0 }T
T{ s9-reset 12 4 s9 ' odd-node? walk-children-unless s9 walk-pending @ -> outcome-invalid 0 }T
T{ s9-reset 4 s9 walk-push drop 6 8 s9 ' odd-node? walk-children-unless -> outcome-full }T
T{ s9-reset 4 s9 walk-push drop 5 s9 walk-push drop 6 8 s9 ' odd-node? walk-children-unless
   s9 walk-pending @ -> outcome-full 2 }T
T{ s9-reset 3 4 s9 ' odd-node? ' walk-children-unless rs-checked -> outcome-ok }T
T{ s" 0 walk2: pbad0" bad-walk? s" -1 walk2: pbad1" bad-walk? s" 1 walk2: pone" bad-walk? -> true true false }T

\ Growable walks (plan task 6.2.0): a push past the record's room moves the
\ stack to the heap, keeping its items in order; a growth the heap refuses
\ is full and changes nothing; walk-free gives the block back and returns
\ to the first room, empty. A walk not made growable stays full at its
\ capacity (above).
2 walk: gw  gw walk-growable
: gw-push5 ( -- ) 6 1 do i gw walk-push drop loop ;
T{ gw-push5 gw walk-pending @ gw walk-capacity @ 4 > gw walk-heap @ 0<> -> 5 true true }T
T{ gw walk-pop gw walk-pop gw walk-pop gw walk-pop gw walk-pop -> 5 4 3 2 1 }T
: gw-fill ( -- ) begin gw walk-pending @ gw walk-capacity @ < while 7 gw walk-push drop repeat ;
gw-fill  1 heap-refusals !
T{ 9 gw walk-push gw walk-pending @ gw walk-capacity @ = heap-refusals @ -> false true 0 }T
T{ gw walk-pop -> 7 }T
T{ gw walk-free gw walk-pending @ gw walk-capacity @ gw walk-heap @ -> 0 2 0 }T
T{ 3 gw walk-push 4 gw walk-push gw walk-heap @ gw walk-pending @ -> true true 0 2 }T
gw walk-free

\ Frame records: passes on an explicit, growable stack (plan task 6.2.0).
\ The test visitor rebuilds the DAG above (node n >= 2 has children n-1
\ and n-2) bottom-up: its result is the number of leaves below n, and the
\ second child is visited one context level deeper. A visit of node n is
\ n frames deep, so node 5 is 5 frames deep. Each step is a word ( ...
\ frames -- ... frames next ); n is kept across the first child's visit,
\ the first count across the second's.
variable deepest-frame  variable deepest-context
: note-depth ( frames -- )
  dup frame-depth @ deepest-frame @ max deepest-frame !
  frame-context @ deepest-context @ max deepest-context ! ;
: leaves-sum ( b outcome frames -- n outcome frames 0 )
  >r r@ frame-restore over ok? if rot + swap else drop then r> 0 ;
: leaves-second ( a outcome frames -- n-2 frames next | -1 outcome frames 0 )
  >r dup ok? 0= if r@ frame-restore drop r> 0 exit then drop
  r@ frame-restore 2 - swap r@ frame-save r> ['] leaves-sum frame-under ;
: leaves-visit ( n frames -- n-1 frames next | 1 outcome frames 0 )
  dup note-depth over 2 < if nip 1 outcome-ok rot 0 exit then
  2dup frame-save swap 1- swap ['] leaves-second frame-call ;
T{ ' leaves-visit frames: f1 -> }T
T{ f1 frame-depth @ f1 frame-fuel @ f1 frame-context @ f1 frame-job @ -> 0 0 0 0 }T
T{ f1 frame-visitor @ f1 frame-block @ f1 frame-used @ f1 frame-capacity @ ->
  ' leaves-visit 0 0 0 }T
T{ -1 f1 frame-budget f1 frame-fuel @ -> false 0 }T
T{ 7 f1 frame-budget f1 frame-fuel @ -> true 7 }T
: leaves-run ( n context fuel -- result outcome )
  f1 frame-budget drop 0 deepest-frame ! 0 deepest-context ! f1 frame-run ;
\ Node 5: 15 visits, 8 leaves, 5 frames deep, context 2 above the root's;
\ the stack empty again and the context the root's.
T{ 5 10 100 leaves-run f1 frame-fuel @ f1 frame-depth @ f1 frame-used @ -> 8 outcome-ok 85 0 0 }T
T{ deepest-frame @ deepest-context @ f1 frame-context @ -> 5 12 10 }T
T{ 5 0 15 leaves-run f1 frame-fuel @ -> 8 outcome-ok 0 }T
\ One unit of fuel short is exhausted: no result, nothing in progress.
T{ 5 0 14 leaves-run f1 frame-fuel @ f1 frame-depth @ f1 frame-used @ f1 frame-context @ ->
  -1 outcome-exhausted 0 0 0 0 }T
T{ 4 0 100 leaves-run f1 frame-fuel @ -> 5 outcome-ok 91 }T
\ No depth limit: node 25 is 25 frames deep, 242785 visits; neither host
\ stack holds more for it than for node 2.
242785 f1 frame-budget drop
T{ 25 0 f1 ' frame-run rs-checked f1 frame-fuel @ -> 121393 outcome-ok 0 }T
T{ deepest-frame @ -> 25 }T
\ No fuel or a corrupted negative fuel is exhausted, spending nothing.
T{ 3 0 0 leaves-run f1 frame-fuel @ -> -1 outcome-exhausted 0 }T
-5 f1 frame-fuel !
T{ 3 0 f1 frame-run f1 frame-fuel @ f1 frame-depth @ -> -1 outcome-exhausted -5 0 }T
\ frame-admit: why a visit would not open: an unsound stack first, then
\ the fuel, then the room. A stack the heap cannot grow is full.
: admit-of ( fuel used -- outcome ) f1 frame-used ! f1 frame-fuel ! f1 frame-admit 0 f1 frame-used ! ;
T{ 1 0 admit-of 0 0 admit-of -1 0 admit-of -> 0 2 2 }T
T{ 1 -1 admit-of 1 f1 frame-capacity @ 1+ admit-of 0 -1 admit-of -> 1 1 1 }T
f1 frame-free  1 heap-refusals !
T{ 1 0 admit-of f1 frame-capacity @ -> 6 0 }T
1 heap-refusals !
T{ 0 0 admit-of heap-refusals @ -> 2 1 }T
0 heap-refusals !
T{ 1 0 admit-of f1 frame-capacity @ frame-need < -> 0 false }T
\ A growth the heap refuses ends the pass full, at any depth: no result,
\ nothing in progress, the stack and context as before.
f1 frame-free  5 0 100 leaves-run 2drop
T{ f1 frame-capacity @ -> 32 }T
1 heap-refusals !
T{ 25 0 1000 leaves-run f1 frame-depth @ f1 frame-used @ f1 frame-context @ ->
  -1 outcome-full 0 0 0 }T
T{ heap-refusals @ f1 frame-capacity @ -> 0 32 }T
100 f1 frame-budget drop
T{ 5 0 f1 ' frame-run rs-checked -> 8 outcome-ok }T
\ The failure paths keep both stacks balanced. A context that cannot grow
\ refuses the deeper visit and stays unchanged, spending nothing; the
\ continuation then runs with no result.
: refused ( x frames cont -- -1 outcome cont ) frame-under nip ;
0 f1 frame-budget drop
T{ 3 f1 ' frame-return ' frame-call rs-checked nip -> -1 outcome-exhausted ' frame-return }T
100 f1 frame-budget drop  max-n f1 frame-context !
T{ 3 f1 ' frame-return ' refused rs-checked f1 frame-context @ f1 frame-fuel @ ->
  -1 outcome-full ' frame-return max-n 100 }T
\ frame-open-or (ROUT3): frame-open when the record admits the visit; else
\ the refusal xt on ( x frames cont outcome ), the record unchanged.
0 f1 frame-context !
: opened-or-not ( x frames cont outcome -- x cont outcome ) rot drop ;
: open-try ( x frames cont -- ... ) ['] frame-left ['] opened-or-not frame-open-or ;
T{ 3 f1 ' frame-return open-try nip f1 frame-depth @ -> 3 ' frame-left 1 }T
f1 frame-reset  0 f1 frame-budget drop
T{ 3 f1 ' frame-return ' open-try rs-checked f1 frame-depth @ -> 3 ' frame-return outcome-exhausted 0 }T
f1 frame-reset  100 f1 frame-budget drop  max-n f1 frame-context !
\ frame-under checks the fuel before the context (ADR 0008): with no fuel
\ left, a context at max-n is exhausted, as any other context is.
0 f1 frame-budget drop
T{ 3 f1 ' frame-return refused f1 frame-context @ f1 frame-fuel @ ->
  -1 outcome-exhausted ' frame-return max-n 0 }T
max-n 1- f1 frame-context !
T{ 3 f1 ' frame-return refused f1 frame-context @ ->
  -1 outcome-exhausted ' frame-return max-n 1- }T
\ With fuel, an unsound stack is invalid before the context is examined.
100 f1 frame-budget drop  -1 f1 frame-used !  max-n f1 frame-context !
T{ 3 f1 ' frame-return refused f1 frame-context @ ->
  -1 outcome-invalid ' frame-return max-n }T
0 f1 frame-used !  0 f1 frame-context !
\ A visitor result outside the outcome vocabulary counts as invalid.
: odd-visit ( n frames -- result outcome frames 0 ) 7 swap 0 ;
' odd-visit f1 frame-visitor !
T{ 2 0 f1 frame-run f1 frame-depth @ -> 2 outcome-invalid 0 }T

\ A busy record refuses a new budget and a new pass, changing nothing. A
\ visitor that restarts the pass on its own record gets no result and
\ invalid, and the pass in progress goes on unharmed.
create inner 2 cells allot  variable inner-budget
: restart-pass ( frames -- )
  >r 0 99 r@ frame-run inner 2! 5 r> frame-budget inner-budget ! ;
: restart-visit ( n frames -- ... frames next ) dup restart-pass leaves-visit ;
' restart-visit f1 frame-visitor !  100 f1 frame-budget drop
T{ 3 7 f1 frame-run f1 frame-fuel @ f1 frame-context @ f1 frame-depth @ ->
  3 outcome-ok 95 7 0 }T
T{ inner 2@ inner-budget @ f1 frame-visitor @ ->
  -1 outcome-invalid false ' restart-visit }T
\ A depth left behind by a THROW, or a corrupted one, keeps the record busy
\ until frame-reset, which also empties the stack.
' leaves-visit f1 frame-visitor !  1 f1 frame-depth !  3 f1 frame-used !
T{ f1 frame-busy? 5 f1 frame-budget 3 0 f1 frame-run f1 frame-fuel @ ->
  true false -1 outcome-invalid 95 }T
T{ 9 f1 frame-start f1 frame-context @ 3 0 f1 ' frame-run rs-checked ->
  false 7 -1 outcome-invalid }T
f1 frame-reset
T{ f1 frame-busy? f1 frame-used @ 3 9 f1 frame-run f1 frame-context @ ->
  false 0 3 outcome-ok 9 }T
-1 f1 frame-depth !
T{ f1 frame-busy? 3 0 f1 frame-run -> true -1 outcome-invalid }T
f1 frame-reset

\ A step may run a loop of its own on the same record (frame-loop from the
\ cells then in use): here a visit of n first counts the leaves below n-1
\ on an inner loop, then returns that count plus one.
: loop-visit ( n frames -- count outcome frames 0 )
  ['] leaves-visit over frame-visitor !
  >r 1- 0 max r@ ['] frame-return r@ frame-used @ >r frame-call r> frame-loop drop
  dup ok? if swap 1+ swap then r> 0 ;
' loop-visit f1 frame-visitor !  100 f1 frame-budget drop
T{ 6 0 f1 ' frame-run rs-checked f1 frame-fuel @ f1 frame-used @ -> 9 outcome-ok 84 0 }T
' leaves-visit f1 frame-visitor !

\ The stack words: frame-pick reads a cell by position (0 the last
\ saved), frame-drop drops n, frame-room@ gives the cells in use and the
\ capacity.
T{ 1 f1 frame-save 2 f1 frame-save 3 f1 frame-save 0 f1 frame-pick 2 f1 frame-pick
   f1 frame-room@ drop -> 3 1 3 }T
T{ 2 f1 frame-drop f1 frame-restore f1 frame-used @ -> 1 0 }T
\ A save the block cannot hold (a step that broke the spare-cell rule, or
\ an unsound count) throws frame-overrun and writes nothing.
: save-caught ( used -- ior used' )
  f1 frame-used ! 7 f1 ['] frame-save catch dup if nip nip then f1 frame-used @ ;
T{ f1 frame-capacity @ save-caught f1 frame-capacity @ = -> frame-overrun true }T
T{ -1 save-caught -> frame-overrun -1 }T
T{ f1 frame-capacity @ 1- save-caught f1 frame-capacity @ = -> 0 true }T
0 f1 frame-used !
\ frame-open opens a visit of another kind, whose results need not be an
\ outcome (frame-left keeps them), on fuel and room the caller found;
\ frame-steps runs a step to its return, frame-through a visit.
: kind-visit ( a frames -- a+1 99 frames 0 ) >r 1+ 99 r> 0 ;
: opened-step ( a frames -- a frames next ) ['] frame-return ['] kind-visit frame-open ;
100 f1 frame-budget drop
T{ 5 f1 ' opened-step frame-steps drop f1 frame-fuel @ f1 frame-depth @ f1 frame-used @
   -> 6 99 99 0 0 }T
: opened-call ( a frames cont -- a frames next ) ['] kind-visit frame-open ;
T{ 5 f1 ' opened-call frame-through drop f1 frame-fuel @ -> 6 99 98 }T
T{ 4 f1 ' frame-call frame-through drop f1 frame-fuel @ -> 5 outcome-ok 89 }T
\ The room a visit may use: frame-spare cells above its admission's own,
\ in all its steps together, also when a child is refused (the review's
\ case: a visit that saved frame-spare cells may not save more after a
\ refusal). A chain of visits, each holding frame-spare cells across its
\ child, stays inside the block at every depth.
variable spare-bad
: spare-save ( frames -- )
  frame-spare 0 do i over frame-save loop frame-sound? 0= if 1 spare-bad +! then ;
: spare-back ( r outcome frames -- r outcome frames 0 )
  frame-spare 0 do dup frame-restore drop loop 0 ;
: spare-visit ( n frames -- ... frames next )
  over 0= if nip 0 outcome-ok rot 0 exit then
  dup spare-save swap 1- swap ['] spare-back frame-call ;
' spare-visit f1 frame-visitor !  f1 frame-free  1000 f1 frame-budget drop  0 spare-bad !
T{ 50 0 f1 frame-run f1 frame-used @ spare-bad @ -> 0 outcome-ok 0 0 }T
10 f1 frame-budget drop
T{ 50 0 f1 frame-run f1 frame-used @ spare-bad @ -> -1 outcome-exhausted 0 0 }T
' leaves-visit f1 frame-visitor !

\ frame-init sets up a record inside a larger one, whose address the
\ visitor finds in frame-job; frame-free gives its stack back.
begin-structure /tjob
  field: tjob-scale
  /frames +field tjob-frames
end-structure
create tj /tjob allot
: scaled-visit ( n frames -- result outcome frames 0 )
  dup >r frame-job @ tjob-scale @ * outcome-ok r> 0 ;
T{ ' scaled-visit tj tjob-frames frame-init -> }T
tj tj tjob-frames frame-job !  6 tj tjob-scale !
T{ tj tjob-frames frame-visitor @ -> ' scaled-visit }T
T{ 9 tj tjob-frames frame-budget 7 0 tj tjob-frames frame-run
  tj tjob-frames frame-fuel @ -> true 42 outcome-ok 8 }T
live-blocks @ constant blocks-held
T{ tj tjob-frames dup frame-free frame-block @ live-blocks @ -> 0 blocks-held 1- }T
f1 frame-free

\ Packed 32-bit fields (src/lib/u32.fs). Both versions run on every host:
\ u32@ and u32! (Gforth's l@ and l! here) and the Forth-2012 u32-bytes@
\ and u32-bytes!. The tests compare values only, never bytes, so they hold
\ for either byte order; a field is read only by the version that wrote it.
\ The module is loaded under HEX: its numbers must not depend on BASE (the
\ load-time check would then fail and silently choose the slower version),
\ and it must leave BASE as it found it. Gforth's l@ and l! pass the check.
hex require ../../src/lib/u32.fs base @ decimal constant u32-base
T{ u32-base u32-native -> 16 true }T
T{ 0 u32s 1 u32s 3 u32s -> 0 4 chars 12 chars }T
T{ u32-mask 1+ $10000 dup * = u32-mask 0= -> true false }T
create packed 3 u32s allot
: field1 ( -- addr ) packed 1 u32s + ;
: via-host ( u -- u' ) field1 u32! field1 u32@ ;
: via-bytes ( u -- u' ) field1 u32-bytes! field1 u32-bytes@ ;
: u32-top ( -- u ) 1 31 lshift ;
T{ 0 via-host 1 via-host 255 via-host 256 via-host -> 0 1 255 256 }T
T{ u32-top via-host u32-top 1- via-host u32-mask via-host -> u32-top u32-top 1- u32-mask }T
T{ 0 via-bytes 1 via-bytes 255 via-bytes 256 via-bytes -> 0 1 255 256 }T
T{ u32-top via-bytes u32-top 1- via-bytes u32-mask via-bytes -> u32-top u32-top 1- u32-mask }T
\ Only the low 32 bits are kept (on a 32-bit host u32-mask 1+ is 0).
T{ u32-mask 1+ 5 + via-host u32-mask 1+ 5 + via-bytes -> 5 5 }T
T{ -1 via-host -1 via-bytes -> u32-mask u32-mask }T
\ The load-time check: Gforth's l@ and l! and the Forth-2012 version are
\ unsigned 32-bit access; a fetch that sign-extends bit 31, or a store of
\ a whole 64-bit cell, is not (on a 32-bit host both are 32-bit access).
: sign-extended@ ( addr -- n ) l@ dup u32-top and if u32-mask invert or then ;
T{ ' l@ ' l! u32-sound? ' u32-bytes@ ' u32-bytes! u32-sound? -> true true }T
T{ ' sign-extended@ ' l! u32-sound? ' @ ' ! u32-sound? -> 1 cells 4 = 1 cells 4 = }T
\ A store changes only its own field: the fields around it keep their
\ values, for each version and for random values.
: sentinels ( xt -- ) >r $A5A5 packed r@ execute $5A5A packed 2 u32s + r> execute ;
: around ( xt -- u0 u2 ) >r packed r@ execute packed 2 u32s + r> execute ;
: fenced-host ( u -- u' u0 u2 ) ['] u32! sentinels via-host ['] u32@ around ;
: fenced-bytes ( u -- u' u0 u2 ) ['] u32-bytes! sentinels via-bytes ['] u32-bytes@ around ;
variable u32-seed  20261102 u32-seed !
: u32-rnd ( -- u ) u32-seed @ 1103515245 * 12345 + u32-mask and dup u32-seed ! ;
: u32-random? ( xt -- flag )
  true 1000 0 do over u32-rnd tuck swap execute $5A5A = swap $A5A5 = and
    -rot = and and loop nip ;
T{ u32-mask fenced-host u32-mask fenced-bytes -> u32-mask $A5A5 $5A5A u32-mask $A5A5 $5A5A }T
T{ ' fenced-host u32-random? ' fenced-bytes u32-random? -> true true }T
T{ u32-mask ' via-host rs-checked u32-mask ' via-bytes rs-checked -> u32-mask u32-mask }T
\ The file-format words: one field as four bytes, least significant first,
\ and the block versions, which copy whole where the host stores fields that
\ way (u32-block?) and agree with the field-by-field ones on every host.
create le-src 8 u32s allot   create le-a 32 chars allot   create le-b 32 chars allot
create le-back 8 u32s allot
: le-fill ( -- ) 8 0 do i 16777619 * $9E3779B9 xor u32-mask and le-src i u32s + u32! loop ;
le-fill
T{ $04030201 le-a u32-le! le-a c@ le-a 1 chars + c@ le-a 2 chars + c@ le-a 3 chars + c@
   -> 1 2 3 4 }T
T{ le-a u32-le@ -> $04030201 }T
T{ $FFFFFFFF le-a u32-le! le-a u32-le@ -> u32-mask }T
T{ le-src le-a 8 u32s>le  le-src le-b 8 u32s>le-fields  le-a 32 le-b 32 compare -> 0 }T
T{ le-a le-back 8 le>u32s  le-back 8 u32s le-src 8 u32s compare -> 0 }T
T{ le-b le-back 8 le>u32s-fields  le-back 8 u32s le-src 8 u32s compare -> 0 }T
T{ le-src u32@ le-a u32-le@ = -> true }T
T{ le-src le-a 0 u32s>le  le-a le-back 0 le>u32s -> }T

\ Tables of execution tokens (src/lib/xt-table.fs): every entry the default
\ until set; the default for any other index, negative or too large; a
\ write outside the table and a bad size abort, changing nothing.
require ../../src/lib/xt-table.fs
: xt-one ( -- n ) 1 ;   : xt-three ( -- n ) 3 ;   : xt-other ( -- n ) -1 ;
4 ' xt-other xt-table: xt-by-tag
' xt-one 1 xt-by-tag xt-table!   ' xt-three 3 xt-by-tag xt-table!
: xt-run ( i -- n ) xt-by-tag xt-table@ execute ;
T{ 0 xt-run 1 xt-run 2 xt-run 3 xt-run -> -1 1 -1 3 }T
T{ 4 xt-run -1 xt-run max-n xt-run max-n negate xt-run -> -1 -1 -1 -1 }T
T{ xt-by-tag xt-table-size @ xt-by-tag xt-table-default @ -> 4 ' xt-other }T
\ A table of one entry, set: the default still answers every other index.
1 ' xt-other xt-table: xt-single   ' xt-one 0 xt-single xt-table!
T{ 0 xt-single xt-table@ 1 xt-single xt-table@ -> ' xt-one ' xt-other }T
: xt-set-fails ( xt i table -- ior ) ['] xt-table! catch dup if nip nip nip then ;
T{ ' xt-one 4 xt-by-tag xt-set-fails ' xt-one -1 xt-by-tag xt-set-fails -> -2 -2 }T
T{ ' xt-one max-n xt-by-tag xt-set-fails -> -2 }T
T{ 4 xt-by-tag xt-table@ 0 xt-by-tag xt-table@ 2 xt-run -> ' xt-other ' xt-other -1 }T
\ ?execute (ROUT3): the xt run, nothing for 0.
T{ 5 ' 1+ ?execute 5 0 ?execute 5 ' 1+ ' ?execute rs-checked -> 6 5 6 }T
: xt-made-fails ( c-addr u -- ior ) ['] evaluate catch dup if nip nip then ;
T{ s" 0 ' xt-one xt-table: xt-none" xt-made-fails [undefined] xt-none -> -2 true }T
T{ s" -1 ' xt-one xt-table: xt-neg" xt-made-fails [undefined] xt-neg -> -2 true }T
T{ s" max-n ' xt-one xt-table: xt-huge" xt-made-fails [undefined] xt-huge -> -2 true }T
\ The record: its size, then the entries after the header.
T{ xt-by-tag /xt-table + 3 cells + @ -> ' xt-three }T

\ Defining lf-u32-portable before the file loads forces the Forth-2012
\ version. The file is loaded again for this, last, under BASE 8, where 8
\ and 9 are not digits: it still reads its numbers in decimal and gives
\ BASE back. (Gforth's warnings about the words it redefines are off.)
[defined] warnings [if] warnings @ false warnings ! [then]
: lf-u32-portable ( -- ) ;
8 base ! include ../../src/lib/u32.fs base @ decimal constant u32-base-forced
[defined] warnings [if] warnings ! [then]
T{ u32-base-forced u32-native -> 8 false }T
T{ -1 field1 u32! field1 u32@ u32-top 1+ field1 u32! field1 u32@ -> u32-mask u32-top 1+ }T
\ With the Forth-2012 words, fields are already little-endian, so the block copy
\ is used; lf-u32-fields forces the field-by-field path. Both give the same bytes.
T{ u32-block? le-src le-b 8 u32s>le  le-a 32 le-b 32 compare -> true 0 }T
[defined] warnings [if] warnings @ false warnings ! [then]
: lf-u32-fields ( -- ) ;
decimal include ../../src/lib/u32.fs   \ a reload on purpose, to get the other path
[defined] warnings [if] warnings ! [then]
T{ u32-block? -> false }T
T{ le-src le-b 8 u32s>le  le-a 32 le-b 32 compare -> 0 }T
T{ le-a le-back 8 le>u32s  le-back 8 u32s le-src 8 u32s compare -> 0 }T
bye
