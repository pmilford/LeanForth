\ Unit tests of src/lib/sort.fs, stable sorting of records in place, in
\ the classes of docs/development/TEST_COVERAGE_REVIEW.md. Results: empty,
\ one, two, sorted, reversed, all equal and duplicate lists on both paths;
\ every list of up to 6 cells over 3 keys and random lists of up to 200,
\ each compared, record for record and comparison for comparison, with a
\ reference insertion sort and a reference bottom-up merge sort (the one of
\ src/kernel/level-normalize.fs); records of 1, 4, a cell, 24 and 100
\ address units against the reference insertion sort; the snapshot's three
\ insertion sorts (src/kernel/env-snapshot.fs, copied) against the library
\ byte for byte; the cut-over; 100,000 records against a counting sort and
\ an insertion sort. Interfaces: the public words and hidden helpers, the
\ orders, the sorter's settings, every refusal, stack effects and the depth
\ an order sees, unbalanced order and key words. Resources: the caller's
\ scratch and a refused allocation (full, nothing changed, nothing held).
\ State: THROWs out of the order, nested sorts, orders that stop deciding
\ (fuel) and inconsistent orders. Loaded under HEX: the module must not
\ depend on BASE. T{ }T checks results and data-stack depth.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/lib/sort.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T

\ ---- The interface (ADR 0010): the public words are found, the helpers
\ are not, until the test opens the private word list.
T{ [defined] /sorter [defined] sorter-init [defined] sorter-cells [defined] sorter-u32s
   -> true true true true }T
T{ [defined] sorter-key! [defined] sorter-buffer! [defined] sorter-short [defined] sort-short
   -> true true true true }T
T{ [defined] sort-records [defined] sort-signed [defined] sort-unsigned -> true true true }T
T{ [defined] sort-after? [defined] sorter-size [defined] sort-chunk [defined] sort-merges
   [defined] sort-unbalanced [defined] sorter-busy -> false false false false false false }T
lf-lib-private order+
T{ sort-short sort-chunk 1 cells / sort-unbalanced -> 32 4 -4131 }T

\ ---- Orders.
max-n negate 1- constant min-n
T{ 1 2 sort-signed 2 1 sort-signed 3 3 sort-signed -> -1 1 0 }T
T{ max-n min-n sort-signed min-n max-n sort-signed -1 0 sort-signed -> 1 -1 -1 }T
T{ -1 1 sort-unsigned 1 -1 sort-unsigned 0 0 sort-unsigned -> 1 -1 0 }T
T{ max-n min-n sort-unsigned min-n -1 sort-unsigned -> -1 -1 }T

\ ---- Test data. A cell list's value is key * 2^20 + id, its position in
\ the input: a stable sort leaves the values increasing.
variable test-seed  2463534242 test-seed !     \ xorshift: 64-bit cells
: rand-below ( n -- u )
  test-seed @ dup 13 lshift xor dup 7 rshift xor dup 17 lshift xor dup test-seed !
  1 rshift swap mod ;
1048576 constant id-span
: keyed ( key id -- x ) swap id-span * + ;
: key-of ( x -- key ) id-span / ;
: id-of ( x -- id ) id-span mod ;
variable compares
: by-key ( x1 x2 -- n ) 1 compares +! key-of swap key-of swap sort-signed ;

100000 constant big-n
big-n cells allocate throw constant data   \ the list the library sorts
big-n cells allocate throw constant copy   \ the reference's copy
big-n cells allocate throw constant want   \ an expected result
live-blocks @ constant blocks-at-start
: blocks ( -- n ) live-blocks @ blocks-at-start - ;
: data@ ( i -- x ) cells data + @ ;
: same-cells? ( addr1 addr2 n -- flag ) cells tuck compare 0= ;
: increasing? ( n -- flag ) true swap 1 max 1 ?do i 1- data@ i data@ < and loop ;
: input>copy ( n -- ) data copy rot cells move ;

\ Comparison logs: the ids of each pair compared, in order.
32768 constant log-room
create lib-log log-room 2* cells allot   variable lib-logged
create ref-log log-room 2* cells allot   variable ref-logged
variable log-at   variable log-count
: log-into ( log count -- ) 0 over ! log-count ! log-at ! ;
: log-slot ( -- addr ) log-count @ @ 2* cells log-at @ + ;
: log-pair ( x1 x2 -- )
  log-count @ @ log-room < if id-of log-slot cell+ ! id-of log-slot ! else 2drop then
  1 log-count @ +! ;
: logged ( x1 x2 -- n ) 2dup log-pair by-key ;
lib-log lib-logged log-into
: logs-same? ( -- flag )
  lib-logged @ ref-logged @ = lib-log lib-logged @ log-room min 2* cells ref-log over compare
  0= and ;

\ The references, over cells with an order ( x1 x2 -- n ): an insertion sort
\ by exchanging neighbours, and src/kernel/level-normalize.fs's bottom-up
\ merge sort (lf-lnorm-merge-sort: runs of one record, a merge through
\ scratch copied back, the right run first only when strictly before).
variable ref-base   variable ref-order   variable ref-short
: ref-at ( i -- addr ) cells ref-base @ + ;
: ref-before? ( j -- flag ) dup 1- ref-at @ swap ref-at @ ref-order @ execute 0> ;
: ref-swap ( j -- ) dup ref-at swap 1- ref-at 2dup @ swap @ rot ! swap ! ;
: ref-sink ( i -- ) begin dup 0> while dup ref-before? while dup ref-swap 1- repeat then drop ;
: ref-insertion ( addr n xt -- ) ref-order ! swap ref-base ! 1 max 1 ?do i ref-sink loop ;
create ref-scratch 2048 cells allot
variable ri  variable rj  variable rk  variable rmid  variable rhi  variable rn  variable rw
: ref-right-first? ( -- flag ) ri @ ref-at @ rj @ ref-at @ ref-order @ execute 0> ;
: ref-put ( cursor -- ) dup @ ref-at @ rk @ cells ref-scratch + ! 1 swap +! 1 rk +! ;
: ref-merge ( lo mid hi -- )
  rhi ! dup rmid ! rj ! dup ri ! dup rk !
  begin ri @ rmid @ < rj @ rhi @ < and while ref-right-first? if rj else ri then ref-put repeat
  begin ri @ rmid @ < while ri ref-put repeat
  begin rj @ rhi @ < while rj ref-put repeat
  dup cells ref-scratch + over ref-at rot rhi @ swap - cells move ;
: ref-run ( lo -- ) dup rw @ + rn @ min over rw @ 2* + rn @ min ref-merge ;
: ref-pass ( -- ) 0 begin dup rn @ < while dup ref-run rw @ 2* + repeat drop ;
: ref-merge-sort ( addr n xt -- )
  ref-order ! rn ! ref-base ! 1 rw ! begin rw @ rn @ < while ref-pass rw @ 2* rw ! repeat ;
: ref-sort ( addr n xt -- ) over ref-short @ > if ref-merge-sort else ref-insertion then ;

\ A trial: the n values at data sorted by the library (sorter s1) and a
\ copy by the reference, both logged; the same values and comparisons.
create s1 /sorter allot   create s2 /sorter allot   create s3 /sorter allot
create s3-guard 8 cells allot   s3-guard 8 cells erase   \ after s3: never written
create s4 /sorter allot   create s5 /sorter allot   create s6 /sorter allot
T{ ' logged s1 sorter-cells -> outcome-ok }T
variable ref-xt   ' logged ref-xt !
variable prime    ' noop prime !     \ run before each side, as a budget's reset
: mode ( short -- ) dup s1 sorter-short ! ref-short ! ;
: library-logged ( n -- outcome )
  prime @ execute lib-log lib-logged log-into data swap s1 sort-records ;
: reference-logged ( n -- ) prime @ execute ref-log ref-logged log-into copy swap ref-xt @ ref-sort ;
: trial ( n -- flag )
  dup input>copy dup reference-logged dup library-logged ok?
  swap data copy rot same-cells? and logs-same? and ;

\ ---- Sorters: settings, refusals and resets.
create spare 64 cells allot
T{ 3 s6 sorter-short ! ' @ s6 sorter-key! spare 10 s6 sorter-buffer! -> }T
T{ 8 ' sort-signed s6 sorter-init -> outcome-ok }T
T{ s6 sorter-size @ s6 sorter-short @ s6 sorter-fetch @ s6 sorter-buffer @ s6 sorter-room @
   s6 sorter-busy @ -> 8 32 0 0 0 0 }T
T{ s6 sorter-order @ ' sort-signed = -> true }T
T{ 0 ' sort-signed s6 sorter-init s6 sorter-size @ data 2 s6 sort-records
   -> outcome-invalid 0 outcome-invalid }T
T{ -8 ' sort-signed s6 sorter-init data 2 s6 sort-records -> outcome-invalid outcome-invalid }T
T{ 8 0 s6 sorter-init data 2 s6 sort-records -> outcome-invalid outcome-invalid }T
T{ 0 s6 sorter-cells 0 s6 sorter-u32s data 2 s6 sort-records
   -> outcome-invalid outcome-invalid outcome-invalid }T
T{ ' sort-signed s6 sorter-cells s6 sorter-size @ s6 sorter-fetch @ ' @ = -> outcome-ok 1 cells true }T
T{ ' sort-signed s6 sorter-u32s s6 sorter-size @ s6 sorter-fetch @ ' u32@ = -> outcome-ok 4 true }T

\ The count: 0 <= n and n records' address units within a cell; a refused
\ sort compares nothing and changes nothing.
: two-down ( -- ) 1 0 keyed data !  0 1 keyed data cell+ ! ;
T{ two-down 0 compares ! data -1 s1 sort-records compares @ 0 data@ key-of
   -> outcome-invalid 0 1 }T
T{ data min-n s1 sort-records compares @ -> outcome-invalid 0 }T
T{ max-n 1 cells / s1 sort-ready? max-n 1 cells / 1+ s1 sort-ready? -1 s1 sort-ready?
   0 s1 sort-ready? -> true false false true }T
T{ max-n s1 sort-ready? data max-n s1 sort-records compares @ -> false outcome-invalid 0 }T
T{ true s1 sorter-busy ! 2 s1 sort-ready? data 2 s1 sort-records 0 data@ key-of
   -> false outcome-invalid 1 }T
false s1 sorter-busy !
\ No record or one: ok, nothing compared.
T{ data 0 s1 sort-records data 1 s1 sort-records compares @ 0 data@ key-of
   -> outcome-ok outcome-ok 0 1 }T
T{ data 2 s1 sort-records compares @ 0 data@ key-of 1 data@ key-of -> outcome-ok 1 0 1 }T

\ ---- Shapes on both paths, each against the references and increasing.
: shape ( n xt -- ) swap 0 ?do i over execute i keyed i cells data + ! loop drop ;
: key-up ( i -- key ) ;
: key-down ( i -- key ) 1000 swap - ;
: key-same ( i -- key ) drop 5 ;
: key-mod3 ( i -- key ) 3 mod ;
: key-pairs ( i -- key ) 2/ 1 and ;
: shaped ( n xt short -- flag ) mode over >r shape r@ trial r> increasing? and ;
create shape-xts ' key-up , ' key-down , ' key-same , ' key-mod3 , ' key-pairs ,
variable shape-bad
: shapes ( n short -- bad )
  0 shape-bad ! 5 0 do 2dup i cells shape-xts + @ swap shaped 0= negate shape-bad +! loop
  2drop shape-bad @ ;
T{ 0 32 shapes 1 32 shapes 2 32 shapes 3 32 shapes 10 32 shapes 32 32 shapes -> 0 0 0 0 0 0 }T
T{ 33 32 shapes 100 32 shapes 1000 32 shapes -> 0 0 0 }T
T{ 2 0 shapes 3 0 shapes 7 0 shapes 64 0 shapes 65 1 shapes 100 max-n shapes -> 0 0 0 0 0 0 }T
\ Comparison counts: a sorted list n - 1 by insertion; a reversed one
\ n(n-1)/2 by insertion, and by merging at most n * ceil(log2 n).
T{ 32 mode 20 ' key-up shape 0 compares ! data 20 s1 sort-records compares @ -> outcome-ok 19 }T
T{ 20 ' key-down shape 0 compares ! data 20 s1 sort-records compares @ -> outcome-ok 190 }T
T{ 1000 ' key-down shape 0 compares ! data 1000 s1 sort-records compares @ 10000 <=
   -> outcome-ok true }T

\ ---- Every list of up to 6 cells over 3 keys, three cut-overs.
: power3 ( n -- 3^n ) 1 swap 0 ?do 3 * loop ;
: digits ( code n -- ) 0 ?do dup 3 mod i keyed i cells data + ! 3 / loop drop ;
: all-lists ( n -- bad ) 0 over power3 0 ?do i 2 pick digits over trial 0= - loop nip ;
: exhaustive ( short -- bad ) mode 0 7 0 do i all-lists + loop ;
T{ 32 exhaustive 0 exhaustive 3 exhaustive -> 0 0 0 }T

\ ---- Random lists of up to 200 cells with 1 to n+1 keys.
: random-list ( n keys -- ) swap 0 ?do dup rand-below i keyed i cells data + ! loop drop ;
: random-trial ( -- flag )
  201 rand-below dup dup 1+ rand-below 1+ random-list dup trial swap increasing? and ;
: random-trials ( count -- bad ) 0 swap 0 ?do random-trial 0= - loop ;
T{ 32 mode 300 random-trials 0 mode 300 random-trials 9 mode 300 random-trials -> 0 0 0 }T
T{ max-n mode 100 random-trials -> 0 }T
32 mode
\ Merged lists equal the insertion sort's result, equal keys and all.
: against-insertion ( n -- flag )
  0 s1 sorter-short ! dup 3 random-list dup input>copy copy over ['] by-key ref-insertion
  data over s1 sort-records ok? swap data copy rot same-cells? and 32 s1 sorter-short ! ;
T{ 100 against-insertion 1000 against-insertion 2000 against-insertion -> true true true }T

\ ---- Records of other sizes, against the reference insertion sort run on
\ their positions: 1 address unit (the key the high four bits), a packed
\ 32-bit field and a cell (the key above bit 16), 24 address units (the
\ key the first cell) and 100 (the first cell through sorter-key!). The
\ other bytes are random; equal keys keep their order byte for byte.
100 100 * constant recs-room
create rec-list recs-room allot   create recs0 recs-room allot   create recs-want recs-room allot
create idx 128 cells allot
variable rsize   variable key-reader   variable key-writer
: bytes ( n -- u ) rsize @ * ;
: rec0 ( i -- addr ) bytes recs0 + ;
: by-index ( i1 i2 -- n ) swap rec0 key-reader @ execute swap rec0 key-reader @ execute sort-signed ;
: index-list ( n -- ) 0 ?do i i cells idx + ! loop ;
: want-records ( n -- ) 0 ?do i cells idx + @ rec0 i bytes recs-want + rsize @ move loop ;
: reference-records ( n -- ) dup index-list idx over ['] by-index ref-insertion want-records ;
: records-trial ( n sorter -- flag )
  over reference-records recs0 rec-list 3 pick bytes move
  rec-list 2 pick rot sort-records ok? swap bytes >r rec-list r@ recs-want r> compare 0= and ;
: random-bytes ( n -- ) bytes 0 ?do 256 rand-below recs0 i + c! loop ;
: keyed-records ( n keys -- ) swap 0 ?do dup rand-below i rec0 key-writer @ execute loop drop ;
: random-records ( n -- ) dup random-bytes dup 1+ rand-below 1+ keyed-records ;
: record-trials ( sorter count -- bad )
  0 swap 0 ?do 101 rand-below dup random-records 2 pick records-trial 0= - loop nip ;
: shorts ( sorter -- bad )
  0 32 2 pick sorter-short ! over 60 record-trials + 0 2 pick sorter-short ! over 60 record-trials +
  5 2 pick sorter-short ! over 60 record-trials + nip ;
\ 1 address unit.
: key-1 ( addr -- key ) c@ 4 rshift ;
: put-1 ( key addr -- ) dup c@ 15 and rot 15 and 4 lshift or swap c! ;
: order-1 ( addr1 addr2 -- n ) key-1 swap key-1 swap sort-signed ;
: size-1 ( -- ) 1 rsize ! ['] key-1 key-reader ! ['] put-1 key-writer ! ;
T{ size-1 1 ' order-1 s3 sorter-init s3 shorts -> outcome-ok 0 }T
\ A packed 32-bit field: sorter-u32s, and an order of keys through sorter-key!.
: key-4 ( addr -- key ) u32@ 65536 / ;
: put-4 ( key addr -- ) swap 65536 * 65536 rand-below + swap u32! ;
: order-high ( x1 x2 -- n ) 65536 / swap 65536 / swap sort-signed ;
: size-4 ( -- ) 1 u32s rsize ! ['] key-4 key-reader ! ['] put-4 key-writer ! ;
T{ size-4 ' order-high s3 sorter-u32s s3 shorts -> outcome-ok 0 }T
T{ 4 ' sort-signed s3 sorter-init ' key-4 s3 sorter-key! s3 shorts -> outcome-ok 0 }T
\ A cell.
: key-cell ( addr -- key ) @ 65536 / ;
: put-cell ( key addr -- ) swap 65536 * 65536 rand-below + swap ! ;
: size-cell ( -- ) 1 cells rsize ! ['] key-cell key-reader ! ['] put-cell key-writer ! ;
T{ size-cell ' order-high s3 sorter-cells s3 shorts -> outcome-ok 0 }T
\ 24 and 100 address units; 100 is above the temp (rotated in parts) and
\ not a whole number of cells. The words after s3 are never written.
: order-first ( addr1 addr2 -- n ) @ swap @ swap sort-signed ;
: size-wide ( u -- ) rsize ! ['] @ key-reader ! ['] ! key-writer ! ;
T{ 24 size-wide 24 ' order-first s3 sorter-init s3 shorts -> outcome-ok 0 }T
T{ 100 size-wide 100 ' sort-signed s3 sorter-init ' @ s3 sorter-key! s3 shorts -> outcome-ok 0 }T
T{ s3-guard 8 cells-zero? 100 sort-chunk > -> true true }T

\ ---- The snapshot's insertion sorts, copied from src/kernel/env-snapshot.fs
\ (look-sort: 8-byte (key, answer) pairs by key; dep-sort: 32-bit fields;
\ o-sort: cells by an order), little-endian fields: the library gives the
\ same bytes. Keys from a few values, high bits set, so many are equal.
: u32-swap ( a1 a2 -- ) 2dup u32-le@ swap u32-le@ rot u32-le! swap u32-le! ;
: entry-swap ( addr -- ) dup dup 8 + u32-swap 4 + dup 8 + u32-swap ;
: entry-sink ( addr k -- )
  begin dup while
    2dup 1- 8 * + dup u32-le@ over 8 + u32-le@ u> 0= if drop 2drop exit then
    entry-swap 1-
  repeat 2drop ;
: look-sort ( addr n -- ) 1 max 1 ?do dup i entry-sink loop drop ;
: dep-sort ( addr n -- )
  dup 2 < if 2drop exit then 1 ?do
    dup i 4 * + u32-le@ i
    begin dup 0> if 2 pick over 1- 4 * + u32-le@ 2 pick u> else false then while
      2 pick over 1- 4 * + u32-le@ 3 pick 2 pick 4 * + u32-le! 1-
    repeat 4 * 2 pick + u32-le!
  loop drop ;
: o-order ( a b -- n ) by-key ;
: cell-swap ( addr -- ) dup 2@ swap rot 2! ;
: o-sink ( addr j -- )
  begin dup while
    2dup 1- cells + dup 2@ swap o-order 0> 0= if drop 2drop exit then cell-swap 1-
  repeat 2drop ;
: o-sort ( addr n -- ) 1 max 1 ?do dup i o-sink loop drop ;
create some-keys 0 , 1 , 7 , 2147483648 , 4294967295 , 2147483647 ,
: some-key ( -- u ) 6 rand-below cells some-keys + @ ;
: le-list ( n -- )
  0 ?do some-key i 8 * recs0 + u32-le! 4294967296 rand-below i 8 * 4 + recs0 + u32-le! loop ;
: same-recs? ( u -- flag ) >r rec-list r@ recs-want r> compare 0= ;
: look-trial ( n -- flag )
  dup le-list recs0 rec-list 2 pick 8 * move recs0 recs-want 2 pick 8 * move
  recs-want over look-sort rec-list over s4 sort-records ok? swap 8 * same-recs? and ;
: dep-trial ( n -- flag )
  dup le-list recs0 rec-list 2 pick 4 * move recs0 recs-want 2 pick 4 * move
  recs-want over dep-sort rec-list over s5 sort-records ok? swap 4 * same-recs? and ;
: o-trial ( n -- flag )
  dup 6 random-list dup input>copy copy over o-sort data over s6 sort-records ok?
  swap data copy rot same-cells? and ;
: snapshot-trials ( xt -- bad ) 0 200 0 do 81 rand-below 2 pick execute 0= - loop nip ;
T{ 8 ' sort-unsigned s4 sorter-init ' u32-le@ s4 sorter-key! ' look-trial snapshot-trials
   -> outcome-ok 0 }T
T{ 4 ' sort-unsigned s5 sorter-init ' u32-le@ s5 sorter-key! ' dep-trial snapshot-trials
   -> outcome-ok 0 }T
T{ ' o-order s6 sorter-cells ' o-trial snapshot-trials -> outcome-ok 0 }T
T{ 0 s4 sorter-short ! 0 s5 sorter-short ! 0 s6 sorter-short ! -> }T
T{ ' look-trial snapshot-trials ' dep-trial snapshot-trials ' o-trial snapshot-trials -> 0 0 0 }T

\ ---- The cut-over: up to sorter-short records by insertion, no heap
\ block held; above it one block during the sort (sampled by the order),
\ freed after.
variable most-blocks
: sampled ( x1 x2 -- n ) blocks most-blocks @ max most-blocks ! by-key ;
T{ ' sampled s2 sorter-cells -> outcome-ok }T
: held ( n -- held outcome ) 0 most-blocks ! dup 1 random-list data swap s2 sort-records most-blocks @ swap ;
T{ 31 held 32 held 33 held 34 held blocks -> 0 outcome-ok 0 outcome-ok 1 outcome-ok 1 outcome-ok 0 }T
T{ 5 s2 sorter-short ! 5 held 6 held -> 0 outcome-ok 1 outcome-ok }T
: fresh-trial ( n -- flag ) dup dup random-list trial ;
T{ 31 fresh-trial 32 fresh-trial 33 fresh-trial 34 fresh-trial -> true true true true }T
T{ 0 mode 1 fresh-trial 2 fresh-trial 32 mode -> true true }T

\ ---- 100,000 records: random keys below 1,000 against a counting sort;
\ nearly sorted (each moved at most 8 places) against the insertion sort.
create counts 1000 cells allot
: counting-sort ( -- )
  counts 1000 cells erase
  big-n 0 do i data@ key-of cells counts + 1 swap +! loop
  0 1000 0 do i cells counts + dup @ >r over swap ! r> + loop drop
  big-n 0 do i data@ dup key-of cells counts + dup @ >r 1 swap +! r> cells want + ! loop ;
' by-key s2 sorter-cells drop
T{ big-n 1000 random-list counting-sort 0 compares ! data big-n s2 sort-records -> outcome-ok }T
T{ data want big-n same-cells? big-n increasing? compares @ big-n 17 * <= blocks -> true true true 0 }T
: near-list ( -- )
  big-n 0 do i 10 / i keyed i cells data + ! loop
  20000 0 do big-n 9 - rand-below dup 9 rand-below 1+ + cells data + swap cells data +
    2dup @ swap @ rot ! swap ! loop ;
T{ near-list big-n input>copy copy big-n ' by-key ref-insertion data big-n s2 sort-records
   data copy big-n same-cells? -> outcome-ok true }T

\ ---- The caller's scratch: used when it holds the records (no heap block,
\ even with the heap refusing); else the heap.
' sampled s2 sorter-cells drop  spare 64 cells s2 sorter-buffer!
T{ 1 heap-refusals ! 64 held heap-refusals @ 64 increasing? -> 0 outcome-ok 1 true }T
0 heap-refusals !
T{ 65 held 65 increasing? blocks -> 1 outcome-ok true 0 }T
T{ spare -1 s2 sorter-buffer! 40 held spare 0 s2 sorter-buffer! 40 held -> 1 outcome-ok 1 outcome-ok }T

\ ---- A refused scratch: full, the records unchanged, nothing held, the
\ sorter ready; insertion needs none.
T{ 33 33 random-list 33 input>copy 1 heap-refusals ! data 33 s2 sort-records heap-refusals @
   -> outcome-full 0 }T
T{ data copy 33 same-cells? blocks s2 sorter-busy @ -> true 0 false }T
T{ data 33 s2 sort-records 33 increasing? -> outcome-ok true }T
T{ 32 32 random-list 1 heap-refusals ! data 32 s2 sort-records heap-refusals @ 32 increasing?
   -> outcome-ok 1 true }T
0 heap-refusals !

\ ---- Stack effects. The return stack is balanced and the caller's cells
\ kept; the order is called at one depth, above them and its arguments.
' by-key s2 sorter-cells drop
T{ 7 20 1 random-list data 20 s2 ' sort-records rs-checked -> 7 outcome-ok }T
variable depth-lo   variable depth-hi
: depth-seen ( x1 x2 -- n ) depth dup depth-lo @ min depth-lo ! depth-hi @ max depth-hi ! by-key ;
: depth-trial ( n -- 1 2 3 outcome lo-ok? same? )
  max-n depth-lo ! 0 depth-hi ! dup 3 random-list >r 1 2 3 data r> s4 sort-records
  depth-lo @ 5 > depth-lo @ depth-hi @ = ;
T{ ' depth-seen s4 sorter-cells -> outcome-ok }T
T{ 20 depth-trial -> 1 2 3 outcome-ok true true }T
T{ 50 depth-trial -> 1 2 3 outcome-ok true true }T
\ Results of any size count by their sign; an order may use the return stack.
: order-wide ( x1 x2 -- n ) by-key max-n * ;
: order-rstack ( x1 x2 -- n ) >r >r 1 2 2drop r> r> by-key ;
: like-by-key ( n xt -- flag )
  s4 sorter-cells drop dup 4 random-list dup input>copy
  copy over ['] by-key ref-insertion data over s4 sort-records ok? swap data copy rot same-cells? and ;
T{ 20 ' order-wide like-by-key 90 ' order-wide like-by-key -> true true }T
T{ 20 ' order-rstack like-by-key 90 ' order-rstack like-by-key -> true true }T
\ Order and key words that change the depth: invalid, the records a
\ permutation of the input, nothing held, the sorter ready.
: order-extra ( x1 x2 -- n n ) by-key dup ;
: order-none ( x1 x2 -- ) 2drop ;
: key-extra ( addr -- x x ) @ dup ;
: key-none ( addr -- ) drop ;
create s-full /sorter allot   ' sort-signed s-full sorter-cells drop   \ by the whole value
: permutation? ( n -- flag )
  >r data r@ s-full sort-records drop copy r@ s-full sort-records drop data copy r> same-cells? ;
: unbalanced ( n sorter -- outcome flag )
  over 2 random-list over input>copy data 2 pick rot sort-records swap permutation? ;
T{ ' order-extra s4 sorter-cells drop 20 s4 unbalanced 90 s4 unbalanced blocks
   -> outcome-invalid true outcome-invalid true 0 }T
T{ ' order-none s4 sorter-cells drop 20 s4 unbalanced 90 s4 unbalanced
   -> outcome-invalid true outcome-invalid true }T
T{ 1 cells ' by-key s4 sorter-init drop ' key-extra s4 sorter-key! 20 s4 unbalanced
   90 s4 unbalanced -> outcome-invalid true outcome-invalid true }T
T{ ' key-none s4 sorter-key! 20 s4 unbalanced 90 s4 unbalanced s4 sorter-busy @ blocks
   -> outcome-invalid true outcome-invalid true false 0 }T
T{ ' @ s4 sorter-key! 90 s4 unbalanced -> outcome-ok true }T

\ ---- THROWs out of the order: passed on, the records a permutation of the
\ input, the scratch freed, the sorter ready; sort-unbalanced's own code
\ reads as invalid.
variable throw-after
: order-throws ( x1 x2 -- n ) throw-after @ 0= if 1234 throw then -1 throw-after +! by-key ;
T{ ' order-throws s5 sorter-cells -> outcome-ok }T
: throw-trial ( n k -- code flag )
  throw-after ! dup 2 random-list dup input>copy data over s5 ['] sort-records catch
  >r 2drop drop r> swap permutation? ;
T{ 20 10 throw-trial 90 100 throw-trial 90 200 throw-trial blocks s5 sorter-busy @
   -> 1234 true 1234 true 1234 true 0 false }T
T{ max-n throw-after ! 90 2 random-list data 90 s5 sort-records 90 increasing? -> outcome-ok true }T
: order-own-code ( x1 x2 -- n ) 2drop sort-unbalanced throw ;
T{ ' order-own-code s5 sorter-cells drop data 90 s5 sort-records blocks -> outcome-invalid 0 }T

\ ---- Nested sorts: the sorter in use refuses (invalid), another sorts.
variable inner
: order-nested ( x1 x2 -- n ) copy 3 s5 sort-records inner ! by-key ;
: order-other ( x1 x2 -- n ) copy 3 s2 sort-records inner ! by-key ;
T{ ' order-nested s5 sorter-cells drop 0 inner ! 20 20 random-list 3 input>copy data 20 s5 sort-records
   inner @ 20 increasing? -> outcome-ok outcome-invalid true }T
T{ 90 90 random-list data 90 s5 sort-records inner @ 90 increasing? s5 sorter-busy @
   -> outcome-ok outcome-invalid true false }T
T{ ' order-other s5 sorter-cells drop 90 90 random-list data 90 s5 sort-records inner @
   90 increasing? blocks -> outcome-ok outcome-ok true 0 }T

\ ---- Orders that stop deciding when a budget (fuel) runs out give, call
\ for call, the references' results; orders that decide at random leave a
\ permutation.
variable budget   variable budget-start
: budgeted ( x1 x2 -- n ) 2dup log-pair budget @ 0> if -1 budget +! by-key else 2drop 0 then ;
: refuel ( -- ) budget-start @ budget ! ;
' budgeted s1 sorter-cells drop  ' budgeted ref-xt !  ' refuel prime !
: budget-trials ( short -- bad )
  mode 0 200 0 do 101 rand-below 400 rand-below budget-start ! dup 4 random-list trial 0= - loop ;
T{ 32 budget-trials 0 budget-trials -> 0 0 }T
' logged s1 sorter-cells drop  ' logged ref-xt !  ' noop prime !  32 mode
: order-random ( x1 x2 -- n ) 2drop 3 rand-below 1- ;
: random-orders ( n -- flag ) ['] order-random s4 sorter-cells drop s4 unbalanced nip ;
T{ 20 random-orders 90 random-orders 1000 random-orders blocks -> true true true 0 }T

\ ---- The header's example.
create by-value /sorter allot   create numbers 5 , 3 , 9 , 3 ,
T{ ' sort-signed by-value sorter-cells numbers 4 by-value sort-records -> outcome-ok outcome-ok }T
T{ numbers @ numbers cell+ @ numbers 2 cells + @ numbers 3 cells + @ -> 3 3 5 9 }T
\ Unsigned 32-bit values, bit 31 set.
create fields 6 u32s allot
: u32-at ( i -- addr ) u32s fields + ;
4294967295 0 u32-at u32!  0 1 u32-at u32!  2147483648 2 u32-at u32!  1 3 u32-at u32!
2147483647 4 u32-at u32!  2147483648 5 u32-at u32!
T{ ' sort-unsigned s6 sorter-u32s fields 6 s6 sort-records -> outcome-ok outcome-ok }T
T{ 0 u32-at u32@ 1 u32-at u32@ 2 u32-at u32@ 3 u32-at u32@ 4 u32-at u32@ 5 u32-at u32@
   -> 0 1 2147483647 2147483648 2147483648 4294967295 }T

T{ blocks -> 0 }T
data free copy free want free 2drop drop
bye
