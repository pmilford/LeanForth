\ Unit tests of src/lib/cons.fs and src/lib/pools.fs, hash-consed sets in
\ two tiers: texts and tuples interned to one number, a sealed set refusing
\ changes, a scratch set over a sealed input finding the input's records
\ and numbering its own after them, marks and rollbacks taking table
\ entries out, resets, exact entry checks, a class limit at and one past
\ its bound, tuples out of order, wide items and a tuple of 100,000
\ items, and a randomized model of a class whose hash has only four values
\ (so most records collide), over two tiers with marks, rollbacks and
\ resets. Loaded under HEX.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/pools.fs decimal
lf-lib-private order+

create inp /cons allot   create sc /cons allot   create unsealed /cons allot
create m0 /cons-mark allot   create m1 /cons-mark allot

\ Texts in one set: equal texts, one number; the empty text too.
T{ 2 text-class inp cons-init -> outcome-ok }T
T{ s" Nat" inp text-intern s" Int" inp text-intern s" Nat" inp text-intern -> 0 0 1 0 0 0 }T
T{ s" " inp text-intern s" " inp text-intern inp cons-numbers -> 2 0 2 0 3 }T
T{ 1 inp text@ s" Int" compare 2 inp text@ nip -> 0 0 }T
T{ s" Nat" inp ' text-intern rs-checked -> 0 0 }T
\ Entry checks: exact.
T{ 0 inp cons-entry? 2 inp cons-entry? 3 inp cons-entry? -1 inp cons-entry? -> true true false false }T
\ Sealing makes the set read-only.
T{ inp cons-seal s" Real" inp text-intern inp cons-seal -> outcome-ok -1 outcome-invalid outcome-invalid }T
T{ m0 inp cons-mark inp cons-reset -> outcome-invalid outcome-invalid }T
\ A scratch set needs a sealed set under it.
2 text-class unsealed cons-init drop
T{ 2 unsealed sc cons-extend -> outcome-invalid }T
T{ 2 inp sc cons-extend sc cons-first @ sc cons-numbers -> outcome-ok 3 3 }T
\ It finds the input's texts and numbers its own after them.
T{ s" Int" sc text-intern s" Real" sc text-intern s" Real" sc text-intern -> 1 0 3 0 3 0 }T
T{ 3 sc text@ s" Real" compare 1 sc text@ s" Int" compare -> 0 0 }T
T{ 1 sc cons-entry? 3 sc cons-entry? 4 sc cons-entry? -> true true false }T
T{ inp cons-numbers inp cons-table htab-count -> 3 3 }T
\ Marks: a rollback gives the records back and takes their entries out.
T{ m0 sc cons-mark -> outcome-ok }T
: two-more ( -- ) s" A" sc text-intern 2drop s" B" sc text-intern 2drop ;
two-more
T{ sc cons-numbers sc cons-table htab-count sc cons-bytes slab-count -> 6 3 6 }T
T{ m0 sc cons-rollback sc cons-numbers sc cons-table htab-count sc cons-bytes slab-count -> outcome-ok 4 1 4 }T
T{ s" B" sc text-intern s" A" sc text-intern s" Real" sc text-intern -> 4 0 5 0 3 0 }T
\ Marks of another set, from before a reset; a reset empties the set.
T{ m0 unsealed cons-rollback m0 sc cons-mark sc cons-reset m0 sc cons-rollback -> outcome-invalid outcome-ok outcome-ok outcome-invalid }T
T{ sc cons-numbers sc cons-table htab-count s" Nat" sc text-intern -> 3 0 0 0 }T
sc cons-free unsealed cons-free inp cons-free
\ Two texts with the same FNV-1a hash (1582148253): the comparison, not
\ the hash, tells them apart, in a table of one slot and growing.
create clash /cons allot
T{ 0 text-class clash cons-init s" costarring" hash-bytes s" liquid" hash-bytes = -> outcome-ok true }T
T{ s" costarring" clash text-intern s" liquid" clash text-intern s" costarring" clash text-intern -> 0 0 1 0 0 0 }T
T{ s" liquid" clash text-intern s" declinate" clash text-intern s" macallums" clash text-intern -> 1 0 2 0 3 0 }T
clash cons-free

\ Tuples: built in steps; equal lists, one number.
create tu /cons allot
T{ 4 tuple-class tu cons-init -> outcome-ok }T
T{ 5 tu tuple-add tu tuple-end -> outcome-invalid -1 outcome-invalid }T
T{ tu tuple-start tu tuple-end tu tuple-start tu tuple-end -> outcome-ok 0 0 outcome-ok 0 0 }T
: pair ( a b -- t outcome ) tu tuple-start drop swap tu tuple-add drop tu tuple-add drop tu tuple-end ;
T{ 7 9 pair 7 9 pair 9 7 pair -> 1 0 1 0 4 0 }T
T{ 1 tu tuple-length 0 1 tu tuple-item 1 1 tu tuple-item 0 tu tuple-length -> 2 7 9 0 }T
\ Two lists with the same hash (computed independently): told apart.
T{ 1 tu cons-at tuple-hash 4 tu cons-at tuple-hash = -> false }T
T{ 908 63501 pair 754 79452 pair 908 63501 pair -> 7 0 10 0 7 0 }T
T{ 7 tu cons-at tuple-hash 10 tu cons-at tuple-hash = -> true }T
\ A number inside a tuple is not a tuple.
T{ 1 tu cons-entry? 2 tu cons-entry? 3 tu cons-entry? 4 tu cons-entry? -> true false false true }T
\ Items beyond 32 bits are refused (on a 32-bit host every cell fits).
u32-mask 0> [if]
T{ tu tuple-start u32-mask 1+ tu tuple-add -1 tu tuple-add u32-mask tu tuple-add -> outcome-ok outcome-invalid outcome-invalid outcome-ok }T
T{ tu tuple-end swap 0 swap tu tuple-item -> outcome-ok u32-mask }T
[then]
\ No fixed length: 100,000 items, built twice, one number.
: long ( -- t outcome )
  tu tuple-start drop 100000 0 do i 3 * tu tuple-add drop loop tu tuple-end ;
long drop constant long-t
T{ long long-t tu tuple-length -> long-t 0 100000 }T
T{ long drop 99999 swap tu tuple-item -> 299997 }T
\ Two tiers: the input's tuples are found from a scratch set.
create tu2 /cons allot
T{ tu cons-seal 4 tu tu2 cons-extend 7 9 pair 2drop -> outcome-ok outcome-ok }T
: pair2 ( a b -- t outcome ) tu2 tuple-start drop swap tu2 tuple-add drop tu2 tuple-add drop tu2 tuple-end ;
T{ 7 9 pair2 1 2 pair2 1 2 pair2 -> 1 0 tu cons-numbers 0 tu cons-numbers 0 }T
\ A rollback or reset abandons a tuple being built.
T{ m0 tu2 cons-mark tu2 tuple-start 5 tu2 tuple-add m0 tu2 cons-rollback 6 tu2 tuple-add -> outcome-ok outcome-ok outcome-ok outcome-ok outcome-invalid }T
T{ tu2 tuple-start tu2 cons-reset tu2 tuple-end -> outcome-ok outcome-ok -1 outcome-invalid }T
tu2 cons-free tu cons-free

\ A class limit at and one past its bound: at most 3 texts. The text
\ hooks are the pools' own.
2 u32s 3 cons-class: three-texts
' text-rehash ' text-same ' text-span three-texts cons-hooks!
create small /cons allot
T{ 1 three-texts small cons-init -> outcome-ok }T
T{ s" a" small text-intern s" b" small text-intern s" c" small text-intern -> 0 0 1 0 2 0 }T
T{ s" d" small text-intern s" b" small text-intern -> -1 outcome-full 1 0 }T
T{ small cons-numbers small cons-table htab-count small cons-bytes slab-count -> 3 3 3 }T
small cons-free

\ At most two tiers: a set over a sealed extension is refused (numbers
\ name records one tier down only), and so is a set over an open one.
create low /cons allot   create mid /cons allot   create top3 /cons allot
T{ 2 text-class low cons-init s" a" low text-intern low cons-seal -> 0 0 0 0 }T
T{ 2 low mid cons-extend s" b" mid text-intern mid cons-seal -> 0 1 0 0 }T
T{ low cons-base? mid cons-base? 2 mid top3 cons-extend -> true false outcome-invalid }T
top3 cons-free mid cons-free
\ Sealing freezes the table: finds through an extension change no byte of
\ the sealed set's record or slots, and count themselves in the extension.
create base-copy /cons allot
: low-slots ( -- addr u ) low cons-table htab-block @ low cons-table htab-bytes ;
create slots-copy 64 u32s allot
T{ low cons-table htab-frozen? low-slots nip 64 u32s <= -> true true }T
low base-copy /cons move  low-slots slots-copy swap move
T{ 2 low mid cons-extend s" a" mid text-intern s" a" mid text-intern s" z" mid text-intern -> 0 0 0 0 0 1 0 }T
T{ low base-copy /cons tuck compare low-slots slots-copy over compare mid cons-under-finds @ -> 0 0 3 }T
mid cons-free low cons-free

\ A text from the set's own byte slab: its address is kept as an offset,
\ found again after the slab moves (here moved by hand, the old block
\ overwritten before it is freed).
create own /cons allot
: move-bytes ( cons -- )
  cons-bytes >r r@ slab-bytes allocate drop r@ slab-block @ over r@ slab-bytes move
  r@ slab-block @ r@ slab-bytes [char] # fill r@ slab-block @ free drop
  r@ slab-capacity r@ slab-block! r> drop ;
T{ 2 text-class own cons-init s" abcdefgh" own text-intern -> 0 0 0 }T
T{ 0 own text@ own cons-key! own cons-key-base @ -> 0 }T
T{ own move-bytes own cons-key-fix own cons-key 2@ s" abcdefgh" compare -> 0 }T
T{ s" elsewhere" own cons-key! own cons-key-base @ -> -1 }T
\ Interning a part of an own text, the slab growing meanwhile.
T{ 0 own text@ 4 - own text-intern 1 own text@ s" abcd" compare -> 1 0 0 }T
T{ 0 own text@ own text-intern 1 own text@ own text-intern -> 0 0 1 0 }T
own cons-free

\ Bounds that reach the cell's end, as a 32-bit host reaches them at 2^32:
\ a class whose numbers, times its record size, pass what a cell
\ addresses still makes a set, its slab limit clamped ...
max-n 8 / constant big-unit
big-unit max-n cons-class: huge-class
' text-rehash ' text-same ' text-span huge-class cons-hooks!
create huge /cons allot
T{ 2 huge-class huge cons-init huge cons-records slab-limit -> 0 max-n big-unit / }T
huge cons-free
\ ... and a commit one number before the class's limit (on a 32-bit host
\ max-n, the cell's end), or past it, is full, never a wrapped sum.
1 u32s max-n cons-class: wide-tuples
' tuple-rehash ' tuple-same ' tuple-span wide-tuples cons-hooks!
create wide /cons allot
T{ 2 wide-tuples wide cons-init -> 0 }T
wide cons-limit 1- wide cons-first !
T{ wide tuple-start 5 wide tuple-add wide tuple-end wide cons-numbers -> 0 0 -1 outcome-full wide cons-limit 1- }T
wide cons-limit 2 + wide cons-first !
T{ wide tuple-start wide tuple-end -> 0 -1 outcome-full }T
0 wide cons-first !  wide cons-reset drop
\ A list whose length field is corrupted to 2^32 - 1 is no entry, found at
\ once: its span saturates instead of wrapping.
T{ wide tuple-start 5 wide tuple-add wide tuple-end -> 0 0 0 0 }T
T{ u32-mask 0 wide cons-at u32! 0 wide cons-entry? 0 wide tuple-span -> false u32-mask }T
wide cons-free
\ A rollback whose table misses an entry gives invalid, after rolling back.
create gap /cons allot  create gap-mark /cons-mark allot
T{ 2 text-class gap cons-init gap-mark gap cons-mark s" p" gap text-intern s" q" gap text-intern -> 0 0 0 0 1 0 }T
T{ 1 s" q" hash-bytes gap cons-table htab-remove gap-mark gap cons-rollback gap cons-numbers -> 0 1 0 }T
gap cons-free

\ A class of single 32-bit values whose hash keeps two bits: most records
\ collide in the table. The key is the value, kept in cons-key.
1 u32s cons-numbers-max cons-class: value-class
: value-hash ( u -- h ) 3 and ;
: value-rehash ( n cons -- h ) cons-at u32@ value-hash ;
: value-same ( n key cons -- flag ) rot swap cons-at u32@ swap cons-key @ = ;
: value-span ( local cons -- units ) 2drop 1 ;
' value-rehash ' value-same ' value-span value-class cons-hooks!
\ Intern u: room, the candidate, find (the under set first), keep.
: value-intern ( u cons -- n outcome )
  >r 1 0 r@ cons-room dup ok? 0= if nip r> drop no-result exit then drop
  dup r@ cons-key ! dup r@ cons-top u32! value-hash true r@ cons-find
  if r> drop outcome-ok else 1 swap r> cons-commit then ;

\ The model: an input of 60 values, sealed; then random interns of values
\ 0 .. 119 into a scratch set with four marks, rollbacks and resets. The
\ model keeps the input's number of each value, the scratch values in
\ order (their numbers continue after the input's) and, per mark, the
\ scratch length it marked and whether it lives.
create vin /cons allot   create vsc /cons allot
create input-of 120 cells allot     \ value -> input number, or -1
create scratch-list 4000 cells allot   variable scratch-n
4 constant #vmarks
create vmarks #vmarks /cons-mark * allot
create vmark-at #vmarks cells allot   create vmark-alive #vmarks cells allot
variable v-seed   variable v-bad
: v-rnd ( n -- u ) v-seed @ 1103515245 * 12345 + $7FFFFFFF and dup v-seed ! 7 rshift swap mod ;
: v-bad! ( -- ) 1 v-bad +! ;
: vmark ( k -- mark ) /cons-mark * vmarks + ;
: inp-number ( u -- n ) cells input-of + @ ;
: scratch-index ( u -- i | -1 )
  -1 scratch-n @ 0 ?do over i cells scratch-list + @ = if drop i leave then loop nip ;
: v-expected ( u -- n new? )
  dup inp-number dup 0< 0= if nip false exit then drop
  scratch-index dup 0< if drop vin cons-numbers scratch-n @ + true else vin cons-numbers + false then ;
: v-intern ( -- )
  120 v-rnd dup v-expected >r over vsc value-intern ok? 0= if v-bad! then
  <> if v-bad! then r> if scratch-n @ cells scratch-list + ! 1 scratch-n +! else drop then ;
: v-mark ( -- ) #vmarks v-rnd dup vmark vsc cons-mark ok? 0= if v-bad! then
  scratch-n @ over cells vmark-at + ! true swap cells vmark-alive + ! ;
: v-kill-above ( n -- )
  #vmarks 0 do dup i cells vmark-at + @ < if false i cells vmark-alive + ! then loop drop ;
: v-rollback ( -- )
  #vmarks v-rnd dup vmark vsc cons-rollback ok? over cells vmark-alive + @ <> if v-bad! then
  dup cells vmark-alive + @ if cells vmark-at + @ dup scratch-n ! v-kill-above else drop then ;
: v-reset ( -- ) vsc cons-reset ok? 0= if v-bad! then 0 scratch-n ! vmark-alive #vmarks cells erase ;
: v-check ( -- )
  vsc cons-numbers vin cons-numbers scratch-n @ + <> if v-bad! then
  vsc cons-table htab-count scratch-n @ <> if v-bad! then
  #vmarks 0 do i vmark vsc cons-mark-valid? i cells vmark-alive + @ <> if v-bad! then loop ;
: v-step ( -- )
  20 v-rnd dup 12 < if drop v-intern else dup 15 < if drop v-mark else
  19 < if v-rollback else v-reset then then then v-check ;
: v-input ( -- )
  input-of 120 cells -1 fill 60 0 do 120 v-rnd dup vin value-intern drop swap cells input-of + ! loop ;
: v-run ( seed log2 steps -- bad )
  rot v-seed ! 0 v-bad ! 0 scratch-n ! vmark-alive #vmarks cells erase
  over value-class vin cons-init drop v-input vin cons-seal drop
  swap vin vsc cons-extend drop 0 ?do v-step loop vsc cons-free vin cons-free v-bad @ ;
T{ 1 1 5000 v-run 2 4 5000 v-run 3 0 5000 v-run -> 0 0 0 }T
bye
