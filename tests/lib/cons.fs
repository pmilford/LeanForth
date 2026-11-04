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

\ Tuples: built in steps; equal lists, one number.
create tu /cons allot
T{ 4 tuple-class tu cons-init -> outcome-ok }T
T{ 5 tu tuple-add tu tuple-end -> outcome-invalid -1 outcome-invalid }T
T{ tu tuple-start tu tuple-end tu tuple-start tu tuple-end -> outcome-ok 0 0 outcome-ok 0 0 }T
: pair ( a b -- t outcome ) tu tuple-start drop swap tu tuple-add drop tu tuple-add drop tu tuple-end ;
T{ 7 9 pair 7 9 pair 9 7 pair -> 1 0 1 0 4 0 }T
T{ 1 tu tuple-length 0 1 tu tuple-item 1 1 tu tuple-item 0 tu tuple-length -> 2 7 9 0 }T
\ A number inside a tuple is not a tuple.
T{ 1 tu cons-entry? 2 tu cons-entry? 3 tu cons-entry? 4 tu cons-entry? -> true false false true }T
\ Items beyond 32 bits are refused (on a 32-bit host every cell fits).
u32-mask 0> [if]
T{ tu tuple-start u32-mask 1+ tu tuple-add -1 tu tuple-add u32-mask tu tuple-add -> outcome-ok outcome-invalid outcome-invalid outcome-ok }T
T{ tu tuple-end nip 0 7 tu tuple-item -> outcome-ok u32-mask }T
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
