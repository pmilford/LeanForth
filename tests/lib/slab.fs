\ Unit tests of src/lib/slab.fs, growable heap stores (plan task 1.1.5):
\ shapes, room and claims, the limit at and one past its bound, growth
\ keeping the contents, trimming, clearing and poisoning, every sealed
\ field corrupted, marks and every refusal of a rollback, and a
\ randomized model of claims, marks, rollbacks and clears. Loaded under
\ HEX. T{ }T checks results and data-stack depth; rs-checked the return
\ stack.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/slab.fs decimal
lf-lib-private order+

create s1 /slab allot   create s2 /slab allot   create s3 /slab allot
create m0 /slab-mark allot   create m1 /slab-mark allot   create m2 /slab-mark allot

\ Shapes: a positive unit, 0 <= limit, limit units within a cell.
T{ 1 cells 10 s1 slab-init -> outcome-ok }T
T{ s1 slab-live? s1 slab-count s1 slab-capacity s1 slab-limit s1 slab-unit -> true 0 0 10 1 cells }T
T{ 0 10 s2 slab-init s2 slab-live? -> outcome-invalid false }T
T{ -1 10 s2 slab-init 1 cells -1 s2 slab-init -> outcome-invalid outcome-invalid }T
T{ 2 max-n s2 slab-init s2 slab-live? -> outcome-invalid false }T
T{ 1 max-n s2 slab-init s2 slab-live? -> outcome-ok true }T
T{ 1 0 s2 slab-init 0 s2 slab-room 1 s2 slab-room -> outcome-ok outcome-ok outcome-full }T
s2 slab-free

\ Claims. The first block holds slab-min-units, or the limit if smaller.
T{ 3 s1 ' slab-claim rs-checked s1 slab-count s1 slab-capacity -> 0 outcome-ok 3 10 }T
\ The limit: room for 7 more, not 8; a claim at the limit, then one past.
T{ 7 s1 slab-room 8 s1 slab-room -> outcome-ok outcome-full }T
T{ 7 s1 slab-claim s1 slab-count -> 3 outcome-ok 10 }T
T{ 1 s1 slab-claim s1 slab-count -> -1 outcome-full 10 }T
T{ 0 s1 slab-room -1 s1 slab-room -1 s1 slab-claim -> outcome-ok outcome-invalid -1 outcome-invalid }T
T{ 0 s1 slab-valid? 9 s1 slab-valid? 10 s1 slab-valid? -1 s1 slab-valid? -> true true false false }T
T{ 1 s1 slab-at 0 s1 slab-at - s1 slab-top 10 s1 slab-at = -> 1 cells true }T

\ Growth keeps the contents: 1,000 cells claimed one at a time.
1 cells 1000 s2 slab-init drop
: fill-cells ( n slab -- ) swap 0 ?do 1 over slab-claim drop i 7 * swap 2 pick slab-at ! loop drop ;
: filled? ( n slab -- flag ) true rot 0 ?do over i swap slab-at @ i 7 * = and loop nip ;
T{ 1000 s2 fill-cells s2 slab-count s2 slab-capacity -> 1000 1000 }T
T{ 1000 s2 filled? 1 s2 slab-room -> true outcome-full }T
\ Doubling: 16, 32, 64, ... capped at the limit.
1 cells 100 s3 slab-init drop
T{ 1 s3 slab-claim 2drop s3 slab-capacity 16 s3 slab-claim 2drop s3 slab-capacity -> 16 32 }T
T{ 40 s3 slab-claim 2drop s3 slab-capacity 50 s3 slab-room s3 slab-capacity -> 64 outcome-full 64 }T
\ slab-reserve pre-sizes; slab-trim shrinks to the count, keeping it.
T{ 100 s3 slab-reserve s3 slab-capacity s3 slab-trim s3 slab-capacity s3 slab-count -> outcome-ok 100 outcome-ok 57 57 }T
T{ 5 s3 slab-claim nip s3 slab-count -> outcome-ok 62 }T
s3 slab-free
T{ s3 slab-live? 0 s3 slab-room -> false outcome-invalid }T

\ Clearing: count 0, generation + 1; at max-n the slab is poisoned.
T{ s2 slab-generation s2 slab-clear s2 slab-count s2 slab-generation -> 0 0 1 }T
max-n 1- s2 slab-epoch !
T{ s2 slab-clear s2 slab-generation s2 slab-live? -> max-n true }T
T{ s2 slab-clear s2 slab-generation s2 slab-live? 1 s2 slab-room -> -1 false outcome-invalid }T
T{ s2 slab-clear s2 slab-generation -> -1 }T
s2 slab-free

\ Corrupting any sealed field, or the count, fails closed.
1 cells 10 s2 slab-init drop  4 s2 slab-claim 2drop
: field+! ( delta xt -- ) s2 swap execute +! ;
: tamper ( xt delta -- flag outcome )   \ change the field xt gives, test, restore
  2dup swap field+! s2 slab-live? 1 s2 slab-room 2swap negate swap field+! ;
T{ ' slab-block 8 tamper -> false outcome-invalid }T
T{ ' slab-room-units 1 tamper -> false outcome-invalid }T
T{ ' slab-unit-size 1 tamper -> false outcome-invalid }T
T{ ' slab-most 1 tamper -> false outcome-invalid }T
T{ ' slab-seal 1 tamper -> false outcome-invalid }T
T{ ' slab-used 100 tamper -> false outcome-invalid }T
T{ ' slab-used -5 tamper -> false outcome-invalid }T
T{ ' slab-epoch max-n negate tamper -> false outcome-invalid }T
T{ s2 slab-live? 1 s2 slab-room -> true outcome-ok }T
s2 slab-free

\ Marks. A mark records the slab, its generation, its entry and count.
1 cells 100 s1 slab-free s1 slab-init drop
T{ m0 s1 ' slab-mark rs-checked -> outcome-ok }T
T{ m0 slab-mark-slab @ s1 = m0 slab-mark-count @ m0 slab-mark-entry @ s1 slab-depth @ -> true 0 0 1 }T
T{ 3 s1 slab-claim nip s1 slab-count -> outcome-ok 3 }T
T{ m0 s1 ' slab-rollback rs-checked s1 slab-count -> outcome-ok 0 }T
\ Still valid: rolling back twice is harmless.
T{ m0 s1 slab-mark-valid? m0 s1 slab-rollback s1 slab-count -> true outcome-ok 0 }T
\ Marks at one count share an entry.
T{ m1 s1 slab-mark s1 slab-depth @ m1 slab-mark-serial @ m0 slab-mark-serial @ = -> outcome-ok 1 true }T
\ A mark above a rollback's target is stale, and stays stale when the
\ count passes it again; the older mark stays valid.
4 s1 slab-claim 2drop
T{ m2 s1 slab-mark m2 slab-mark-count @ s1 slab-depth @ -> outcome-ok 4 2 }T
T{ m1 s1 slab-rollback s1 slab-count s1 slab-depth @ -> outcome-ok 0 1 }T
T{ m2 s1 slab-mark-valid? m2 s1 slab-rollback s1 slab-count -> false outcome-invalid 0 }T
6 s1 slab-claim 2drop
T{ m2 s1 slab-rollback s1 slab-count m0 s1 slab-rollback s1 slab-count -> outcome-invalid 6 outcome-ok 0 }T
\ A mark of another slab, and one from before a clear.
1 cells 100 s2 slab-init drop
T{ m0 s2 slab-rollback m0 s2 slab-mark-valid? -> outcome-invalid false }T
T{ m0 s1 slab-mark s1 slab-clear m0 s1 slab-rollback m0 s1 slab-mark-valid? -> outcome-ok outcome-invalid false }T
\ A forged entry position, and a forged count, are refused.
T{ m0 s1 slab-mark 99 m0 slab-mark-entry ! m0 s1 slab-rollback -> outcome-ok outcome-invalid }T
T{ m0 s1 slab-mark 1 m0 slab-mark-count ! m0 s1 slab-rollback -> outcome-ok outcome-invalid }T
\ A slab that is not live cannot be marked; the mark is then refused.
T{ m1 s3 slab-mark m1 slab-mark-slab @ m1 s3 slab-rollback -> outcome-invalid 0 outcome-invalid }T
\ The mark stack grows: 100 marks at counts 0 .. 99, then a rollback to
\ the 50th leaves 51 entries.
create many 100 /slab-mark * allot
: mark# ( k -- mark ) /slab-mark * many + ;
: mark-all ( -- flag ) true 100 0 do i mark# s1 slab-mark ok? and 1 s1 slab-claim nip ok? and loop ;
T{ s1 slab-clear mark-all s1 slab-depth @ s1 slab-count -> true 100 100 }T
: valid-all ( -- n ) 0 100 0 do i mark# s1 slab-mark-valid? if 1+ then loop ;
T{ valid-all 50 mark# s1 slab-rollback s1 slab-depth @ valid-all s1 slab-count -> 100 outcome-ok 51 51 50 }T
s1 slab-free s2 slab-free

\ A randomized model: claims, marks into eight records, rollbacks and
\ clears, compared at every step with a model that keeps the count and,
\ per mark, whether it lives (a mark dies when a rollback goes below its
\ count or the slab is cleared) and its count.
8 constant #model-marks
create model-alive #model-marks cells allot
create model-at #model-marks cells allot
variable model-n   variable model-seed   variable model-bad
: model-rnd ( n -- u ) model-seed @ 1103515245 * 12345 + $7FFFFFFF and dup model-seed ! 7 rshift swap mod ;
: alive ( k -- addr ) cells model-alive + ;
: at ( k -- addr ) cells model-at + ;
: bad ( -- ) 1 model-bad +! ;
: model-kill-above ( n -- ) #model-marks 0 do dup i at @ < if false i alive ! then loop drop ;
: model-claim ( -- )
  4 model-rnd dup s1 slab-claim 2 pick model-n @ + 60 >
  if nip outcome-full <> if bad then drop exit then
  ok? 0= if bad then model-n @ <> if bad then model-n +! ;
: model-mark ( -- )
  #model-marks model-rnd dup mark# s1 slab-mark ok? 0= if bad then
  true over alive ! model-n @ swap at ! ;
: model-rollback ( -- )
  #model-marks model-rnd dup mark# s1 slab-rollback ok? over alive @ <> if bad then
  dup alive @ if at @ dup model-n ! model-kill-above else drop then ;
: model-clear ( -- ) s1 slab-clear 0 model-n ! model-alive #model-marks cells erase ;
: model-check ( -- )
  s1 slab-count model-n @ <> if bad then
  #model-marks 0 do i mark# s1 slab-mark-valid? i alive @ <> if bad then loop ;
: model-step ( -- )
  20 model-rnd dup 8 < if drop model-claim else dup 13 < if drop model-mark else
  19 < if model-rollback else model-clear then then then model-check ;
: model-run ( seed steps -- bad )
  swap model-seed ! 0 model-bad ! 0 model-n ! model-alive #model-marks cells erase
  1 cells 60 s1 slab-init drop 0 ?do model-step loop s1 slab-free model-bad @ ;
T{ 1 20000 model-run 2 20000 model-run 3 20000 model-run -> 0 0 0 }T
bye
