\ Tests of store marks (src/lib/store.fs, plan task 1.1.3): store-mark,
\ store-mark-valid? and store-rollback. A rollback restores the count, also
\ after a partial failure, and never rewinds identities; a mark of another
\ store, from before a reset, of a poisoned store, above the current count,
\ stale after an earlier rollback went below it, or forged is refused with
\ invalid and nothing changed. A randomized model then runs long random
\ sequences of allocations, marks, rollbacks and resets and compares every
\ result with a model that tracks which marks are still live by events: a
\ mark dies when the count drops below it or the store is reset.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs

5 1 cells 0 store: s
5 1 cells 0 store: t
3 1 cells 1 store: s1
create m0 /store-mark allot
create m1 /store-mark allot
create m2 /store-mark allot
: count@ ( store -- n ) store-count @ ;
: news ( n store -- ) swap 0 ?do dup store-new 0= abort" full" drop loop drop ;

\ A mark records the store, its generation, serial and count.
T{ m0 s ' store-mark rs-checked -> outcome-ok }T
T{ m0 mark-store @ s = m0 mark-count @ m0 mark-serial @ m0 mark-generation @ -> true 0 0 0 }T
T{ m0 s store-mark-valid? -> true }T

\ Rollback restores the count; identities are not rewound.
3 s news
T{ s count@ s store-serial @ -> 3 3 }T
T{ m0 s ' store-rollback rs-checked s count@ s store-serial @ -> outcome-ok 0 3 }T
T{ s store-new 0 s store-identity@ -> 0 true 4 true }T
\ The same mark again: still valid, and rolling back twice is harmless.
T{ m0 s store-rollback m0 s store-rollback s count@ -> outcome-ok outcome-ok 0 }T

\ A partial failure: allocate until the store is full, then roll back.
1 s news
T{ m1 s store-mark m1 mark-count @ -> outcome-ok 1 }T
T{ s store-new s store-new s store-new s store-new -> 1 true 2 true 3 true 4 true }T
T{ s store-new s count@ -> false 5 }T
T{ m1 s store-rollback s count@ -> outcome-ok 1 }T
T{ 0 s store-identity@ 1 s store-identity@ -> 5 true false }T

\ A mark above the current count is refused and changes nothing.
3 s news
T{ m2 s store-mark m2 mark-count @ -> outcome-ok 4 }T
T{ m1 s store-rollback s count@ -> outcome-ok 1 }T
T{ m2 s ' store-rollback rs-checked s count@ m2 s store-mark-valid? -> outcome-invalid 1 false }T
\ ... and stays refused once the count has grown past it again: the
\ records below it were allocated after the mark.
4 s news
T{ s count@ m2 s store-rollback s count@ -> 5 outcome-invalid 5 }T
\ An older mark below both is still valid.
T{ m1 s store-rollback s count@ -> outcome-ok 1 }T

\ A mark of another store.
T{ m1 t store-rollback m1 t store-mark-valid? -> outcome-invalid false }T
T{ m0 t store-mark m0 s store-rollback -> outcome-ok outcome-invalid }T

\ A mark from before a reset, even at the base, is refused.
T{ m0 s store-mark m0 s store-mark-valid? -> outcome-ok true }T
s store-clear
T{ s count@ m0 s store-rollback m0 s store-mark-valid? -> 0 outcome-invalid false }T
T{ m0 s store-mark m0 s store-rollback -> outcome-ok outcome-ok }T

\ A base-1 store is invalid until its first clear: marking fails, and the
\ failed mark names no store.
T{ m1 s1 store-mark m1 mark-store @ m1 s1 store-rollback -> outcome-invalid 0 outcome-invalid }T
s1 store-clear
T{ m1 s1 store-mark m1 mark-count @ -> outcome-ok 1 }T
T{ s1 store-new s1 store-new s1 count@ -> 1 true 2 true 3 }T
T{ m1 s1 store-rollback s1 count@ -> outcome-ok 1 }T

\ A poisoned store: marking fails and an old mark is refused.
T{ m2 s1 store-mark -> outcome-ok }T
s1 store-poison
T{ m2 s1 store-rollback m0 s1 store-mark m0 mark-store @ -> outcome-invalid outcome-invalid 0 }T

\ Forged marks: each wrong field alone is refused.
3 t news
: forge ( -- ) m2 t store-mark drop ;
forge
T{ m2 t store-mark-valid? -> true }T
forge 0 m2 mark-store !
T{ m2 t store-rollback t count@ -> outcome-invalid 3 }T
forge 1 m2 mark-generation +!
T{ m2 t store-rollback -> outcome-invalid }T
forge 1 m2 mark-serial +!
T{ m2 t store-rollback -> outcome-invalid }T
forge -1 m2 mark-serial !
T{ m2 t store-rollback -> outcome-invalid }T
forge -1 m2 mark-count !
T{ m2 t store-rollback -> outcome-invalid }T
forge 1 m2 mark-count +!
T{ m2 t store-rollback t count@ -> outcome-invalid 3 }T
\ A count below the real one with the real serial: the record at the
\ count is older than the mark claims.
forge -1 m2 mark-count +!
T{ m2 t store-rollback t count@ -> outcome-invalid 3 }T
\ A count above the real one with an older serial: the record below the
\ count is newer than the mark claims.
forge 1 m2 mark-count +! t store-new 2drop
T{ m2 t store-rollback t count@ -> outcome-invalid 4 }T
\ A corrupted store fails closed.
forge t store-seal @ 1+ t store-seal !
T{ m2 t store-rollback m2 t store-mark-valid? -> outcome-invalid false }T
t store-seal @ 1- t store-seal !
T{ m2 t store-rollback -> outcome-ok }T
T{ depth -> 0 }T

\ ---------------------------------------------------------------------------
\ Randomized model. Store r (capacity 6, base 0) and four mark records.
\ The model keeps the count and, per mark, its count and whether it is
\ live: marking makes it live; a rollback to a live mark sets the count;
\ any drop of the count below a mark's count (a rollback or a reset)
\ kills that mark for good.

variable mark-seed  2718 mark-seed !
: mark-rnd ( n -- r )
  mark-seed @ 1103515245 * 12345 + dup mark-seed ! 16 rshift 32767 and swap mod ;
6 1 cells 0 store: r
4 constant marks
create mark-records marks /store-mark * allot
create model-live marks cells allot   model-live marks cells erase
create model-at marks cells allot
variable model-count  0 model-count !
variable mismatches  0 mismatches !
: mark# ( k -- mark ) /store-mark * mark-records + ;
: live ( k -- addr ) cells model-live + ;
: at ( k -- addr ) cells model-at + ;
: differ ( -- ) 1 mismatches +! ;
: check ( flag -- ) 0= if differ then ;

\ Model events.
: kill-above ( n -- ) marks 0 ?do dup i at @ < if false i live ! then loop drop ;
: model-drop ( n -- ) dup kill-above model-count ! ;
: model-reset ( -- ) marks 0 ?do false i live ! loop 0 model-count ! ;

\ Operations, each compared with the model.
: op-new ( -- )
  r store-new dup if nip then model-count @ 6 < tuck = check if 1 model-count +! then ;
: op-mark ( k -- )
  dup mark# r store-mark ok? check true over live ! model-count @ swap at ! ;
: op-rollback ( k -- )
  dup mark# r store-rollback ok? over live @ = check
  dup live @ if at @ model-drop else drop then ;
: op-valid ( k -- ) dup mark# r store-mark-valid? swap live @ = check ;
: op-reset ( -- ) r store-clear model-reset ;
: op ( -- )
  100 mark-rnd marks mark-rnd swap
  dup 40 < if 2drop op-new exit then
  dup 60 < if drop op-mark exit then
  dup 85 < if drop op-rollback exit then
  dup 98 < if drop op-valid exit then 2drop op-reset ;
: run-model ( n -- ) 0 ?do op r count@ model-count @ = check loop ;
T{ 20000 run-model mismatches @ -> 0 }T
T{ depth -> 0 }T
bye
