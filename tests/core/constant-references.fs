include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/generation-handles.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../support/store-faults.fs

\ These rows make equal references as records of their own: interning (one
\ switch with the terms, compact-store plan step S4) is off until its rows
\ at the end.
false lf-term-sharing!
create args 4 cells allot
variable name-id
variable ref-id
variable old-id
variable level-id
create eight-args 16 cells allot
: setup ( -- )
lf-name-reset lf-level-reset lf-cref-reset
0 s" alpha" lf-name-str 0= abort" name" name-id !
0 args ! 0 level-identity@ args cell+ !
0 0 level-identity@ lf-hlevel-succ 0= abort" level"
 dup level-id ! args 3 cells + ! args 2 cells + ! ;
setup
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> 0 1 true }T
T{ 0 1 lf-cref-read -> name-id @ lf-name-generation @ 0 true }T
T{ name-id @ lf-name-generation @ args 2 lf-cref-new -> 1 2 true }T
2 ref-id !
T{ 1 ref-id @ lf-cref-read -> name-id @ lf-name-generation @ 2 true }T
T{ 1 ref-id @ 0 lf-cref-level -> 0 0 level-identity@ true }T
T{ 1 ref-id @ 1 lf-cref-level -> 1 level-id @ true }T
T{ 1 ref-id @ 2 lf-cref-level -> false }T
T{ -1 1 lf-cref-valid? -> false }T
T{ 2 1 lf-cref-valid? -> false }T
T{ 1 ref-id @ -1 lf-cref-level -> false }T
T{ name-id @ lf-name-generation @ args -1 lf-cref-new -> false }T
T{ name-id @ lf-name-generation @ args 9 lf-cref-new -> false }T
T{ -1 lf-name-generation @ args 2 lf-cref-new -> false }T
T{ name-id @ lf-name-generation @ 1- args 2 lf-cref-new -> false }T
-1 args 3 cells + !
T{ name-id @ lf-name-generation @ args 2 lf-cref-new -> false }T
T{ lf-cref-count @ lf-cref-serial @ -> 2 2 }T
level-id @ args 3 cells + !
\ Rollback and reuse a level slot invalidates the captured pair.
1 lf-level-count !
: reuse-level ( -- ) 0 0 level-identity@ lf-hlevel-succ 0= abort" level reuse" 2drop ;
reuse-level
T{ 1 ref-id @ lf-cref-valid? -> false }T
\ Rollback and reuse a reference slot must not resurrect the old handle.
1 lf-cref-count !
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> 1 3 true }T
T{ 1 ref-id @ lf-cref-valid? -> false }T
3 old-id !
lf-cref-reset
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> 0 4 true }T
T{ 0 4 lf-cref-valid? -> true }T
\ Slot zero was reused after reset; its first identity remains stale.
T{ 0 1 lf-cref-valid? -> false }T
T{ 1 old-id @ lf-cref-valid? -> false }T
lf-name-reset
: reuse-name ( -- ) 0 s" alpha" lf-name-str 0= abort" name reuse" drop ;
reuse-name
T{ 0 4 lf-cref-valid? -> false }T
\ Fill reference storage; the rejected allocation does not advance serial.
lf-cref-reset
: fill-refs ( -- ) lf-cref-capacity 0 do
  0 lf-name-generation @ 0 0 lf-cref-new 0= abort" fill" 2drop
loop ;
fill-refs
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> false }T
T{ lf-cref-count @ lf-cref-serial @ -> lf-cref-capacity 36 }T
\ Maximum argument count preserves every ordered pair.
lf-cref-reset
: prepare-eight ( -- ) 8 0 do
  i 2 mod if 1 else 0 then eight-args i 2 * cells + !
  i 2 mod if level-serial else 0 level-identity@ then
  eight-args i 2 * 1+ cells + !
loop ;
prepare-eight
T{ 0 lf-name-generation @ eight-args 8 lf-cref-new -> 0 37 true }T
T{ 0 37 0 lf-cref-level -> 0 0 level-identity@ true }T
T{ 0 37 7 lf-cref-level -> 1 level-serial true }T
lf-level-reset
T{ 0 37 lf-cref-valid? -> false }T
\ Saturation refuses allocation without changing the live reference count.
lf-cref-reset
-1 1 rshift lf-cref-serial !
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> false }T
T{ lf-cref-count @ -> 0 }T

\ A negative serial invalidates the whole store; nothing is allocated or read.
0 lf-cref-serial !
setup prepare-eight
T{ 0 lf-name-generation @ eight-args 8 lf-cref-new -> 0 1 true }T
-1 lf-cref-serial !
T{ lf-cref-state-valid? -> false }T
T{ 0 1 lf-cref-valid? -> false }T
T{ 0 lf-name-generation @ 0 0 lf-cref-new -> false }T
T{ lf-cref-count @ -> 1 }T
1 lf-cref-serial !

\ lf-cref-levels: the validated level pairs of a live reference, in order;
\ a stale identity or a reset name table gives only false.
T{ 0 1 lf-cref-levels -> 0 lf-cref-slot lf-cref-pairs drop 8 true }T
T{ 0 1 lf-cref-levels 2drop 7 2* cells + 2@ swap -> 1 level-serial }T
T{ 0 2 lf-cref-levels -> false }T
T{ 1 1 lf-cref-levels -> false }T
lf-name-reset
T{ 0 1 lf-cref-levels -> false }T
T{ 0 1 0 lf-cref-level -> false }T

\ A failed construction changes neither the count nor the serial.
lf-cref-reset
lf-cref-serial @ constant cref-serial1
T{ 0 lf-name-generation @ eight-args -1 lf-cref-new -> false }T
T{ 999 lf-name-generation @ 0 0 lf-cref-new -> false }T
T{ lf-cref-count @ lf-cref-serial @ -> 0 cref-serial1 }T
\ An invalid name or store is refused before the level array is read, so
\ even an unreadable address is never touched.
T{ 999 lf-name-generation @ 0 1 lf-cref-new -> false }T
-1 lf-cref-count !
T{ name-id @ lf-name-generation @ 0 1 lf-cref-new -> false }T
0 lf-cref-count !

\ A corrupted count makes every reference invalid; nothing is allocated.
setup
T{ name-id @ lf-name-generation @ args 2 lf-cref-new -> 0 cref-serial1 1+ true }T
cref-serial1 1+ constant live-id
33 lf-cref-count !
T{ 0 live-id lf-cref-valid? name-id @ lf-name-generation @ 0 0 lf-cref-new -> false false }T
-1 lf-cref-count !
T{ 0 live-id lf-cref-valid? 0 live-id lf-cref-levels -> false false }T
1 lf-cref-count !

\ A negative stored argument count, or pairs outside the pool, make the
\ record invalid everywhere (there is no other limit on the count).
: arity! ( n -- ) 0 lf-cref-slot lf-crec-arity ! ;
: offset! ( n -- ) 0 lf-cref-slot lf-crec-offset ! ;
-1 offset!
T{ 0 live-id lf-cref-valid? 0 live-id lf-cref-levels -> false false }T
lf-cref-pool slab-capacity 1- offset!
T{ 0 live-id lf-cref-valid? 0 live-id lf-cref-levels -> false false }T
\ Far outside the pool: refused before any address is formed (without the
\ check, reading there would fault).
1 30 lshift offset!
T{ 0 live-id lf-cref-valid? 0 live-id lf-cref-levels -> false false }T
0 offset!
T{ 0 live-id lf-cref-valid? -> true }T
lf-cref-pool slab-capacity 1+ arity!
T{ 0 live-id lf-cref-valid? 0 live-id lf-cref-read -> false false }T
T{ 0 live-id lf-cref-levels 0 live-id 0 lf-cref-level -> false false }T
-1 arity!
T{ 0 live-id lf-cref-valid? 0 live-id lf-cref-levels -> false false }T
0 arity!
T{ 0 live-id lf-cref-levels -> 0 lf-cref-slot lf-cref-pairs drop 0 true }T
T{ 0 live-id 0 lf-cref-level -> false }T
2 arity!

\ The serial never wraps: at max-n one more reference is refused.
max-n 1- lf-cref-serial !
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> 1 max-n true }T
T{ name-id @ lf-name-generation @ 0 0 lf-cref-new -> false }T
T{ lf-cref-count @ -> 2 }T

\ The public words keep the return stack balanced.
T{ 0 live-id ' lf-cref-valid? rs-checked -> true }T
T{ 0 live-id ' lf-cref-read rs-checked -> name-id @ lf-name-generation @ 2 true }T
T{ 0 live-id 1 ' lf-cref-level rs-checked -> 1 level-id @ true }T
T{ 0 live-id ' lf-cref-levels rs-checked rot drop -> 2 true }T
lf-cref-reset 0 lf-cref-serial !
T{ name-id @ lf-name-generation @ args 2 ' lf-cref-new rs-checked -> 0 1 true }T

\ Interning (compact-store plan step S4): an equal live reference is the
\ same record with its identity; another name, generation, arity or level
\ is a new one; a rollback takes the records it gives back out of the
\ table, and a reset empties it.
true lf-term-sharing!
setup 0 lf-cref-serial !
: ref ( addr count -- index identity true | false )
  name-id @ lf-name-generation @ 2swap lf-cref-new ;
T{ args 2 ref args 2 ref -> 0 1 true 0 1 true }T
T{ args 1 ref 0 0 ref args 2 ref lf-cref-count @ -> 1 2 true 2 3 true 0 1 true 3 }T
create other-args 4 cells allot   \ the two levels in the other order
args 2 cells + other-args 2 cells move   args other-args 2 cells + 2 cells move
T{ other-args 2 ref other-args 1 ref -> 3 4 true 4 5 true }T
\ The table's equality hook compares the level pairs too (a hash only
\ leads to a candidate).
name-id @ lf-name-generation @ args 2 lf-cref-key!
T{ 0 lf-cref-key lf-cref-table lf-cref-same -> true }T
name-id @ lf-name-generation @ other-args 2 lf-cref-key!
T{ 0 lf-cref-key lf-cref-table lf-cref-same -> false }T
create cref-mark /store-mark allot
T{ cref-mark lf-crefs store-mark -> outcome-ok }T
T{ args 2 ref other-args 2 ref -> 0 1 true 3 4 true }T
0 s" beta" lf-name-str drop name-id !
T{ args 2 ref args 2 ref -> 5 6 true 5 6 true }T
T{ cref-mark lf-cref-rollback lf-cref-count @ -> outcome-ok 5 }T
T{ args 2 ref -> 5 7 true }T
T{ cref-mark lf-cref-rollback lf-cref-table htab-count -> outcome-ok 5 }T
lf-cref-reset
T{ args 2 ref -> 0 8 true }T
\ An equal record is not given where a new one would be refused.
max-n lf-cref-serial !
T{ args 2 ref -> false }T
bye
