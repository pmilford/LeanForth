\ Unit tests of src/lib/htab.fs, open-addressing hash tables: finding and
\ putting, growth at 3/4, the size limit at and one past its bound,
\ collisions forced by a hook that gives every entry the same hash, removal
\ by Algorithm R inside and across runs that wrap around the table,
\ spreading, presizing, clearing, statistics, and a randomized model with
\ both hooks. Loaded under HEX.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/htab.fs require ../../src/lib/hash32.fs decimal
lf-lib-private order+

\ Entries are numbers of values kept in an array; the key is a value.
create values 6000 cells allot
variable #values
: value@ ( n -- x ) cells values + @ ;
: value-add ( x -- n ) #values @ tuck cells values + ! 1 #values +! ;
: spread-rehash ( n htab -- h ) drop value@ hash-fmix ;
: same-value ( n key htab -- flag ) drop swap value@ = ;
\ Every entry hashes to slot 5 (mod the size): one run holds them all.
: one-rehash ( n htab -- h ) 2drop 5 ;
create spread-hooks /htab-hooks allot
create one-hooks /htab-hooks allot
' spread-rehash ' same-value spread-hooks htab-hooks!
' one-rehash ' same-value one-hooks htab-hooks!
create t /htab allot

\ Find, put, key-find again.
variable hooks-in-use
: key-hash ( x -- h ) hooks-in-use @ one-hooks = if drop 5 else hash-fmix then ;
: key-find ( x -- n true | i false ) dup key-hash t htab-find ;
\ Insert x unless present: its entry number.
: key-add ( x -- n )
  t htab-ready ok? 0= abort" key-add: full" dup key-find if nip else swap value-add tuck swap t htab-put then ;
: start ( log2 hooks -- outcome ) dup hooks-in-use ! 0 #values ! t htab-init ;
T{ 2 spread-hooks start t htab-count t htab-slots -> outcome-ok 0 4 }T
T{ 42 key-find nip -> false }T
T{ 42 key-add 42 key-add 43 key-add t htab-count -> 0 0 1 2 }T
T{ 42 key-find 43 key-find 44 key-find nip -> 0 true 1 true false }T
\ Growth: the third entry fits 4 slots (3/4), the fourth doubles them.
T{ 44 key-add t htab-slots 45 key-add t htab-slots t htab-count -> 2 4 3 8 4 }T
T{ 42 key-find 45 key-find -> 0 true 3 true }T
T{ t htab-stats nip nip -> 1 }T

\ The limit: at most 2^3 slots, so 6 entries fit and the 7th is full.
T{ 3 t htab-limit 46 key-add 47 key-add t htab-ready -> 4 5 outcome-full }T
T{ t htab-count t htab-slots -> 6 8 }T
T{ 4 t htab-limit t htab-ready t htab-slots -> outcome-ok 16 }T
T{ 99 t htab-limit t htab-ready drop t htab-most @ -> htab-log2-max }T
\ A start beyond the host's largest size is full, with no block.
t htab-free
T{ htab-log2-max 1+ spread-hooks start t htab-block @ -> outcome-full 0 }T

\ Collisions: every entry in one run from slot 5 of 16, wrapping around.
T{ 4 one-hooks start -> outcome-ok }T
: key-add-many ( n -- ) 0 ?do 100 i + key-add drop loop ;
T{ 12 key-add-many t htab-count t htab-slots -> 12 16 }T
: all-found? ( lo hi -- flag ) true -rot swap ?do 100 i + key-find nip and loop ;
T{ 0 12 all-found? 112 key-find nip -> true false }T
\ The run wraps: slots 5 .. 15 and then 0.
T{ 0 t htab@ 4 t htab@ -> 12 0 }T
\ Remove from the middle of the run: the others move back and stay found.
: key-remove ( x -- outcome ) dup key-find 0= abort" key-remove: absent" swap key-hash t htab-remove ;
T{ 103 key-remove 0 3 all-found? 4 12 all-found? 103 key-find nip t htab-count -> outcome-ok true true false 11 }T
T{ 100 key-remove 111 key-remove 106 key-remove t htab-count -> outcome-ok outcome-ok outcome-ok 8 }T
T{ 1 3 all-found? 4 6 all-found? 7 11 all-found? -> true true true }T
\ An absent entry is refused.
T{ 0 5 t htab-remove 99 5 t htab-remove t htab-count -> outcome-invalid outcome-invalid 8 }T
T{ 101 key-find drop 5 t ' htab-holds? rs-checked 0 5 t htab-holds? -> true false }T
\ Spreading: 8 entries need 16 slots at most half full; presizing grows.
T{ t htab-spread t htab-slots 6 t htab-presize t htab-slots 3 t htab-presize t htab-slots -> outcome-ok 16 outcome-ok 64 outcome-ok 64 }T
T{ 1 3 all-found? 7 11 all-found? -> true true }T
T{ t htab-spread t htab-slots -> outcome-ok 16 }T
T{ t htab-clear t htab-count 101 key-find nip -> 0 false }T
t htab-free

\ A randomized model: inserts and removals of keys 0 .. 63, compared with a
\ table of which keys are present and their entries.
create present 64 cells allot
variable model-seed   variable model-bad
: model-rnd ( n -- u ) model-seed @ 1103515245 * 12345 + $7FFFFFFF and dup model-seed ! 7 rshift swap mod ;
: present@ ( x -- n|-1 ) cells present + @ ;
: present! ( n x -- ) cells present + ! ;
: model-bad! ( -- ) 1 model-bad +! ;
: model-key-add ( x -- )
  dup key-add over present@ dup 0< if drop swap present! else rot drop <> if model-bad! then then ;
: model-key-remove ( x -- )
  dup present@ 0< if drop exit then dup key-remove ok? 0= if model-bad! then -1 swap present! ;
: model-count ( -- n ) 0 64 0 do i present@ 0< 0= if 1+ then loop ;
: model-check ( -- )
  64 0 do i key-find if i present@ <> if model-bad! then else drop i present@ 0< 0= if model-bad! then then loop
  t htab-count model-count <> if model-bad! then ;
: model-step ( -- ) 64 model-rnd 3 model-rnd if model-key-add else model-key-remove then model-check ;
: model-run ( seed log2 hooks steps -- bad )
  >r start drop model-seed ! 0 model-bad ! present 64 cells -1 fill
  r> 0 ?do model-step loop t htab-free model-bad @ ;
T{ 1 2 spread-hooks 3000 model-run 2 0 one-hooks 3000 model-run 3 5 one-hooks 2000 model-run -> 0 0 0 }T
bye
