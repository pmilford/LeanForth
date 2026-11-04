\ The checker's heap stores growing under stress (ADR 0016 C9 step 3; the
\ independent review rvKC's finding M3). The checker trials of
\ tests/support/checker-trial.fs normally run at the default settings,
\ where every store starts at its capacity limit and never grows; here
\ each trial also runs, in a new context of its own, in three more ways,
\ and must give the same digest of every outcome, result, fuel, count and
\ diagnostic:
\ - shrunk: before every check each heap store (terms, levels, names,
\   references) gives back its free records, its block cut to its count,
\   so every check grows the stores it fills, in the middle of its passes;
\ - moved: at every allocation the allocating store's block moves to a
\   new address, with its columns, reference pool or name index, and the
\   old memory is filled with $A5 and freed only later, so an address
\   kept across a growth reads poison;
\ - both.
\ The same at raised capacity limits (4,096 records): shrunk and moved
\ against plain. Then the two growths that are not a store's own block
\ ask the fault hook too: the input's name index while declarations are
\ loaded, and the reference pool's first reserve when a context is made.
\ Test-only; nothing here checks or accepts a theorem.

: store-fault-hooks ( -- ) ;   \ the test hook of src/lib/store.fs
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/lib/task.fs
require ../../src/kernel/mixed-definition-probe.fs
require ../../src/kernel/env-publish.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs
include ../support/checker-trial.fs
lf-lib-private order+

\ ---------------------------------------------------------------------------
\ Moving blocks. Retired memory is poisoned and freed 64 retirements later.
64 constant ring#
create ring ring# cells allot  ring ring# cells erase
variable ring-at
: ring-cell ( -- addr ) ring-at @ ring# mod cells ring + ;
: retire ( addr u -- )
  over swap $A5 fill ring-cell dup @ ?dup if free drop then ! 1 ring-at +! ;
: retire-all ( -- ) ring# 0 do i cells ring + dup @ ?dup if free drop then 0 swap ! loop ;
: fresh-copy ( addr u -- addr' ) dup 1 max allocate throw dup >r swap move r> ;
: store-move ( store -- )
  dup store-heap? 0= if drop exit then
  >r r@ store-identities r@ store-bytes 2dup fresh-copy -rot retire
  r@ store-block ! r> store-seal! ;
: slab-move ( slab -- )
  dup slab-capacity 0= if drop exit then
  >r 0 r@ slab-at r@ slab-bytes 2dup fresh-copy -rot retire
  r@ slab-capacity r> slab-block! ;
: column-move ( column -- ) column-slab slab-move ;
: columns-move ( group -- ) ['] column-move swap columns-each ;
variable moving
variable moves
: mover ( store -- false )
  moving @ 0= if drop false exit then
  1 moves +! dup store-move
  dup lf-terms = if lf-term-columns columns-move then
  dup lf-levels = if lf-level-columns columns-move then
  dup lf-crefs = if lf-cref-pool slab-move then
  lf-inputs = if lf-input-names slab-move then false ;
' mover is store-refuse?

\ Shrinking every heap store to its count, keeping its limit.
variable shrinking
: shrunk ( store -- )
  dup store-limit @ >r dup store-count @ 1 max over store-limit! drop r> swap store-limit! drop ;
: shrink-all ( -- )
  shrinking @ 0= if exit then lf-terms shrunk lf-levels shrunk lf-crefs shrunk lf-names shrunk ;
' shrink-all is before-check

\ ---------------------------------------------------------------------------
\ The trials: each in a new context, at the limits of limit (0: default).
60 constant trials#
300 constant steps#
create digests trials# cells allot
create baseline trials# cells allot
variable limit
: limits! ( n -- )
  dup lf-term-capacity! drop dup lf-level-capacity! drop
  dup lf-cref-capacity! drop lf-name-capacity! drop ;
: one-trial ( k -- digest )
  context-new throw dup >r context-use limit @ ?dup if limits! then
  steps# 0 trial-start trial-run digest context-main context-use r> context-free throw ;
: run-all ( -- ) trials# 0 do i one-trial i cells digests + ! loop ;
: keep-base ( -- ) digests baseline trials# cells move ;
: differing ( -- n ) 0 trials# 0 do i cells digests + @ i cells baseline + @ <> - loop ;
: mode ( limit shrink move -- ) moving ! shrinking ! limit ! 0 moves ! ;

0 0 0 mode run-all keep-base
T{ 0 1 0 mode run-all differing -> 0 }T
T{ 0 0 1 mode run-all differing moves @ 1000 > -> 0 true }T
T{ 0 1 1 mode run-all differing moves @ 1000 > -> 0 true }T
4096 0 0 mode run-all keep-base
T{ 4096 1 1 mode run-all differing moves @ 1000 > -> 0 true }T
.( trials alike shrunk and moved: ) trials# . .( of ) steps# . .( steps; moves: ) moves @ . cr
0 0 0 mode retire-all

\ ---------------------------------------------------------------------------
\ The input's name index grows through the fault hook while declarations
\ are loaded: refused, the declaration is full and not added, and the
\ index has not grown (the hook was asked before the index grew, not only
\ by the input store); the index moved, the links read back through it
\ are the same.
lf-input-reset lf-term-reset lf-level-reset lf-name-reset
create decl /lf-idecl allot
: axiom ( name -- decl )
  decl /lf-idecl erase lf-kind-axiom decl lf-idecl-kind ! decl lf-idecl-name !
  lf-safety-safe decl lf-idecl-safety ! lf-hint-opaque decl lf-idecl-hint !
  0 lf-term-sort drop decl lf-idecl-type ! -1 decl lf-idecl-value ! decl ;
: id-of ( n -- id ) 0 swap lf-name-num drop ;
\ Every declaration's name index: names beyond the index's first units.
200 lf-name-capacity! drop
: ids ( n -- ) 0 ?do i id-of drop loop ;
150 ids
variable refuse-index
: refuse-inputs ( store -- flag ) dup lf-inputs = refuse-index @ and if drop true else mover then ;
' refuse-inputs is store-refuse?
true refuse-index !
T{ lf-input-names slab-capacity -> 0 }T
T{ 149 id-of axiom lf-input-add lf-input-count lf-input-names slab-capacity
   -> -1 outcome-full 0 0 }T
false refuse-index !  true moving !
T{ 149 id-of axiom lf-input-add 148 id-of axiom lf-input-add lf-input-count
   -> 0 outcome-ok 1 outcome-ok 2 }T
T{ 149 id-of lf-input-newest 148 id-of lf-input-newest -> 0 1 }T
false moving ! retire-all ' mover is store-refuse?
lf-input-reset lf-name-reset

\ The reference pool's first reserve, when a context is made, asks the
\ fault hook: refused, no context is made and nothing stays allocated.
variable refuse-crefs
: refuse-pool ( store -- flag ) lf-crefs = refuse-crefs @ and ;
' refuse-pool is store-refuse?
live-blocks @ constant blocks-before
true refuse-crefs !
T{ context-new 0= nip -> false }T
false refuse-crefs !
T{ live-blocks @ blocks-before - -> 0 }T
T{ context-new throw context-free -> 0 }T
' mover is store-refuse?

cases-done
bye
