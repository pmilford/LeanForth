\ Randomized model tests of the general Forth library (src/lib): long
\ random sequences of store operations compared after every step with a
\ simple independent model, and random DAG walks compared with recursive
\ definitions of the visit visit-order, the fuel used and the deepest context.
\ Also direct cases for public words that tests/lib/lib.fs reaches only
\ indirectly. The generator is deterministic and cell-size neutral.
include ../support/tester.fs
include ../support/checks.fs
include ../../src/lib/lib.fs

variable lm-seed  12345 lm-seed !
: lm-rnd ( n -- r ) lm-seed @ 1103515245 * 12345 + dup lm-seed ! 16 rshift 32767 and swap mod ;
variable failures
: fail ( c-addr u -- ) type cr 1 failures +! ;

\ ---------------------------------------------------------------------------
\ Direct cases.

T{ 2 /node 0 store: d0 -> }T
T{ d0 store-open? d0 store-room? -> true true }T
T{ d0 ' store-new-slot rs-checked -> 0 d0 store-slot 0 true }T
T{ d0 store-new-slot -> 1 d0 store-slot 1 true }T
T{ d0 store-new-slot d0 store-open? d0 store-room? -> false false false }T
d0 store-clear
max-n d0 store-serial !
T{ d0 store-open? d0 store-room? d0 store-new-slot -> false true false }T
0 d0 store-serial !
\ The seal cell itself is a shape field: corrupting it fails closed.
d0 store-seal @ constant d0-seal
d0-seal 1+ d0 store-seal !
T{ d0 store-sealed? d0 store-count-valid? d0 store-new -> false false false }T
d0-seal d0 store-seal !
T{ d0 store-sealed? d0 store-count-valid? -> true true }T
\ A poisoned store stays poisoned through clear, and live? says so.
T{ d0 store-live? -> true }T
d0 store-poison d0 store-clear
T{ d0 store-live? d0 store-open? 0 d0 store-identity@ -> false false false }T

T{ 4 outcome-sane 5 outcome-sane max-n outcome-sane -> 4 5 1 }T
T{ 9 outcome-ok ok-then? 9 outcome-rejected ok-then? -> 9 true outcome-rejected false }T
T{ outcome-unsupported ok? outcome-rejected outcome? -> false true }T

T{ 2 walk: dw -> }T
T{ dw walk-room? 1 dw walk-push-outcome 2 dw walk-push-outcome -> true outcome-ok outcome-ok }T
T{ dw walk-room? 3 dw walk-push-outcome dw walk-pending @ -> false outcome-exhausted 2 }T
\ walk-read fails on an index the store does not hold.
T{ 1 /node 0 store: dn -> }T
5 dw walk-node !
T{ dw dn walk-read -> false }T
4 5 6 dn node-new 2drop 0 dw walk-node !
T{ dw dn walk-read -> 5 6 dw 4 true }T

\ ---------------------------------------------------------------------------
\ Store model: count, serial, generation and per-index identities, for a
\ base-0 and a base-1 store, under random allocation, reset, lookups at
\ indices just outside the valid range, and occasional serial exhaustion.

6 constant mcap
create m-ids mcap cells allot
variable m-count variable m-serial variable m-gen variable m-base
: m-reset ( base -- ) m-base ! 0 m-count ! 0 m-serial ! 0 m-gen ! m-ids mcap cells erase ;
: m-live? ( -- flag ) m-gen @ 0< 0= m-count @ m-base @ mcap between? and ;
: m-open? ( -- flag ) m-live? m-count @ mcap < and m-serial @ max-n <> and ;
: m-new ( -- index true | false )
  m-open? 0= if false exit then
  1 m-serial +! m-serial @ m-count @ cells m-ids + ! m-count @ 1 m-count +! true ;
: m-clear ( -- ) m-base @ m-count ! m-gen @ epoch+ m-gen ! ;
: m-valid? ( index -- flag ) m-live? if 0 m-count @ within else drop false then ;
: m-identity@ ( index -- identity true | false )
  dup m-valid? if cells m-ids + @ true else drop false then ;

: same-fields? ( store -- flag )
  dup store-count @ m-count @ = over store-serial @ m-serial @ = and
  swap store-generation @ m-gen @ = and ;
: norm ( x true | false -- x flag ) dup 0= if -1 swap then ;
: same? ( x1 f1 x2 f2 -- flag ) rot = >r = r> and ;
: check-new ( store -- )
  store-new norm m-new norm same? 0= if s" store-new differs" fail then ;
: check-identity ( index store -- )
  over m-identity@ norm 2>r store-identity@ norm 2r> same?
  0= if s" identity@ differs" fail then ;
: check-valid ( index store -- )
  over m-valid? >r store-valid? r> <> if s" store-valid? differs" fail then ;
: random-op ( store -- )
  20 lm-rnd case
    0 of dup store-clear m-clear endof
    1 of 5 lm-rnd 0= if max-n 2 lm-rnd - 2dup swap store-serial ! m-serial ! then endof
    2 of dup mcap 3 + lm-rnd 1- swap check-valid endof
    3 of dup mcap 3 + lm-rnd 1- swap check-identity endof
    4 of dup mcap 3 + lm-rnd 1- swap check-identity endof
    5 of dup mcap 3 + lm-rnd 1- swap check-valid endof
    drop dup check-new 0
  endcase
  same-fields? 0= if s" store fields differ" fail then ;
: run-store ( store n -- ) 0 ?do dup random-op loop drop ;

mcap /node 0 store: ms0
mcap /node 1 store: ms1
0 m-reset 0 failures !
ms0 3000 run-store
T{ failures @ -> 0 }T
1 m-reset
T{ ms1 store-count-valid? m-live? -> false false }T
ms1 3000 run-store
T{ failures @ -> 0 }T

\ ---------------------------------------------------------------------------
\ Walk model: random DAGs in which node k (k >= 2) has two earlier
\ children. The walk must visit nodes in the visit-order of the recursive
\ definition (second child before first), use one unit of fuel per path,
\ stop with exhausted and fuel 0 when the fuel is short, and in a paired
\ walk reach the deepest context of the recursive definition.

16 constant gmax
create g-first gmax cells allot
create g-second gmax cells allot
: g-first@ ( k -- c ) cells g-first + @ ;
: g-second@ ( k -- c ) cells g-second + @ ;
: random-dag ( n -- ) 2 ?do i lm-rnd i cells g-first + ! i lm-rnd i cells g-second + ! loop ;

create visit-order 2000 cells allot
variable visits
: note ( node -- ) visits @ 2000 < if visits @ cells visit-order + ! then 1 visits +! ;
create expected 2000 cells allot
variable expecting
: expect-node ( node -- ) expecting @ 2000 < if expecting @ cells expected + ! then 1 expecting +! ;

\ The recursive definitions.
: model-visit-order ( k -- ) dup expect-node dup 2 < if drop exit then dup g-second@ recurse g-first@ recurse ;
: paths ( k -- n ) dup 2 < if drop 1 exit then dup g-first@ recurse swap g-second@ recurse + 1+ ;
: deepest ( k depth -- d )
  over 2 < if nip exit then
  2dup swap g-first@ swap recurse >r 1+ swap g-second@ swap recurse r> max ;

: dag-visit ( walk -- outcome )
  dup walk-node @ dup note dup 2 < if 2drop outcome-ok exit then
  dup g-first@ swap g-second@ rot walk-push2 ;
variable max-context
: dag-visit-pair ( walk -- outcome )
  dup walk-context @ max-context @ max max-context !
  dup walk-node @ dup note dup 2 < if 2drop outcome-ok exit then
  dup g-first@ swap g-second@ rot dup walk-context @ 1+ swap walk-children-at ;

gmax 2* walk: gw
gmax 2* walk2: gp
: orders-agree? ( -- flag )
  visits @ expecting @ <> if false exit then
  visits @ 2000 min 0 ?do i cells visit-order + @ i cells expected + @ <>
    if false unloop exit then loop true ;
: check-dag ( n -- )
  dup random-dag 1- ( root )
  0 visits ! 0 expecting ! dup model-visit-order
  dup paths 3 + gw walk-budget drop
  dup ['] dag-visit gw walk-run outcome-ok <> if s" walk outcome" fail then
  gw walk-fuel @ 3 <> if s" walk fuel" fail then
  orders-agree? 0= if s" walk visit-order" fail then
  0 visits ! 0 max-context ! dup paths gp walk-budget drop
  dup 7 ['] dag-visit-pair gp walk-run-pair outcome-ok <> if s" pair outcome" fail then
  gp walk-fuel @ 0<> if s" pair fuel" fail then
  orders-agree? 0= if s" pair visit-order" fail then
  dup 7 deepest max-context @ <> if s" pair depth" fail then
  dup paths 1- gw walk-budget drop
  dup ['] dag-visit gw walk-run outcome-exhausted <> if s" short fuel outcome" fail then
  gw walk-fuel @ 0<> if s" short fuel left" fail then
  drop ;
0 failures !
: run-dags ( -- ) 400 0 do 3 13 lm-rnd + check-dag loop ;
run-dags
T{ failures @ -> 0 }T

\ Stack need. A chain through first children keeps at most two items
\ pending. A chain through second children leaves a pending first child at
\ every level, so from node 9 it needs nine items: capacity 9 suffices and
\ capacity 8 stops with exhausted, never ok.
: chain-first ( n -- ) 2 ?do i 1- i cells g-first + ! 0 i cells g-second + ! loop ;
: chain-second ( n -- ) 2 ?do 0 i cells g-first + ! i 1- i cells g-second + ! loop ;
T{ 2 walk: w2 -> }T  T{ 9 walk: w9 -> }T  T{ 8 walk: w8 -> }T
10 chain-first
1000 w2 walk-budget drop
T{ 9 ' dag-visit w2 walk-run -> outcome-ok }T
10 chain-second
1000 w9 walk-budget drop 1000 w8 walk-budget drop
T{ 9 ' dag-visit w9 walk-run 9 ' dag-visit w8 walk-run -> outcome-ok outcome-exhausted }T
bye
