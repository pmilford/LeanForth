\ Randomized model tests of the general Forth library (src/lib): long
\ random sequences of store operations compared after every step with a
\ simple independent model, random DAG walks compared with recursive
\ definitions of the visit visit-order, the fuel used and the deepest context,
\ and random recursive visits through frame records compared with a direct
\ recursive model. Also direct cases for public words that tests/lib/lib.fs
\ reaches only indirectly. The generator is deterministic and cell-size
\ neutral.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs

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

\ ---------------------------------------------------------------------------
\ Frame model: random DAGs as above, visited recursively through a frames
\ record. The visitor's result for node k at context c is c+1 for a leaf
\ and the sum of its children's results otherwise, the second child one
\ context level deeper. A direct recursive model with explicit fuel and
\ depth counters must agree on the outcome, the result, the fuel left, the
\ deepest frame and the record afterwards, for random fuel and limits
\ (too little of either, a corrupted limit), contexts near max-n, negative
\ fuel and busy records. A second visitor of two values (frame-call2)
\ compares the trees below two nodes.

variable m-fuel  variable m-limit  variable m-deepest
: model-open? ( depth -- flag ) m-limit @ < m-fuel @ 0> and ;
: model-enter ( depth -- depth' ) -1 m-fuel +! 1+ dup m-deepest @ max m-deepest ! ;
\ Node k at context c with d frames in use: its result and true, or false.
: model-frame ( c d k -- r true | false )
  over model-open? 0= if drop 2drop false exit then
  swap model-enter swap dup 2 < if 2drop 1+ true exit then
  >r 2dup r@ g-first@ recurse 0= if 2drop r> drop false exit then
  -rot swap dup max-n = if 2drop drop r> drop false exit then
  1+ swap r> g-second@ recurse if + true else drop false then ;
\ Whether the trees below a and b are equal, d frames in use.
: model-same ( a b d -- outcome )
  dup model-open? 0= if drop 2drop outcome-exhausted exit then model-enter >r
  2dup = if 2drop r> drop outcome-ok exit then
  2dup min 2 < if 2drop r> drop outcome-rejected exit then
  2dup g-first@ swap g-first@ r@ recurse dup ok? 0= if nip nip r> drop exit then drop
  g-second@ swap g-second@ r> recurse ;


\ The words under test: the same results through frame-call, frame-under
\ and frame-call2. f-deepest records the most frames in use at a visit.
variable f-deepest
: f-note ( frames -- ) frame-depth @ f-deepest @ max f-deepest ! ;
: fdag-visit ( k frames -- result outcome )
  dup f-note over 2 < if nip frame-context @ 1+ outcome-ok exit then
  over g-first@ over frame-call ok-keep2? 0= if exit then
  -rot swap g-second@ swap frame-under ok-keep? if + outcome-ok then ;
: fsame-visit ( a b frames -- outcome )
  dup f-note >r 2dup = if 2drop r> drop outcome-ok exit then
  2dup min 2 < if 2drop r> drop outcome-rejected exit then
  2dup g-first@ swap g-first@ r@ frame-call2 dup ok? 0= if nip nip r> drop exit then drop
  g-second@ swap g-second@ r> frame-call2 ;
gmax 1+ ' fdag-visit frames: gf
gmax 1+ ' fsame-visit frames: gs

\ Random parameters: usually enough fuel and frames for the visit, else
\ any amount up to that, or a negative fuel or a limit corrupted to -1; a
\ small context, or one near max-n.
variable p-fuel  variable p-limit  variable p-context  variable m-result
: height ( k -- h ) dup 2 < if drop 1 exit then
  dup g-first@ recurse swap g-second@ recurse max 1+ ;
: some-amount ( need -- n )
  8 lm-rnd ?dup 0= if drop -1 exit then 1 = if 1+ lm-rnd else 3 lm-rnd + then ;
: random-fuel ( k -- fuel ) paths some-amount ;
: random-limit ( k -- limit ) height some-amount ;
: random-context ( -- c ) 4 lm-rnd if 9 lm-rnd else max-n 3 lm-rnd - then ;
: random-params ( k -- )
  dup random-fuel p-fuel ! random-limit p-limit ! random-context p-context ! ;
\ Set both the model and a record to the parameters.
: start ( frames -- )
  p-fuel @ over frame-budget drop p-limit @ swap frame-limit !
  p-fuel @ m-fuel ! p-limit @ m-limit ! 0 m-deepest ! 0 f-deepest ! ;
\ After a pass the record holds the model's fuel, is idle, and its visits
\ went as deep as the model's.
: same-record? ( frames -- flag )
  dup frame-fuel @ m-fuel @ = swap frame-depth @ 0= and f-deepest @ m-deepest @ = and ;
\ A refused budget returns false and stores nothing.
: refused? ( fuel frames -- flag )
  dup frame-fuel @ >r tuck frame-budget 0= swap frame-fuel @ r> = and ;

\ One pass from root: the model's result and ok, or -1 and exhausted.
variable frame-oks  variable frame-fails
: model-run ( root -- flag ) >r p-context @ 0 r> model-frame dup if swap m-result ! then ;
: agree? ( result outcome flag -- flag )
  if ok? swap m-result @ = and 1 frame-oks +!
  else outcome-exhausted = swap -1 = and 1 frame-fails +! then ;
: check-run ( root -- )
  gf start dup model-run >r p-context @ gf frame-run r> agree?
  0= if s" frame result" fail then
  gf same-record? 0= if s" frame record" fail then
  gf frame-context @ p-context @ <> if s" frame context" fail then ;
: check-frame ( root -- )
  dup random-params p-fuel @ 0<
  if drop p-fuel @ gf refused? 0= if s" negative budget" fail then else check-run then ;
\ A busy record refuses a budget and a pass, visiting nothing.
: check-busy ( root frames -- )
  1 over frame-depth !  5 over refused? 0= if s" busy budget" fail then
  0 f-deepest !  tuck 7 swap frame-run outcome-invalid <> swap -1 <> or
  f-deepest @ or if s" busy run" fail then  frame-reset ;
\ Two nodes compared through frame-call2.
create same-counts 6 cells allot  same-counts 6 cells erase
: count-same ( outcome -- ) cells same-counts + 1 swap +! ;
: check-same ( a b -- )
  over random-params p-fuel @ 0< if 2drop exit then
  gs start 2dup 0 model-same >r 0 gs frame-start drop gs frame-call2
  dup count-same r> <> if s" same outcome" fail then
  gs same-record? 0= if s" same record" fail then ;
: some-node ( root -- k ) 1+ lm-rnd ;
: frame-round ( n -- )
  dup random-dag 1- dup check-frame dup check-frame
  8 lm-rnd 0= if dup gf check-busy then
  dup some-node over some-node check-same dup dup some-node check-same drop ;
0 failures !  0 frame-oks !  0 frame-fails !
: run-frames ( -- ) 600 0 do 3 13 lm-rnd + frame-round loop ;
run-frames
T{ failures @ -> 0 }T
\ Every kind of ending was reached.
T{ frame-oks @ 0> frame-fails @ 0> -> true true }T
T{ same-counts @ 0> outcome-rejected cells same-counts + @ 0>
  outcome-exhausted cells same-counts + @ 0> -> true true true }T
bye
