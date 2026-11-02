\ Tests of run-time records and checker contexts (src/lib/store.fs,
\ walk.fs, context.fs): store-init and walk-init give byte for byte the
\ records store:, walk: and walk2: give; context members are initialised in
\ the main context as they are declared and in every new context; contexts
\ are independent. A randomized model then runs the same operations on
\ context stores and walks, switching context at every step, and on
\ dictionary records, and compares results and every byte.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs

: same-bytes? ( addr1 addr2 u -- flag ) tuck compare 0= ;
: aborts? ( addr u -- flag ) ['] evaluate catch dup if nip nip then 0<> ;
create junk 64 cells allot
: junk! ( -- ) junk 64 cells 165 fill ;
create junk-copy 64 cells allot  junk-copy 64 cells 165 fill
: junk-intact? ( -- flag ) junk junk-copy 64 cells same-bytes? ;

\ ---------------------------------------------------------------------------
\ Store plans and sizes.
T{ 3 /node store-size -> store-header 3 /node cell+ * + }T
T{ 0 /node store-size -> store-header }T
T{ 3 /node 0 store-plan? 3 /node 3 store-plan? 0 /node 0 store-plan? -> true true true }T
T{ -1 /node 0 store-plan? 2 /node 3 store-plan? -> false false }T
T{ 2 /node -1 store-plan? -> false }T
T{ 2 0 0 store-plan? 2 /node 1+ 0 store-plan? 2 -8 0 store-plan? -> false false false }T
max-n store-header - /node cell+ / constant cap-max
T{ cap-max /node 0 store-plan? cap-max 1+ /node 0 store-plan? -> true false }T
T{ cap-max /node store-size 0> max-n /node 0 store-plan? -> true false }T
T{ 3 /node 1 ' store-plan? rs-checked 2 0 0 ' store-plan? rs-checked -> true false }T

\ store-init over junk gives the bytes of store:, and the store works the
\ same; an unsound shape gives false and writes nothing.
4 /node 1 store: d4
create b4 4 /node store-size allot  b4 4 /node store-size 165 fill
T{ 4 /node 1 b4 ' store-init rs-checked -> true }T
T{ d4 b4 4 /node store-size same-bytes? -> true }T
T{ b4 store-count-valid? b4 store-new -> false false }T
d4 store-clear b4 store-clear
T{ 7 8 9 d4 node-new 7 8 9 b4 node-new -> 1 true 1 true }T
T{ 1 b4 node-read 1 b4 store-identity@ -> 7 8 9 true 1 true }T
T{ d4 b4 4 /node store-size same-bytes? -> true }T
junk!
T{ -1 /node 0 junk ' store-init rs-checked junk-intact? -> false true }T
T{ 2 /node 3 junk store-init 2 0 0 junk store-init -> false false }T
T{ 2 /node 1+ 0 junk store-init max-n /node 0 junk store-init -> false false }T
T{ cap-max 1+ /node 0 junk store-init junk-intact? -> false true }T
\ A store over exactly its size leaves the bytes after it alone.
3 /node store-size constant s3
junk!
T{ 3 /node 0 junk store-init -> true }T
T{ junk s3 + junk-copy s3 + 64 cells s3 - same-bytes? -> true }T

\ ---------------------------------------------------------------------------
\ Walk plans and sizes.
T{ 5 walk-size 5 walk2-size -> 5 walk-bytes 10 walk-bytes }T
T{ 1 1 walk-plan? 0 1 walk-plan? -1 2 walk-plan? -> true false false }T
max-n walk-header - 1 cells / constant walk-max
T{ walk-max 1 walk-plan? walk-max 1+ 1 walk-plan? -> true false }T
T{ walk-max 2 walk-plan? -> false }T
5 walk: dw5
3 walk2: dp3
junk!
T{ 5 junk ' walk-init rs-checked junk dw5 5 walk-size same-bytes? -> true true }T
junk!
T{ 3 junk ' walk2-init rs-checked junk dp3 3 walk2-size same-bytes? -> true true }T
T{ junk walk-capacity @ junk walk-width @ junk walk-pending @ -> 6 2 0 }T
junk!
T{ 0 junk walk-init -1 junk walk2-init walk-max 1+ junk walk-init -> false false false }T
T{ 0 junk ' walk-init rs-checked junk-intact? -> false true }T
\ A run-time walk record walks like a dictionary one.
: fib-visit ( walk -- outcome )
  dup walk-node @ dup 2 < if 2drop outcome-ok else dup 1- swap 2 - rot walk-push2 then ;
8 junk walk-init drop
100 junk walk-budget drop
T{ 5 ' fib-visit junk walk-run junk walk-fuel @ -> outcome-ok 85 }T

\ ---------------------------------------------------------------------------
\ Declaring context members. The main context is selected from the start;
\ each declaration grows it and initialises the new member in it.
T{ lf-context @ context-main = context-main context? context-sealed? -> true true false }T
T{ 0 context? junk context? -> false false }T
3 cells context-record: c-rec
4 /node 0 context-store: c-terms
2 /node 1 context-store: c-levels
5 context-walk: c-walk
3 context-walk2: c-pairs
4 /node 0 store: d-terms
: terms-pristine? ( -- flag ) c-terms d-terms 4 /node store-size same-bytes? ;
: walks-pristine? ( -- flag )
  c-walk dw5 5 walk-size same-bytes? c-pairs dp3 3 walk2-size same-bytes? and ;
T{ c-rec @ c-rec cell+ @ c-rec 2 cells + @ -> 0 0 0 }T
T{ terms-pristine? walks-pristine? c-levels store-count-valid? -> true true false }T
T{ c-rec c-terms < c-terms c-levels < -> true true }T
T{ c-levels c-walk < c-walk c-pairs < -> true true }T
T{ c-pairs 3 walk2-size + lf-context @ context-bytes + > -> false }T
T{ c-rec lf-context @ - /context-header < c-rec aligned c-rec = -> false true }T

\ A later declaration keeps the main context's contents, wherever it moves.
42 c-rec !  c-terms store-new 2drop
1 cells context-record: c-late
T{ c-rec @ c-terms store-count @ c-late @ lf-context @ context-main = -> 42 1 0 true }T

\ Setup words run at once in the main context, and in every new context.
variable setups  0 setups !
1 cells context-record: c-runs
: c-setup ( -- ) c-levels store-clear 1 c-runs +! 1 setups +! ;
' c-setup context-setup
T{ setups @ c-runs @ c-levels store-count-valid? -> 1 1 true }T
variable hook-fails  0 hook-fails !
: c-maybe-fail ( -- ) hook-fails @ if 55 throw then ;
' c-maybe-fail context-setup

\ Bad declarations abort and define nothing.
context-bytes constant bytes-before
T{ s" -1 /node 0 context-store: cbad1" aborts? -> true }T
T{ s" 2 /node 3 context-store: cbad2" aborts? -> true }T
T{ s" 0 context-walk: cbad3" aborts? s" 0 context-walk2: cbad4" aborts? -> true true }T
T{ s" -1 context-record: cbad5" aborts? -> true }T
T{ s" max-n context-record: cbad6" aborts? -> true }T
T{ context-bytes [undefined] cbad1 [undefined] cbad5 -> bytes-before true true }T

\ Model-test members (see the end of this file).
6 constant mcap
8 constant mwalk
mcap /node 0 context-store: m-store
mwalk context-walk: m-walk

\ ---------------------------------------------------------------------------
\ New contexts: fresh members, sealed layout, independent state.
T{ context-new swap constant ctx1 -> 0 }T
T{ context-sealed? ctx1 context? ctx1 context-main = -> true true false }T
T{ lf-context @ context-main = setups @ -> true 2 }T
T{ s" 1 cells context-record: clate" aborts? [undefined] clate -> true true }T
T{ ctx1 ' context-use rs-checked lf-context @ -> ctx1 }T
T{ c-rec @ c-terms store-count @ c-late @ -> 0 0 0 }T
T{ c-runs @ c-levels store-count-valid? -> 1 true }T
T{ terms-pristine? walks-pristine? -> true true }T
7 c-rec !  c-terms store-new 2drop c-terms store-new 2drop
context-main context-use
T{ c-rec @ c-terms store-count @ -> 42 1 }T
ctx1 context-use
T{ c-rec @ c-terms store-count @ -> 7 2 }T

\ A failing setup word: no context, the THROW code, the current context kept.
1 hook-fails !
T{ lf-context @ ' context-new rs-checked rot lf-context @ = -> 0 55 true }T
0 hook-fails !

\ Selecting anything but a context aborts and keeps the current one.
: use-fails? ( addr -- flag ) ['] context-use catch dup if nip then 0<> ;
T{ junk use-fails? 0 use-fails? lf-context @ ctx1 = -> true true true }T

\ Freeing: the main context and non-contexts abort; freeing the current
\ context returns the task to the main one.
: free-aborts? ( addr -- flag ) ['] context-free catch if drop true else drop false then ;
T{ context-main free-aborts? junk free-aborts? -> true true }T
T{ ctx1 ' context-free rs-checked lf-context @ context-main = -> 0 true }T
T{ context-new drop context-free -> 0 }T

\ ---------------------------------------------------------------------------
\ Randomized model: three contexts, each with a store and a walk record,
\ and three dictionary stores and walks as the reference. Every step picks
\ a context, selects it, and applies one random operation to its members
\ and to the reference: allocate, reset, look up an index near the valid
\ range, nearly spend the serial, walk a fixed random DAG from a random
\ root with random fuel, or replace the context by a new one (and the
\ reference by a pristine copy). After every step both must match byte for
\ byte, and every result must agree.
variable cm-seed  2718 cm-seed !
: cm-rnd ( n -- r )
  cm-seed @ 1103515245 * 12345 + dup cm-seed ! 16 rshift 32767 and swap mod ;
3 constant ctxs
create cm-contexts ctxs cells allot
mcap /node 0 store: ref0   mcap /node 0 store: ref1   mcap /node 0 store: ref2
mcap /node 0 store: pristine
mwalk walk: wref0   mwalk walk: wref1   mwalk walk: wref2
mwalk walk: wpristine
create refs ref0 , ref1 , ref2 ,
create wrefs wref0 , wref1 , wref2 ,
: ref-of ( k table -- x ) swap cells + @ ;
: ctx-slot ( k -- addr ) cells cm-contexts + ;
variable cm-failures  variable cm-steps  variable cm-renewals
variable cm-walks-ok  variable cm-walks-short
: cm-fail ( -- ) 1 cm-failures +! ;

\ The DAG: node n >= 2 has two earlier children.
16 constant gmax
create g-first gmax cells allot  create g-second gmax cells allot
: g-child! ( k -- ) dup cm-rnd over cells g-first + ! dup cm-rnd swap cells g-second + ! ;
: random-dag ( -- ) gmax 2 ?do i g-child! loop ;
random-dag
: dag-visit ( walk -- outcome )
  dup walk-node @ dup 2 < if 2drop outcome-ok exit then
  dup cells g-first + @ swap cells g-second + @ rot walk-push2 ;

\ Operations on the current context's members and on the reference.
: norm ( x true | false -- x flag ) dup 0= if -1 swap then ;
: same? ( x1 f1 x2 f2 -- flag ) rot = >r = r> and ;
: op-new ( ref -- ) store-new norm m-store store-new norm same? 0= if cm-fail then ;
: op-clear ( ref -- ) store-clear m-store store-clear ;
: op-lookup ( ref -- )
  mcap 3 + cm-rnd 1- tuck swap store-identity@ norm rot m-store store-identity@ norm
  same? 0= if cm-fail then ;
: op-spend ( ref -- ) max-n 2 cm-rnd - tuck swap store-serial ! m-store store-serial ! ;
: tally ( outcome -- outcome )
  dup ok? if 1 cm-walks-ok +! else 1 cm-walks-short +! then ;
: walk-one ( root fuel walk -- outcome fuel-left )
  tuck walk-budget drop tuck ['] dag-visit swap walk-run swap walk-fuel @ ;
: op-walk ( wref -- )
  gmax cm-rnd 200 cm-rnd 2dup m-walk walk-one 2>r rot walk-one
  2r> over tally drop d= 0= if cm-fail then ;
: op-renew ( k -- )
  dup ctx-slot @ context-free throw context-new throw dup context-use over ctx-slot !
  pristine over refs ref-of mcap /node store-size move
  wpristine swap wrefs ref-of mwalk walk-size move 1 cm-renewals +! ;
: cm-op ( k -- )
  12 cm-rnd case
    0 of refs ref-of op-clear endof
    1 of refs ref-of op-lookup endof
    2 of 5 cm-rnd 0= if refs ref-of op-spend else drop then endof
    3 of wrefs ref-of op-walk endof
    4 of wrefs ref-of op-walk endof
    5 of 9 cm-rnd 0= if op-renew else drop then endof
    swap refs ref-of op-new endcase ;
: cm-compare ( k -- )
  dup refs ref-of m-store mcap /node store-size same-bytes? 0= if cm-fail then
  wrefs ref-of m-walk mwalk walk-size same-bytes? 0= if cm-fail then ;
: cm-step ( -- )
  ctxs cm-rnd dup ctx-slot @ context-use dup cm-op cm-compare 1 cm-steps +! ;
: cm-setup ( -- ) ctxs 0 ?do context-new throw i ctx-slot ! loop ;
: cm-run ( n -- ) 0 ?do cm-step loop context-main context-use ;
: cm-free ( -- ) ctxs 0 ?do i ctx-slot @ context-free throw loop ;

cm-setup
T{ 6000 ' cm-run rs-checked cm-failures @ -> 0 }T
T{ cm-walks-ok @ 0> cm-walks-short @ 0> cm-renewals @ 0> -> true true true }T
." context model: seed 2718, " cm-steps @ . ." steps, " cm-renewals @ . ." new contexts, "
cm-walks-ok @ . ." walks ok, " cm-walks-short @ . ." exhausted, "
cm-failures @ . ." differences" cr
\ The comparison catches a planted fault: one reset applied to a context
\ store but not to its reference.
0 ctx-slot @ context-use m-store store-clear 0 cm-compare context-main context-use
T{ cm-failures @ -> 1 }T
cm-free
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T
bye
