\ Tests of run-time records and checker contexts (src/lib/store.fs,
\ walk.fs, context.fs): store-init and walk-init give byte for byte the
\ records store:, walk: and walk2: give; context members (records, stores,
\ walks, frames records, setup words) are initialised in the main context
\ as they are declared and in every new context; a refused declaration,
\ even one whose memory cannot be allocated, changes nothing, and a setup
\ word that throws is not registered; contexts are independent; ownership
\ limits who may select, claim, release and free a context; call-balanced
\ catches a word with a wrong stack effect, and context-catch restores the
\ current context after a word; teardown words (the release hook) free a
\ member's heap blocks when its context is freed, also after a THROW, a
\ failed context-new or a teardown word that fails, newest first and in
\ the context being freed (heap-watch.fs counts the blocks). A randomized
\ model then runs the same operations on context stores and walks,
\ switching context at every step, and on dictionary records, and
\ compares results and every byte.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
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
\ A context's walks are growable (plan task 6.2.0), like these made so.
dw5 walk-growable dp3 walk-growable
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
T{ s" 0 context-record: cbad7" aborts? -> true }T
T{ context-bytes [undefined] cbad1 [undefined] cbad5 -> bytes-before true true }T
T{ [undefined] cbad7 -> true }T
\ A size that fits a cell but cannot be allocated: the main context
\ cannot grow, and nothing is defined or changed.
T{ s" max-n 4 / context-record: chuge" aborts? [undefined] chuge -> true true }T
T{ context-bytes context-main context? -> bytes-before true }T
T{ lf-context @ context-main = -> true }T
T{ c-rec @ c-terms store-count @ -> 42 1 }T
\ A setup word that throws while it is declared is not registered: new
\ contexts never run it.
variable bad-runs  0 bad-runs !
: c-bad-setup ( -- ) 1 bad-runs +! 66 throw ;
T{ ' c-bad-setup ' context-setup catch nip bad-runs @ -> 66 1 }T
T{ context-bytes -> bytes-before }T
\ Members are laid down aligned whatever HERE was.
1 allot  ' noop context-setup
lf-lib-private order+
T{ context-last @ dup aligned = -> true }T
order-  align

\ A frames record as a member: initialised with frame-init in the main
\ context and in every new one; its visitor reaches it through its
\ frames argument. fr-visit x nests x deep and counts the visits, on the
\ record's stack, which grows (plan task 6.2.0).
: fr-up ( r outcome frames -- r' outcome frames 0 )
  >r ok-then? if 1+ outcome-ok else no-result then r> 0 ;
: fr-visit ( x frames -- ... frames next )
  over 0= if nip 0 outcome-ok rot 0 exit then
  swap 1- swap ['] fr-up frame-call ;
' fr-visit context-frames: c-frames
T{ c-frames frame-visitor @ c-frames frame-block @ -> ' fr-visit 0 }T
T{ c-frames frame-busy? -> false }T
T{ 10 c-frames frame-budget 2 0 c-frames frame-run -> true 2 outcome-ok }T
T{ c-frames frame-fuel @ -> 7 }T
T{ 100 c-frames frame-budget 50 0 c-frames frame-run c-frames frame-fuel @ ->
  true 50 outcome-ok 49 }T

\ allocate0 gives zeroed memory, here most likely the block just freed.
5 cells allocate throw dup 5 cells 165 fill free throw
T{ 5 cells allocate0 swap dup 5 cells-zero? swap free -> 0 true 0 }T

\ A member that owns heap blocks (the release hook): its setup word
\ allocates one, a check may hang a second on it, and its teardown word
\ frees whichever it finds. Two teardown words record the order they ran
\ in (tear-tick), and the later one the context it ran in; on request it
\ throws or leaves an extra item. A setup word declared after the
\ allocating one fails on request, so a failed context-new has a block to
\ give back.
2 cells context-record: c-heap
: c-heap-extra ( -- addr ) c-heap cell+ ;
: c-heap-make ( -- ) 64 allocate throw c-heap ! ;
: c-block-free ( addr -- ) dup @ ?dup if free throw then 0 swap ! ;
: c-heap-free ( -- ) c-heap c-block-free c-heap-extra c-block-free ;
' c-heap-make context-setup
variable late-setup-fails  0 late-setup-fails !
: c-late-setup ( -- ) late-setup-fails @ if 56 throw then ;
' c-late-setup context-setup
variable tear-count  variable early-at  variable late-at  variable tear-context
variable tear-throws  0 tear-throws !  variable tear-unbalance  0 tear-unbalance !
variable tear-careless  0 tear-careless !
variable tear-early-throws  0 tear-early-throws !
: tear-tick ( addr -- ) 1 tear-count +! tear-count @ swap ! ;
\ On request it throws, after it freed what it found.
: c-tear-early ( -- )
  early-at tear-tick c-heap-free tear-early-throws @ ?dup if throw then ;
\ On request it also selects the main context before it throws, as a
\ helper that saves and restores lf-context without CATCH would.
: c-tear-late ( -- )
  late-at tear-tick lf-context @ tear-context ! tear-unbalance @ if 1 then
  tear-careless @ if context-main lf-context ! then tear-throws @ ?dup if throw then ;
' c-tear-early context-teardown
' c-tear-late context-teardown

\ Model-test members (see the end of this file).
6 constant mcap
8 constant mwalk
mcap /node 0 context-store: m-store
mwalk context-walk: m-walk
\ Growable arrays, empty (no heap block) until reserved.
1 cells context-slab: m-slab
2 cells context-slab: m-slab2

\ ---------------------------------------------------------------------------
\ New contexts: fresh members, sealed layout, independent state.
T{ context-new swap constant ctx1 -> 0 }T
T{ context-sealed? ctx1 context? ctx1 context-main = -> true true false }T
T{ lf-context @ context-main = setups @ -> true 2 }T
T{ s" 1 cells context-record: clate" aborts? [undefined] clate -> true true }T
T{ ctx1 ' context-use rs-checked lf-context @ -> ctx1 }T
T{ c-rec @ c-terms store-count @ c-late @ -> 0 0 0 }T
T{ c-runs @ c-levels store-count-valid? bad-runs @ -> 1 true 1 }T
T{ terms-pristine? walks-pristine? -> true true }T
T{ c-frames frame-block @ c-frames frame-fuel @ -> 0 0 }T
T{ c-frames frame-visitor @ -> ' fr-visit }T
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

\ Ownership (task.fs claims a job's context): only an idle context other
\ than the main and the current one can be claimed, by a nonzero token.
\ An owned context is selected only under its owner's token and cannot be
\ freed; under a nonzero token (inside a job) no context can be made,
\ freed, claimed or released and no other context selected.
: free-fails? ( addr -- flag ) ['] context-free catch dup if nip then 0<> ;
: new-fails? ( -- flag ) ['] context-new catch 0<> ;
: release-fails? ( addr -- flag ) ['] context-release catch dup if nip then 0<> ;
\ context-claim's flag and the THROW code it raised (0 for none).
: claim-caught ( owner addr -- flag ior )
  ['] context-claim catch dup if nip nip 0 swap then ;
\ An address no process can read on Linux (the first page is never mapped).
8 constant unreadable
context-new throw constant ctx2
T{ 7 context-main context-claim 7 junk context-claim -> false false }T
T{ 7 0 context-claim -> false }T
T{ 7 ctx1 context-claim ctx1 context-idle? -> false true }T
T{ 7 ctx2 context-claim ctx2 context-idle? 8 ctx2 context-claim -> true false false }T
T{ ctx2 use-fails? ctx2 free-fails? lf-context @ ctx1 = -> true true true }T
T{ context-in-job? -> false }T
7 lf-owner !
T{ context-in-job? ctx2 ' context-use rs-checked lf-context @ ctx2 = -> true true }T
T{ ctx1 use-fails? context-main use-fails? -> true true }T
T{ new-fails? ctx1 free-fails? -> true true }T
T{ lf-context @ ctx2 = -> true }T
\ Nor can a job claim another context or release its own (the review's
\ M1): claiming gives false and releasing aborts, changing nothing.
T{ 7 ctx1 context-claim ctx2 release-fails? -> false true }T
T{ ctx1 context-idle? ctx2 context-owner @ -> true 7 }T
\ The claim is refused before the address is read (the fifth review's
\ probe p10): false even for an address that cannot be read.
T{ 7 unreadable claim-caught -> false 0 }T
\ A check run outside the job pool holds context-check-owner: it counts as
\ inside a job, and no context is its own, not even the current one.
context-check-owner lf-owner !
T{ context-in-job? context-check-owner 0= -> true false }T
T{ ctx2 use-fails? ctx1 use-fails? context-main use-fails? -> true true true }T
T{ new-fails? ctx1 free-fails? lf-context @ ctx2 = -> true true true }T
\ Such a check claims and releases nothing either (probes p1 and p5).
T{ context-check-owner ctx1 context-claim ctx2 release-fails? -> false true }T
T{ ctx1 context-idle? ctx2 context-owner @ -> true 7 }T
T{ context-check-owner unreadable claim-caught -> false 0 }T
0 lf-owner !  ctx1 context-use
T{ ctx2 context-release ctx2 context-idle? ctx2 context-free -> true 0 }T

\ call-balanced runs a word above a cell and throws context-unbalanced
\ when the word changed the stack depth or that cell; another THROW
\ passes through. The cells below stay as they were.
: balanced-ior ( xt -- ior ) 7 swap ['] call-balanced catch dup if nip nip then ;
: c-keeps ( -- ) ;
: c-leaves ( -- x ) 1 ;
: c-eats ( x -- ) drop ;
: c-swaps ( x -- y ) drop 8 ;
: c-throws ( -- ) 55 throw ;
T{ context-unbalanced ' c-keeps balanced-ior ' c-leaves balanced-ior -> -4096 0 context-unbalanced }T
T{ ' c-eats balanced-ior ' c-swaps balanced-ior -> context-unbalanced context-unbalanced }T
T{ 1 2 ' c-throws balanced-ior 3 ' c-keeps balanced-ior -> 1 2 55 3 0 }T
T{ true ?call-balanced false ' ?call-balanced catch nip -> context-unbalanced }T

\ context-catch is CATCH that restores the current context afterwards,
\ whether the word returned or threw.
: c-select-throw ( context -- ) context-use 56 throw ;
T{ lf-context @ context-main ' context-use context-catch lf-context @ rot = -> 0 true }T
T{ 1 2 context-main ' c-select-throw context-catch nip lf-context @ ctx1 = -> 1 2 56 true }T

\ Freeing: the main context and non-contexts abort; freeing the current
\ context returns the task to the main one.
: free-aborts? ( addr -- flag ) ['] context-free catch if drop true else drop false then ;
T{ context-main free-aborts? junk free-aborts? -> true true }T
T{ ctx1 ' context-free rs-checked lf-context @ context-main = -> 0 true }T
T{ context-new drop context-free -> 0 }T

\ ---------------------------------------------------------------------------
\ The release hook. A teardown is refused once the layout is sealed. A new
\ context holds two blocks, its own and c-heap's, and a third once a pass
\ has run on its frames; freeing it gives them all back, after running the
\ teardown words newest first in that context.
T{ s" ' noop context-teardown" aborts? -> true }T
live-blocks @ constant blocks-before
: blocks-held ( -- n ) live-blocks @ blocks-before - ;
0 tear-count !
context-new throw constant ctx3
T{ blocks-held -> 2 }T
ctx3 context-use
T{ c-heap @ 0<> c-heap-extra @ -> true 0 }T
10 c-frames frame-budget drop  2 0 c-frames frame-run 2drop
T{ blocks-held -> 3 }T
context-main context-use
T{ ctx3 ' context-free rs-checked blocks-held -> 0 0 }T
T{ late-at @ early-at @ -> 1 2 }T
T{ tear-context @ ctx3 = lf-context @ context-main = -> true true }T
\ Freeing the current context: the teardown words still see it, and the
\ task returns to the main context.
context-new throw constant ctx5
ctx5 context-use
T{ ctx5 context-free blocks-held -> 0 0 }T
T{ lf-context @ context-main = tear-context @ ctx5 = -> true true }T
\ A check that throws after its member grew a second block: freeing the
\ context afterwards gives every block back.
: c-grow-throw ( context -- )
  context-use c-heap @ 4096 resize throw c-heap !
  32 allocate throw c-heap-extra ! 77 throw ;
context-new throw constant ctx4
T{ ctx4 ' c-grow-throw context-catch nip lf-context @ context-main = -> 77 true }T
T{ blocks-held -> 3 }T
T{ ctx4 context-free blocks-held -> 0 0 }T
\ A teardown word that throws, or leaves an extra item, does not stop the
\ others or keep the context's block: context-free gives its code.
91 tear-throws !
T{ context-new throw context-free blocks-held -> 91 0 }T
0 tear-throws !  true tear-unbalance !
T{ context-new throw context-free blocks-held -> context-unbalanced 0 }T
false tear-unbalance !
\ One that throws with the main context selected: the next still frees
\ the freed context's block, never the main context's.
c-heap @ constant main-heap
92 tear-throws !  true tear-careless !
T{ context-new throw context-free blocks-held c-heap @ main-heap = -> 92 0 true }T
0 tear-throws !  false tear-careless !
\ A setup word that fails after another allocated: context-new gives
\ that block back through the teardown words.
1 late-setup-fails !
T{ context-new blocks-held -> 0 56 0 }T
0 late-setup-fails !
\ Two teardown words that throw different codes: context-free gives the
\ code of the one that ran first, the newest (the context review's L1).
91 tear-throws !  93 tear-early-throws !
T{ context-new throw context-free blocks-held -> 91 0 }T
\ A setup word and a teardown word that both throw in context-new: it
\ gives the setup word's code, which came first, and holds no block.
1 late-setup-fails !
T{ context-new blocks-held -> 0 56 0 }T
0 late-setup-fails !  0 tear-throws !  0 tear-early-throws !
\ A context's walk grown past its first room into a heap block: freeing
\ the context gives that block back too (walks-free).
: m-walk-fill ( n -- ) 0 ?do i m-walk walk-push drop loop ;
context-new throw constant ctx6
ctx6 context-use  mwalk 2* m-walk-fill
T{ m-walk walk-pending @ m-walk walk-heap @ 0<> blocks-held -> mwalk 2* true 3 }T
context-main context-use
T{ ctx6 context-free blocks-held -> 0 0 }T
\ A context's slab member reserved into a heap block: freeing the context
\ gives it back (slabs-free; the item-1 review's L1).
context-new throw constant ctx7
ctx7 context-use
T{ m-slab slab-count m-slab slab-capacity blocks-held -> 0 0 2 }T
T{ 100 m-slab slab-reserve m-slab slab-capacity 99 > blocks-held -> outcome-ok true 3 }T
\ Both slab members, the older and the newer: every listed member is freed
\ (listed-each; the item-2 review's L2).
T{ 10 m-slab2 slab-reserve blocks-held -> outcome-ok 4 }T
context-main context-use
T{ ctx7 context-free blocks-held -> 0 0 }T

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
\ A context's walks are growable (plan task 6.2.0); so are the references.
wref0 walk-growable wref1 walk-growable wref2 walk-growable wpristine walk-growable
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
cm-walks-ok @ . ." walks ok, " cm-walks-short @ . ." exhausted or full, "
cm-failures @ . ." differences" cr
\ The comparison catches a planted fault: one reset applied to a context
\ store but not to its reference.
0 ctx-slot @ context-use m-store store-clear 0 cm-compare context-main context-use
T{ cm-failures @ -> 1 }T
cm-free
T{ lf-context @ context-main = blocks-held -> true 0 }T
T{ depth -> 0 }T
bye
