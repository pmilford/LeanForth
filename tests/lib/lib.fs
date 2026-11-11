\ Unit tests of the general Forth library (src/lib): portability words,
\ range checks, bounded stores, tagged nodes, outcomes, walk and frame
\ records, and packed 32-bit fields. T{ }T checks results and data-stack
\ depth; rs-checked also checks the return stack around a call.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
require ../../src/lib/lib.fs

\ Portability: comparisons and the largest cell.
T{ 2 1 >= -> true }T
T{ 1 2 >= -> false }T
T{ 1 1 <= -> true }T
T{ 0 0<= -> true }T
T{ 1 0<= -> false }T
T{ max-n 0> max-n 1+ 0< -> true true }T

\ between? and upto?: inclusive, signed, and never wrapping around.
T{ 3 1 5 between? -> true }T
T{ 1 1 5 between? 5 1 5 between? -> true true }T
T{ 0 1 5 between? 6 1 5 between? -> false false }T
T{ 3 5 1 between? -> false }T
T{ max-n 0 max-n between? -1 0 max-n between? -> true false }T
T{ 2 0 7 ' between? rs-checked -> true }T
T{ 0 0 upto? -> true }T
T{ 5 5 upto? -> true }T
T{ 6 5 upto? -> false }T
T{ -1 5 upto? -> false }T
T{ max-n max-n upto? -> true }T
T{ -1 max-n upto? -> false }T
T{ 0 -1 upto? -> false }T
T{ 3 -5 upto? max-n -5 upto? -> false false }T
T{ 3 7 ' upto? rs-checked -> true }T

\ cells-zero?: any nonzero cell in range makes it false.
create zero-cells 3 cells allot
zero-cells 3 cells erase
T{ zero-cells 3 cells-zero? -> true }T
T{ zero-cells 0 cells-zero? -> true }T
T{ zero-cells -1 cells-zero? -> true }T
7 zero-cells 2 cells + !
T{ zero-cells 3 cells-zero? -> false }T
T{ zero-cells 2 cells-zero? -> true }T
T{ zero-cells 3 ' cells-zero? rs-checked -> false }T

\ epoch+: grows by one, saturates to -1, and a negative value stays.
T{ 0 epoch+ -> 1 }T
T{ max-n epoch+ -> -1 }T
T{ -1 epoch+ -> -1 }T
T{ -5 epoch+ -> -5 }T

\ Defining stores: shape fields set, counters zero, layout as documented.
T{ 3 /node 0 store: s0 -> }T
T{ 2 /node 1 store: s1 -> }T
T{ s0 store-capacity @ s0 store-width @ s0 store-base @ -> 3 /node 0 }T
T{ s0 store-count @ s0 store-generation @ s0 store-serial @ -> 0 0 0 }T
T{ s0 store-bytes -> 3 /node cell+ * }T
T{ s0 store-records s0 store-identities - -> 3 cells }T
T{ 1 s0 store-slot 0 s0 store-slot - -> /node }T
T{ 0 s0 store-slot s0 store-records = -> true }T
T{ s1 s0 store-records 3 /node * + u< -> false }T
T{ s0 store-count-valid? -> true }T
T{ s1 store-count-valid? -> false }T
T{ s1 store-new -> false }T
T{ s1 store-serial @ -> 0 }T

\ A bad shape aborts the definition: negative capacity, base above
\ capacity, a zero or unaligned width.
\ CATCH leaves the string only when the definition throws.
: bad-store? ( addr u -- flag ) ['] evaluate catch dup if nip nip then 0<> ;
T{ s" -1 /node 0 store: bad1" bad-store? -> true }T
T{ s" 2 /node 3 store: bad2" bad-store? -> true }T
T{ s" 2 0 0 store: bad3" bad-store? -> true }T
T{ s" 2 /node 1+ 0 store: bad4" bad-store? -> true }T
T{ s" 0 /node 0 store: empty0" bad-store? -> false }T

\ Allocation: indices in order, identities from the serial, nothing changes
\ when the store is full.
T{ s0 ' store-new rs-checked -> 0 true }T
T{ s0 store-new -> 1 true }T
T{ s0 store-new -> 2 true }T
T{ s0 store-new -> false }T
T{ s0 store-count @ s0 store-serial @ -> 3 3 }T
T{ 0 2 s0 store-pair-valid? 0 3 s0 store-pair-valid? 3 0 s0 store-pair-valid? -> true false false }T
T{ 0 s0 store-identity@ -> 1 true }T
T{ 2 s0 ' store-identity@ rs-checked -> 3 true }T
T{ 3 s0 store-identity@ -> false }T
T{ -1 s0 store-valid? -> false }T
T{ 2 s0 store-valid? -> true }T
T{ 3 s0 store-valid? -> false }T

\ A reset empties the store and advances the generation; identities are
\ never reused.
s0 store-clear
T{ s0 store-count @ s0 store-generation @ s0 store-serial @ -> 0 1 3 }T
T{ 0 s0 store-valid? -> false }T
T{ s0 store-new -> 0 true }T
T{ 0 s0 store-identity@ -> 4 true }T

\ A store with base 1 keeps record 0, and its identity, through a reset.
s1 ' store-clear rs-checked
T{ s1 store-count @ s1 store-count-valid? -> 1 true }T
0 s1 store-identity @ constant s1-identity0
s1 store-clear
T{ 0 s1 store-identity@ -> s1-identity0 true }T
T{ 0 s1 store-valid? -> true }T
T{ s1 store-new -> 1 true }T
T{ s1 store-new -> false }T

\ A spent serial refuses allocation and changes nothing.
s0 store-clear
max-n s0 store-serial !
T{ s0 store-spent? -> true }T
T{ s0 store-new -> false }T
T{ s0 store-count @ s0 store-serial @ -> 0 max-n }T

\ A saturated generation poisons the store, and it stays poisoned.
0 s0 store-serial !
max-n s0 store-generation !
s0 store-clear
T{ s0 store-generation @ -> -1 }T
T{ s0 store-count-valid? -> false }T
T{ s0 store-new -> false }T
T{ s0 store-serial @ -> 0 }T
s0 store-clear
T{ s0 store-generation @ -> -1 }T

\ Corrupted counts fail closed before any record is addressed.
0 s0 store-generation !
-1 s0 store-count !
T{ s0 store-count-valid? -> false }T
T{ 0 s0 store-valid? -> false }T
T{ s0 store-new -> false }T
T{ 0 s0 store-identity@ -> false }T
4 s0 store-count !
T{ s0 store-count-valid? -> false }T
T{ 3 s0 store-valid? -> false }T
T{ s0 store-new -> false }T
T{ s0 store-count @ -> 4 }T

\ A corrupted shape field breaks the seal: every check fails closed and
\ nothing is allocated, until the field is restored.
0 s0 store-count !
: shape-broken? ( store -- flag )
  dup store-count-valid? swap store-new if drop true else false then or 0= ;
1000 s0 store-capacity !
T{ s0 shape-broken? -> true }T
3 s0 store-capacity !
T{ s0 store-count-valid? -> true }T
2 s0 store-base !
T{ s0 shape-broken? -> true }T
0 s0 store-base !
/node 2* s0 store-width !
T{ s0 shape-broken? -> true }T
/node s0 store-width !
T{ s0 store-count-valid? -> true }T
T{ s0 store-count @ -> 0 }T
\ The block and the limit are shape fields too.
s0 store-limit @ 1+ s0 store-limit !
T{ s0 shape-broken? -> true }T
s0 store-limit @ 1- s0 store-limit !
1 s0 store-block !
T{ s0 shape-broken? -> true }T
0 s0 store-block !
T{ s0 store-count-valid? -> true }T
\ A store made in place never grows: full when every record is used.
T{ s0 store-heap? s0 store-grow -> false outcome-ok }T

\ Heap stores (plan task 1.1.5): a header in the caller's memory, a block
\ on the heap that grows by doubling up to the limit, records and
\ identities kept, marks valid across growth; then full at the limit.
create h0 store-header allot
T{ 2 /node 0 h0 store-heap-init -> outcome-ok }T
T{ h0 store-heap? h0 store-capacity @ h0 store-limit @ h0 store-count @ -> true 2 2 0 }T
T{ 1 2 3 h0 node-new 4 5 6 h0 node-new -> 0 true 1 true }T
T{ h0 store-grow 7 8 9 h0 node-new -> outcome-full false }T
T{ 1 h0 store-limit! -> outcome-invalid }T
T{ 40 h0 store-limit! h0 store-limit @ h0 store-capacity @ -> outcome-ok 40 2 }T
create hm /store-mark allot
T{ hm h0 store-mark -> outcome-ok }T
: h0-fill ( n -- ) 0 ?do h0 store-grow drop i dup dup h0 node-new 2drop loop ;
T{ 38 h0-fill h0 store-count @ h0 store-capacity @ -> 40 40 }T
T{ h0 store-grow 1 1 1 h0 node-new -> outcome-full false }T
T{ 0 h0 node-read 1 h0 node-read 39 h0 node-read -> 1 2 3 true 4 5 6 true 37 37 37 true }T
T{ 0 h0 store-identity@ 39 h0 store-identity@ -> 1 true 40 true }T
T{ hm h0 store-rollback h0 store-count @ h0 store-capacity @ -> outcome-ok 2 40 }T
\ A smaller limit shrinks the block, keeping the records in use.
T{ 2 h0 store-limit! h0 store-capacity @ 1 h0 node-read -> outcome-ok 2 4 5 6 true }T
T{ h0 ' store-grow rs-checked -> outcome-full }T
h0 store-heap-free
T{ h0 store-heap? h0 store-count-valid? h0 store-grow -> false false outcome-invalid }T
T{ 0 /node 3 h0 store-heap-init h0 store-heap? -> outcome-invalid false }T

\ store-poison: empty and permanently invalid.
s0 store-poison
T{ s0 store-count @ s0 store-generation @ -> 0 -1 }T
T{ 1 2 3 s0 node-new -> false }T

\ Tagged nodes: three named cells, whole-node store and fetch.
create n1 /node allot
T{ /node -> 3 cells }T
T{ 7 8 9 n1 node! n1 node@ -> 7 8 9 }T
T{ 1 2 3 n1 ' node! rs-checked n1 ' node@ rs-checked -> 1 2 3 }T
7 8 9 n1 node!
T{ n1 node-tag @ n1 node-first @ n1 node-second @ -> 7 8 9 }T

\ node-new and node-read on a store of nodes, including a full store and
\ invalid indices.
T{ 2 /node 0 store: s2 -> }T
T{ 1 2 3 s2 node-new -> 0 true }T
T{ 4 5 6 s2 ' node-new rs-checked -> 1 true }T
T{ 7 8 9 s2 node-new -> false }T
T{ s2 store-count @ s2 store-serial @ -> 2 2 }T
T{ 0 s2 node-read -> 1 2 3 true }T
T{ 1 s2 ' node-read rs-checked -> 4 5 6 true }T
T{ 2 s2 node-read -> false }T
T{ -1 s2 node-read -> false }T

\ Outcomes: the vocabulary, the sanitizer and the flag conversion.
T{ outcome-ok outcome-invalid outcome-exhausted -> 0 1 2 }T
T{ outcome-unknown outcome-rejected outcome-unsupported outcome-full -> 3 4 5 6 }T
T{ 0 outcome? 6 outcome? -1 outcome? 7 outcome? -> true true false false }T
T{ 3 outcome-sane 6 outcome-sane 7 outcome-sane -1 outcome-sane true outcome-sane ->
  3 6 1 1 1 }T
T{ outcome-full ok? outcome-exhausted ok? -> false false }T
T{ outcome-ok ok? outcome-unknown ok? -> true false }T
T{ true flag>outcome false flag>outcome -> outcome-ok outcome-invalid }T
\ room>outcome: only a true flag is room. visit-outcome: no fuel (zero or
\ negative) is exhausted whatever the room; with fuel, the room decides.
T{ true room>outcome false room>outcome 1 room>outcome -> outcome-ok outcome-full 6 }T
T{ 1 true visit-outcome 1 false visit-outcome max-n true visit-outcome ->
  outcome-ok outcome-full outcome-ok }T
T{ 0 true visit-outcome 0 false visit-outcome -1 false visit-outcome ->
  outcome-exhausted outcome-exhausted outcome-exhausted }T
T{ max-n 1+ true visit-outcome 1 2 visit-outcome 3 true ' visit-outcome rs-checked ->
  outcome-exhausted outcome-full outcome-ok }T
\ outcome-text: every outcome's name; anything else reads as invalid.
: named? ( outcome c-addr u -- flag ) rot outcome-text compare 0= ;
T{ outcome-ok s" ok" named? outcome-invalid s" invalid" named? -> true true }T
T{ outcome-exhausted s" exhausted" named? outcome-unknown s" unknown" named? -> true true }T
T{ outcome-rejected s" rejected" named? outcome-unsupported s" unsupported" named?
   -> true true }T
T{ outcome-full s" full" named? 7 s" invalid" named? -1 s" invalid" named? -> true true true }T
T{ outcome-full ' outcome-text rs-checked nip max-n outcome-text nip -> 4 7 }T

\ Walk records: definition, budget and the bounded work stack.
T{ 4 walk: w1 -> }T
T{ w1 walk-capacity @ w1 walk-pending @ w1 walk-fuel @ -> 4 0 0 }T
T{ -1 w1 walk-budget w1 walk-fuel @ -> false 0 }T
T{ 7 w1 walk-budget w1 walk-fuel @ -> true 7 }T
T{ 10 w1 walk-push 11 w1 walk-push 12 w1 walk-push 13 w1 walk-push -> true true true true }T
T{ 14 w1 walk-push w1 walk-pending @ -> false 4 }T
T{ w1 walk-pop w1 walk-pop -> 13 12 }T
-1 w1 walk-pending !
T{ 15 w1 ' walk-push rs-checked -> false }T
2 w1 walk-pending !

\ Children must come before the node being visited.
3 w1 walk-node !
T{ 0 w1 walk-child? 2 w1 walk-child? 3 w1 walk-child? -1 w1 walk-child? -> true true false false }T
0 w1 walk-pending !
T{ 2 w1 walk-child 3 w1 walk-child -> outcome-ok outcome-invalid }T
T{ 0 1 w1 walk-children 0 3 w1 walk-children 3 0 w1 walk-children -> outcome-ok outcome-invalid outcome-invalid }T
T{ w1 walk-pending @ -> 3 }T
\ With room for one item only the second push fails, and with none the
\ first: both are full.
T{ 0 1 w1 walk-push2 w1 walk-pending @ -> outcome-full 4 }T
T{ 0 1 w1 walk-push2 w1 walk-pending @ -> outcome-full 4 }T
T{ 1 2 w1 99 walk-bad-tag -> outcome-invalid 99 }T

\ walk-run over a DAG where node n >= 2 has children n-1 and n-2: shared
\ nodes are visited once per path, so root n costs V(n) = 1 + V(n-1) +
\ V(n-2) visits with V(0) = V(1) = 1, and V(5) = 15.
: fib-visit ( walk -- outcome )
  dup walk-node @ dup 2 < if 2drop outcome-ok else dup 1- swap 2 - rot walk-push2 then ;
T{ 8 walk: w2 -> }T
15 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-fuel @ -> outcome-ok 0 }T
14 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run -> outcome-exhausted }T
100 w2 walk-budget drop
T{ 5 ' fib-visit w2 ' walk-run rs-checked w2 walk-fuel @ -> outcome-ok 85 }T
T{ 0 w2 walk-budget drop 5 ' fib-visit w2 walk-run -> outcome-exhausted }T
\ Out of room rather than fuel: a work stack of two items cannot hold the
\ pending children, which is full, with fuel left.
T{ 2 walk: w3 -> }T
100 w3 walk-budget drop
T{ 5 ' fib-visit w3 walk-run w3 walk-fuel @ 0> -> outcome-full true }T
\ Room for a push is checked where it happens, independently of fuel (ADR
\ 0008): a visit that took the last unit and finds no room for its second
\ child is full, with no fuel left; with room for both it is exhausted at
\ the next step.
T{ 1 walk: w4 -> }T
1 w4 walk-budget drop
T{ 5 ' fib-visit w4 walk-run w4 walk-fuel @ -> outcome-full 0 }T
1 w3 walk-budget drop
T{ 5 ' fib-visit w3 walk-run w3 walk-fuel @ -> outcome-exhausted 0 }T

\ The first outcome that is not ok stops the walk.
: stop-at-3 ( walk -- outcome ) dup walk-node @ 3 = if drop outcome-unknown else fib-visit then ;
100 w2 walk-budget drop
T{ 5 ' stop-at-3 w2 walk-run -> outcome-unknown }T
\ A walk that ends before its first visit names no node (-1), not the node
\ of the walk before: here the root cannot be pushed (a corrupted
\ capacity, invalid), or no fuel is left (exhausted).
T{ w2 walk-node @ -> 3 }T
w2 walk-capacity @  0 w2 walk-capacity !
T{ 5 ' fib-visit w2 walk-run w2 walk-node @ -> outcome-invalid -1 }T
w2 walk-capacity !
T{ 5 ' stop-at-3 w2 walk-run w2 walk-node @ -> outcome-unknown 3 }T
0 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-node @ -> outcome-exhausted -1 }T
T{ 2 walk2: pz -> }T
3 pz walk-node !
T{ 5 6 ' fib-visit pz walk-run-pair pz walk-node @ -> outcome-exhausted -1 }T

\ Re-entrancy: a visitor may run a complete walk on another record, as the
\ session check runs a level-scope check inside its own walk.
: nested-visit ( walk -- outcome ) 2 ['] fib-visit w1 walk-run dup ok? if drop fib-visit else nip then ;
0 w1 walk-pending !
1000 w1 walk-budget drop
100 w2 walk-budget drop
T{ 4 ' nested-visit w2 walk-run w2 walk-fuel @ w1 walk-fuel @ -> outcome-ok 91 973 }T

\ Outcomes at the edges, the strict flag conversion and the helpers.
T{ 0 outcome-sane 4 outcome-sane 5 outcome-sane -> 0 4 5 }T
T{ max-n outcome-sane max-n 1+ outcome-sane -> 1 1 }T
T{ 1 flag>outcome 2 flag>outcome 3 flag>outcome -> 1 1 1 }T
T{ 7 outcome-ok ok-then? -> 7 true }T
T{ 7 outcome-unknown ok-then? -> outcome-unknown false }T
T{ 7 drop-invalid -> outcome-invalid }T
\ ok-keep? and ok-keep2? keep the values below a result only on ok; a
\ failure keeps the result and the outcome, whatever the result is.
T{ 7 8 outcome-ok ok-keep? -> 7 8 true }T
T{ 7 -1 outcome-exhausted ok-keep? -> -1 outcome-exhausted false }T
T{ 7 8 outcome-unknown ok-keep? -> 8 outcome-unknown false }T
T{ 6 7 8 outcome-ok ok-keep2? -> 6 7 8 true }T
T{ 6 7 -1 outcome-invalid ok-keep2? -> -1 outcome-invalid false }T
T{ 6 7 8 outcome-rejected ok-keep2? -> 8 outcome-rejected false }T
T{ 6 7 8 outcome-ok ' ok-keep2? rs-checked 7 8 outcome-unknown ' ok-keep? rs-checked ->
  6 7 8 true 8 outcome-unknown false }T
T{ outcome-exhausted no-result outcome-ok no-result ->
  -1 outcome-exhausted -1 outcome-ok }T

\ walk: refuses a capacity below 1.
: bad-walk? ( addr u -- flag ) ['] evaluate catch dup if nip nip then 0<> ;
T{ s" 0 walk: wbad0" bad-walk? s" -1 walk: wbad1" bad-walk? s" -100 walk: wbad2" bad-walk? -> true true true }T
T{ s" 1 walk: wone" bad-walk? -> false }T

\ A corrupted capacity or pending count refuses pushes. A root that cannot
\ be pushed can only mean a corrupted capacity, so walk-run reports invalid
\ without spending fuel, with fuel or without.
-1 w2 walk-capacity !
20 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-fuel @ -> outcome-invalid 20 }T
0 w2 walk-capacity !  0 w2 walk-budget drop
T{ 5 ' fib-visit w2 ' walk-run rs-checked w2 walk-fuel @ -> outcome-invalid 0 }T
8 w2 walk-capacity !
9 w2 walk-pending !
T{ 1 w2 walk-push w2 walk-pending @ -> false 9 }T
0 w2 walk-pending !

\ After exhaustion part way, fuel is 0 and work is left on the stack.
14 w2 walk-budget drop
T{ 5 ' fib-visit w2 walk-run w2 walk-fuel @ w2 walk-pending @ -> outcome-exhausted 0 1 }T

\ Node 0 has no possible children.
0 w1 walk-node !
T{ 0 w1 walk-child? -1 w1 walk-child? -> false false }T

\ A visitor result outside the vocabulary counts as invalid.
: bad-visit ( walk -- outcome ) drop 7 ;
100 w2 walk-budget drop
T{ 3 ' bad-visit w2 walk-run -> outcome-invalid }T

\ The pushing helpers keep the return stack balanced.
0 w1 walk-pending !
3 w1 walk-node !
T{ 0 1 w1 ' walk-children rs-checked 0 1 w1 ' walk-push2 rs-checked -> outcome-ok outcome-ok }T

\ walk-visit reads the current node of a node store and dispatches on it.
: show-node ( first second walk tag -- outcome ) nip + + ;
T{ 2 /node 0 store: s3 -> }T
4 5 6 s3 node-new 2drop
0 w1 walk-node !
T{ w1 s3 ' show-node walk-visit -> 15 }T
1 w1 walk-node !
T{ w1 s3 ' show-node walk-visit -> outcome-invalid }T
\ Paired walks: each item is a node and a context cell, popped together.
T{ 3 walk2: p1 -> }T
T{ p1 walk-capacity @ p1 walk-width @ w1 walk-width @ p1 walk-pending @ -> 6 2 1 0 }T
T{ 10 100 p1 walk-push-pair 11 101 p1 walk-push-pair 12 102 p1 walk-push-pair -> true true true }T
T{ 13 103 p1 walk-push-pair p1 walk-pending @ -> false 6 }T
T{ p1 walk-pop-pair -> 12 102 }T
T{ p1 walk-take p1 walk-node @ p1 walk-context @ p1 walk-pending @ -> 11 101 2 }T
T{ 2 p1 walk-room-for? 4 p1 walk-room-for? 5 p1 walk-room-for? -> true true false }T
-1 p1 walk-pending !
T{ 1 2 p1 walk-push-pair p1 walk-pending @ -> false -1 }T
5 p1 walk-pending !
T{ 1 2 p1 walk-push-pair -> false }T

\ walk-children-at pushes the first child with the current context and the
\ second with the given one, so the second is visited first.
0 p1 walk-pending ! 7 p1 walk-context !
T{ 1 2 9 p1 walk-children-at p1 walk-pop-pair p1 walk-pop-pair -> outcome-ok 2 9 1 7 }T
4 p1 walk-pending !
T{ 1 2 9 p1 walk-children-at p1 walk-pending @ -> outcome-full 6 }T
T{ 1 2 9 p1 walk-children-at p1 walk-pending @ -> outcome-full 6 }T
T{ 1 2 p1 walk-pair-outcome p1 walk-pending @ -> outcome-full 6 }T
0 p1 walk-pending !
T{ 1 2 3 p1 ' walk-children-at rs-checked 4 5 p1 ' walk-pair-outcome rs-checked -> outcome-ok outcome-ok }T

\ walk-run-pair over the DAG above, where the second child (n-2) sits one
\ level deeper: 15 visits, and the deepest context is two below the root.
variable deepest
: depth-visit ( walk -- outcome )
  dup walk-context @ deepest @ max deepest !
  dup walk-node @ dup 2 < if 2drop outcome-ok exit then
  dup 1- swap 2 - rot dup walk-context @ 1+ swap walk-children-at ;
T{ 8 walk2: p2 -> }T
0 deepest ! 100 p2 walk-budget drop
T{ 5 10 ' depth-visit p2 walk-run-pair p2 walk-fuel @ deepest @ -> outcome-ok 85 12 }T
14 p2 walk-budget drop
T{ 5 10 ' depth-visit p2 walk-run-pair -> outcome-exhausted }T
T{ 2 walk2: p3 -> }T
100 p3 walk-budget drop
T{ 5 0 ' depth-visit p3 walk-run-pair -> outcome-full }T
\ As above, the last unit of fuel spent and no room for a child is full.
T{ 1 walk2: p4 -> }T
1 p4 walk-budget drop
T{ 5 0 ' depth-visit p4 walk-run-pair p4 walk-fuel @ -> outcome-full 0 }T
\ A corrupted capacity (-1, or one cell: less than an item) is invalid.
-1 p3 walk-capacity !
20 p3 walk-budget drop
T{ 5 0 ' depth-visit p3 walk-run-pair p3 walk-fuel @ -> outcome-invalid 20 }T
1 p3 walk-capacity !
T{ 5 0 ' depth-visit p3 ' walk-run-pair rs-checked p3 walk-fuel @ -> outcome-invalid 20 }T
T{ s" 0 walk2: pbad0" bad-walk? s" -1 walk2: pbad1" bad-walk? s" 1 walk2: pone" bad-walk? -> true true false }T

\ Growable walks (plan task 6.2.0): a push past the record's room moves the
\ stack to the heap, keeping its items in order; a growth the heap refuses
\ is full and changes nothing; walk-free gives the block back and returns
\ to the first room, empty. A walk not made growable stays full at its
\ capacity (above).
2 walk: gw  gw walk-growable
: gw-push5 ( -- ) 6 1 do i gw walk-push drop loop ;
T{ gw-push5 gw walk-pending @ gw walk-capacity @ 4 > gw walk-heap @ 0<> -> 5 true true }T
T{ gw walk-pop gw walk-pop gw walk-pop gw walk-pop gw walk-pop -> 5 4 3 2 1 }T
: gw-fill ( -- ) begin gw walk-pending @ gw walk-capacity @ < while 7 gw walk-push drop repeat ;
gw-fill  1 heap-refusals !
T{ 9 gw walk-push gw walk-pending @ gw walk-capacity @ = heap-refusals @ -> false true 0 }T
T{ gw walk-pop -> 7 }T
T{ gw walk-free gw walk-pending @ gw walk-capacity @ gw walk-heap @ -> 0 2 0 }T
T{ 3 gw walk-push 4 gw walk-push gw walk-heap @ gw walk-pending @ -> true true 0 2 }T
gw walk-free

\ Frame records: passes on an explicit, growable stack (plan task 6.2.0).
\ The test visitor rebuilds the DAG above (node n >= 2 has children n-1
\ and n-2) bottom-up: its result is the number of leaves below n, and the
\ second child is visited one context level deeper. A visit of node n is
\ n frames deep, so node 5 is 5 frames deep. Each step is a word ( ...
\ frames -- ... frames next ); n is kept across the first child's visit,
\ the first count across the second's.
variable deepest-frame  variable deepest-context
: note-depth ( frames -- )
  dup frame-depth @ deepest-frame @ max deepest-frame !
  frame-context @ deepest-context @ max deepest-context ! ;
: leaves-sum ( b outcome frames -- n outcome frames 0 )
  >r r@ frame-restore over ok? if rot + swap else drop then r> 0 ;
: leaves-second ( a outcome frames -- n-2 frames next | -1 outcome frames 0 )
  >r dup ok? 0= if r@ frame-restore drop r> 0 exit then drop
  r@ frame-restore 2 - swap r@ frame-save r> ['] leaves-sum frame-under ;
: leaves-visit ( n frames -- n-1 frames next | 1 outcome frames 0 )
  dup note-depth over 2 < if nip 1 outcome-ok rot 0 exit then
  2dup frame-save swap 1- swap ['] leaves-second frame-call ;
T{ ' leaves-visit frames: f1 -> }T
T{ f1 frame-depth @ f1 frame-fuel @ f1 frame-context @ f1 frame-job @ -> 0 0 0 0 }T
T{ f1 frame-visitor @ f1 frame-block @ f1 frame-used @ f1 frame-capacity @ ->
  ' leaves-visit 0 0 0 }T
T{ -1 f1 frame-budget f1 frame-fuel @ -> false 0 }T
T{ 7 f1 frame-budget f1 frame-fuel @ -> true 7 }T
: leaves-run ( n context fuel -- result outcome )
  f1 frame-budget drop 0 deepest-frame ! 0 deepest-context ! f1 frame-run ;
\ Node 5: 15 visits, 8 leaves, 5 frames deep, context 2 above the root's;
\ the stack empty again and the context the root's.
T{ 5 10 100 leaves-run f1 frame-fuel @ f1 frame-depth @ f1 frame-used @ -> 8 outcome-ok 85 0 0 }T
T{ deepest-frame @ deepest-context @ f1 frame-context @ -> 5 12 10 }T
T{ 5 0 15 leaves-run f1 frame-fuel @ -> 8 outcome-ok 0 }T
\ One unit of fuel short is exhausted: no result, nothing in progress.
T{ 5 0 14 leaves-run f1 frame-fuel @ f1 frame-depth @ f1 frame-used @ f1 frame-context @ ->
  -1 outcome-exhausted 0 0 0 0 }T
T{ 4 0 100 leaves-run f1 frame-fuel @ -> 5 outcome-ok 91 }T
\ No depth limit: node 25 is 25 frames deep, 242785 visits; neither host
\ stack holds more for it than for node 2.
242785 f1 frame-budget drop
T{ 25 0 f1 ' frame-run rs-checked f1 frame-fuel @ -> 121393 outcome-ok 0 }T
T{ deepest-frame @ -> 25 }T
\ No fuel or a corrupted negative fuel is exhausted, spending nothing.
T{ 3 0 0 leaves-run f1 frame-fuel @ -> -1 outcome-exhausted 0 }T
-5 f1 frame-fuel !
T{ 3 0 f1 frame-run f1 frame-fuel @ f1 frame-depth @ -> -1 outcome-exhausted -5 0 }T
\ frame-admit: why a visit would not open: an unsound stack first, then
\ the fuel, then the room. A stack the heap cannot grow is full.
: admit-of ( fuel used -- outcome ) f1 frame-used ! f1 frame-fuel ! f1 frame-admit 0 f1 frame-used ! ;
T{ 1 0 admit-of 0 0 admit-of -1 0 admit-of -> 0 2 2 }T
T{ 1 -1 admit-of 1 f1 frame-capacity @ 1+ admit-of 0 -1 admit-of -> 1 1 1 }T
f1 frame-free  1 heap-refusals !
T{ 1 0 admit-of f1 frame-capacity @ -> 6 0 }T
1 heap-refusals !
T{ 0 0 admit-of heap-refusals @ -> 2 1 }T
0 heap-refusals !
T{ 1 0 admit-of f1 frame-capacity @ frame-need < -> 0 false }T
\ A growth the heap refuses ends the pass full, at any depth: no result,
\ nothing in progress, the stack and context as before.
f1 frame-free  5 0 100 leaves-run 2drop
T{ f1 frame-capacity @ -> 32 }T
1 heap-refusals !
T{ 25 0 1000 leaves-run f1 frame-depth @ f1 frame-used @ f1 frame-context @ ->
  -1 outcome-full 0 0 0 }T
T{ heap-refusals @ f1 frame-capacity @ -> 0 32 }T
100 f1 frame-budget drop
T{ 5 0 f1 ' frame-run rs-checked -> 8 outcome-ok }T
\ The failure paths keep both stacks balanced. A context that cannot grow
\ refuses the deeper visit and stays unchanged, spending nothing; the
\ continuation then runs with no result.
: refused ( x frames cont -- -1 outcome cont ) frame-under nip ;
0 f1 frame-budget drop
T{ 3 f1 ' frame-return ' frame-call rs-checked nip -> -1 outcome-exhausted ' frame-return }T
100 f1 frame-budget drop  max-n f1 frame-context !
T{ 3 f1 ' frame-return ' refused rs-checked f1 frame-context @ f1 frame-fuel @ ->
  -1 outcome-full ' frame-return max-n 100 }T
\ frame-under checks the fuel before the context (ADR 0008): with no fuel
\ left, a context at max-n is exhausted, as any other context is.
0 f1 frame-budget drop
T{ 3 f1 ' frame-return refused f1 frame-context @ f1 frame-fuel @ ->
  -1 outcome-exhausted ' frame-return max-n 0 }T
max-n 1- f1 frame-context !
T{ 3 f1 ' frame-return refused f1 frame-context @ ->
  -1 outcome-exhausted ' frame-return max-n 1- }T
\ With fuel, an unsound stack is invalid before the context is examined.
100 f1 frame-budget drop  -1 f1 frame-used !  max-n f1 frame-context !
T{ 3 f1 ' frame-return refused f1 frame-context @ ->
  -1 outcome-invalid ' frame-return max-n }T
0 f1 frame-used !  0 f1 frame-context !
\ A visitor result outside the outcome vocabulary counts as invalid.
: odd-visit ( n frames -- result outcome frames 0 ) 7 swap 0 ;
' odd-visit f1 frame-visitor !
T{ 2 0 f1 frame-run f1 frame-depth @ -> 2 outcome-invalid 0 }T

\ A busy record refuses a new budget and a new pass, changing nothing. A
\ visitor that restarts the pass on its own record gets no result and
\ invalid, and the pass in progress goes on unharmed.
create inner 2 cells allot  variable inner-budget
: restart-pass ( frames -- )
  >r 0 99 r@ frame-run inner 2! 5 r> frame-budget inner-budget ! ;
: restart-visit ( n frames -- ... frames next ) dup restart-pass leaves-visit ;
' restart-visit f1 frame-visitor !  100 f1 frame-budget drop
T{ 3 7 f1 frame-run f1 frame-fuel @ f1 frame-context @ f1 frame-depth @ ->
  3 outcome-ok 95 7 0 }T
T{ inner 2@ inner-budget @ f1 frame-visitor @ ->
  -1 outcome-invalid false ' restart-visit }T
\ A depth left behind by a THROW, or a corrupted one, keeps the record busy
\ until frame-reset, which also empties the stack.
' leaves-visit f1 frame-visitor !  1 f1 frame-depth !  3 f1 frame-used !
T{ f1 frame-busy? 5 f1 frame-budget 3 0 f1 frame-run f1 frame-fuel @ ->
  true false -1 outcome-invalid 95 }T
T{ 9 f1 frame-start f1 frame-context @ 3 0 f1 ' frame-run rs-checked ->
  false 7 -1 outcome-invalid }T
f1 frame-reset
T{ f1 frame-busy? f1 frame-used @ 3 9 f1 frame-run f1 frame-context @ ->
  false 0 3 outcome-ok 9 }T
-1 f1 frame-depth !
T{ f1 frame-busy? 3 0 f1 frame-run -> true -1 outcome-invalid }T
f1 frame-reset

\ A step may run a loop of its own on the same record (frame-loop from the
\ cells then in use): here a visit of n first counts the leaves below n-1
\ on an inner loop, then returns that count plus one.
: loop-visit ( n frames -- count outcome frames 0 )
  ['] leaves-visit over frame-visitor !
  >r 1- 0 max r@ ['] frame-return r@ frame-used @ >r frame-call r> frame-loop drop
  dup ok? if swap 1+ swap then r> 0 ;
' loop-visit f1 frame-visitor !  100 f1 frame-budget drop
T{ 6 0 f1 ' frame-run rs-checked f1 frame-fuel @ f1 frame-used @ -> 9 outcome-ok 84 0 }T
' leaves-visit f1 frame-visitor !

\ The stack words: frame-pick reads a cell by position (0 the last
\ saved), frame-drop drops n, frame-room@ gives the cells in use and the
\ capacity.
T{ 1 f1 frame-save 2 f1 frame-save 3 f1 frame-save 0 f1 frame-pick 2 f1 frame-pick
   f1 frame-room@ drop -> 3 1 3 }T
T{ 2 f1 frame-drop f1 frame-restore f1 frame-used @ -> 1 0 }T
\ A save the block cannot hold (a step that broke the spare-cell rule, or
\ an unsound count) throws frame-overrun and writes nothing.
: save-caught ( used -- ior used' )
  f1 frame-used ! 7 f1 ['] frame-save catch dup if nip nip then f1 frame-used @ ;
T{ f1 frame-capacity @ save-caught f1 frame-capacity @ = -> frame-overrun true }T
T{ -1 save-caught -> frame-overrun -1 }T
T{ f1 frame-capacity @ 1- save-caught f1 frame-capacity @ = -> 0 true }T
0 f1 frame-used !
\ frame-open opens a visit of another kind, whose results need not be an
\ outcome (frame-left keeps them), on fuel and room the caller found;
\ frame-steps runs a step to its return, frame-through a visit.
: kind-visit ( a frames -- a+1 99 frames 0 ) >r 1+ 99 r> 0 ;
: opened-step ( a frames -- a frames next ) ['] frame-return ['] kind-visit frame-open ;
100 f1 frame-budget drop
T{ 5 f1 ' opened-step frame-steps drop f1 frame-fuel @ f1 frame-depth @ f1 frame-used @
   -> 6 99 99 0 0 }T
: opened-call ( a frames cont -- a frames next ) ['] kind-visit frame-open ;
T{ 5 f1 ' opened-call frame-through drop f1 frame-fuel @ -> 6 99 98 }T
T{ 4 f1 ' frame-call frame-through drop f1 frame-fuel @ -> 5 outcome-ok 89 }T
\ The room a visit may use: frame-spare cells above its admission's own,
\ in all its steps together, also when a child is refused (the review's
\ case: a visit that saved frame-spare cells may not save more after a
\ refusal). A chain of visits, each holding frame-spare cells across its
\ child, stays inside the block at every depth.
variable spare-bad
: spare-save ( frames -- )
  frame-spare 0 do i over frame-save loop frame-sound? 0= if 1 spare-bad +! then ;
: spare-back ( r outcome frames -- r outcome frames 0 )
  frame-spare 0 do dup frame-restore drop loop 0 ;
: spare-visit ( n frames -- ... frames next )
  over 0= if nip 0 outcome-ok rot 0 exit then
  dup spare-save swap 1- swap ['] spare-back frame-call ;
' spare-visit f1 frame-visitor !  f1 frame-free  1000 f1 frame-budget drop  0 spare-bad !
T{ 50 0 f1 frame-run f1 frame-used @ spare-bad @ -> 0 outcome-ok 0 0 }T
10 f1 frame-budget drop
T{ 50 0 f1 frame-run f1 frame-used @ spare-bad @ -> -1 outcome-exhausted 0 0 }T
' leaves-visit f1 frame-visitor !

\ frame-init sets up a record inside a larger one, whose address the
\ visitor finds in frame-job; frame-free gives its stack back.
begin-structure /tjob
  field: tjob-scale
  /frames +field tjob-frames
end-structure
create tj /tjob allot
: scaled-visit ( n frames -- result outcome frames 0 )
  dup >r frame-job @ tjob-scale @ * outcome-ok r> 0 ;
T{ ' scaled-visit tj tjob-frames frame-init -> }T
tj tj tjob-frames frame-job !  6 tj tjob-scale !
T{ tj tjob-frames frame-visitor @ -> ' scaled-visit }T
T{ 9 tj tjob-frames frame-budget 7 0 tj tjob-frames frame-run
  tj tjob-frames frame-fuel @ -> true 42 outcome-ok 8 }T
live-blocks @ constant blocks-held
T{ tj tjob-frames dup frame-free frame-block @ live-blocks @ -> 0 blocks-held 1- }T
f1 frame-free

\ Packed 32-bit fields (src/lib/u32.fs). Both versions run on every host:
\ u32@ and u32! (Gforth's l@ and l! here) and the Forth-2012 u32-bytes@
\ and u32-bytes!. The tests compare values only, never bytes, so they hold
\ for either byte order; a field is read only by the version that wrote it.
\ The module is loaded under HEX: its numbers must not depend on BASE (the
\ load-time check would then fail and silently choose the slower version),
\ and it must leave BASE as it found it. Gforth's l@ and l! pass the check.
hex require ../../src/lib/u32.fs base @ decimal constant u32-base
T{ u32-base u32-native -> 16 true }T
T{ 0 u32s 1 u32s 3 u32s -> 0 4 chars 12 chars }T
T{ u32-mask 1+ $10000 dup * = u32-mask 0= -> true false }T
create packed 3 u32s allot
: field1 ( -- addr ) packed 1 u32s + ;
: via-host ( u -- u' ) field1 u32! field1 u32@ ;
: via-bytes ( u -- u' ) field1 u32-bytes! field1 u32-bytes@ ;
: u32-top ( -- u ) 1 31 lshift ;
T{ 0 via-host 1 via-host 255 via-host 256 via-host -> 0 1 255 256 }T
T{ u32-top via-host u32-top 1- via-host u32-mask via-host -> u32-top u32-top 1- u32-mask }T
T{ 0 via-bytes 1 via-bytes 255 via-bytes 256 via-bytes -> 0 1 255 256 }T
T{ u32-top via-bytes u32-top 1- via-bytes u32-mask via-bytes -> u32-top u32-top 1- u32-mask }T
\ Only the low 32 bits are kept (on a 32-bit host u32-mask 1+ is 0).
T{ u32-mask 1+ 5 + via-host u32-mask 1+ 5 + via-bytes -> 5 5 }T
T{ -1 via-host -1 via-bytes -> u32-mask u32-mask }T
\ The load-time check: Gforth's l@ and l! and the Forth-2012 version are
\ unsigned 32-bit access; a fetch that sign-extends bit 31, or a store of
\ a whole 64-bit cell, is not (on a 32-bit host both are 32-bit access).
: sign-extended@ ( addr -- n ) l@ dup u32-top and if u32-mask invert or then ;
T{ ' l@ ' l! u32-sound? ' u32-bytes@ ' u32-bytes! u32-sound? -> true true }T
T{ ' sign-extended@ ' l! u32-sound? ' @ ' ! u32-sound? -> 1 cells 4 = 1 cells 4 = }T
\ A store changes only its own field: the fields around it keep their
\ values, for each version and for random values.
: sentinels ( xt -- ) >r $A5A5 packed r@ execute $5A5A packed 2 u32s + r> execute ;
: around ( xt -- u0 u2 ) >r packed r@ execute packed 2 u32s + r> execute ;
: fenced-host ( u -- u' u0 u2 ) ['] u32! sentinels via-host ['] u32@ around ;
: fenced-bytes ( u -- u' u0 u2 ) ['] u32-bytes! sentinels via-bytes ['] u32-bytes@ around ;
variable u32-seed  20261102 u32-seed !
: u32-rnd ( -- u ) u32-seed @ 1103515245 * 12345 + u32-mask and dup u32-seed ! ;
: u32-random? ( xt -- flag )
  true 1000 0 do over u32-rnd tuck swap execute $5A5A = swap $A5A5 = and
    -rot = and and loop nip ;
T{ u32-mask fenced-host u32-mask fenced-bytes -> u32-mask $A5A5 $5A5A u32-mask $A5A5 $5A5A }T
T{ ' fenced-host u32-random? ' fenced-bytes u32-random? -> true true }T
T{ u32-mask ' via-host rs-checked u32-mask ' via-bytes rs-checked -> u32-mask u32-mask }T
\ The file-format words: one field as four bytes, least significant first,
\ and the block versions, which copy whole where the host stores fields that
\ way (u32-block?) and agree with the field-by-field ones on every host.
create le-src 8 u32s allot   create le-a 32 chars allot   create le-b 32 chars allot
create le-back 8 u32s allot
: le-fill ( -- ) 8 0 do i 16777619 * $9E3779B9 xor u32-mask and le-src i u32s + u32! loop ;
le-fill
T{ $04030201 le-a u32-le! le-a c@ le-a 1 chars + c@ le-a 2 chars + c@ le-a 3 chars + c@
   -> 1 2 3 4 }T
T{ le-a u32-le@ -> $04030201 }T
T{ $FFFFFFFF le-a u32-le! le-a u32-le@ -> u32-mask }T
T{ le-src le-a 8 u32s>le  le-src le-b 8 u32s>le-fields  le-a 32 le-b 32 compare -> 0 }T
T{ le-a le-back 8 le>u32s  le-back 8 u32s le-src 8 u32s compare -> 0 }T
T{ le-b le-back 8 le>u32s-fields  le-back 8 u32s le-src 8 u32s compare -> 0 }T
T{ le-src u32@ le-a u32-le@ = -> true }T
T{ le-src le-a 0 u32s>le  le-a le-back 0 le>u32s -> }T

\ Defining lf-u32-portable before the file loads forces the Forth-2012
\ version. The file is loaded again for this, last, under BASE 8, where 8
\ and 9 are not digits: it still reads its numbers in decimal and gives
\ BASE back. (Gforth's warnings about the words it redefines are off.)
[defined] warnings [if] warnings @ false warnings ! [then]
: lf-u32-portable ( -- ) ;
8 base ! include ../../src/lib/u32.fs base @ decimal constant u32-base-forced
[defined] warnings [if] warnings ! [then]
T{ u32-base-forced u32-native -> 8 false }T
T{ -1 field1 u32! field1 u32@ u32-top 1+ field1 u32! field1 u32@ -> u32-mask u32-top 1+ }T
\ With the Forth-2012 words, fields are already little-endian, so the block copy
\ is used; lf-u32-fields forces the field-by-field path. Both give the same bytes.
T{ u32-block? le-src le-b 8 u32s>le  le-a 32 le-b 32 compare -> true 0 }T
[defined] warnings [if] warnings @ false warnings ! [then]
: lf-u32-fields ( -- ) ;
include ../../src/lib/u32.fs
[defined] warnings [if] warnings ! [then]
T{ u32-block? -> false }T
T{ le-src le-b 8 u32s>le  le-a 32 le-b 32 compare -> 0 }T
T{ le-a le-back 8 le>u32s  le-back 8 u32s le-src 8 u32s compare -> 0 }T
bye
