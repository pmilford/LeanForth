\ Unit tests of the general Forth library (src/lib): portability words,
\ range checks, bounded stores, tagged nodes, outcomes, walk and frame
\ records. T{ }T checks results and data-stack depth; rs-checked also checks
\ the return stack around a call.
include ../support/tester.fs
include ../support/checks.fs
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
T{ 0 w2 walk-budget drop 5 ' fib-visit w2 walk-run w2 walk-node @ -> outcome-exhausted -1 }T
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

\ Frame records: bounded recursion. The test visitor rebuilds the DAG above
\ (node n >= 2 has children n-1 and n-2) bottom-up: its result is the number
\ of leaves below n, and the second child is visited one context level
\ deeper. A visit of node n is n frames deep, so node 5 needs 5 frames.
variable deepest-frame  variable deepest-context
: note-depth ( frames -- )
  dup frame-depth @ deepest-frame @ max deepest-frame !
  frame-context @ deepest-context @ max deepest-context ! ;
: leaves-pair ( n frames -- result outcome )
  over 1- over frame-call ok-keep2? 0= if exit then
  -rot swap 2 - swap frame-under ok-keep? if + outcome-ok then ;
: leaves-visit ( n frames -- result outcome )
  dup note-depth over 2 < if 2drop 1 outcome-ok else leaves-pair then ;
T{ 4 ' leaves-visit frames: f1 -> }T
T{ f1 frame-limit @ f1 frame-depth @ f1 frame-fuel @ f1 frame-context @ f1 frame-job @ ->
  4 0 0 0 0 }T
T{ f1 frame-visitor @ -> ' leaves-visit }T
T{ -1 f1 frame-budget f1 frame-fuel @ -> false 0 }T
T{ 7 f1 frame-budget f1 frame-fuel @ -> true 7 }T
T{ s" 0 0 frames: fbad0" bad-walk? s" -3 0 frames: fbad1" bad-walk?
  s" 1 0 frames: fone" bad-walk? -> true true false }T
: leaves-run ( n context limit fuel -- result outcome )
  f1 frame-budget drop f1 frame-limit ! 0 deepest-frame ! 0 deepest-context !
  f1 frame-run ;
\ Node 5: 15 visits, 8 leaves, 5 frames deep, context 2 above the root's.
T{ 5 10 5 100 leaves-run f1 frame-fuel @ f1 frame-depth @ -> 8 outcome-ok 85 0 }T
T{ deepest-frame @ deepest-context @ f1 frame-context @ -> 5 12 10 }T
T{ 5 0 5 15 leaves-run f1 frame-fuel @ -> 8 outcome-ok 0 }T
\ One unit of fuel short is exhausted, one frame short is full: no result,
\ nothing left in progress.
T{ 5 0 5 14 leaves-run f1 frame-fuel @ f1 frame-depth @ -> -1 outcome-exhausted 0 0 }T
T{ 5 0 4 100 leaves-run f1 frame-depth @ f1 frame-context @ -> -1 outcome-full 0 0 }T
T{ 4 0 4 100 leaves-run f1 frame-fuel @ -> 5 outcome-ok 91 }T
\ No fuel or a corrupted negative fuel is exhausted, and a corrupted limit
\ (below 1, which frame-init never sets) invalid, with fuel or without;
\ none opens a visit or spends anything. With neither fuel nor a free
\ frame, the fuel decides: exhausted.
T{ 3 0 4 0 leaves-run f1 frame-fuel @ -> -1 outcome-exhausted 0 }T
T{ 3 0 -1 9 leaves-run f1 frame-fuel @ -> -1 outcome-invalid 9 }T
T{ 3 0 -1 0 leaves-run f1 frame-fuel @ -> -1 outcome-invalid 0 }T
T{ 3 0 0 9 leaves-run f1 frame-fuel @ f1 frame-depth @ -> -1 outcome-invalid 9 0 }T
4 f1 frame-limit !  -5 f1 frame-fuel !
T{ 3 0 f1 frame-run f1 frame-fuel @ f1 frame-depth @ -> -1 outcome-exhausted -5 0 }T
\ frame-room: why a visit would not open, the limit first, then the fuel,
\ then the frames.
: room-of ( limit fuel depth -- outcome )
  f1 frame-depth ! f1 frame-fuel ! f1 frame-limit ! f1 frame-room 0 f1 frame-depth ! ;
T{ 4 1 3 room-of 4 1 4 room-of 4 0 4 room-of 4 0 0 room-of -> 0 6 2 2 }T
T{ 0 1 0 room-of -1 0 0 room-of max-n 1 max-n room-of 2 max-n 1 room-of -> 1 1 6 0 }T
5 f1 frame-limit !  100 f1 frame-budget drop
T{ 5 0 f1 ' frame-run rs-checked -> 8 outcome-ok }T
\ The failure paths keep both stacks balanced. A context that cannot grow
\ refuses the deeper visit and stays unchanged, spending nothing.
0 f1 frame-budget drop
T{ 3 f1 ' frame-call rs-checked f1 frame-depth @ -> -1 outcome-exhausted 0 }T
100 f1 frame-budget drop  max-n f1 frame-context !
T{ 3 f1 ' frame-under rs-checked f1 frame-context @ f1 frame-fuel @ ->
  -1 outcome-full max-n 100 }T
\ frame-under checks the fuel before the context (ADR 0008): with no fuel
\ left, a context at max-n is exhausted, as any other context is.
0 f1 frame-budget drop
T{ 3 f1 ' frame-under rs-checked f1 frame-context @ f1 frame-fuel @ ->
  -1 outcome-exhausted max-n 0 }T
max-n 1- f1 frame-context !
T{ 3 f1 frame-under f1 frame-context @ -> -1 outcome-exhausted max-n 1- }T
\ With fuel, every frame in use is full and a corrupted limit invalid, both
\ before the context is examined.
100 f1 frame-budget drop  5 f1 frame-depth !
T{ 3 f1 frame-under f1 frame-context @ f1 frame-fuel @ -> -1 outcome-full max-n 1- 100 }T
0 f1 frame-depth !  -1 f1 frame-limit !  max-n f1 frame-context !
T{ 3 f1 frame-under f1 frame-context @ -> -1 outcome-invalid max-n }T
5 f1 frame-limit !  0 f1 frame-context !
\ A visitor result outside the outcome vocabulary counts as invalid.
: odd-visit ( n frames -- result outcome ) drop 7 ;
' odd-visit f1 frame-visitor !
T{ 2 0 f1 frame-run f1 frame-depth @ -> 2 outcome-invalid 0 }T

\ A busy record refuses a new budget and a new pass, changing nothing. A
\ visitor that restarts the pass on its own record gets no result and
\ invalid, and the pass in progress goes on unharmed.
create inner 2 cells allot  variable inner-budget
: restart-pass ( frames -- )
  >r 0 99 r@ frame-run inner 2! 5 r> frame-budget inner-budget ! ;
: restart-visit ( n frames -- result outcome ) dup restart-pass leaves-visit ;
' restart-visit f1 frame-visitor !  4 f1 frame-limit !  100 f1 frame-budget drop
T{ 3 7 f1 frame-run f1 frame-fuel @ f1 frame-context @ f1 frame-depth @ ->
  3 outcome-ok 95 7 0 }T
T{ inner 2@ inner-budget @ f1 frame-visitor @ ->
  -1 outcome-invalid false ' restart-visit }T
\ A depth left behind by a THROW, or a corrupted one, keeps the record busy
\ until frame-reset.
' leaves-visit f1 frame-visitor !  1 f1 frame-depth !
T{ f1 frame-busy? 5 f1 frame-budget 3 0 f1 frame-run f1 frame-fuel @ ->
  true false -1 outcome-invalid 95 }T
T{ 9 f1 frame-start f1 frame-context @ 3 0 f1 ' frame-run rs-checked ->
  false 7 -1 outcome-invalid }T
f1 frame-reset
T{ f1 frame-busy? 3 9 f1 frame-run f1 frame-context @ -> false 3 outcome-ok 9 }T
-1 f1 frame-depth !
T{ f1 frame-busy? 3 0 f1 frame-run -> true -1 outcome-invalid }T
f1 frame-reset

\ frame-call2: a visitor of two values, here comparing two chains n, n-1,
\ ..., 0 step by step; unequal values are rejected. Chains from 2 need
\ three visits, three frames deep.
: same-visit ( x y frames -- outcome )
  >r 2dup <> if 2drop r> drop outcome-rejected exit then
  drop dup 0= if drop r> drop outcome-ok exit then 1- dup r> frame-call2 ;
T{ 3 ' same-visit frames: f2 -> }T
: same-run ( x y fuel -- outcome )
  f2 frame-budget drop 0 f2 frame-start drop f2 frame-call2 ;
T{ 2 2 100 same-run f2 frame-fuel @ f2 frame-depth @ -> outcome-ok 97 0 }T
T{ 3 3 100 same-run f2 frame-depth @ -> outcome-full 0 }T
T{ 2 2 2 same-run f2 frame-fuel @ -> outcome-exhausted 0 }T
\ No free frame with fuel left is full, spending nothing; a corrupted limit
\ is invalid, with fuel or without.
100 f2 frame-budget drop  3 f2 frame-depth !
T{ 2 2 f2 ' frame-call2 rs-checked f2 frame-fuel @ f2 frame-depth @ ->
  outcome-full 100 3 }T
0 f2 frame-depth !  0 f2 frame-limit !
T{ 2 2 f2 ' frame-call2 rs-checked f2 frame-fuel @ -> outcome-invalid 100 }T
0 f2 frame-budget drop
T{ 2 2 f2 frame-call2 -> outcome-invalid }T
3 f2 frame-limit !  100 f2 frame-budget drop
T{ 2 1 100 same-run f2 frame-fuel @ -> outcome-rejected 99 }T
0 f2 frame-budget drop
T{ 2 2 f2 ' frame-call2 rs-checked -> outcome-exhausted }T
100 f2 frame-budget drop
T{ 2 2 f2 ' frame-call2 rs-checked f2 frame-depth @ -> outcome-ok 0 }T
\ Here too a result outside the outcome vocabulary counts as invalid.
: odd-visit2 ( x y frames -- outcome ) drop 2drop 9 ;
' odd-visit2 f2 frame-visitor !
T{ 1 2 f2 frame-call2 f2 frame-depth @ f2 frame-fuel @ -> outcome-invalid 0 96 }T
' same-visit f2 frame-visitor !

\ frame-init sets up a record inside a larger one, whose address the
\ visitor finds in frame-job. A bad limit aborts before anything changes.
begin-structure /tjob
  field: tjob-scale
  /frames +field tjob-frames
end-structure
create tj /tjob allot
: scaled-visit ( n frames -- result outcome ) frame-job @ tjob-scale @ * outcome-ok ;
T{ 2 ' scaled-visit tj tjob-frames frame-init -> }T
tj tj tjob-frames frame-job !  6 tj tjob-scale !
T{ tj tjob-frames frame-limit @ tj tjob-frames frame-visitor @ -> 2 ' scaled-visit }T
T{ 9 tj tjob-frames frame-budget 7 0 tj tjob-frames frame-run
  tj tjob-frames frame-fuel @ -> true 42 outcome-ok 8 }T
T{ s" 0 0 tj tjob-frames frame-init" bad-walk? tj tjob-frames frame-limit @ -> true 2 }T
bye
