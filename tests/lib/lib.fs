\ Unit tests of the general Forth library (src/lib): portability words,
\ range checks, bounded stores and tagged nodes. T{ }T checks results and
\ data-stack depth; rs-checked also checks the return stack around a call.
include ../support/tester.fs
include ../support/checks.fs
include ../../src/lib/lib.fs

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
bye
