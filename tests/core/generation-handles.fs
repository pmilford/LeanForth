\ Development-only handle tests: slot identities detect resets and reuse, not
\ forgery, raw mutation, wrong arena kinds or stale references stored in nodes.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../support/store-faults.fs

variable old-level-identity
variable old-term-identity
variable rolled-level-identity
variable rolled-term-identity
lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 42 lf-lscope-context-add -> true }T
T{ 42 lf-hlevel-param -> 1 level-serial true }T
level-serial old-level-identity !
\ Before any session begins, no term is built even from a live level handle.
T{ lf-ssession-current? -> false }T
T{ 1 old-level-identity @ ' lf-hterm-sort rs-checked -> false }T
T{ 0 ' lf-hterm-bvar rs-checked -> false }T
T{ lf-term-count @ -> 0 }T
T{ lf-ssession-begin -> true }T
T{ 1 old-level-identity @ lf-hterm-sort -> 0 term-serial true }T
term-serial old-term-identity !
T{ 0 old-term-identity @ 100 lf-hterm-check -> outcome-ok }T
T{ 0 old-term-identity @ lf-hterm-valid? -> true }T
T{ 1 old-level-identity @ lf-hlevel-valid? -> true }T
T{ 777 999 true lf-hlevel-result -> 777 false }T
T{ 777 999 true lf-hterm-result -> 777 false }T
T{ 0 lf-hterm-bvar -> 1 term-serial true }T
T{ 0 old-term-identity @ 1 term-serial lf-hterm-app -> 2 term-serial true }T
T{ 2 term-serial 100 lf-hterm-check -> outcome-ok }T
\ lf-made-term: a maker's index and ok, or -1 and full for its false.
T{ 5 6 true lf-made-term 7 false lf-made-term -> 5 outcome-ok 7 -1 outcome-full }T
\ Reset both arenas and reuse their indices. Old handles must not be accepted
\ by the new session even when their integer indices are currently allocated.
lf-term-reset lf-level-reset
T{ 42 lf-hlevel-param -> 1 level-serial true }T
\ The reset ended the old session: even the new live level builds no term.
T{ lf-ssession-current? -> false }T
T{ 1 level-serial ' lf-hterm-sort rs-checked -> false }T
T{ 0 ' lf-hterm-bvar rs-checked -> false }T
T{ lf-term-count @ -> 0 }T
\ The old level handle names a reused, live index but cannot extend it.
T{ 1 old-level-identity @ ' lf-hlevel-succ rs-checked -> false }T
T{ lf-level-count @ -> 2 }T
T{ lf-ssession-begin -> true }T
T{ 1 level-serial lf-hterm-sort -> 0 term-serial true }T
T{ 1 old-level-identity @ lf-hlevel-valid? -> false }T
T{ 1 old-level-identity @ lf-hterm-sort -> false }T
T{ 0 old-term-identity @ lf-hterm-valid? -> false }T
T{ 0 old-term-identity @ 100 lf-hterm-check -> outcome-invalid }T
T{ 0 old-term-identity @ 0 term-serial lf-hterm-app -> false }T
T{ 0 term-serial 0 old-term-identity @ lf-hterm-app -> false }T
T{ lf-term-count @ -> 1 }T
T{ 0 term-serial 100 lf-hterm-check -> outcome-ok }T
\ Simulate an allocation transaction that discards its last slot and then
\ reuses it. The old handle must not match the new occupant even though the
\ arena generation did not change. No node may retain a rolled-back level.
\ The slots are given back through store marks (lib/store.fs).
create rollback-mark /store-mark allot
T{ rollback-mark lf-terms store-mark -> outcome-ok }T
T{ 0 lf-hterm-bvar -> 1 term-serial true }T
term-serial rolled-term-identity !
T{ rollback-mark lf-term-rollback lf-term-count @ -> outcome-ok 1 }T
T{ 1 lf-hterm-bvar -> 1 term-serial true }T
T{ 1 rolled-term-identity @ lf-hterm-valid? -> false }T
T{ 1 term-serial lf-hterm-valid? -> true }T
T{ lf-hlevel-zero -> 0 0 level-identity@ true }T
T{ rollback-mark lf-levels store-mark -> outcome-ok }T
T{ 0 0 level-identity@ lf-hlevel-succ -> 2 level-serial true }T
level-serial rolled-level-identity !
T{ rollback-mark lf-levels store-rollback lf-level-count @ -> outcome-ok 2 }T
T{ 0 0 level-identity@ lf-hlevel-succ -> 2 level-serial true }T
T{ 2 rolled-level-identity @ lf-hlevel-valid? -> false }T
T{ 2 level-serial lf-hlevel-valid? -> true }T
\ A handle is a checked root (compact-store plan step S2): with the seal
\ broken, the count still sound, the node's identity still reads, but no
\ handle of the store is valid and none is made.
term-seal-flip
T{ 1 lf-term-identity nip 1 term-serial lf-hterm-valid? 0 lf-hterm-bvar
   -> true false false }T
term-seal-flip
T{ 1 term-serial lf-hterm-valid? -> true }T
level-seal-flip
T{ 2 lf-level-identity nip 2 level-serial lf-hlevel-valid? lf-hlevel-zero
   -> true false false }T
level-seal-flip
T{ 2 level-serial lf-hlevel-valid? -> true }T
\ The final serial is usable once; then allocation fails without wrapping or
\ damaging the existing handle. Level reset at saturation also fails closed.
-1 1 rshift 1- term-serial!
T{ 0 lf-hterm-bvar -> 2 term-serial true }T
T{ 2 term-serial lf-hterm-valid? -> true }T
T{ 0 lf-hterm-bvar -> false }T
T{ lf-term-count @ -> 3 }T
-1 1 rshift level-serial!
T{ 0 0 level-identity@ lf-hlevel-succ -> false }T
T{ lf-level-count @ -> 3 }T
lf-level-reset
T{ lf-level-count-valid? -> false }T
T{ lf-hlevel-zero -> false }T
bye
