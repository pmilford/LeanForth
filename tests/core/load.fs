\ Tests for the untrusted decoded-node staging interface. No proof is checked.
include ../support/tester.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/import/load.fs

\ A batch can follow existing nodes, but its child indices are batch-local.
lf-term-reset
T{ 9 lf-term-sort -> 0 true }T
T{ lf-load-begin -> true }T
T{ lf-load-begin -> false }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 1 lf-tag-bvar 0 0 lf-load-node -> true }T
T{ 2 lf-tag-lam 0 1 lf-load-node -> true }T
T{ lf-load-finish -> true }T
T{ lf-term-count @ -> 4 }T
T{ 3 lf-term-read -> lf-tag-lam 1 2 true }T
T{ lf-load-finish -> false }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> false }T

\ A bad index or a forward reference rolls back the entire active batch.
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 2 lf-tag-sort 0 0 lf-load-node -> false }T
T{ lf-term-count @ -> 4 }T
T{ lf-load-finish -> false }T
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 1 lf-tag-app 0 1 lf-load-node -> false }T
T{ lf-term-count @ -> 4 }T

\ Unknown tags, negative fields and nonzero unused fields all fail closed.
T{ lf-load-begin -> true }T
T{ 0 999 0 0 lf-load-node -> false }T
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 1 999 0 0 lf-load-node -> false }T
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 1 lf-tag-app -1 0 lf-load-node -> false }T
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort -1 0 lf-load-node -> false }T
T{ lf-load-begin -> true }T
T{ 0 lf-tag-bvar 0 1 lf-load-node -> false }T
T{ lf-term-count @ -> 4 }T

\ The loader stages concrete Sorts only (ADR 0007): a symbolic Sort record
\ is refused, as the first record or after a valid one, and the batch rolls
\ back.
T{ lf-load-begin -> true }T
T{ 0 lf-tag-symbolic-sort 0 0 lf-load-node -> false }T
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 1 lf-tag-symbolic-sort 0 0 lf-load-node -> false }T
T{ lf-term-count @ -> 4 }T
T{ lf-load-finish -> false }T

\ Explicit abort is idempotent and preserves preexisting arena nodes.
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 1 0 lf-load-node -> true }T
lf-load-abort lf-load-abort
T{ lf-term-count @ -> 4 }T
T{ 0 lf-term-read -> lf-tag-sort 9 0 true }T

\ Both remaining binary tags preserve the order of their child references.
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 1 lf-tag-bvar 0 0 lf-load-node -> true }T
T{ 2 lf-tag-pi 0 1 lf-load-node -> true }T
T{ 3 lf-tag-app 2 0 lf-load-node -> true }T
T{ lf-load-finish -> true }T
T{ 6 lf-term-read -> lf-tag-pi 4 5 true }T
T{ 7 lf-term-read -> lf-tag-app 6 4 true }T

\ Capacity exhaustion aborts the batch without losing earlier nodes.
lf-term-reset
: fill-load-arena ( -- )
  begin lf-term-count @ lf-term-capacity 1- < while
    0 lf-term-sort 0= if -1 throw then drop
  repeat ;
fill-load-arena
T{ lf-load-begin -> true }T
T{ 0 lf-tag-sort 0 0 lf-load-node -> true }T
T{ 1 lf-tag-sort 0 0 lf-load-node -> false }T
T{ lf-term-count @ -> lf-term-capacity 1- }T
T{ lf-load-finish -> false }T

\ A batch belongs to the context it was opened in, like the term store it
\ rolls back. A batch open in the main context is not open in another: a
\ record there is refused and changes nothing (no rollback to the main
\ batch's start, which would bring rolled-back nodes back), a batch opened
\ and aborted there rolls back only that context's store, and the main
\ batch stays open.
lf-term-reset
: bvars ( n -- ) 0 ?do 0 lf-term-bvar 0= abort" bvar" drop loop ;
context-new throw constant other
create other-mark /store-mark allot   \ the other context's terms after 2 nodes
other context-use 2 bvars
T{ other-mark lf-terms store-mark 6 bvars other-mark lf-terms store-rollback
   -> outcome-ok outcome-ok }T
context-main context-use 10 bvars
T{ lf-load-begin -> true }T
other context-use
T{ lf-load-open? 0 lf-tag-sort 0 0 lf-load-node lf-term-count @ -> false false 2 }T
T{ 5 lf-term-valid? -> false }T
T{ lf-load-begin 0 lf-tag-sort 0 0 lf-load-node lf-term-count @ -> true true 3 }T
lf-load-abort
T{ lf-load-open? lf-term-count @ -> false 2 }T
context-main context-use
T{ lf-load-open? lf-term-count @ -> true 10 }T
T{ 0 lf-tag-sort 0 0 lf-load-node lf-load-finish lf-term-count @ -> true true 11 }T
T{ other context-free -> 0 }T
bye
