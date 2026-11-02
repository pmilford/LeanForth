\ Tests for the untrusted decoded-node staging interface. No proof is checked.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/import/load.fs

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
bye
