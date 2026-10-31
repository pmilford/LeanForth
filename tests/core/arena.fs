\ Exercise arena construction, failure paths, capacity, and reset.
\ The tester adapter makes assertion failures visible to CI.
include ../support/tester.fs
include ../../src/core/arena.fs

lf-arena-reset
T{ 100 lf-node-atom -> 0 true }T
T{ 200 lf-node-atom -> 1 true }T
T{ 0 lf-node-address @ -> 1 }T
T{ 0 lf-node-address cell+ @ -> 100 }T
T{ 0 1 lf-node-pair -> 2 true }T
T{ 2 lf-node-address @ -> 2 }T
T{ 2 lf-node-address cell+ @ -> 0 }T
T{ 2 lf-node-address 2 cells + @ -> 1 }T
T{ -1 0 lf-node-pair -> false }T
T{ 0 -1 lf-node-pair -> false }T
T{ 0 3 lf-node-pair -> false }T
T{ 3 0 lf-node-pair -> false }T
T{ lf-arena-count @ -> 3 }T

\ Fill remaining slots, throwing if allocation unexpectedly fails.
: fill-arena ( -- )
  begin lf-arena-count @ lf-arena-capacity < while
    0 lf-node-atom 0= if -1 throw then drop
  repeat ;
fill-arena
T{ 9 lf-node-atom -> false }T
T{ 0 1 lf-node-pair -> false }T
T{ lf-arena-count @ -> lf-arena-capacity }T
lf-arena-reset
T{ 0 lf-node-valid? -> false }T
\ A corrupted allocation count must not authorize accesses or writes.
-1 lf-arena-count !
T{ 0 lf-node-valid? -> false }T
T{ 1 lf-node-atom -> false }T
T{ 0 0 lf-node-pair -> false }T
T{ lf-arena-count @ -> -1 }T
lf-arena-capacity 1+ lf-arena-count !
T{ 0 lf-node-valid? -> false }T
T{ 1 lf-node-atom -> false }T
T{ 0 0 lf-node-pair -> false }T
T{ lf-arena-count @ -> lf-arena-capacity 1+ }T
lf-arena-reset
bye
