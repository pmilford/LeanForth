\ Tests of untrusted symbolic universe storage; no theorem is checked.
include ../support/tester.fs
include ../../src/experimental/levels.fs

\ Zero, parameters and operations retain distinct syntax and child order.
lf-level-reset
T{ lf-level-count @ -> 1 }T
T{ 0 lf-level-read -> lf-level-tag-zero 0 0 true }T
T{ 2 lf-level-param -> 1 true }T
T{ 1 lf-level-succ -> 2 true }T
T{ 0 2 lf-level-max -> 3 true }T
T{ 3 1 lf-level-imax -> 4 true }T
T{ 1 lf-level-read -> lf-level-tag-param 2 0 true }T
T{ 2 lf-level-read -> lf-level-tag-succ 1 0 true }T
T{ 3 lf-level-read -> lf-level-tag-max 0 2 true }T
T{ 4 lf-level-read -> lf-level-tag-imax 3 1 true }T

\ Invalid payloads, tags and child references must not advance the count.
T{ 0 lf-level-param -> false }T
T{ -1 lf-level-param -> false }T
T{ -1 lf-level-succ -> false }T
T{ 5 lf-level-succ -> false }T
T{ 0 5 lf-level-max -> false }T
T{ 5 0 lf-level-max -> false }T
T{ -1 0 lf-level-imax -> false }T
T{ 0 -1 lf-level-imax -> false }T
T{ 0 0 99 lf-level-binary -> false }T
T{ lf-level-count @ -> 5 }T
T{ -1 lf-level-read -> false }T
T{ 5 lf-level-read -> false }T
T{ -1 1 rshift lf-level-read -> false }T

\ Fill storage, then confirm exhausted constructors preserve existing nodes.
: fill-level-arena ( -- )
  begin lf-level-count @ lf-level-capacity < while
    0 lf-level-succ 0= if -1 throw then drop
  repeat ;
fill-level-arena
T{ 0 lf-level-succ -> false }T
T{ 1 lf-level-param -> false }T
T{ 0 0 lf-level-max -> false }T
T{ 0 0 lf-level-imax -> false }T
T{ lf-level-count @ -> lf-level-capacity }T
T{ 4 lf-level-read -> lf-level-tag-imax 3 1 true }T

\ Invalid global counts fail before addressing; reset starts a fresh arena.
-1 lf-level-count !
T{ 0 lf-level-read -> false }T
T{ 0 lf-level-succ -> false }T
T{ 1 lf-level-param -> false }T
T{ lf-level-count @ -> -1 }T
0 lf-level-count !
T{ 0 lf-level-read -> false }T
T{ 1 lf-level-param -> false }T
T{ lf-level-count @ -> 0 }T
lf-level-capacity 1+ lf-level-count !
T{ 0 lf-level-read -> false }T
T{ 0 0 lf-level-imax -> false }T
T{ lf-level-count @ -> lf-level-capacity 1+ }T
lf-level-reset
T{ lf-level-count @ -> 1 }T
T{ 0 lf-level-read -> lf-level-tag-zero 0 0 true }T
T{ 1 lf-level-read -> false }T
bye
