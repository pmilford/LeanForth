\ Tests of untrusted symbolic universe storage; no theorem is checked.
include ../support/tester.fs
require ../../src/lib/lib.fs
require ../../src/core/levels.fs

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

\ Each reset gives the zero level a fresh identity and advances the
\ generation; identities are never reused.
lf-level-serial @ constant level-serial0
lf-level-generation @ constant level-generation0
T{ 0 lf-level-identity -> level-serial0 true }T
T{ 1 lf-level-param -> 1 true }T
T{ 1 lf-level-identity -> level-serial0 1+ true }T
lf-level-reset
T{ 0 lf-level-identity -> level-serial0 2 + true }T
T{ lf-level-generation @ -> level-generation0 1+ }T
T{ 1 lf-level-identity -> false }T

\ A spent serial at reset poisons the store instead of reusing an identity.
max-n lf-level-serial !
lf-level-reset
T{ lf-level-count @ lf-level-generation @ -> 0 -1 }T
T{ 0 lf-level-read -> false }T
T{ 1 lf-level-param -> false }T
0 lf-level-serial !
0 lf-level-generation !
lf-level-reset
T{ lf-level-count @ 0 lf-level-read -> 1 lf-level-tag-zero 0 0 true }T

\ Failed constructors leave the serial unchanged; identities are unreadable
\ under a corrupted count.
lf-level-serial @ constant level-serial1
T{ 0 0 99 lf-level-binary -> false }T
T{ 5 0 lf-level-max -> false }T
T{ 5 0 99 lf-level-binary -> false }T
T{ 0 lf-level-param -> false }T
T{ lf-level-serial @ lf-level-count @ -> level-serial1 1 }T
-1 lf-level-count !
T{ 0 lf-level-identity -> false }T
1 lf-level-count !

\ A reset with a poisoned generation but a live serial leaves the store
\ invalid: the generation stays negative.
-1 lf-level-generation !
lf-level-reset
T{ lf-level-generation @ lf-level-count-valid? -> -1 false }T
\ Every root refuses it; a read after a checked root checks only that the
\ index is allocated (compact-store plan step S2), so it still reads.
T{ 0 lf-level-root? 0 0 lf-level-pair-valid? -> false false }T
T{ 0 lf-level-read 0 lf-level-valid? -> lf-level-tag-zero 0 0 true true }T
T{ 1 lf-level-param -> false }T
0 lf-level-generation !
lf-level-reset
T{ lf-level-count-valid? -> true }T

\ One field of a validated node, as lf-level-read gives them.
T{ 0 lf-level-succ 7 lf-level-param -> 1 true 2 true }T
T{ 1 0 lf-level-max -> 3 true }T
T{ 3 lf-level-tag@ 3 lf-level-first@ 3 lf-level-second@ -> lf-level-tag-max 1 0 }T
T{ 2 lf-level-tag@ 2 lf-level-first@ 2 lf-level-second@ 2 lf-level-read
  -> lf-level-tag-param 7 0 lf-level-tag-param 7 0 true }T
bye
