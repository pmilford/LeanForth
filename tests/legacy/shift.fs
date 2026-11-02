\ Tests for the untrusted shift experiment. These exercise syntax operations
\ and failure cleanup only; they do not establish kernel or proof validity.
include ../support/tester.fs
include ../../src/legacy/shift.fs

lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-app -> 3 true }T
T{ 0 3 lf-term-lam -> 4 true }T

\ Under the lambda, variable zero stays bound while variable one shifts to two.
T{ 4 0 1 20 lf-shift -> 7 lf-shift-ok }T
T{ 5 lf-term-read -> lf-tag-bvar 2 0 true }T
T{ 6 lf-term-read -> lf-tag-app 1 5 true }T
T{ 7 lf-term-read -> lf-tag-lam 0 6 true }T
T{ lf-term-count @ -> 8 }T

\ Exhaustion, invalid arguments and malformed roots cannot retain allocations.
T{ 4 0 1 0 lf-shift -> -1 lf-shift-exhausted }T
T{ 4 -1 1 10 lf-shift -> -1 lf-shift-invalid }T
T{ 4 0 -1 10 lf-shift -> -1 lf-shift-invalid }T
T{ 4 0 1 -1 lf-shift -> -1 lf-shift-invalid }T
T{ -1 0 1 10 lf-shift -> -1 lf-shift-invalid }T
T{ 8 0 1 10 lf-shift -> -1 lf-shift-invalid }T
T{ lf-term-count @ -> 8 }T
T{ 4 lf-shift-cell-max 0 20 lf-shift -> -1 lf-shift-exhausted }T
T{ lf-term-count @ -> 8 }T

\ Corrupted tags, payloads and child pointers must be rejected, not traversed.
99 4 lf-term-slot !
T{ 4 0 1 20 lf-shift -> -1 lf-shift-invalid }T
lf-tag-lam 4 lf-term-slot !
4 4 lf-term-slot 2 cells + !
T{ 4 0 1 20 lf-shift -> -1 lf-shift-invalid }T
3 4 lf-term-slot 2 cells + !
1 0 lf-term-slot 2 cells + !
T{ 0 0 1 20 lf-shift -> -1 lf-shift-invalid }T
0 0 lf-term-slot 2 cells + !
T{ lf-term-count @ -> 8 }T

\ The first child allocates before the second runs out of fuel. Failure must
\ roll the count back to its original value and allow the next operation.
lf-term-reset
T{ 0 lf-term-bvar -> 0 true }T
T{ 1 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-app -> 2 true }T
T{ 2 0 1 2 lf-shift -> -1 lf-shift-exhausted }T
T{ lf-term-count @ -> 3 }T
T{ 2 0 1 3 lf-shift -> 5 lf-shift-ok }T
T{ 5 lf-term-read -> lf-tag-app 3 4 true }T

\ Overflow and corrupted arena metadata fail closed without changing counts.
lf-term-reset
T{ lf-shift-cell-max lf-term-bvar -> 0 true }T
T{ 0 0 1 1 lf-shift -> -1 lf-shift-exhausted }T
T{ lf-term-count @ -> 1 }T
\ Fill the arena and verify allocation failure cannot overwrite source nodes.
: fill-shift-arena ( -- )
  begin lf-term-count @ lf-term-capacity < while
    0 lf-term-sort 0= if -1 throw then drop
  repeat ;
fill-shift-arena
T{ 0 0 0 1 lf-shift -> -1 lf-shift-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
T{ 0 lf-term-read -> lf-tag-bvar lf-shift-cell-max 0 true }T
-1 lf-term-count !
T{ 0 0 1 10 lf-shift -> -1 lf-shift-invalid }T
T{ lf-term-count @ -> -1 }T
lf-term-reset
bye
