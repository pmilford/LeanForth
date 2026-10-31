\ Emit untrusted comparison diagnostics for the pinned Lean level cases.
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
decimal

\ Construct the two scoped parameters and corresponding test level DAGs.
: build-level-comparison-table ( -- )
  lf-level-reset lf-lscope-context-reset
  10 lf-lscope-context-add 0= if -1 throw then
  11 lf-lscope-context-add 0= if -1 throw then
  10 lf-level-param 0= if -1 throw then drop
  11 lf-level-param 0= if -1 throw then drop
  1 lf-level-succ 0= if -1 throw then drop
  1 lf-level-succ 0= if -1 throw then drop
  1 0 lf-level-max 0= if -1 throw then drop
  0 lf-level-succ 0= if -1 throw then drop
  6 0 lf-level-max 0= if -1 throw then drop
  1 0 lf-level-imax 0= if -1 throw then drop
  1 2 lf-level-max 0= if -1 throw then drop
  2 1 lf-level-max 0= if -1 throw then drop ;

\ Emit one case index and its conservative status.
: emit-level-comparison ( case left right -- )
  rot . 50000 lf-level-compare . cr ;
build-level-comparison-table
0 1 1 emit-level-comparison
1 3 4 emit-level-comparison
2 1 2 emit-level-comparison
3 1 5 emit-level-comparison
4 6 7 emit-level-comparison
5 0 6 emit-level-comparison
6 8 0 emit-level-comparison
7 9 10 emit-level-comparison
bye
