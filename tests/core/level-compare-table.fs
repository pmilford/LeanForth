\ Emit LeanForth's level comparison for the pinned Lean level cases of
\ tests/reference/level-compare-table.lean: 0 (ok) where Lean's kernel
\ finds the levels equal, 3 (unknown) where it does not (ADR 0011,
\ Amendment 1). The parameters u and v are interned names, as Lean's name
\ order needs them.
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/kernel/level-compare.fs
decimal

: must ( flag -- ) 0= if -1 throw then ;
variable u-id variable v-id
\ Construct the two scoped parameters and corresponding test level DAGs.
: build-level-comparison-table ( -- )
  lf-name-reset lf-level-reset lf-lscope-context-reset
  0 s" u" lf-name-str must u-id !  0 s" v" lf-name-str must v-id !
  u-id @ lf-lscope-context-add must
  v-id @ lf-lscope-context-add must
  u-id @ lf-level-param must drop
  v-id @ lf-level-param must drop
  1 lf-level-succ must drop
  1 lf-level-succ must drop
  1 0 lf-level-max must drop
  0 lf-level-succ must drop
  6 0 lf-level-max must drop
  1 0 lf-level-imax must drop
  1 2 lf-level-max must drop
  2 1 lf-level-max must drop
  0 1 lf-level-max must drop
  5 lf-level-succ must drop
  3 0 lf-level-imax must drop
  0 5 lf-level-max must drop
  12 2 lf-level-max must drop
  3 2 lf-level-max must drop
  12 2 lf-level-imax must drop
  3 2 lf-level-imax must drop
  0 1 lf-level-imax must drop ;

\ Emit one case index and its status.
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
8 1 11 emit-level-comparison
9 12 3 emit-level-comparison
10 13 0 emit-level-comparison
11 14 1 emit-level-comparison
12 15 16 emit-level-comparison
13 17 18 emit-level-comparison
14 19 0 emit-level-comparison
bye
