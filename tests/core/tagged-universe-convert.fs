\ Emit statuses for selected symbolic Sort conversions; no theorem is accepted.
include ../../src/core/terms.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/tagged-shift.fs
include ../../src/experimental/tagged-instantiate.fs
include ../../src/experimental/tagged-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/tagged-convert.fs
decimal
: require-node ( index true | false -- index ) 0= abort" allocation" ;
: sort-node ( level -- node )
  dup lf-level-identity 0= abort" level identity"
  lf-hterm-sort 0= abort" sort" drop ;
: handle ( node -- node identity ) dup lf-term-identity 0= abort" identity" ;
: emit-case ( case left right -- ) >r >r . r> handle r> handle 10000 lf-tagged-convert . cr ;
: build-fixture ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  42 lf-lscope-context-add 0= abort" context"
  43 lf-lscope-context-add 0= abort" context"
  42 lf-level-param require-node drop
  43 lf-level-param require-node drop
  1 0 lf-level-max require-node drop
  1 0 lf-level-imax require-node drop
  0 lf-level-succ require-node drop
  3 lf-level-succ require-node drop
  1 lf-level-succ require-node drop
  0 1 lf-level-imax require-node drop
  1 2 lf-level-max require-node drop
  2 1 lf-level-max require-node drop
  lf-ssession-begin 0= abort" session"
  11 0 do i sort-node drop loop ;
build-fixture
0 1 3 emit-case
1 4 0 emit-case
2 1 2 emit-case
3 0 5 emit-case
4 6 7 emit-case
5 8 0 emit-case
6 9 10 emit-case
bye
