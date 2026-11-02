\ Selected untrusted conversions paired with Lean's compare-table oracle.
include ../../src/core/terms.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/legacy/tagged-shift.fs
include ../../src/legacy/tagged-instantiate.fs
include ../../src/legacy/tagged-beta.fs
include ../../src/core/level-value.fs
include ../../src/core/level-compare.fs
include ../../src/legacy/tagged-convert.fs
decimal
: node ( index identity true | false -- index ) 0= abort" allocation" drop ;
: handle ( index -- index identity ) dup lf-term-identity 0= abort" identity" ;
: binary-node ( left right tag -- index ) >r handle rot handle 2swap r> lf-hterm-binary node ;
: lam-node ( domain body -- index ) lf-tag-lam binary-node ;
: pi-node ( domain body -- index ) lf-tag-pi binary-node ;
: app-node ( fn arg -- index ) lf-tag-app binary-node ;
: build-conversion-cases ( -- )
  lf-term-reset lf-level-reset lf-lscope-context-reset
  lf-ssession-begin 0= abort" session"
  lf-hlevel-zero 0= abort" zero" lf-hterm-sort node drop
  lf-hlevel-zero 0= abort" zero" lf-hlevel-succ 0= abort" succ"
  lf-hterm-sort node drop
  0 lf-hterm-bvar node drop
  1 lf-hterm-bvar node drop
  1 2 lam-node drop
  4 0 app-node drop
  0 2 lam-node drop
  5 2 lam-node drop
  2 3 pi-node drop
  0 8 pi-node drop
  2 2 lam-node drop
  0 10 lam-node drop ;
: emit-conversion ( case left right -- )
  >r >r . r> handle r> handle 20000 lf-tagged-convert . cr ;
build-conversion-cases
0 0 0 emit-conversion
1 0 1 emit-conversion
2 5 0 emit-conversion
3 11 11 emit-conversion
4 0 11 emit-conversion
5 6 7 emit-conversion
bye
