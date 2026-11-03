\ Inference at the deepest nesting a 64-node term store allows, on the
\ default host stacks of Gforth 0.7.3 and 1.0 (inference recurses on the
\ host stacks; an overflow would throw and fail this test). Outcomes and
\ fuel equal those of the code before the refactor.
include ../support/tester.fs
require ../../src/main.fs

create ids 64 cells allot
variable token
: save ( index identity true | false -- ) 0= abort" alloc" swap cells ids + ! ;
: h ( index -- index identity ) dup cells ids + @ ;
: newest ( -- index ) lf-term-count @ 1- ;
: setup ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  42 lf-lscope-context-add 0= abort" ctx"
  42 lf-level-param 0= abort" level" drop
  lf-ssession-begin 0= abort" session"
  1 dup lf-level-identity 0= abort" lid" lf-hterm-sort save   \ 0: Sort u
  0 lf-hterm-bvar save                                       \ 1: bvar 0
  lf-msp-begin 0= abort" index" lf-msp-token 0= abort" token" token ! ;
\ lam (x1 : S) ... lam (xn : S) => bvar 0
: lams ( n -- root ) setup 1 swap 0 ?do 0 h rot h lf-hterm-lam save newest loop ;
\ lam (f : S -> S) (c : S) => f (f ... (f c)), n applications
: apps ( n -- root )
  setup 0 h 0 h lf-hterm-pi save 1 lf-hterm-bvar save
  1 swap 0 ?do 3 h rot h lf-hterm-app save newest loop
  0 h rot h lf-hterm-lam save newest 2 h rot h lf-hterm-lam save newest ;
: infer ( root fuel -- type status ) >r h token @ -rot r> lf-mixed-infer nip ;

\ The deepest successful inference: 26 applications under two binders; its
\ type fills the store exactly.
T{ 26 apps 100000 infer lf-minfer-fuel @ lf-term-count @ -> 63 outcome-ok 98439 64 }T
\ Deeper inputs run out of room for their output types: full (not
\ exhausted: fuel is plentiful), with every count rolled back and no fuel
\ left, never a crash. With too little fuel the same input is exhausted.
T{ 29 apps 100000 infer lf-minfer-fuel @ lf-term-count @ -> -1 outcome-full 0 35 }T
T{ 31 lams 100000 infer lf-minfer-fuel @ lf-term-count @ -> -1 outcome-full 0 33 }T
T{ 29 apps 100 infer lf-minfer-fuel @ lf-term-count @ -> -1 outcome-exhausted 0 35 }T
bye
