\ Inference at the deepest nesting a 64-node term store allows, on the
\ default host stacks of Gforth 0.7.3 and 1.0. Outcomes and fuel equalled
\ those of the code before the refactor; since free variables (plan task
\ 4.2.2a) a variable's type is its entry's (no shift) and an
\ application's type is instantiated without an audit, so less fuel is
\ spent and one more application fits; since plan task 6.2.0 inference
\ keeps its pending work on an explicit stack, with the same outcomes and
\ fuel. Then the deepest normalize the level store allows, at the deepest
\ inference visit.
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

\ The deepest successful inference: 27 applications under two binders; its
\ type is node 62 (one more application is full). Fuel left: 98896 since
\ the audits check a shared node once (agent EX), 98894 since
\ conversion is Lean's is_def_eq (plan task 4.2.2b: each argument's type
\ equals the domain by Lean's ==), 98705 since free variables (98517 for
\ 26 applications, whose type filled the store exactly, since ADR 0011
\ Amendment 1; 98439 before).
T{ 27 apps 100000 infer lf-minfer-fuel @ lf-term-count @ -> 62 outcome-ok 98896 63 }T
T{ 26 apps 100000 infer lf-minfer-fuel @ lf-term-count @ -> 60 outcome-ok 98962 61 }T
\ Deeper inputs run out of room for their output types: full (not
\ exhausted: fuel is plentiful), with every count rolled back and no fuel
\ left, never a crash. With too little fuel the same input is exhausted.
T{ 29 apps 100000 infer lf-minfer-fuel @ lf-term-count @ -> -1 outcome-full 0 35 }T
T{ 31 lams 100000 infer lf-minfer-fuel @ lf-term-count @ -> -1 outcome-full 0 33 }T
T{ 29 apps 100 infer lf-minfer-fuel @ lf-term-count @ -> -1 outcome-exhausted 0 35 }T

\ The deepest normalize at the deepest inference: fun (f : S -> S)
\ (c : Sort L) => f (f ... (f c)) with 25 applications (Sort L is one
\ more node than above), L m levels alternating imax and max over u,
\ which hold the most cells per level and which Lean's normalize reduces
\ to u. The innermost application, at the deepest inference frame,
\ compares Sort u with Sort L by normalize. With m = 59 the level store
\ is full at the end; with m = 0, L is u and the comparison needs no
\ normalize. Painted, the cells the normalize adds stay within its stated
\ need (level-normalize.fs) and are a few dozen, whatever the depth of L
\ or of the inference (both keep their pending work on explicit stacks:
\ plan task 6.2.0; before it, over 4 return cells per level of L); the
\ whole inference stays within lf-minfer-return-cells and
\ lf-minfer-data-cells.
require ../support/stack-paint.fs
: alternating ( m -- level )
  1 swap 0 ?do 1 i 1 and if lf-level-max else lf-level-imax then 0= abort" level" loop ;
: deep-sort ( m -- ) alternating dup lf-level-identity 0= abort" lid" lf-hterm-sort save ;
\ 2: Sort L, 3: S -> S, 4: f (bvar 1), then the applications and binders.
: deep-apps ( n m -- root )
  setup deep-sort 0 h 0 h lf-hterm-pi save 1 lf-hterm-bvar save
  1 swap 0 ?do 4 h rot h lf-hterm-app save newest loop
  2 h rot h lf-hterm-lam save newest 3 h rot h lf-hterm-lam save newest ;
variable deep-root  variable deep-status
: infer-deep ( -- ) deep-root @ 100000 infer deep-status ! drop ;
: painted-infer ( n m -- return-cells data-cells )
  deep-apps deep-root ! ['] infer-deep stack-painted ;
: at-most ( n limit -- flag ) > 0= ;
: difference ( r1 d1 r2 d2 -- r d ) rot swap - >r - r> ;
25 59 painted-infer 2constant with-normalize
\ Fuel left: 98433 and 99023 since the audits check a shared node once
\ (agent EX), 98432 and 99022 since conversion is Lean's is_def_eq (plan
\ task 4.2.2b), 98143 and 98849 before.
T{ deep-status @ lf-minfer-fuel @ lf-term-count @ lf-level-count @
   -> outcome-ok 98433 60 64 }T
25 0 painted-infer 2constant without-normalize
T{ deep-status @ lf-minfer-fuel @ lf-term-count @ -> outcome-ok 99023 60 }T
: added ( -- return-cells data-cells ) with-normalize without-normalize difference ;
T{ added lf-lnorm-data-cells at-most swap lf-lnorm-return-cells at-most -> true true }T
T{ added drop 64 at-most -> true }T
T{ with-normalize lf-minfer-data-cells at-most
   swap lf-minfer-return-cells at-most -> true true }T

\ Local-context entries go with the scratch they name (plan task 4.2.2a,
\ review F3): P0 = Prop -> Prop, P(k+1) = P(k) -> P(k) is a DAG of k + 1
\ Pis whose inference opens 2^(k+1) - 1 binders, one entry each; every Pi
\ discards its scratch, entries included, so none is left and the local
\ context never grows past its first block (64 entries). Before, k = 14
\ left 32,767 entries, and k = 18 about 100,000. (Each Pi's level is made
\ in the level store, which scratch discards do not give back: hence its
\ large capacity here.)
include ../support/plain-terms.fs
variable dag-token
: dag ( k -- node ) 0 make-sort 0 make-sort make-pi swap 0 ?do dup make-pi loop ;
: dag-infer ( k -- status entries )
  fresh-session 100000 lf-level-capacity! drop
  empty-token dag-token ! dag handle >r >r dag-token @ r> r>
  1000000 lf-mixed-infer nip nip lf-lctx-count @ ;
T{ 10 dag-infer lf-lctx store-capacity @ -> outcome-ok 0 64 }T
T{ 14 dag-infer lf-lctx store-capacity @ -> outcome-ok 0 64 }T
bye
