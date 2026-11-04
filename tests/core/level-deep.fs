\ The deepest nesting a full level store allows: a chain of 63 successor
\ steps above zero, evaluated and compared within the default host stacks
\ of Gforth 0.7.3 and 1.0 (both passes recurse on the host stacks), and
\ Lean's normalize on its deepest inputs, whose stack use, painted, stays
\ within the need level-normalize.fs states. A host stack overflow would
\ throw and fail this test.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/kernel/level-compare.fs
require ../../src/kernel/level-value.fs

lf-level-reset lf-lscope-context-reset
: succ-chain ( n -- top ) 0 swap 0 ?do lf-level-succ 0= abort" chain" loop ;
63 succ-chain constant top
T{ top lf-level-count @ -> 63 64 }T
T{ top 1000 lf-level-value lf-lvalue-fuel @ -> 63 outcome-ok 1000 128 - }T
\ Structurally equal: only the two scope checks of 64 visits are charged.
T{ top top 1000 lf-level-compare lf-lcmp-fuel @ -> outcome-ok 872 }T
\ The same nesting with too little fuel is exhaustion, never a crash.
T{ top 100 lf-level-value nip -> outcome-exhausted }T
T{ top top 100 lf-level-compare -> outcome-exhausted }T
\ The depth limits lie one level below what a full store can reach, so they
\ are reached here white-box: a visit at the limit is full and spends no
\ fuel; with no fuel either, the fuel decides (exhausted).
10 lf-lvalue-fuel !
T{ 0 lf-lvalue-depth-limit lf-lvalue-walk lf-lvalue-fuel @ -> -1 outcome-full 10 }T
T{ 0 lf-lvalue-depth-limit 1- lf-lvalue-walk lf-lvalue-fuel @ -> 0 outcome-ok 9 }T
0 lf-lvalue-fuel !
T{ 0 lf-lvalue-depth-limit lf-lvalue-walk -> -1 outcome-exhausted }T
\ Lean's normalize (level-normalize) recurses once per imax or max level:
\ an imax chain of 62 levels over u (each step's normal form is u again,
\ so nothing is allocated) and a max chain of 60 levels over v, whose 61
\ arguments are flattened, normalized, sorted and reduced to max u v (one
\ new node, in the one free record), compared with u.
require ../../src/core/names.fs
: must ( flag -- ) 0= abort" deep" ;
\ n nodes of tag over the previous one and right, from start.
: chain ( right start tag n -- top )
  0 ?do >r 2dup swap r@ lf-level-binary must nip r> loop drop nip ;
lf-name-reset lf-level-reset lf-lscope-context-reset
0 s" u" lf-name-str must constant u-id   0 s" v" lf-name-str must constant v-id
u-id lf-lscope-context-add must v-id lf-lscope-context-add must
u-id lf-level-param must constant u
T{ u u lf-level-tag-imax 62 chain lf-level-count @ -> 63 64 }T
T{ 63 u 100000 lf-level-compare -> outcome-ok }T
T{ u 63 100000 lf-level-inequivalent? -> false outcome-ok }T
lf-level-reset
u-id lf-level-param must drop v-id lf-level-param must constant v
T{ v u lf-level-tag-max 60 chain lf-level-count @ -> 62 63 }T
T{ 62 u 100000 lf-level-inequivalent? lf-level-count @ -> true outcome-ok 63 }T
T{ 62 62 100000 lf-level-compare -> outcome-ok }T

\ The host stacks normalize needs (level-normalize.fs), painted below a
\ comparison from here. The deepest normalize: levels alternating imax
\ and max over u, which hold the most cells per level, filling the store
\ (62 levels); Lean's normalize reduces them to u, allocating nothing.
\ Their cells per level stay within the need stated per level node, and
\ all within lf-lnorm-return-cells and lf-lnorm-data-cells (2026-11-03,
\ both hosts: 409 return and 150 data cells for 62 levels, 205 and 72
\ for 31; names of 31 and of 15 components alike 19 and 2, as the name
\ order is iterative).
require ../support/stack-paint.fs
: at-most ( n limit -- flag ) > 0= ;
: alternating ( n -- top )
  u swap 0 ?do u i 1 and if lf-level-max else lf-level-imax then must loop ;
variable deepest  variable other  variable verdict
: compare-deepest ( -- ) deepest @ other @ 100000 lf-level-compare verdict ! ;
: painted-alternating ( n -- return-cells data-cells )
  lf-level-reset u-id lf-level-param must drop
  alternating deepest ! u other ! ['] compare-deepest stack-painted ;
62 painted-alternating 2constant alternating-62
T{ verdict @ lf-level-count @ -> outcome-ok 64 }T
31 painted-alternating 2constant alternating-31
T{ verdict @ lf-level-count @ -> outcome-ok 33 }T
\ Cells per level: the difference over 31 levels; return and data.
: difference ( r1 d1 r2 d2 -- r d ) rot swap - >r - r> ;
T{ alternating-62 alternating-31 difference 31 lf-lnorm-ds-level * at-most
   swap 31 lf-lnorm-rs-level * at-most -> true true }T
T{ alternating-62 lf-lnorm-data-cells at-most
   swap lf-lnorm-return-cells at-most -> true true }T
\ The deepest name order: two parameters whose names have n components
\ (31 at most: the name store holds 63), different in every one; max p q
\ is sorted, so its normal form is new, and differs from q (Lean's false:
\ unknown).
: deep-name ( c-addr u n -- id )
  >r 0 -rot r> 0 ?do 2>r 2r@ lf-name-str must 2r> loop 2drop ;
: param ( id -- level ) dup lf-lscope-context-add must lf-level-param must ;
: name-params ( n -- p q )
  lf-name-reset lf-level-reset lf-lscope-context-reset
  >r s" x" r@ deep-name param s" y" r> deep-name param ;
: painted-names ( n -- return-cells data-cells )
  name-params dup other ! lf-level-max must deepest !
  ['] compare-deepest stack-painted ;
31 painted-names 2constant names-31
T{ verdict @ lf-level-count @ -> outcome-unknown 4 }T
15 painted-names 2constant names-15
T{ names-31 names-15 difference 16 lf-lnorm-ds-name * at-most
   swap 16 lf-lnorm-rs-name * at-most -> true true }T

\ With a larger level capacity (as a feed sets it) a graph can be deeper
\ than the scope check's walks allow. Normalize called on it directly
\ counts its level frames: beyond lf-level-depth-limit it is full, with
\ the depth limit recorded, never a host-stack overflow (the review's
\ finding M1; at depth 2,000 that was a THROW). Names of 300 components
\ are ordered in the same constant stack space.
1024 lf-level-capacity! drop  1024 lf-name-capacity! drop
: imax-chain ( n -- top ) lf-level-reset u-id lf-level-param must drop alternating ;
: deeper ( n -- flag outcome code )
  imax-chain dup u lf-level-max must swap u swap lf-level-max must
  lf-diag-clear 100000 lf-level-equivalent lf-diag-code@ ;
T{ 300 deeper -> false outcome-full lf-diag-depth-limit }T
T{ 1000 deeper -> false outcome-full lf-diag-depth-limit }T
T{ 40 deeper drop -> true outcome-ok }T
\ Lean's is_geq (level-geq.fs) recurses once per argument of a max chain,
\ through normalize's normal forms: max p0 (... p(n-1)) >= q, false, is
\ n frames deep, each counted as two level frames, so a chain of 60
\ (the scope context holds 63 parameters) is full at the depth limit, not
\ a deeper host stack (review of the heap stores); 10 is decided.
require ../../src/kernel/level-geq.fs
: p-name ( i -- c-addr u ) 0 <# #s [char] p hold #> ;
: p-level ( i -- level ) 0 swap p-name lf-name-str must param ;
: max-chain ( n -- top ) 1- dup p-level swap 0 ?do i p-level swap lf-level-max must loop ;
: geq-deep ( n -- flag outcome code )
  lf-name-reset lf-level-reset lf-lscope-context-reset max-chain
  0 s" q" lf-name-str must param lf-diag-clear 100000 lf-level-geq? lf-diag-code@ ;
T{ 60 geq-deep -> false outcome-full lf-diag-depth-limit }T
T{ 10 geq-deep drop nip -> outcome-ok }T
\ Its painted stacks, 20 frames: within the need normalize states.
variable chain-top
: geq-chain ( -- ) chain-top @ other @ 100000 lf-level-geq? verdict ! drop ;
: painted-geq ( n -- return-cells data-cells )
  lf-name-reset lf-level-reset lf-lscope-context-reset max-chain chain-top !
  0 s" q" lf-name-str must param other ! ['] geq-chain stack-painted ;
T{ 20 painted-geq lf-lnorm-data-cells at-most swap lf-lnorm-return-cells at-most
   verdict @ -> true true outcome-ok }T
300 painted-names 2constant names-300
T{ verdict @ names-300 names-31 difference -> outcome-unknown 0 0 }T
lf-level-default lf-level-capacity! drop  lf-name-default lf-name-capacity! drop
bye
