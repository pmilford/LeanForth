\ Deep levels (plan task 6.2.0): evaluation, Lean's normalize and is_geq
\ keep their pending work on explicit stacks that grow with the depth, so
\ a chain of any depth the level store holds is evaluated, normalized and
\ compared in a constant number of host-stack cells (painted here on
\ Gforth 0.7.3 and 1.0 alike), and a stack the heap cannot grow is full,
\ never a host-stack overflow.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
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
\ An evaluation whose frames the heap cannot grow is full and spends no
\ fuel; with no fuel either, the fuel decides (exhausted).
10 lf-lvalue-fuel !  lf-lvalue-frames frame-free  1 heap-refusals !
T{ 0 lf-lvalue-walk lf-lvalue-fuel @ -> -1 outcome-full 10 }T
T{ 0 lf-lvalue-walk lf-lvalue-fuel @ -> 0 outcome-ok 9 }T
0 lf-lvalue-fuel !  1 heap-refusals !
T{ 0 lf-lvalue-walk heap-refusals @ -> -1 outcome-exhausted 1 }T
0 heap-refusals !
\ Lean's normalize (level-normalize) visits each imax or max level: an
\ imax chain of 62 levels over u (each step's normal form is u again, so
\ nothing is allocated) and a max chain of 60 levels over v, whose 61
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

\ Host stacks, painted below a comparison from here: levels alternating
\ imax and max over u (Lean's normalize reduces them to u, allocating
\ nothing), 31 and 62 deep, and names of 15 and 31 components take the
\ same cells, within lf-lnorm-return-cells and lf-lnorm-data-cells: at
\ most a few cells apart, where a growable array or the frames grow at
\ different points (near?).
require ../support/stack-paint.fs
: at-most ( n limit -- flag ) > 0= ;
: near? ( r1 d1 r2 d2 -- flag ) rot - abs 8 at-most >r - abs 8 at-most r> and ;
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
T{ alternating-62 alternating-31 near? -> true }T
T{ alternating-62 lf-lnorm-data-cells at-most
   swap lf-lnorm-return-cells at-most -> true true }T
\ And 10,000 deep, in a larger level store (as a feed sets it).
32768 lf-level-capacity! drop
10000 painted-alternating 2constant alternating-10000
T{ verdict @ alternating-10000 alternating-31 near? -> outcome-ok true }T
\ The deepest name order: two parameters whose names have n components,
\ different in every one; max p q is sorted, so its normal form is new,
\ and differs from q (Lean's false: unknown).
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
T{ names-31 names-15 near? -> true }T

\ With a larger level capacity (as a feed sets it) a graph can be far
\ deeper: alternating chains of 300, 1,000 and 10,000 levels normalize to
\ u, in the same host-stack cells as 31 (above; at depth 2,000 this was a THROW
\ before the frame count of the review's finding M1, and full at 64 after
\ it); a succ chain of 10,000 evaluates. Normalize's frames that the heap
\ cannot grow are full, recorded with their cells in use and capacity.
1024 lf-name-capacity! drop
: imax-chain ( n -- top ) lf-level-reset u-id lf-level-param must drop alternating ;
: deeper-pair ( n -- l1 l2 )
  imax-chain dup u lf-level-max must swap u swap lf-level-max must ;
: deeper ( n -- flag outcome ) deeper-pair 10000000 lf-level-equivalent ;
T{ 300 deeper -> true outcome-ok }T
T{ 1000 deeper -> true outcome-ok }T
T{ 10000 deeper -> true outcome-ok }T
lf-level-reset
T{ 10000 succ-chain 100000 lf-level-value -> 10000 outcome-ok }T
1000 deeper-pair 2constant pair-1000
T{ pair-1000 10000000 lf-level-equivalent -> true outcome-ok }T
lf-lnorm-frames frame-free  1 heap-refusals !  lf-diag-clear
T{ pair-1000 10000000 lf-level-equivalent lf-diag-code@ -> false outcome-full lf-diag-frame-limit }T
0 heap-refusals !
\ Lean's is_geq (level-geq.fs) goes through normalize's normal forms one
\ argument of a max chain at a time: max p0 (... p(n-1)) >= q, false,
\ for 10, 60 and 200 arguments, in constant host-stack cells (each step
\ normalizes a normal form again, as Lean's does, so the store holds about
\ n*n/2 new nodes).
require ../../src/kernel/level-geq.fs
: p-name ( i -- c-addr u ) 0 <# #s [char] p hold #> ;
: p-level ( i -- level ) 0 swap p-name lf-name-str must param ;
: max-chain ( n -- top ) 1- dup p-level swap 0 ?do i p-level swap lf-level-max must loop ;
: geq-deep ( n -- flag outcome )
  lf-name-reset lf-level-reset lf-lscope-context-reset max-chain
  0 s" q" lf-name-str must param 10000000 lf-level-geq? ;
T{ 10 geq-deep -> false outcome-ok }T
T{ 60 geq-deep -> false outcome-ok }T
T{ 200 geq-deep -> false outcome-ok }T
\ After a call has sized normalize's arrays, a call whose frames the heap
\ cannot grow is full, recorded with their cells in use and capacity.
: geq-refused ( n -- flag outcome code )
  lf-name-reset lf-level-reset lf-lscope-context-reset max-chain
  0 s" q" lf-name-str must param 2dup 10000000 lf-level-geq? 2drop
  lf-lnorm-frames frame-free 1 heap-refusals ! lf-diag-clear
  10000000 lf-level-geq? lf-diag-code@ ;
T{ 60 geq-refused -> false outcome-full lf-diag-frame-limit }T
0 heap-refusals !
variable chain-top
: geq-chain ( -- ) chain-top @ other @ 10000000 lf-level-geq? verdict ! drop ;
: painted-geq ( n -- return-cells data-cells )
  lf-name-reset lf-level-reset lf-lscope-context-reset max-chain chain-top !
  0 s" q" lf-name-str must param other ! ['] geq-chain stack-painted ;
\ (Past 32 arguments a sort merges, which nests a few more words: 60 and
\ 200 arguments take the same cells.)
60 painted-geq 2constant geq-60
T{ geq-60 lf-lnorm-data-cells at-most swap lf-lnorm-return-cells at-most
   verdict @ -> true true outcome-ok }T
T{ 200 painted-geq geq-60 near? verdict @ -> true outcome-ok }T
300 painted-names 2constant names-300
T{ verdict @ names-300 names-31 near? -> outcome-unknown true }T
\ The arguments' sort (lib/sort.fs): 60 arguments, pushed as the max's
\ and again normalized (120 cells), are merged through 60 scratch cells
\ above them in the argument stack. With that stack given back to one
\ cell, a normalization grows it four times for the pushes (to 128 cells)
\ and once for the scratch; each growth refused in turn is full, recorded
\ as a full work stack with the cells in use and the capacity (the
\ scratch's: 120 of 128), and with none refused the answer is Lean's.
: pair-60 ( -- l1 l2 )
  lf-name-reset lf-level-reset lf-lscope-context-reset 60 max-chain
  0 s" q" lf-name-str must param ;
T{ pair-60 10000000 lf-level-equivalent -> false outcome-ok }T
: trimmed-60 ( k -- flag outcome left code )
  pair-60 lf-lnorm-arg-cells slab-trim drop lf-diag-clear rot heap-refusals !
  10000000 lf-level-equivalent heap-refusals @ 0 heap-refusals ! lf-diag-code@ ;
: growths-60 ( -- flag outcome n ) max-n trimmed-60 drop max-n swap - ;
T{ growths-60 -> false outcome-ok 5 }T
T{ 1 trimmed-60 -> false outcome-full 0 lf-diag-work-stack-full }T
T{ 4 trimmed-60 -> false outcome-full 0 lf-diag-work-stack-full }T
T{ 5 trimmed-60 -> false outcome-full 0 lf-diag-work-stack-full }T
T{ lf-diag@ 2drop -> 120 128 }T
T{ 6 trimmed-60 -> false outcome-ok 1 lf-diag-none }T
lf-level-default lf-level-capacity! drop  lf-name-default lf-name-capacity! drop
bye
