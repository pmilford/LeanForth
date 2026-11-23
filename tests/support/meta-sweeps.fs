\ Test support: resource sweeps of one front-end pass on one term (class
\ 5 of docs/development/TEST_COVERAGE_REVIEW.md; S2's coverage debt,
\ 2026-11-19). A scenario is a term e, made before, and a pass
\ ( e -- x outcome ); sweep-normal runs it once for its answer (x and
\ outcome), and each sweep then runs it again and again:
\ - heap-sweep: with the k-th heap allocation refused (heap-watch.fs's
\   heap-refusals), every k until a run makes fewer than k, the slabs the
\   test names (sweep-slabs-xt) given back to the heap before each run,
\   so that each one's first claim allocates;
\ - room-sweep: with room for j more records in a store (sweep-store-xt:
\   lf-terms by default, lf-levels), every j from 0 until the run gives
\   its answer, with sharing off, so that every node the pass makes is
\   new as on its first run (the normal run made them all before), and
\   the scratch rolled back after each run (core/scratch-marks.fs: the
\   terms, levels, references and the local context's new entries).
\ - slab-sweep: with room for j units in a slab (sweep-slab-xt), every
\   j from 1 until the run gives its answer: the slab given back with the
\   limit j before each run, so that each claim past j is refused (a
\   heap sweep refuses only the claims that grow a slab), and its old
\   limit after the sweep. The run must empty the slab at its start.
\ Each run must give the scenario's answer, x equal up to its nodes'
\ identities (term-eqv.fs's lf-meta-eqv) or the same cell, or end full:
\ a refusal never becomes another answer. Both give ( fulls bad ), the
\ runs that ended full and those that gave another answer; swept? holds
\ for some full and none bad. Used by tests/front/whnf.fs and infer.fs;
\ slab-sweep by tests/front/tactics/blocks-2/test.fs.
\ Include after heap-watch.fs and before the test loads its input (a
\ module loaded later grows the checker context, which the input's marks
\ do not follow). State: test-only variables; single-threaded.
require ../../src/lib/slab.fs
require ../../src/core/scratch-marks.fs
require ../../src/front/term-eqv.fs

\ A slab given back to the heap, empty, its unit and limit kept.
: sweep-slab-anew ( slab -- )
  dup slab-unit over slab-limit rot dup slab-free slab-init ok? 0= abort" sweep-slab-anew" ;
variable sweep-slabs-xt   \ ( -- ) gives the pass's slabs back (sweep-slab-anew)
variable sweep-store-xt   \ ( -- store ) the store a room sweep limits
' noop sweep-slabs-xt !  ' lf-terms sweep-store-xt !
variable sweep-e  variable sweep-xt
variable sweep-x  variable sweep-out  variable sweep-fulls  variable sweep-bad
: sweep-run ( -- x outcome ) sweep-e @ sweep-xt @ execute ;
: sweep-normal ( e xt -- )
  sweep-xt ! sweep-e ! sweep-run sweep-out ! sweep-x ! 0 sweep-fulls ! 0 sweep-bad ! ;
: sweep-bad+ ( -- ) 1 sweep-bad +! ;
: sweep-same? ( x x' -- flag ) 2dup = if 2drop true exit then lf-meta-eqv drop ;
: sweep-tally ( x outcome -- )
  dup outcome-full = if 2drop 1 sweep-fulls +! exit then
  sweep-out @ <> if drop sweep-bad+ exit then sweep-x @ sweep-same? 0= if sweep-bad+ then ;
: sweep-result ( -- fulls bad ) sweep-fulls @ sweep-bad @ ;

\ The k-th allocation refused; true when the refusal fired.
: refused-run ( k -- fired? )
  sweep-slabs-xt @ execute heap-refusals ! sweep-run heap-refusals @ 0= 0 heap-refusals !
  >r sweep-tally r> ;
: heap-sweep ( e xt -- fulls bad )
  sweep-normal 0 begin 1+ dup refused-run 0= until drop sweep-result ;

\ Room for j more records in the store, the old limit given back after.
create sweep-mark /lf-scratch allot
: sweep-room! ( j store -- limit ) dup store-limit @ >r tuck store-count @ + swap store-limit!
  ok? 0= abort" sweep-room!" r> ;
\ The caller's sharing setting and the store's old limit are put back.
: sweep-limit-back ( limit -- )
  sweep-store-xt @ execute store-limit! ok? 0= abort" room-runs: limit" ;
: room-runs ( j -- x outcome )
  lf-term-sharing? >r false lf-term-sharing!
  sweep-store-xt @ execute sweep-room! >r sweep-run r> sweep-limit-back r> lf-term-sharing! ;
\ True when the run gave its answer.
: room-run ( j -- done? )
  sweep-mark lf-scratch-mark ok? 0= abort" room-run: mark"
  room-runs dup outcome-full <> >r sweep-tally r>
  sweep-mark lf-scratch-rollback ok? 0= abort" room-run: rollback" ;
: room-sweep ( e xt -- fulls bad )
  sweep-normal -1 begin 1+ dup room-run until drop sweep-result ;

\ A slab given back to the heap, empty, with room for j units.
variable sweep-slab-xt    \ ( -- slab ) the slab a slab sweep limits
: sweep-slab-limit ( j slab -- )
  dup slab-unit -rot dup slab-free slab-init ok? 0= abort" sweep-slab-limit" ;
: sweep-slab ( -- slab ) sweep-slab-xt @ execute ;
\ True when the run gave its answer.
: slab-run ( j -- done? )
  sweep-slab sweep-slab-limit sweep-run dup outcome-full <> >r sweep-tally r> ;
: slab-sweep ( e xt -- fulls bad )
  sweep-slab slab-limit >r sweep-normal 0 begin 1+ dup slab-run until drop
  r> sweep-slab sweep-slab-limit sweep-result ;
: swept? ( fulls bad -- flag ) 0= swap 0> and ;
