\ Report-only benchmark of the compact store (ADR 0016): what building one
\ expression costs in a scratch tier over a loaded, sealed input tier, the
\ three cases of the prototype's bench.fs (docs/development/measurements/
\ compact-store-2026-11-02/). For every application app(f, a) of the
\ input:
\   swapped  app(a, f): children in the input, so the input's table is
\            probed first (it mostly misses), then the scratch table; new;
\   chained  app(previous result, f): a scratch child, so only the scratch
\            table is probed; always new;
\   again    app(f, a): found in the input.
\ The scratch tier is emptied every 2^18 new expressions, as a check would
\ be. Usage (gforth-fast for timings):
\   gforth-fast tests/core/compact-bench.fs -e 's" init.ndjson" 16 compact-bench bye'
require ../support/compact-load.fs

: scratch-ready ( -- )
  compact-tier compact-scratch tier-extend ok? 0= abort" bench: no scratch tier" ;
: input-exprs ( -- n ) compact-tier tier-exprs cons-numbers ;
: app? ( e -- flag ) compact-tier expr-tag@ tag-app = ;
: parts ( e -- f a ) dup compact-tier expr-a@ swap compact-tier expr-b@ ;
: built ( e outcome -- e ) ok? 0= abort" bench: build failed" ;
: scratch-made ( -- n ) compact-scratch tier-exprs cons-records slab-count ;
: maybe-reset ( -- )
  scratch-made $40000 u> if compact-scratch tier-reset ok? 0= abort" bench: reset" then ;
: swapped ( prev e -- prev ) parts swap compact-scratch expr-app built drop maybe-reset ;
: chained ( prev e -- prev' )
  over 0< if nip dup then compact-tier expr-a@ compact-scratch expr-app built
  maybe-reset scratch-made 0= if drop -1 then ;
: found-again ( prev e -- prev ) parts compact-scratch expr-app built drop ;
: apps ( -- n ) 0 input-exprs 0 ?do i app? if 1+ then loop ;
\ Run xt ( prev e -- prev' ) on every input application; time per build.
: build-loop ( xt -- us )
  compact-scratch tier-reset drop now >r -1 input-exprs 0 ?do
    i app? if i 2 pick execute then loop
  2drop now r> - ;
: .per ( us n c-addr u -- ) type ." : " swap 1000 * swap 1 max / 0 .r ."  ns per build" cr ;
: .finds ( -- )
  ."   input table finds/compared " compact-tier tier-exprs cons-table htab-stats drop swap 0 .r
  ." /" 0 .r ."   scratch table " compact-scratch tier-exprs cons-table htab-stats drop
  swap 0 .r ." /" 0 .r cr ;
: compact-bench ( c-addr u log2 -- )
  compact-load ok? 0= abort" bench: load failed" scratch-ready
  ." input table slots " compact-tier tier-exprs cons-table htab-slots 0 .r
  ."  entries " compact-tier tier-exprs cons-table htab-count 0 .r cr
  apps ['] swapped build-loop over s" swapped (input children, new)" .per .finds
  ['] chained build-loop over s" chained (a scratch child, new)" .per .finds
  ['] found-again build-loop over s" again (found in the input)" .per .finds
  drop compact-scratch tier-free compact-free ;
