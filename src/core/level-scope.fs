\ Bounded shape and parameter-scope validation for level DAGs: every node is
\ well formed, children come earlier, and every parameter is in the current
\ context. Untrusted. It does not compare levels, establish Lean name
\ identity, check types or authorize a theorem. Requires levels.fs.
\ State: one context record, lf-lscope-state (a duplicate-free list of
\ positive parameter IDs with a generation that advances on every change),
\ and one walk record, lf-lscope-walk. Not re-entrant and single-threaded:
\ the check must not run again while its walk record is in use. Callers
\ prevent external mutation.

outcome-ok constant lf-lscope-ok
outcome-invalid constant lf-lscope-invalid
outcome-exhausted constant lf-lscope-exhausted

begin-structure /lf-lsctx
  field: lf-lsctx-count         \ parameter IDs in the context
  field: lf-lsctx-generation    \ advances on every change; negative when spent
  lf-level-capacity cells +field lf-lsctx-ids
end-structure
create lf-lscope-state /lf-lsctx allot
lf-lscope-state /lf-lsctx erase
lf-level-capacity walk: lf-lscope-walk

\ The context's fields under their established names (other modules read
\ the count and generation; tests corrupt them).
: lf-lscope-context ( -- addr ) lf-lscope-state lf-lsctx-ids ;
: lf-lscope-context-count ( -- addr ) lf-lscope-state lf-lsctx-count ;
: lf-lscope-generation ( -- addr ) lf-lscope-state lf-lsctx-generation ;

\ Fuel left after a check, under its established name; level-value,
\ level-compare, level-substitute and constant-term-boundary read it.
: lf-lscope-fuel ( -- addr ) lf-lscope-walk walk-fuel ;

\ The parameter context. Every change advances the generation, so sessions
\ that captured the old one become stale; saturation poisons the context.
: lf-lscope-advance ( -- ) lf-lscope-generation dup @ epoch+ swap ! ;
: lf-lscope-context-reset ( -- ) 0 lf-lscope-context-count ! lf-lscope-advance ;
: lf-lscope-count-valid? ( -- flag )
  lf-lscope-context-count @ lf-level-capacity upto? lf-lscope-generation @ 0< 0= and ;
: lf-lscope-slot ( i -- addr ) cells lf-lscope-context + ;
: lf-lscope-id@ ( i -- id ) lf-lscope-slot @ ;
\ Search the first n entries; the caller has validated n.
: lf-lscope-in? ( id n -- flag )
  0 ?do dup i lf-lscope-id@ = if drop true unloop exit then loop drop false ;
: lf-lscope-member? ( id -- flag ) lf-lscope-context-count @ lf-lscope-in? ;
\ Entry i is positive and differs from every earlier entry. Checking all
\ entries is quadratic, bounded by 64, and separate from visit fuel.
: lf-lscope-entry-ok? ( i -- flag )
  dup lf-lscope-id@ dup 0> if swap lf-lscope-in? 0= else 2drop false then ;
: lf-lscope-entries-ok? ( -- flag )
  lf-lscope-context-count @ 0 ?do
    i lf-lscope-entry-ok? 0= if false unloop exit then loop true ;
: lf-lscope-context-valid? ( -- flag )
  lf-lscope-count-valid? if lf-lscope-entries-ok? else false then ;

\ Add a positive, new identifier to a valid context. Failure, including
\ corrupted entries, a full context or a spent generation, changes nothing.
: lf-lscope-new-id? ( id -- flag ) dup 0> swap lf-lscope-member? 0= and ;
: lf-lscope-room? ( -- flag )
  lf-lscope-context-count @ lf-level-capacity < lf-lscope-generation @ max-n <> and ;
: lf-lscope-addable? ( id -- flag ) lf-lscope-new-id? lf-lscope-room? and ;
: lf-lscope-append ( id -- )
  lf-lscope-context-count @ lf-lscope-slot ! 1 lf-lscope-context-count +! ;
: lf-lscope-context-add ( id -- flag )
  lf-lscope-context-valid? if dup lf-lscope-addable? else false then
  if lf-lscope-append lf-lscope-advance lf-lscope-count-valid? else drop false then ;

\ Visiting one level node. Zero is valid only as node 0 with zero fields; a
\ parameter needs a positive ID in the context; succ, max and imax push
\ their earlier children.
: lf-lscope-zero ( first second walk -- outcome ) walk-node @ or or 0= flag>outcome ;
: lf-lscope-param ( first second walk -- outcome )
  drop 0= over 0> and if lf-lscope-member? flag>outcome else drop outcome-invalid then ;
: lf-lscope-succ ( first second walk -- outcome ) swap 0<> if 2drop outcome-invalid else walk-child then ;
: lf-lscope-dispatch ( first second walk tag -- outcome )
  dup lf-level-binary-tag? if drop walk-children exit then
  case lf-level-tag-zero of lf-lscope-zero endof
    lf-level-tag-param of lf-lscope-param endof
    lf-level-tag-succ of lf-lscope-succ endof walk-bad-tag endcase ;
: lf-lscope-visit ( walk -- outcome ) lf-levels ['] lf-lscope-dispatch walk-visit ;

\ Validate a root against the current context with a visit budget. Each DAG
\ occurrence consumes fuel; shared nodes are deliberately visited repeatedly.
\ The zero node is checked even when the root does not reach it. Success is
\ only structural evidence, not a level equality judgment.
: lf-lscope-zero-ok? ( -- flag ) 0 lf-level-read if or or 0= else false then ;
: lf-lscope-ready? ( root -- flag )
  lf-lscope-context-valid? swap lf-level-valid? and lf-lscope-zero-ok? and ;
: lf-lscope-run ( root -- status ) ['] lf-lscope-visit lf-lscope-walk walk-run ;
: lf-lscope-check ( root fuel -- status )
  lf-lscope-walk walk-budget 0= if drop-invalid exit then
  dup lf-lscope-ready? if lf-lscope-run else drop-invalid then ;

\ Check a level from inside another walk, charging that walk's fuel and
\ continuing with the fuel the level check leaves.
: lf-lscope-walk-check ( level walk -- outcome )
  tuck walk-fuel @ lf-lscope-check lf-lscope-fuel @ rot walk-fuel ! outcome-sane ;

0 lf-lscope-generation !
lf-lscope-context-reset
