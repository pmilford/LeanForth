\ Bounded shape and parameter-scope validation for level DAGs: every node is
\ well formed, children come earlier, and every parameter is in the current
\ context. Untrusted. It does not compare levels, establish Lean name
\ identity, check types or authorize a theorem.
\ State: one parameter-context record, lf-lscope-state (a duplicate-free
\ list of positive parameter IDs with a generation that advances on every
\ change), and one walk record, lf-lscope-walk, both members of the
\ checker context (lib/context.fs); a set-up word starts every context's
\ parameter context empty. Single-threaded within one context: the check
\ must not run again while its walk record is in use. Callers prevent
\ external mutation.

require ../lib/lib.fs
require ./diagnostics.fs
require ./levels.fs

\ The audit of the entries (lf-lscope-entries-ok?) finds repeats through a
\ scratch table of lf-lscope-slots# cells, twice the most entries.
lf-level-params-limit 2* constant lf-lscope-slots#
begin-structure /lf-lsctx
  field: lf-lsctx-count         \ parameter IDs in the context
  field: lf-lsctx-generation    \ advances on every change; negative when spent
  lf-level-params-limit cells +field lf-lsctx-ids
  lf-lscope-slots# cells +field lf-lsctx-seen   \ the audit's scratch table
end-structure
/lf-lsctx context-record: lf-lscope-state
lf-level-depth-limit context-walk: lf-lscope-walk

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
  lf-lscope-context-count @ lf-level-params-limit upto? lf-lscope-generation @ 0< 0= and ;
: lf-lscope-slot ( i -- addr ) cells lf-lscope-context + ;
: lf-lscope-id@ ( i -- id ) lf-lscope-slot @ ;
\ Search the first n entries; the caller has validated n.
: lf-lscope-in? ( id n -- flag )
  0 ?do dup i lf-lscope-id@ = if drop true unloop exit then loop drop false ;
: lf-lscope-member? ( id -- flag ) lf-lscope-context-count @ lf-lscope-in? ;
\ Every entry is positive and differs from every other; the count was
\ checked first. Separate from visit fuel. A few entries are compared
\ pairwise; more, such as every universe parameter of a whole export, go
\ through the scratch table: each ID into the first free slot from its
\ hash (open addressing; the table, twice the most entries, never fills),
\ and an ID met there already is a repeat, so the audit stays linear.
16 constant lf-lscope-few
: lf-lscope-pair-ok? ( i -- flag )
  dup lf-lscope-id@ dup 0> if swap lf-lscope-in? 0= else 2drop false then ;
: lf-lscope-seen ( slot -- addr ) cells lf-lscope-state lf-lsctx-seen + ;
: lf-lscope-next ( slot -- slot' ) 1+ lf-lscope-slots# 1- and ;
\ Unchecked: id > 0. True when id is in the table already, else put it in.
: lf-lscope-seen? ( id -- flag )
  dup lf-lscope-slots# 1- and begin dup lf-lscope-seen @ ?dup while
    2 pick = if 2drop true exit then lf-lscope-next
  repeat lf-lscope-seen ! false ;
: lf-lscope-hash-ok? ( i -- flag )
  lf-lscope-id@ dup 0> if lf-lscope-seen? 0= else drop false then ;
: lf-lscope-pairs-ok? ( -- flag )
  lf-lscope-context-count @ 0 ?do
    i lf-lscope-pair-ok? 0= if false unloop exit then loop true ;
: lf-lscope-hashed-ok? ( -- flag )
  0 lf-lscope-seen lf-lscope-slots# cells erase lf-lscope-context-count @ 0 ?do
    i lf-lscope-hash-ok? 0= if false unloop exit then loop true ;
: lf-lscope-entries-ok? ( -- flag )
  lf-lscope-context-count @ lf-lscope-few <
  if lf-lscope-pairs-ok? else lf-lscope-hashed-ok? then ;
: lf-lscope-context-valid? ( -- flag )
  lf-lscope-count-valid? if lf-lscope-entries-ok? else false then ;

\ Add a positive, new identifier to a valid context. Failure, including
\ corrupted entries, a full context or a spent generation, changes nothing.
: lf-lscope-new-id? ( id -- flag ) dup 0> swap lf-lscope-member? 0= and ;
: lf-lscope-room? ( -- flag )
  lf-lscope-context-count @ lf-level-params-limit < lf-lscope-generation @ max-n <> and ;
: lf-lscope-addable? ( id -- flag ) lf-lscope-new-id? lf-lscope-room? and ;
: lf-lscope-append ( id -- )
  lf-lscope-context-count @ lf-lscope-slot ! 1 lf-lscope-context-count +! ;
: lf-lscope-context-add ( id -- flag )
  lf-lscope-context-valid? if dup lf-lscope-addable? else false then
  if lf-lscope-append lf-lscope-advance lf-lscope-count-valid? else drop false then ;

\ Visiting one level node. Zero is valid only as node 0 with zero fields; a
\ parameter needs a positive ID in the context; succ, max and imax push
\ their earlier children.
: lf-lscope-site ( -- site ) c" level-scope lf-lscope-check" ;
: lf-lscope-zero ( first second walk -- outcome ) walk-node @ or or 0= flag>outcome ;
\ A parameter outside the context is recorded as out of scope.
: lf-lscope-outside ( id -- outcome )
  0 lf-lscope-site lf-diag-out-of-scope lf-diag-note outcome-invalid ;
: lf-lscope-param-in ( id -- outcome )
  dup lf-lscope-member? if drop outcome-ok else lf-lscope-outside then ;
: lf-lscope-param ( first second walk -- outcome )
  drop 0= over 0> and if lf-lscope-param-in else drop outcome-invalid then ;
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
: lf-lscope-run ( root -- status )
  ['] lf-lscope-visit lf-lscope-walk walk-run lf-lscope-walk lf-lscope-site lf-diag-walk ;
: lf-lscope-check ( root fuel -- status )
  lf-lscope-walk walk-budget 0= if drop-invalid exit then
  dup lf-lscope-ready? if lf-lscope-run else drop-invalid then ;

\ Check a level from inside another walk, charging that walk's fuel and
\ continuing with the fuel the level check leaves.
: lf-lscope-walk-check ( level walk -- outcome )
  tuck walk-fuel @ lf-lscope-check lf-lscope-fuel @ rot walk-fuel ! outcome-sane ;

\ Every context starts with an empty parameter context of generation 1
\ (the record starts zeroed).
' lf-lscope-context-reset context-setup
