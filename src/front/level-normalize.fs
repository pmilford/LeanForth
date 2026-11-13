\ Lean 4.35.0's Level.normalize (Lean/Level.lean) for the front end (plan
\ FE1c; ADR 0021 D6), which Meta's isLevelDefEqAux applies to both sides
\ (level-defeq.fs). It is not the kernel's normalize (src/kernel/
\ level-normalize.fs, a port of level.cpp): Meta's orders names otherwise
\ and puts offsets elsewhere.
\ - lf-meta-level-normalize ( level -- level' outcome ): a level whose
\   base (under its successors) is zero, a parameter or a metavariable is
\   kept (isAlreadyNormalizedCheap). For succ^k (max a b): the arguments
\   (getMaxArgsAux: a and b through their maxes, every other level
\   normalized and its maxes flattened) sorted by normLt; of the explicit
\   ones (successors of zero) only the largest kept, and it is dropped too
\   when another argument's offset is at least as large (skipExplicit,
\   isExplicitSubsumed); of the arguments over one base only the last,
\   the largest offset; each with k more successors, put into a max from
\   the left (mkMaxAux). For succ^k (imax a b): when b is never zero, the
\   normal form of max a b under k successors; else mkIMaxAux of the
\   normal forms of a and b (zero for b zero, b for a zero or one, a when
\   they are equal, else an imax) under k successors.
\ - normLt: by base, then by offset. Two bases: max with max and imax
\   with imax by their first sides, or their second when the first are
\   equal; parameters by Lean's Name.lt; metavariables by number (Lean's
\   names _uniq.N, made in the same order); else by kind (zero, parameter,
\   metavariable, succ, max, imax).
\ - lf-meta-name-cmp ( a b -- n ): Lean's Name.cmp, -1, 0 or 1: the
\   prefixes first (a name that ends first is smaller), a number before a
\   string, then the last components (strings by bytes, numbers by value).
\ normLt orders unequal levels totally, so any sort gives the order of
\ Lean's qsort and the result is Lean's, node for node. Each node gets
\ its normal form once, bottom up, on dag-walk.fs's heap stacks; a max's
\ arguments are its sides' normal forms flattened, which after the sort
\ and the dropping are getMaxArgsAux's. No depth needs the host's stacks
\ (plan task 6.2.0), and a level shared in a DAG is normalized once (Lean
\ walks a max's arguments once per path). Cost: an insertion sort, and
\ each max of a chain gets its own normal form, so a max of n arguments
\ costs about n^2 comparisons and n^2 / 2 new levels (Lean: n log n
\ comparisons); plan FE1c lists bringing it down.
\ Outcomes: ok; invalid for a level not in the store or a parameter whose
\ name is no valid name; full when the store or the heap has no room.
\ Untrusted front-end code.
\ Words: lf-meta-level-normalize, lf-meta-name-cmp.
\ State: the record ln-state (the walk, the offset pushed into a max) and
\ the slabs ln-args and ln-todo, members of the checker context (ADR 0009).

require ../lib/lib.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/mvar-leaves.fs
require ./dag-walk.fs
require ./level-simp.fs

begin-structure /ln
  field: ln-k           \ the offset pushed into a max's arguments
  /dw +field ln-dw      \ the walk
end-structure
/ln context-record: ln-state
1 cells context-slab: ln-args   \ a max's arguments
1 cells context-slab: ln-todo   \ levels still to flatten

: ln-refuse ( outcome -- ) ln-state ln-dw dw-refuse ;
: ln-made ( level true | false -- level ) 0= if outcome-full ln-refuse 0 then ;
: ln-succs ( level k -- level' ) 0 ?do lf-level-succ ln-made loop ;
: ln-tag ( level -- tag ) lf-level-tag@ ;
: ln-zero? ( level -- flag ) ln-tag lf-level-tag-zero = ;
: ln-max? ( level -- flag ) ln-tag lf-level-tag-max = ;
: ln-offset ( level -- k ) ld-offset nip ;
\ Level.beq and isNeverZero; a failure ends the walk.
: ln-eq? ( a b -- flag ) lf-meta-level= dup ok? if drop else ln-refuse drop false then ;
: ln-never-zero? ( level -- flag )
  lf-meta-never-zero? dup ok? if drop else ln-refuse drop false then ;

\ Name.cmp: down both prefix chains while both go on with components of
\ one kind, keeping the comparison of the highest pair that differs;
\ then where they stopped decides (an end, or a number against a
\ string), else the kept comparison.
: ln-str? ( id -- flag ) lf-name-tag@ lf-name-tag-str = ;
: ln-both? ( a b -- flag ) 0<> swap 0<> and ;
: ln-going? ( a b -- flag )
  2dup = if 2drop false exit then
  2dup ln-both? if ln-str? swap ln-str? = else 2drop false then ;
: ln-ucmp ( u1 u2 -- -1|0|1 ) 2dup = if 2drop 0 exit then u< if -1 else 1 then ;
: ln-part ( a b -- n )
  over ln-str? if lf-name-text rot lf-name-text 2swap compare exit then
  lf-name-payload swap lf-name-payload swap ln-ucmp ;
: ln-keep ( n a b -- n' a b ) 2dup ln-part ?dup if >r rot drop r> -rot then ;
: ln-up ( a b -- a' b' ) lf-name-prefix@ swap lf-name-prefix@ swap ;
: ln-ends ( a b -- n )
  2dup = if 2drop 0 exit then 2dup ln-both? if drop ln-str? 1 and 2* 1- exit then
  0= swap 0= swap - ;
: lf-meta-name-cmp ( a b -- n )
  0 -rot begin 2dup ln-going? while ln-keep ln-up repeat ln-ends ?dup if nip then ;
\ A name each of whose components is valid (names.fs).
: ln-limb-ok? ( id -- flag ) dup lf-name-valid? if lf-name-part-ok? else drop false then ;
: ln-name-ok? ( id -- flag )
  begin dup while dup ln-limb-ok? 0= if drop false exit then lf-name-prefix@ repeat
  drop true ;

\ normLt. ln-strip gives the bases and k1 - k2 (Lean's k1 < k2 is d 0<).
: ln-strip ( l1 l2 -- b1 b2 d ) ld-offset >r swap ld-offset r> - >r swap r> ;
\ Lean's ctorToNat: zero 0, param 1, mvar 2, succ 3, max 4, imax 5.
: ln-ctor ( level -- n ) ln-tag dup 4 < if dup 0<> 2 and + else 3 - then ;
: ln-firsts ( a b -- a' b' ) lf-level-first@ swap lf-level-first@ swap ;
: ln-seconds ( a b -- a' b' ) lf-level-second@ swap lf-level-second@ swap ;
: ln-other< ( b1 b2 d -- flag )
  >r 2dup ln-eq? if 2drop r> 0< exit then r> drop ln-ctor swap ln-ctor swap < ;
: ln-sides ( b1 b2 -- l1 l2 ) 2dup ln-firsts ln-eq? if ln-seconds else ln-firsts then ;
: ln-pairs< ( b1 b2 d -- flag true | l1 l2 false )
  >r 2dup ln-eq? if 2drop r> 0< true exit then r> drop ln-sides false ;
: ln-names< ( b1 b2 -- flag )
  ln-firsts 2dup ln-name-ok? swap ln-name-ok? and
  if lf-meta-name-cmp 0< else 2drop outcome-invalid ln-refuse false then ;
: ln-leaves< ( b1 b2 d -- flag )
  >r 2dup ln-firsts = if 2drop r> 0< exit then r> drop
  dup ld-param? if ln-names< else ln-firsts < then ;
: ln-leaf? ( level -- flag ) dup ld-param? swap lf-level-mvar? or ;
: ln-step ( b1 b2 d -- flag true | l1 l2 false )
  >r 2dup ln-tag swap ln-tag <> if r> ln-other< true exit then
  dup ln-tag lf-level-binary-tag? if r> ln-pairs< exit then
  dup ln-leaf? if r> ln-leaves< else r> ln-other< then true ;
: ln-lt? ( l1 l2 -- flag ) begin ln-strip ln-step 0= while repeat ;

\ The arguments: flattened through max nodes, then sorted by insertion.
: ln-arg ( i -- addr ) ln-args slab-at ;
: ln-count ( -- n ) ln-args slab-count ;
: ln-put ( level slab -- )
  1 over slab-claim dup ok? if drop swap slab-at ! else ln-refuse 2drop drop then ;
: ln-pop ( -- level ) ln-todo dup slab-count 1- swap slab-at @ -1 ln-todo slab-commit ;
: ln-spread ( level -- )
  dup ln-max? 0= if ln-args ln-put exit then
  dup lf-level-second@ ln-todo ln-put lf-level-first@ ln-todo ln-put ;
: ln-flatten ( a b -- )
  ln-args slab-clear ln-todo slab-clear ln-todo ln-put ln-todo ln-put
  begin ln-todo slab-count 0> while ln-pop ln-spread repeat ;
: ln-before? ( x j -- x j flag ) dup 0> if 2dup 1- ln-arg @ ln-lt? else false then ;
: ln-insert ( i -- )
  dup ln-arg @ swap begin ln-before? while dup 1- ln-arg @ over ln-arg ! 1- repeat
  ln-arg ! ;
: ln-sort ( -- ) ln-count 1 max 1 ?do i ln-insert loop ;

\ skipExplicit and isExplicitSubsumed: the first argument kept.
: ln-explicit? ( level -- flag ) ld-base ln-zero? ;
: ln-plain ( -- i )
  ln-count dup 0 ?do i ln-arg @ ln-explicit? 0= if drop i leave then loop ;
: ln-above? ( k i -- flag ) ln-arg @ ln-offset <= ;
: ln-subsumed? ( f -- flag )
  dup 0= if exit then dup 1- ln-arg @ ln-offset false rot ln-count swap
  ?do over i ln-above? or loop nip ;
: ln-first ( -- i ) ln-plain dup ln-subsumed? 0= if 1- 0 max then ;
\ mkMaxAux from the first argument kept: an argument is added (accMax)
\ when the next has another base, and the last at the end.
: ln-lift ( level -- level' ) ln-state ln-k @ ln-succs ;
: ln-acc ( result level -- result' )
  ln-lift over ln-zero? if nip else lf-level-max ln-made then ;
: ln-new-base? ( j -- flag ) dup ln-arg @ ld-base swap 1- ln-arg @ ld-base ln-eq? 0= ;
: ln-fold-step ( result j -- result' )
  dup ln-new-base? if 1- ln-arg @ ln-acc else drop then ;
: ln-fold ( i -- level )
  0 swap ln-count swap 1+ ?do i ln-fold-step loop ln-count 1- ln-arg @ ln-acc ;
: ln-max-image ( a b k -- level ) ln-state ln-k ! ln-flatten ln-sort ln-first ln-fold ;
\ mkIMaxAux.
: ln-one? ( level -- flag ) dup ld-succ? if ld-pred ln-zero? else drop false then ;
: ln-imax-aux ( a b -- level )
  dup ln-zero? if nip exit then over ln-zero? if nip exit then
  over ln-one? if nip exit then 2dup ln-eq? if drop exit then lf-level-imax ln-made ;

\ The walk: a node over a max or an imax waits for its base's two sides.
: ln-open? ( level -- flag ) ld-base ln-tag lf-level-binary-tag? ;
: ln-parts ( level -- a b ) ld-base dup lf-level-first@ swap lf-level-second@ ;
: ln-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: ln-pair-pending ( a b walk -- child true | false )
  rot over ln-undone if nip nip true else ln-undone then ;
: ln-pending ( node walk -- child true | false )
  over ln-open? if >r ln-parts r> ln-pair-pending else 2drop false then ;
: ln-images ( node walk -- a' b' ) >r ln-parts r@ dw-image swap r> dw-image swap ;
: ln-imax ( node walk -- level )
  over ld-base lf-level-second@ ln-never-zero?
  if ln-images 0 ln-max-image else ln-images ln-imax-aux then ;
: ln-build ( node walk -- image )
  over ln-open? 0= if drop exit then over ln-offset >r
  over ld-base ln-max? if ln-images r> ln-max-image exit then ln-imax r> ln-succs ;
: ln-walk ( -- walk )
  ln-state ln-dw ['] ln-build over dw-build ! ['] ln-pending over dw-pending !
  lf-level-count @ over dw-size ! ;
: lf-meta-level-normalize ( level -- level' outcome )
  dup lf-level-root? 0= if drop -1 outcome-invalid exit then
  dup ln-open? if ln-walk dw-run else outcome-ok then ;
