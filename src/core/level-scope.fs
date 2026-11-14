\ Bounded shape and parameter-scope validation for level DAGs: every node is
\ well formed, children come earlier, and every parameter is in the current
\ context. Untrusted. It does not compare levels, establish Lean name
\ identity, check types or authorize a theorem.
\ State: one parameter-context record, lf-lscope-state (the count of a
\ duplicate-free list of positive parameter IDs, a generation that
\ advances on every change, and the count of the audit's copy), the list
\ itself, the audit's scratch table and the copy of the list the audit
\ last passed, growable arrays with no fixed limit (context-slab:, plan
\ task 6.2.0: a context that cannot grow is full), and one walk record,
\ lf-lscope-walk, all members of the checker context (lib/context.fs); a
\ set-up word starts every context's parameter context empty. Single-threaded within one context: the check
\ must not run again while its walk record is in use. Callers prevent
\ external mutation.

require ../lib/lib.fs
require ./diagnostics.fs
require ./levels.fs

\ The audit of the entries (lf-lscope-entries-ok?) finds repeats through a
\ scratch table of lf-lscope-slots cells for n entries: the smallest power
\ of two at least 2n and 32. The probe masks with slots - 1, so the count
\ must be a power of two; the audit checks it before use.
: lf-lscope-power-of-two? ( n -- flag ) dup 0> swap dup 1- and 0= and ;
: lf-lscope-slots ( n -- slots ) 2* 32 begin 2dup > while 2* repeat nip ;
begin-structure /lf-lsctx
  field: lf-lsctx-count         \ parameter IDs in the context
  field: lf-lsctx-generation    \ advances on every change; negative when spent
  field: lf-lsctx-passed        \ IDs in lf-lscope-audited plus one; 0: no copy
end-structure
/lf-lsctx context-record: lf-lscope-state
1 cells context-slab: lf-lscope-ids     \ the parameter IDs, in order
1 cells context-slab: lf-lscope-table   \ the audit's scratch table
1 cells context-slab: lf-lscope-audited \ the IDs the audit last passed
lf-level-walk-room context-walk: lf-lscope-walk

\ The context's fields under their established names (other modules read
\ the count and generation; tests corrupt them). lf-lscope-context is the
\ first ID's address, valid while the list does not grow.
: lf-lscope-context ( -- addr ) lf-lscope-ids slab-base ;
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
  lf-lscope-context-count @ lf-lscope-ids slab-capacity upto?
  lf-lscope-generation @ 0< 0= and ;
: lf-lscope-slot ( i -- addr ) cells lf-lscope-context + ;
: lf-lscope-id@ ( i -- id ) lf-lscope-slot @ ;
\ Search the first n entries; the caller has validated n.
: lf-lscope-in? ( id n -- flag ) lf-lscope-context swap cells-has? ;
: lf-lscope-member? ( id -- flag ) lf-lscope-context-count @ lf-lscope-in? ;
\ Every entry is positive and differs from every other; the count was
\ checked first. Separate from visit fuel. A few entries are compared
\ pairwise; more, such as every universe parameter of a whole export, go
\ through the scratch table: each ID into the first free slot from its
\ hash (open addressing; the table, at least twice the entries, never
\ fills), and an ID met there already is a repeat, so the audit stays
\ linear. A table the heap cannot give falls back to the pairwise audit.
16 constant lf-lscope-few
\ Whether entry i of the list of IDs at addr is positive and differs from
\ every entry before it (here and level-substitute.fs's formals).
: lf-lscope-fresh? ( i addr -- flag )
  2dup swap cells + @ dup 0> if -rot swap cells-has? 0= else drop 2drop false then ;
: lf-lscope-pair-ok? ( i -- flag ) lf-lscope-context lf-lscope-fresh? ;
: lf-lscope-seen ( slot -- addr ) cells lf-lscope-table slab-base + ;
\ Unchecked: id > 0 and mask + 1 a power of two of free or used slots.
\ True when id is in the table already, else put it in.
: lf-lscope-seen? ( id mask -- flag )
  2dup and begin dup lf-lscope-seen @ ?dup while
    3 pick = if 2drop drop true exit then 1+ over and   \ next slot, wrapped
  repeat nip lf-lscope-seen ! false ;
: lf-lscope-hash-ok? ( mask i -- mask flag )
  lf-lscope-id@ dup 0> if over lf-lscope-seen? 0= else drop false then ;
: lf-lscope-pairs-ok? ( -- flag ) lf-lscope-context-count @ ['] lf-lscope-pair-ok? all? ;
: lf-lscope-hashed ( slots -- flag )
  dup cells 0 lf-lscope-seen swap erase 1- lf-lscope-context-count @
  ['] lf-lscope-hash-ok? all? nip ;
: lf-lscope-table? ( slots -- flag )
  dup lf-lscope-power-of-two? if lf-lscope-table slab-hold ok? else drop false then ;
: lf-lscope-hashed-ok? ( -- flag )
  lf-lscope-context-count @ lf-lscope-slots dup lf-lscope-table?
  if lf-lscope-hashed else drop lf-lscope-pairs-ok? then ;
: lf-lscope-audit ( -- flag )
  lf-lscope-context-count @ lf-lscope-few <
  if lf-lscope-pairs-ok? else lf-lscope-hashed-ok? then ;
\ The audit's answer depends only on the entries, which the checker reads
\ (feed.fs puts every parameter of an export in the context) but never
\ changes while it checks. So the entries the audit last passed are kept,
\ and entries equal to them, byte for byte, pass again without the audit
\ (agent PERF1: the audit, linear in the entries, ran at every level
\ check, about 6% of Init's checking time); any other entries, corrupted
\ or changed, are audited anew. A copy the heap cannot hold is not kept.
\ The copy's count (passed - 1) is checked against the copy's capacity
\ before the compared range is formed, as the entries' count was against
\ theirs, so a corrupted count never reads beyond the copy: it goes to the
\ audit (review rvPF1 3).
: lf-lscope-entries ( -- addr u ) lf-lscope-context lf-lscope-context-count @ cells ;
: lf-lscope-passed ( -- addr ) lf-lscope-state lf-lsctx-passed ;
: lf-lscope-copied ( -- n ) lf-lscope-passed @ 1- ;
: lf-lscope-copy ( -- addr u ) lf-lscope-audited slab-base lf-lscope-copied cells ;
: lf-lscope-held? ( n -- flag ) lf-lscope-audited slab-capacity upto? ;
: lf-lscope-copy-fits? ( -- flag )
  lf-lscope-copied dup lf-lscope-held? swap lf-lscope-context-count @ = and ;
\ COMPARE orders cells by their bytes, an order that depends on the host;
\ only its 0= is used here, equal or not, which does not.
: lf-lscope-passed? ( -- flag )
  lf-lscope-copy-fits?
  if lf-lscope-entries lf-lscope-copy compare 0= else false then ;
\ A pass drops the old copy, then keeps the n entries as the new one when
\ the copy's slab can hold them (lf-lscope-keep), else none.
: lf-lscope-keep ( n -- )
  lf-lscope-entries lf-lscope-audited slab-base swap move 1+ lf-lscope-passed ! ;
: lf-lscope-pass ( -- )
  0 lf-lscope-passed !  lf-lscope-context-count @ dup lf-lscope-audited slab-hold ok?
  if lf-lscope-keep else drop then ;
\ Unchecked: the count was checked (lf-lscope-count-valid?).
: lf-lscope-entries-ok? ( -- flag )
  lf-lscope-passed? if true exit then lf-lscope-audit dup if lf-lscope-pass then ;
: lf-lscope-context-valid? ( -- flag )
  lf-lscope-count-valid? if lf-lscope-entries-ok? else false then ;

\ Add a positive, new identifier to a valid context. Failure, including
\ corrupted entries, a context the heap cannot grow or a spent
\ generation, changes nothing.
: lf-lscope-new-id? ( id -- flag ) dup 0> swap lf-lscope-member? 0= and ;
: lf-lscope-room? ( -- flag )
  lf-lscope-generation @ max-n <> dup 0= if exit then
  drop lf-lscope-context-count @ 1+ lf-lscope-ids slab-hold ok? ;
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
  lf-lscope-context-valid? swap lf-level-root? and lf-lscope-zero-ok? and ;
: lf-lscope-run ( root -- status )
  ['] lf-lscope-visit lf-lscope-walk lf-lscope-site lf-diag-run ;
\ A root found in scope is passed to the hook lf-lscope-reached ( root -- ),
\ by default nothing; core/constant-term-boundary.fs keeps it as reached
\ in this check (agent PF, ADR 0014 Amendment 7).
defer lf-lscope-reached ( root -- )
' drop is lf-lscope-reached
: lf-lscope-noted ( root status -- status )
  dup ok? if swap lf-lscope-reached else nip then ;
: lf-lscope-check ( root fuel -- status )
  lf-lscope-walk walk-budget 0= if drop-invalid exit then
  dup lf-lscope-ready? if dup lf-lscope-run lf-lscope-noted else drop-invalid then ;

\ Check a level from inside another walk, charging that walk's fuel and
\ continuing with the fuel the level check leaves.
: lf-lscope-walk-check ( level walk -- outcome )
  tuck walk-fuel @ lf-lscope-check lf-lscope-fuel @ rot walk-fuel ! outcome-sane ;

\ Every context starts with an empty parameter context of generation 1
\ (the record starts zeroed).
' lf-lscope-context-reset context-setup
