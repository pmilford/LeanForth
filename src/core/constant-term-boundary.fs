\ Constant nodes in symbolic terms, and the structural check of a whole
\ constant-bearing term graph. Untrusted: no lookup, typing, binder scope or
\ proof checking. A constant node's fields hold its reference's index and
\ 0 (compact-store plan step S4: no 32-bit identity field, so no count of
\ references made limits a context), and a stamp table binds it to this
\ exact term allocation and that reference's identity, so a reset cannot
\ resurrect it. Binary constructors capture child indices, not identities;
\ their safety relies on backward edges and no raw mutation or count edits.
\ State: the stamps of generation-handles.fs (a map from term index to
\ stamp unit; a constant's stamps are its own identity, as a symbolic
\ Sort's term stamp is, and its reference's, as a Sort's level stamp is,
\ both full cells), the marks column lf-term-marks with
\ its run counter lf-mark-runs, the input nodes' mark pages (their
\ directory lf-mark-pages and list lf-mark-made, the pages heap blocks
\ freed by a teardown word) and their spare lf-mark-spare (below), the
\ pair set of one run (its table lf-pair-table, entries lf-pair-entries
\ and record lf-pair-state, below; the table's block freed by a teardown
\ word), the audit memo's record
\ lf-audit-state and its list lf-audit-reached (below), the levels' and
\ references' reach marks lf-level-reach and lf-cref-reach, and one
\ walk record, lf-cterm-walker, all members of the checker context
\ (lib/context.fs). The hook lf-audit-checking? is set while loading
\ (kernel/check-declaration.fs) and read-only afterwards, as is the table
\ lf-audit-facts. Each constant and symbolic Sort visit also runs a
\ level-scope check on level-scope's walk record (lf-lscope-walk), so this
\ check must not run while another module borrows that record.
\ Single-threaded within one context. Identities are forgeable,
\ context-local diagnostics; the memory layout is not a serialization
\ format.

require ../lib/lib.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ../lib/slab.fs
require ../lib/store-columns.fs
require ./constant-references.fs
require ./diagnostics.fs
require ./generation-handles.fs
require ./let-terms.fs
require ./level-scope.fs
require ./local-context.fs
require ./literals.fs
require ./string-literals.fs
require ./projections.fs
require ./symbolic-session.fs
require ./tagged-sort-boundary.fs
require ./terms.fs

7 constant lf-tag-constant
\ An input constant of a term view (terms.fs) has its reference in the
\ leaf table.
lf-tag-constant tag-const lf-term-input-leaf-tag
lf-walk-room context-walk: lf-cterm-walker

\ The data words of the checker's leaves (terms.fs's hook lf-term-leaf-data;
\ ADR 0016 C1, compact-store plan step S3), the facts kernel/caches.fs's
\ memo finds for them: a bound variable its index plus one; a free
\ variable the free-variable bit; a symbolic Sort and a constant the
\ parameter bit of their levels (levels.fs keeps it per level), when the
\ level, or the reference and its levels, are valid when the node is
\ made, else no data; a projection, literal, string literal or let leaf
\ nothing (0); any other leaf (a concrete Sort, an unsupported form) no
\ data.
: lf-data-params ( flag -- data ) 0 swap false lf-data ;
: lf-cterm-sort-data ( level second -- data )
  drop dup lf-level-valid? 0= if drop lf-data-unknown exit then
  lf-level-params? lf-data-params ;
: lf-cterm-params? ( addr count -- flag )
  false swap 0 ?do over i lf-cref-pair@ drop lf-level-params? or loop nip ;
\ A constant's reference by its index (its second field is 0): the record
\ there, which lf-cterm-new checked just before making the node.
: lf-cterm-const-data ( cref second -- data )
  if drop lf-data-unknown exit then
  dup lf-cref-current lf-cref-levels
  if lf-cterm-params? lf-data-params else lf-data-unknown then ;
: lf-cterm-leaf-data ( tag first second -- data )
  rot case
    lf-tag-bvar of lf-bvar-data endof
    lf-tag-symbolic-sort of lf-cterm-sort-data endof
    lf-tag-constant of lf-cterm-const-data endof
    lf-tag-fvar of 2drop 0 false true lf-data endof
    lf-tag-proj of 2drop 0 endof  lf-tag-lit of 2drop 0 endof
    lf-tag-str of 2drop 0 endof
    >r 2drop lf-data-unknown r> endcase ;
' lf-cterm-leaf-data is lf-term-leaf-data

\ Marks: audits that check each node once, however many paths reach it.
\ Lean keeps a node's closedness data in the node itself, computed once
\ (expr.cpp 105, lean_expr_mk_data), and reads it in constant time
\ (check_no_metavar_no_fvar, environment.cpp 87-100; infer_type_core's
\ has_loose_bvars, type_checker.cpp 326), so its checks grow with the
\ nodes, never with the paths. A marking walk keeps, per term, the run
\ that reached the node and the depth at which it did (the walk's context
\ cell; 0 in a walk of single cells). Each run takes a new number from
\ the context's counter into its walk's arg cell, so a walk run inside
\ another's visit can never make that one skip a node it has not checked;
\ a counter that wraps to 0 erases every mark. The visitor (after
\ walk-read has validated the node) skips a node this run reached before
\ at a depth no greater -- a bound variable in scope at one depth is in
\ scope at any greater one -- and the skip costs only the visit's unit of
\ fuel. Every node a run that ends ok has reached was checked.
/slab context-record: lf-term-marks
2 cells ' lf-term-marks lf-term-columns column-add
1 cells context-record: lf-mark-runs
\ The input nodes of a term view (terms.fs) have their units (one per
\ tier record and leaf entry, terms.fs's lf-term-input-unit) in pages of
\ 2^lf-mark-page-bits units, each made, zeroed, when a unit of it is
\ first reached, listed, and given back by lf-marks-release, which every
\ check runs first (lf-audit-afresh): a unit is read only by the run or
\ the memo epoch that wrote it, every check starts new ones, so no mark
\ outlives its check, and a context holds only the pages its current
\ check reached (shared input, ADR 0016 S8; before, one slab over every
\ input unit, 16 bytes each, about 1.7 GB per worker for all of Mathlib).
\ The directory holds a page's block per page, 0 for none; it is sized,
\ and every page given back, when a view is attached or detached
\ (lf-term-view-hook). A node beyond it (a view whose directory the
\ heap could not hold, which terms.fs then detaches) or whose page the
\ heap cannot give gets a spare unit, erased each time, so it is never
\ held: more visits, never another outcome.
8 constant lf-mark-page-bits
1 lf-mark-page-bits lshift 1- constant lf-mark-page-mask
1 cells context-slab: lf-mark-pages   \ the directory: per page, its block or 0
1 cells context-slab: lf-mark-made    \ the pages made since the last release
2 cells context-record: lf-mark-spare
: lf-mark-page ( p -- addr ) lf-mark-pages slab-at ;
: lf-mark-page-bytes ( -- u ) 1 lf-mark-page-bits lshift 2* cells ;
\ Every page made given back, its directory cell emptied (also the
\ teardown: a context's pages are freed with it).
: lf-mark-unmake ( p -- ) lf-mark-page dup @ ?dup if free drop then 0 swap ! ;
: lf-marks-release ( -- )
  lf-mark-made slab-count 0 ?do i lf-mark-made slab-at @ lf-mark-unmake loop
  lf-mark-made slab-clear ;
' lf-marks-release context-teardown
: lf-mark-pages# ( -- n )
  lf-term-input-units lf-mark-page-mask + lf-mark-page-bits rshift ;
: lf-input-marks-ready ( -- outcome )
  lf-marks-release lf-mark-pages# lf-mark-pages slab-hold dup ok?
  if 0 lf-mark-page lf-mark-pages slab-capacity cells erase then ;
' lf-input-marks-ready is lf-term-view-hook
: lf-mark-spared ( -- unit ) lf-mark-spare dup 2 cells erase ;
\ Page p made: listed first, so that the release finds it whatever
\ fails; its block, or 0 when the list or the heap has no room.
: lf-mark-zeroed ( p -- addr|0 )
  lf-mark-page-bytes allocate0 if 2drop 0 exit then tuck swap lf-mark-page ! ;
: lf-mark-listed ( p -- addr|0 )
  1 lf-mark-made slab-claim ok? 0= if 2drop 0 exit then
  lf-mark-made slab-at over swap ! lf-mark-zeroed ;
: lf-mark-paged ( p -- addr|0 ) dup lf-mark-page @ ?dup if nip else lf-mark-listed then ;
: lf-mark-in-page ( u addr -- unit ) swap lf-mark-page-mask and 2* cells + ;
: lf-input-mark-at ( node -- unit )
  lf-term-input-unit 0= if lf-mark-spared exit then
  dup lf-mark-page-bits rshift dup lf-mark-pages slab-capacity u<
  if lf-mark-paged ?dup if lf-mark-in-page exit then else drop then
  drop lf-mark-spared ;
\ A node's unit (two cells), input or store.
: lf-mark-at ( node -- unit )
  dup lf-term-input? if lf-input-mark-at exit then
  lf-term-base - lf-term-marks column-at ;

\ The pair set (review rvKN 1 and 2): the (node, depth) pairs one run
\ reached, for a walk whose marks a unit cannot keep -- a node met at
\ several depths (lf-walk-once-at), or a run inside another walk's visit
\ (lf-walk-once-aside), which must leave that walk's units as they are.
\ Lean keeps such a set per call: for_each_offset_fn its cache of (node,
\ offset) pairs, find_fn its cache of nodes (for_each_fn.cpp,
\ find_fn.cpp). A hash table (lib/htab.fs) over a slab of (node depth)
\ entries holds the pairs of one run, the set's: lf-walk-pairing starts a
\ run and empties the set for it. A lookup by another run (one started
\ inside the set's run took the set) finds nothing and keeps nothing, and
\ a table or slab the heap cannot grow keeps nothing more: more visits,
\ never a pair skipped unvisited. A counter that wraps (lf-marks-erase)
\ leaves the set no run (0, which no run has).
/htab context-record: lf-pair-table
2 cells context-slab: lf-pair-entries
begin-structure /lf-pairs
  field: lf-pairs-run          \ the run whose pairs the set holds; 0: none
  field: lf-pairs-count        \ its entries
  2 cells +field lf-pairs-key  \ the pair being found
end-structure
/lf-pairs context-record: lf-pair-state
: lf-pair-entry ( n -- addr ) lf-pair-entries slab-at ;
: lf-pair-hash ( node depth -- h ) swap hash-fmix swap hash-step ;
: lf-pair-rehash ( n htab -- h ) drop lf-pair-entry 2@ lf-pair-hash ;
: lf-pair-same ( n key htab -- flag ) drop swap lf-pair-entry 2@ rot 2@ d= ;
create lf-pair-hooks /htab-hooks allot
' lf-pair-rehash ' lf-pair-same lf-pair-hooks htab-hooks!
: lf-pair-table-make ( -- ) 4 lf-pair-hooks lf-pair-table htab-init drop ;
' lf-pair-table-make context-setup
:noname ( -- ) lf-pair-table htab-free ; context-teardown
\ The set emptied for run; a table grown above 1024 slots is made again,
\ so that one large run leaves later ones no large table to clear.
: lf-pairs-small? ( -- flag )
  lf-pair-table dup htab-live? if htab-slots 1024 <= else drop false then ;
: lf-pairs-reset ( run -- )
  lf-pair-state tuck lf-pairs-run ! 0 swap lf-pairs-count !
  lf-pairs-small? if lf-pair-table htab-clear exit then
  lf-pair-table htab-free lf-pair-table-make ;
: lf-pairs# ( -- n ) lf-pair-state lf-pairs-count @ ;
\ Keep (node depth) at the empty slot i a find gave, if the slab can grow.
: lf-pairs-put ( node depth i -- )
  >r lf-pairs# lf-pair-entry 2! lf-pairs# r> lf-pair-table htab-put
  1 lf-pair-state lf-pairs-count +! ;
: lf-pairs-keep ( node depth i -- )
  lf-pairs# 1+ lf-pair-entries slab-hold ok? if lf-pairs-put else drop 2drop then ;
: lf-pairs-find ( node depth -- n true | i false )
  2dup lf-pair-state lf-pairs-key 2! lf-pair-hash
  lf-pair-state lf-pairs-key swap lf-pair-table htab-find ;
\ Whether run's set holds (node depth); when not, the pair is kept.
: lf-pairs-own? ( run -- flag ) lf-pair-state lf-pairs-run @ = ;
: lf-pairs-seen? ( node depth run -- flag )
  lf-pairs-own? 0= if 2drop false exit then
  lf-pair-table htab-ready ok? 0= if 2drop false exit then
  2dup lf-pairs-find if drop 2drop true else lf-pairs-keep false then ;

: lf-marks-erase ( -- )
  lf-term-marks column-erase lf-marks-release 0 lf-pair-state lf-pairs-run ! ;
: lf-mark-next ( -- run )
  lf-mark-runs @ 1+ dup 0= if lf-marks-erase 1+ then dup lf-mark-runs ! ;
: lf-walk-marking ( walk -- ) lf-mark-next swap walk-arg ! ;
: lf-walk-depth ( walk -- depth ) dup walk-paired? if walk-context @ else drop 0 then ;
: lf-mark-unit ( walk -- unit ) walk-node @ lf-mark-at ;
\ A unit holds a run, then a depth.
: lf-mark-held? ( depth run unit -- flag )
  tuck @ = if cell+ @ < 0= else 2drop false then ;
: lf-mark-set ( depth run unit -- ) tuck ! cell+ ! ;
\ Whether this run reached the node before at a depth no greater; when
\ not, the node is marked at its depth.
: lf-walk-seen? ( walk -- flag )
  dup lf-walk-depth over walk-arg @ rot lf-mark-unit
  >r 2dup r@ lf-mark-held? if r> drop 2drop true else r> lf-mark-set false then ;
\ Dispatch with xt ( first second walk tag -- outcome ) a node not seen
\ before; one seen before is ok, nothing pushed.
: lf-walk-skip ( first second walk tag -- outcome ) 2drop 2drop outcome-ok ;
: lf-walk-unless ( first second walk tag xt flag -- outcome )
  if drop lf-walk-skip else execute then ;
: lf-walk-once ( first second walk tag xt -- outcome )
  2 pick lf-walk-seen? lf-walk-unless ;
\ The same at exactly the node's depth, for a check whose verdict at a
\ node can change with its depth either way, as Lean's for_each with an
\ offset visits each shared (term, offset) pair once (for_each_fn.cpp,
\ for_each_offset_fn's cache): a walk started by lf-walk-pairing skips a
\ pair (node, depth) it reached before, and only such a pair. The node's
\ unit keeps the first depth the run reached it at; the run's pair set
\ the others (review rvKN 1: a unit keeping only the latest depth made a
\ node met at alternating depths be walked again, its subtree too, up to
\ exponentially often).
: lf-walk-pairing ( walk -- ) dup lf-walk-marking walk-arg @ lf-pairs-reset ;
: lf-walk-pair ( walk -- node depth run )
  dup walk-node @ over lf-walk-depth rot walk-arg @ ;
: lf-mark-other? ( node depth run unit -- flag )
  cell+ @ 2 pick = if 2drop drop true else lf-pairs-seen? then ;
: lf-walk-seen-at? ( walk -- flag )
  lf-walk-pair 2 pick lf-mark-at 2dup @ =
  if lf-mark-other? else lf-mark-set drop false then ;
: lf-walk-once-at ( first second walk tag xt -- outcome )
  2 pick lf-walk-seen-at? lf-walk-unless ;
\ The same for a walk run inside another's visit (review rvKN 2), also
\ started by lf-walk-pairing: every pair it reaches is kept in the pair
\ set alone, so the outer walk's units, and the nodes they let it skip,
\ stay as they are.
: lf-walk-seen-aside? ( walk -- flag ) lf-walk-pair lf-pairs-seen? ;
: lf-walk-once-aside ( first second walk tag xt -- outcome )
  2 pick lf-walk-seen-aside? lf-walk-unless ;

\ The audit memo (compact-store plan step S6 (c); ADR 0014 Amendment 4):
\ in a check, the structural audit below checks a node once, not once per
\ comparison, rebuilding pass or substitution that takes it as a root.
\ Lean runs no such audit (its terms are well formed by construction);
\ the audit is LeanForth's own fail-closed defence, kept wherever a pass
\ takes a root, so only its repetition goes. A node reached by a run
\ that ends ok was checked with its whole graph (the marks above), and
\ that stays true while what the check read stays: the node's record
\ and children (records never change, children come earlier, a rollback
\ gives back a suffix, and an index made again has a new identity), its
\ stamps (written when it is made), the term, level, reference and name
\ stores, the literal and string slabs and the parameter context (their
\ generations advance on every reset or change), and, for a node with a
\ free variable (its data word's bit), the local context, whose
\ generation advances when inference empties it for a new job (within a
\ job an entry goes only with its node, local-context.fs's lf-lctx-drop).
\ So while the memo is on, a run that ends ok keeps each node it checked
\ (lf-audit-reached) in its marks unit as (epoch, identity): the closed
\ epoch for a node without a free variable, the open epoch for one with,
\ and nothing for a node without a data word. Both epochs are new
\ numbers from the run counter (never a run's number) when a check
\ begins (lf-audit-renew), when the memo turns on, and when one of those
\ generations differs from the ones the epochs captured; the open epoch
\ alone when the local context's does. A kept node is not pushed again
\ and a kept root costs no fuel; a run that does not end ok keeps
\ nothing. Off (outside a check, or lf-audit-memo! lf-memo-off), every
\ audit runs as before. A list the heap cannot grow keeps fewer nodes:
\ more work, never another outcome.
0 constant lf-memo-auto   \ on while lf-audit-checking? says a check runs
1 constant lf-memo-on
2 constant lf-memo-off
defer lf-audit-checking? ( -- flag )
:noname ( -- flag ) false ; is lf-audit-checking?
\ The generations an audit of a node without a free variable reads.
: lf-gen-terms ( -- n ) lf-term-generation @ ;
: lf-gen-levels ( -- n ) lf-level-generation @ ;
: lf-gen-crefs ( -- n ) lf-crefs store-generation @ ;
: lf-gen-scope ( -- n ) lf-lscope-generation @ ;
: lf-gen-names ( -- n ) lf-name-generation @ ;
: lf-gen-lits ( -- n ) lf-lit-limbs slab-generation ;
: lf-gen-strs ( -- n ) lf-str-bytes slab-generation ;
create lf-audit-facts 7 ,
  ' lf-gen-terms , ' lf-gen-levels , ' lf-gen-crefs , ' lf-gen-scope ,
  ' lf-gen-names , ' lf-gen-lits , ' lf-gen-strs ,
begin-structure /lf-amemo
  field: lf-aud-mode      \ lf-memo-auto, lf-memo-on or lf-memo-off
  field: lf-aud-active    \ true while the current audit uses the memo
  field: lf-aud-closed    \ epoch of nodes without a free variable; 0: none
  field: lf-aud-open      \ epoch of nodes with one; 0: none
  field: lf-aud-local     \ the local context's generation the open epoch saw
  field: lf-aud-count     \ nodes in lf-audit-reached
  7 cells +field lf-aud-gens   \ the generations the closed epoch saw
end-structure
/lf-amemo context-record: lf-audit-state
1 cells context-slab: lf-audit-reached   \ nodes the current run checked
: lf-audit-memo! ( mode -- ) lf-audit-state lf-aud-mode ! ;
: lf-audit-on? ( -- flag )
  lf-audit-state lf-aud-mode @ dup lf-memo-auto = if drop lf-audit-checking? exit then
  lf-memo-on = ;
: lf-audit-fact ( i -- n ) 1+ cells lf-audit-facts + @ execute ;
: lf-audit-gen ( i -- addr ) cells lf-audit-state lf-aud-gens + ;
: lf-audit-same? ( -- flag )
  lf-audit-facts @ 0 ?do
    i lf-audit-fact i lf-audit-gen @ <> if false unloop exit then loop true ;
: lf-audit-capture ( -- )
  lf-audit-facts @ 0 ?do i lf-audit-fact i lf-audit-gen ! loop ;
: lf-gen-local ( -- n ) lf-lctx store-generation @ ;
: lf-audit-reopen ( -- )
  lf-mark-next lf-audit-state lf-aud-open ! lf-gen-local lf-audit-state lf-aud-local ! ;
\ New epochs: nothing kept before counts any more.
: lf-audit-renew ( -- )
  lf-mark-next lf-audit-state lf-aud-closed ! lf-audit-capture lf-audit-reopen ;
\ A check's start (kernel/check-declaration.fs): the input's mark pages
\ given back, then new epochs. Exact only where no marking run is under
\ way, as at a check's start; a renewal within a check keeps the pages.
: lf-audit-afresh ( -- ) lf-marks-release lf-audit-renew ;
\ Stale: no epoch yet, the memo was off, a generation moved, or the run
\ counter wrapped (it is below the newest epoch; the marks were erased).
: lf-audit-wrapped? ( -- flag ) lf-mark-runs @ lf-audit-state lf-aud-open @ u< ;
: lf-audit-stale? ( -- flag )
  lf-audit-state lf-aud-closed @ 0= lf-audit-state lf-aud-active @ 0= or
  lf-audit-wrapped? or lf-audit-same? 0= or ;
: lf-audit-local? ( -- flag ) lf-gen-local lf-audit-state lf-aud-local @ = ;
\ Before an audit: whether the memo is on, with epochs for today's facts.
: lf-audit-current ( -- )
  lf-audit-stale? if lf-audit-renew exit then lf-audit-local? 0= if lf-audit-reopen then ;
: lf-audit-ready ( -- )
  lf-audit-on? dup if lf-audit-current then lf-audit-state lf-aud-active ! ;
\ The epoch a node is kept under: 0 (never) for a node without a data
\ word. Unchecked: the node is allocated.
: lf-audit-epoch ( node -- epoch )
  lf-term-data-word dup lf-data-known? 0= if drop 0 exit then
  lf-data-fvar? if lf-audit-state lf-aud-open else lf-audit-state lf-aud-closed then @ ;
\ Whether the memo is on and holds node as checked in its epoch.
\ Unchecked: the node is allocated.
: lf-audit-same-node? ( node unit -- flag )
  cell+ @ swap lf-term-identity if = else drop false then ;
: lf-audit-unit? ( node epoch -- flag )
  over lf-mark-at tuck @ = if lf-audit-same-node? else 2drop false then ;
: lf-audit-held? ( node -- flag )
  dup lf-audit-epoch ?dup if lf-audit-unit? else drop false then ;
: lf-audited? ( node -- flag )
  lf-audit-state lf-aud-active @ 0= if drop false exit then lf-audit-held? ;
\ Whether node was checked by an audit of this check, in today's epoch, at
\ any time (not only inside an audit run): what the check has reached
\ (terms.fs's lf-term-findable?, set by kernel/check-declaration.fs).
\ False while the memo is off. Unchecked: the node is allocated.
: lf-audit-reached? ( node -- flag )
  lf-audit-on? 0= if drop false exit then lf-audit-held? ;
\ Levels reached in this check, the same way: a level root a scope check
\ found in scope (level-scope.fs's hook lf-lscope-reached) is kept in a
\ column of the level store with its identity and today's closed epoch.
/slab context-record: lf-level-reach
2 cells ' lf-level-reach lf-level-columns column-add
: lf-level-reach-unit ( level -- addr ) lf-level-reach column-at ;
: lf-audit-level-mark ( level -- )
  lf-audit-on? 0= if drop exit then
  dup lf-level-identity 0= if drop exit then over lf-level-reach-unit !
  lf-audit-state lf-aud-closed @ swap lf-level-reach-unit cell+ ! ;
' lf-audit-level-mark is lf-lscope-reached
: lf-audit-level-epoch? ( level -- flag )
  lf-level-reach-unit cell+ @ lf-audit-state lf-aud-closed @ = ;
: lf-audit-level-reached? ( level -- flag )
  lf-audit-on? 0= if drop false exit then
  dup lf-audit-level-epoch? 0= if drop false exit then
  dup lf-level-reach-unit @ swap lf-level-identity if = else drop false then ;
\ References reached in this check, the same way (review rvRS F1): the
\ reference of a constant node an audit checked (lf-cterm-reference
\ below) is kept in a unit of lf-cref-reach, by its number, with its
\ identity and today's closed epoch. The slab grows, zeroed, to the
\ largest number kept; one the heap cannot grow keeps nothing (a new
\ reference made instead: never another outcome).
2 cells context-slab: lf-cref-reach
: lf-cref-reach-unit ( cref -- addr ) lf-cref-reach slab-at ;
: lf-cref-reach-zeroed ( old -- )
  dup lf-cref-reach-unit lf-cref-reach slab-capacity rot - 2* cells erase ;
: lf-cref-reach-room? ( cref -- flag )
  1+ lf-cref-reach slab-capacity tuck over u< 0= if 2drop true exit then
  lf-cref-reach slab-hold ok? if lf-cref-reach-zeroed true else drop false then ;
: lf-audit-cref-mark ( cref identity -- )
  lf-audit-on? 0= if 2drop exit then over lf-cref-reach-room? 0= if 2drop exit then
  swap lf-cref-reach-unit tuck ! lf-audit-state lf-aud-closed @ swap cell+ ! ;
: lf-audit-cref-epoch? ( cref -- flag )
  dup lf-cref-reach slab-capacity u< 0= if drop false exit then
  lf-cref-reach-unit cell+ @ lf-audit-state lf-aud-closed @ = ;
: lf-audit-cref-reached? ( cref -- flag )
  lf-audit-on? 0= if drop false exit then
  dup lf-audit-cref-epoch? 0= if drop false exit then
  dup lf-cref-reach-unit @ swap lf-cref-current = ;
\ A node the current run checks, kept on the list for lf-audit-keep.
: lf-audit-slot ( i -- addr ) lf-audit-reached slab-at ;
: lf-audit-add ( node count -- )
  tuck lf-audit-slot ! 1+ lf-audit-state lf-aud-count ! ;
: lf-audit-reach ( node -- )
  lf-audit-state lf-aud-active @ 0= if drop exit then
  lf-audit-state lf-aud-count @ dup 1+ lf-audit-reached slab-hold ok?
  if lf-audit-add else 2drop then ;
\ After a run: kept as checked when it ended ok; the list emptied.
: lf-audit-mark ( node -- )
  dup lf-audit-epoch ?dup 0= if drop exit then
  over lf-term-identity drop rot lf-mark-at tuck cell+ ! ! ;
: lf-audit-keep ( -- )
  lf-audit-state lf-aud-count @ 0 ?do i lf-audit-slot @ lf-audit-mark loop ;
: lf-audit-settle ( outcome -- outcome )
  dup ok? lf-audit-state lf-aud-active @ and if lf-audit-keep then
  0 lf-audit-state lf-aud-count ! ;

\ Fuel left after a check; the kernel passes continue with it. Negative
\ fuel leaves it unchanged; an invalid root leaves the fuel given.
: lf-cterm-fuel ( -- addr ) lf-cterm-walker walk-fuel ;

\ Stamp cells of a constant node at a valid term index: its own identity
\ and its reference's.
: lf-cterm-stamp-cell ( index -- addr ) lf-term-stamps lf-stamp-own ;
: lf-cterm-ref-cell ( index -- addr ) lf-term-stamps lf-stamp-ref ;
: lf-cterm-stamp ( term identity -- ) swap lf-cterm-stamp-cell ! ;
\ The reference a constant node was made for: its index and the identity
\ stamped with the node (0 for a node made raw).
: lf-cterm-ref ( node -- cref identity ) dup lf-term-first@ swap lf-cterm-ref-cell @ ;
\ The reference of a constant's fields (first second) from the record at
\ the index: what lf-cterm-ref gives for an audited node, whose stamped
\ identity the audit found the record's.
: lf-cterm-pair ( first second -- cref identity ) drop dup lf-cref-current ;

\ Sharing constants and symbolic Sorts (compact-store plan step S4). With
\ levels hash-consed and references interned, equal constants have equal
\ fields (an interned reference) and so do equal Sorts (a hash-consed
\ level), so the term table finds them. A found node is given again only
\ while it is stamped as lf-cterm-new or lf-hterm-sort stamps it: a
\ constant with its own identity, a Sort with its own and its level's
\ current identity. So a raw node with those fields, or a Sort whose
\ level index was reset and made again, is never given out under a new
\ stamp: lf-term-add makes a new node instead (terms.fs's
\ lf-term-reusable?). Re-stamping a node given again writes what it holds.
\ A constant's reference, like a Sort's level, must still be the record
\ it was made for.
: lf-cterm-stamped? ( node -- flag )
  dup lf-term-identity if swap lf-cterm-stamp-cell @ = else drop false then ;
: lf-cterm-ref-live? ( node -- flag )
  lf-cterm-ref swap lf-cref-current dup 0<> -rot = and ;
: lf-cterm-made? ( node -- flag )
  dup lf-cterm-stamped? if lf-cterm-ref-live? else drop false then ;
: lf-cterm-reusable? ( n -- flag )
  dup lf-term-tag@ case
    lf-tag-constant of lf-cterm-made? endof
    lf-tag-symbolic-sort of dup lf-term-first@ swap lf-hsort-stamped? endof
    nip true swap endcase ;
' lf-cterm-reusable? is lf-term-reusable?

\ Allocate a constant node, fields (reference index, 0), for a live
\ reference in the current session and stamp it with its own identity and
\ the reference's. Failure leaves the term store unchanged.
: lf-cterm-source? ( cref identity -- flag ) lf-cref-valid? lf-ssession-current? and ;
: lf-cterm-stamps ( ref-identity term identity -- )
  swap lf-term-stamps tuck lf-stamp-own ! lf-stamp-ref ! ;
: lf-cterm-made ( ref-identity term identity -- term identity true )
  2dup 2>r lf-cterm-stamps 2r> true ;
: lf-cterm-new ( cref identity -- term identity true | false )
  2dup lf-cterm-source? 0= if 2drop false exit then
  >r lf-tag-constant swap 0 lf-term-add lf-hterm-result
  if r> -rot lf-cterm-made else r> drop false then ;

\ Check each level of a reference's (index identity) pairs in the current
\ context from inside this walk, with its fuel. The pairs come from
\ lf-cref-levels, already validated, so count is not negative and
\ identities are not checked again.
: lf-cterm-levels ( addr count walk -- outcome )
  swap 0 ?do over i lf-cref-pair@ drop over lf-lscope-walk-check dup ok? 0=
    if nip nip unloop exit then drop loop 2drop outcome-ok ;

\ Visiting one node. A constant must carry its own stamp and a live
\ reference whose levels all pass; a symbolic Sort must carry the handle
\ stamps (lf-hterm-sort) and a level that passes; a free variable must be
\ live, named by its own entry of the local context (local-context.fs), so
\ only a check's scratch can hold one; binary children must come earlier.
\ A constant's second field is 0, and its stamped reference must be live;
\ a reference whose levels all pass is reached (lf-audit-cref-mark).
: lf-cterm-reached ( outcome walk -- outcome )
  over ok? if walk-node @ lf-cterm-ref lf-audit-cref-mark else drop then ;
: lf-cterm-reference ( first second walk -- outcome )
  swap if 2drop outcome-invalid exit then nip
  dup walk-node @ lf-cterm-stamped? 0= if drop outcome-invalid exit then
  >r r@ walk-node @ lf-cterm-ref lf-cref-levels
  if r@ lf-cterm-levels r> lf-cterm-reached else r> drop outcome-invalid then ;
: lf-cterm-sort? ( first second node -- flag )
  >r over swap lf-repr-leaf? if r> lf-hsort-stamped? else r> 2drop false then ;
: lf-cterm-sort ( first second walk -- outcome )
  >r 2dup r@ walk-node @ lf-cterm-sort?
  if drop r> lf-lscope-walk-check else 2drop r> drop outcome-invalid then ;
: lf-cterm-fvar ( first second walk -- outcome )
  nip nip walk-node @ lf-fvar-live? flag>outcome ;
\ Binary children must come earlier (walk-children's test); each is pushed
\ unless the memo holds it checked, first then second (so the second is
\ visited first), and a push without room is full.
: lf-cterm-push ( index walk -- outcome )
  over lf-audited? if 2drop outcome-ok else walk-push-outcome then ;
: lf-cterm-pushed ( first second walk -- outcome )
  rot over lf-cterm-push dup ok? if drop lf-cterm-push else nip nip then ;
: lf-cterm-children ( first second walk -- outcome )
  >r 2dup r@ walk-child? swap r@ walk-child? and
  if r> lf-cterm-pushed else 2drop r> drop outcome-invalid then ;
\ The children of a let (core/let-terms.fs) and of a projection
\ (core/projections.fs) are checked as any binary node's, and their
\ shape too: a let's second child is a lambda, a projection's first a
\ projection leaf; anything else is malformed.
: lf-cterm-shaped ( first second walk child tag -- outcome )
  >r dup 2 pick walk-child? if lf-term-tag@ r> = else drop r> drop false then
  if lf-cterm-children else drop 2drop outcome-invalid then ;
: lf-cterm-binary ( first second walk tag -- outcome )
  case lf-tag-projection of 2 pick lf-tag-proj lf-cterm-shaped endof
    lf-tag-let of over lf-tag-lam lf-cterm-shaped endof
    lf-tag-let-nondep of over lf-tag-lam lf-cterm-shaped endof
    drop lf-cterm-children 0 endcase ;
: lf-cterm-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if lf-cterm-binary exit then
  case lf-tag-constant of lf-cterm-reference endof
    lf-tag-bvar of lf-repr-bvar endof  lf-tag-fvar of lf-cterm-fvar endof
    lf-tag-symbolic-sort of lf-cterm-sort endof
    lf-tag-proj of lf-proj-check endof  lf-tag-lit of lf-lit-check endof
    lf-tag-str of lf-str-check endof  walk-bad-tag endcase ;
\ A node first reached in this run goes on the memo's list.
: lf-cterm-first ( first second walk tag -- outcome )
  over walk-node @ lf-audit-reach lf-cterm-dispatch ;
: lf-cterm-once ( first second walk tag -- outcome ) ['] lf-cterm-first lf-walk-once ;
: lf-cterm-visit ( walk -- outcome ) ['] lf-cterm-once lf-term-visit ;

\ Validate a live root and its reachable mixed symbolic graph, each node
\ once (the marks above). Each term and level visit costs one unit of
\ fuel; a term reached again by another path costs one and is not checked
\ again; the bounded context and reference scans are not charged. Negative fuel is
\ invalid; zero exhausts, and a full work stack is full. Success is
\ structural evidence only. The outcome is always ok, invalid, exhausted or
\ full, never another one: the kernel's rebuilding passes (mixed-rebuild.fs)
\ pass it on without narrowing, and tests/core/constant-term-boundary.fs
\ pins that set. Full needs a graph deeper than the walk's work stack,
\ which only a term or level capacity raised above it allows (children
\ come earlier, so at the default capacities a work stack never holds
\ more items than its store has nodes).
\ A root that is not a live handle is recorded as a stale handle. With the
\ audit memo on, a node checked earlier in the check (its epoch) is not
\ visited again, and a root so checked costs no fuel.
: lf-cterm-site ( -- site ) c" constant-term-boundary lf-cterm-check" ;
: lf-cterm-run ( root -- status )
  lf-cterm-walker lf-walk-marking ['] lf-cterm-visit lf-cterm-walker walk-run
  lf-audit-settle lf-cterm-walker lf-cterm-site lf-diag-walk ;
: lf-cterm-audit ( root -- status )
  lf-audit-ready dup lf-audited? if drop outcome-ok else lf-cterm-run then ;
: lf-cterm-stale ( index identity -- status )
  lf-cterm-site lf-diag-stale-handle lf-diag-note outcome-invalid ;
: lf-cterm-check ( index identity fuel -- status )
  lf-cterm-walker walk-budget 0= if 2drop outcome-invalid exit then
  2dup lf-hterm-valid? if drop lf-cterm-audit else lf-cterm-stale then ;
