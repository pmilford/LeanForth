\ Constant nodes in symbolic terms, and the structural check of a whole
\ constant-bearing term graph. Untrusted: no lookup, typing, binder scope or
\ proof checking. A constant node's fields hold a full reference pair, and a
\ stamp table binds it to this exact term allocation, so a reset cannot
\ resurrect it. Binary constructors capture child indices, not identities;
\ their safety relies on backward edges and no raw mutation or count edits.
\ State: the stamps of generation-handles.fs (a map from term index to
\ stamp unit; a constant's stamp is its own identity, as a symbolic Sort's
\ term stamp is), the marks column lf-term-marks with
\ its run counter lf-mark-runs (below), the audit memo's record
\ lf-audit-state and its list lf-audit-reached (below), and one
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
\ A constant node is never shared (terms.fs): it carries a stamp of its
\ own identity.
lf-tag-constant lf-term-unshare
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
: lf-cterm-const-data ( cref identity -- data )
  lf-cref-levels if lf-cterm-params? lf-data-params else lf-data-unknown then ;
: lf-cterm-leaf-data ( tag first second -- data )
  rot case
    lf-tag-bvar of lf-bvar-data endof
    lf-tag-symbolic-sort of lf-cterm-sort-data endof
    lf-tag-constant of lf-cterm-const-data endof
    lf-tag-fvar of 2drop 0 false true lf-data endof
    lf-tag-proj of 2drop 0 endof  lf-tag-lit of 2drop 0 endof
    lf-tag-str of 2drop 0 endof  lf-tag-let of 2drop 0 endof
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
: lf-mark-next ( -- run )
  lf-mark-runs @ 1+ dup 0= if lf-term-marks column-erase 1+ then dup lf-mark-runs ! ;
: lf-walk-marking ( walk -- ) lf-mark-next swap walk-arg ! ;
: lf-walk-depth ( walk -- depth ) dup walk-paired? if walk-context @ else drop 0 then ;
: lf-mark-unit ( walk -- unit ) walk-node @ lf-term-marks column-at ;
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
: lf-walk-once ( first second walk tag xt -- outcome )
  >r over lf-walk-seen? if r> drop lf-walk-skip else r> execute then ;

\ The audit memo (compact-store plan step S6 (c); ADR 0014 Amendment 3):
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
  over lf-term-marks column-at tuck @ = if lf-audit-same-node? else 2drop false then ;
: lf-audited? ( node -- flag )
  lf-audit-state lf-aud-active @ 0= if drop false exit then
  dup lf-audit-epoch ?dup if lf-audit-unit? else drop false then ;
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
  over lf-term-identity drop rot lf-term-marks column-at tuck cell+ ! ! ;
: lf-audit-keep ( -- )
  lf-audit-state lf-aud-count @ 0 ?do i lf-audit-slot @ lf-audit-mark loop ;
: lf-audit-settle ( outcome -- outcome )
  dup ok? lf-audit-state lf-aud-active @ and if lf-audit-keep then
  0 lf-audit-state lf-aud-count ! ;

\ Fuel left after a check; the kernel passes continue with it. Negative
\ fuel leaves it unchanged; an invalid root leaves the fuel given.
: lf-cterm-fuel ( -- addr ) lf-cterm-walker walk-fuel ;

\ Stamp cell of a constant node at a valid term index.
: lf-cterm-stamp-cell ( index -- addr ) lf-term-stamps lf-stamp-own ;

: lf-cterm-stamp ( term identity -- ) swap lf-cterm-stamp-cell ! ;

\ Allocate a constant node for a live reference in the current session and
\ stamp it with its own identity. Failure leaves the term store unchanged.
: lf-cterm-source? ( cref identity -- flag ) lf-cref-valid? lf-ssession-current? and ;
: lf-cterm-new ( cref identity -- term identity true | false )
  2dup lf-cterm-source? 0= if 2drop false exit then
  lf-tag-constant -rot lf-term-add lf-hterm-result
  if 2dup lf-cterm-stamp true else false then ;

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
: lf-cterm-stamped? ( node -- flag )
  dup lf-term-identity if swap lf-cterm-stamp-cell @ = else drop false then ;
: lf-cterm-reference ( first second walk -- outcome )
  dup walk-node @ lf-cterm-stamped? 0= if drop 2drop outcome-invalid exit then
  >r lf-cref-levels if r> lf-cterm-levels else r> drop outcome-invalid then ;
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
: lf-cterm-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop lf-cterm-children exit then
  case lf-tag-constant of lf-cterm-reference endof
    lf-tag-bvar of lf-repr-bvar endof  lf-tag-fvar of lf-cterm-fvar endof
    lf-tag-symbolic-sort of lf-cterm-sort endof
    lf-tag-proj of lf-proj-check endof  lf-tag-lit of lf-lit-check endof
    lf-tag-str of lf-str-check endof
    lf-tag-let of lf-let-check endof  walk-bad-tag endcase ;
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
