\ Constant nodes in symbolic terms, and the structural check of a whole
\ constant-bearing term graph. Untrusted: no lookup, typing, binder scope or
\ proof checking. A constant node's fields hold a full reference pair, and a
\ stamp table binds it to this exact term allocation, so a reset cannot
\ resurrect it. Binary constructors capture child indices, not identities;
\ their safety relies on backward edges and no raw mutation or count edits.
\ State: the stamp column lf-cterm-stamps of the term store (indexed by
\ term index; lib/store-columns.fs), the marks column lf-term-marks with
\ its run counter lf-mark-runs (below), and one
\ walk record, lf-cterm-walker, all members of the checker context
\ (lib/context.fs). Each constant and symbolic Sort visit also runs a
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
/slab context-record: lf-cterm-stamps
1 cells ' lf-cterm-stamps lf-term-columns column-add
lf-walk-room context-walk: lf-cterm-walker

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

\ Fuel left after a check; the kernel passes continue with it. Negative
\ fuel leaves it unchanged; an invalid root leaves the fuel given.
: lf-cterm-fuel ( -- addr ) lf-cterm-walker walk-fuel ;

\ Stamp cell of a constant node at a valid term index.
: lf-cterm-stamp-cell ( index -- addr ) lf-cterm-stamps column-at ;

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
: lf-cterm-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-children exit then
  case lf-tag-constant of lf-cterm-reference endof
    lf-tag-bvar of lf-repr-bvar endof  lf-tag-fvar of lf-cterm-fvar endof
    lf-tag-symbolic-sort of lf-cterm-sort endof
    lf-tag-proj of lf-proj-check endof  lf-tag-lit of lf-lit-check endof
    lf-tag-str of lf-str-check endof
    lf-tag-let of lf-let-check endof  walk-bad-tag endcase ;
: lf-cterm-once ( first second walk tag -- outcome ) ['] lf-cterm-dispatch lf-walk-once ;
: lf-cterm-visit ( walk -- outcome ) lf-terms ['] lf-cterm-once walk-visit ;

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
\ A root that is not a live handle is recorded as a stale handle.
: lf-cterm-site ( -- site ) c" constant-term-boundary lf-cterm-check" ;
: lf-cterm-run ( root -- status )
  lf-cterm-walker lf-walk-marking ['] lf-cterm-visit lf-cterm-walker walk-run
  lf-cterm-walker lf-cterm-site lf-diag-walk ;
: lf-cterm-stale ( index identity -- status )
  lf-cterm-site lf-diag-stale-handle lf-diag-note outcome-invalid ;
: lf-cterm-check ( index identity fuel -- status )
  lf-cterm-walker walk-budget 0= if 2drop outcome-invalid exit then
  2dup lf-hterm-valid? if drop lf-cterm-run else lf-cterm-stale then ;
