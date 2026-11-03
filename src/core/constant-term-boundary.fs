\ Constant nodes in symbolic terms, and the structural check of a whole
\ constant-bearing term graph. Untrusted: no lookup, typing, binder scope or
\ proof checking. A constant node's fields hold a full reference pair, and a
\ stamp table binds it to this exact term allocation, so a reset cannot
\ resurrect it. Binary constructors capture child indices, not identities;
\ their safety relies on backward edges and no raw mutation or count edits.
\ State: the stamp table (global, indexed by term index) and one walk
\ record, lf-cterm-walker. Each constant and symbolic Sort visit also runs a
\ level-scope check on level-scope's walk record (lf-lscope-walk), so this
\ check must not run while another module borrows that record. Not
\ re-entrant and single-threaded. Identities are forgeable, instance-local
\ diagnostics; the memory layout is not a serialization format.

require ../lib/lib.fs
require ./constant-references.fs
require ./generation-handles.fs
require ./level-scope.fs
require ./symbolic-session.fs
require ./tagged-sort-boundary.fs
require ./terms.fs

7 constant lf-tag-constant
create lf-cterm-stamps lf-term-capacity cells allot
lf-cterm-stamps lf-term-capacity cells erase
lf-term-capacity walk: lf-cterm-walker

\ Fuel left after a check; the kernel passes continue with it. Negative
\ fuel leaves it unchanged; an invalid root leaves the fuel given.
: lf-cterm-fuel ( -- addr ) lf-cterm-walker walk-fuel ;

\ Stamp cell of a constant node at a valid term index.
: lf-cterm-stamp-cell ( index -- addr ) cells lf-cterm-stamps + ;

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
\ lf-cref-levels, already validated, so count is 0..8 and identities are
\ not checked again.
: lf-cterm-levels ( addr count walk -- outcome )
  swap 0 ?do over i lf-cref-pair@ drop over lf-lscope-walk-check dup ok? 0=
    if nip nip unloop exit then drop loop 2drop outcome-ok ;

\ Visiting one node. A constant must carry its own stamp and a live
\ reference whose levels all pass; a symbolic Sort must carry the handle
\ stamps (lf-hterm-sort) and a level that passes; binary children must come
\ earlier.
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
: lf-cterm-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-children exit then
  case lf-tag-constant of lf-cterm-reference endof
    lf-tag-bvar of lf-repr-bvar endof
    lf-tag-symbolic-sort of lf-cterm-sort endof walk-bad-tag endcase ;
: lf-cterm-visit ( walk -- outcome ) lf-terms ['] lf-cterm-dispatch walk-visit ;

\ Validate a live root and its reachable mixed symbolic graph. Each term and
\ level visit costs one unit of fuel, including repeated DAG visits; the
\ bounded context and reference scans are not charged. Negative fuel is
\ invalid; zero exhausts, and a full work stack is full. Success is
\ structural evidence only. The outcome is always ok, invalid, exhausted or
\ full, never another one: the kernel's rebuilding passes (mixed-rebuild.fs)
\ pass it on without narrowing, and tests/core/constant-term-boundary.fs
\ pins it.
: lf-cterm-run ( root -- status ) ['] lf-cterm-visit lf-cterm-walker walk-run ;
: lf-cterm-check ( index identity fuel -- status )
  lf-cterm-walker walk-budget 0= if 2drop outcome-invalid exit then
  2dup lf-hterm-valid? if drop lf-cterm-run else 2drop outcome-invalid then ;
