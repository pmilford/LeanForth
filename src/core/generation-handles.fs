\ Allocation-identity handles: a handle is two stack cells, an index and
\ that slot's identity, so a handle from before a reset or rollback no
\ longer matches. Untrusted; not a capability system, kernel interface,
\ serialization or theorem checker. Handles are forgeable and do not record
\ which store they belong to; callers prevent concurrent mutation, raw
\ writes and cross-store confusion.
\ State: two stamp columns of the term store (lib/store-columns.fs),
\ indexed by term index, record which term and level identities each
\ symbolic Sort was built from (raw symbolic Sorts have no stamp and fail
\ lf-hterm-check); the audit uses one walk record, lf-href-walker. All
\ three are members of the checker context (lib/context.fs).
\ Single-threaded within one context.

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/store-columns.fs
require ./diagnostics.fs
require ./levels.fs
require ./symbolic-session.fs
require ./tagged-sort-boundary.fs
require ./terms.fs

/slab context-record: lf-hsort-term-identities
1 cells ' lf-hsort-term-identities lf-term-columns column-add
/slab context-record: lf-hsort-level-identities
1 cells ' lf-hsort-level-identities lf-term-columns column-add
lf-walk-room context-walk: lf-href-walker

\ Stamp cells of a symbolic Sort at a valid term index.
: lf-hsort-term-stamp ( index -- addr ) lf-hsort-term-identities column-at ;
: lf-hsort-level-stamp ( index -- addr ) lf-hsort-level-identities column-at ;

\ The fuel the last audit left, under its established name.
: lf-href-fuel ( -- addr ) lf-href-walker walk-fuel ;

\ A pair names a live slot with that identity. Level pairs say nothing about
\ shape or scope; term pairs also need the session to be current.
: lf-hlevel-valid? ( index identity -- flag ) swap lf-level-identity if = else drop false then ;
: lf-hterm-valid? ( index identity -- flag )
  swap lf-term-identity if = else drop false then lf-ssession-current? and ;
: lf-hterms-valid? ( left lid right rid -- flag ) lf-hterm-valid? >r lf-hterm-valid? r> and ;

\ Turn an allocator's result into a handle.
: lf-hlevel-result ( index true | false -- index identity true | false )
  if dup lf-level-identity dup 0= if nip then else false then ;
: lf-hterm-result ( index true | false -- index identity true | false )
  if dup lf-term-identity dup 0= if nip then else false then ;

\ Level handles: zero, an opaque parameter, or the successor of a live level.
\ Parameters must still be in the session context when checked.
: lf-hlevel-zero ( -- index identity true | false )
  0 lf-level-valid? if 0 dup lf-level-identity else false then ;
: lf-hlevel-param ( name-id -- index identity true | false ) lf-level-param lf-hlevel-result ;
: lf-hlevel-succ ( index identity -- index identity true | false )
  2dup lf-hlevel-valid? if drop lf-level-succ lf-hlevel-result else 2drop false then ;

\ Symbolic Sort from a live level handle while the session is current; the
\ stamps tie the new term to both identities. Level scope is checked later.
: lf-hsort-stamp ( level-identity term-index term-identity -- )
  over lf-hsort-term-stamp ! lf-hsort-level-stamp ! ;
: lf-hsort-source? ( level-index level-identity -- flag ) lf-hlevel-valid? lf-ssession-current? and ;
: lf-hsort-new ( level-identity level-index -- index identity true | false )
  lf-term-symbolic-sort lf-hterm-result if >r tuck r@ lf-hsort-stamp r> true else drop false then ;
: lf-hterm-sort ( level-index level-identity -- index identity true | false )
  2dup lf-hsort-source? if swap lf-hsort-new else 2drop false then ;

\ Variable in the current session; binding scope is not checked.
: lf-hterm-bvar ( depth -- index identity true | false )
  lf-ssession-current? if lf-term-bvar lf-hterm-result else drop false then ;

\ Binary syntax from two live handles. The raw constructor checks the tag
\ and child indices, not typing or scope. Five inputs: two handles and a tag.
: lf-hterm-binary ( left lid right rid tag -- index identity true | false )
  >r 2over 2over lf-hterms-valid?
  if drop nip r> lf-term-binary lf-hterm-result else 2drop 2drop r> drop false then ;
: lf-hterm-app ( left lid right rid -- index identity true | false ) lf-tag-app lf-hterm-binary ;
: lf-hterm-lam ( domain did body bid -- index identity true | false ) lf-tag-lam lf-hterm-binary ;
: lf-hterm-pi ( domain did body bid -- index identity true | false ) lf-tag-pi lf-hterm-binary ;

\ Audit of a structurally checked term: each symbolic Sort must carry the
\ stamps of this exact term allocation and a level that still has the
\ stamped identity. Children point backwards, so a count rollback cannot
\ keep a parent while removing its child. Raw mutation is excluded.
: lf-hsort-term-ok? ( node -- flag )
  dup lf-term-identity if swap lf-hsort-term-stamp @ = else drop false then ;
: lf-hsort-level-ok? ( level node -- flag )
  swap lf-level-identity if swap lf-hsort-level-stamp @ = else drop false then ;
: lf-hsort-stamped? ( level node -- flag )
  dup lf-hsort-term-ok? if lf-hsort-level-ok? else 2drop false then ;
: lf-href-sort ( first second walk -- outcome ) nip walk-node @ lf-hsort-stamped? flag>outcome ;
: lf-href-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-push2 exit then
  case lf-tag-symbolic-sort of lf-href-sort endof
    lf-tag-bvar of drop 2drop outcome-ok endof walk-bad-tag endcase ;
: lf-href-visit ( walk -- outcome ) lf-terms ['] lf-href-dispatch walk-visit ;
\ Internal: audit an already structurally checked root. Negative fuel is
\ invalid.
: lf-href-site ( -- site ) c" generation-handles lf-hterm-check" ;
: lf-href-run ( root -- status )
  ['] lf-href-visit lf-href-walker walk-run lf-href-walker lf-href-site lf-diag-walk ;
: lf-href-check ( root fuel -- status )
  lf-href-walker walk-budget if lf-href-run else drop-invalid then ;

\ Check a live handle's reachable syntax, levels and Sort stamps with one
\ budget. Structural and level-scope evidence only: binder scope, typing and
\ theorem validity are not checked.
: lf-hterm-check ( index identity fuel -- status )
  >r 2dup lf-hterm-valid? 0= if 2drop r> drop outcome-invalid exit then
  drop dup r> lf-ssession-check ok-then? if lf-ssession-fuel @ lf-href-check then ;
