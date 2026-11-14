\ Allocation-identity handles: a handle is two stack cells, an index and
\ that slot's identity, so a handle from before a reset or rollback no
\ longer matches. Untrusted; not a capability system, kernel interface,
\ serialization or theorem checker. Handles are forgeable and do not record
\ which store they belong to; callers prevent concurrent mutation, raw
\ writes and cross-store confusion.
\ State: the stamps, which record which term and level identities each
\ symbolic Sort was built from (raw symbolic Sorts have no stamp and fail
\ lf-hterm-check) and which identity each constant node was
\ (constant-term-boundary.fs), with lf-stamp-input, the unit an input
\ node of a term view reads as (below); the audit uses one walk record,
\ lf-href-walker. All are members of the checker context
\ (lib/context.fs). Single-threaded within one context.
\
\ The stamps (compact-store plan step S3) are kept only for the nodes
\ that have them, in a map from term index to a stamp unit: a growable
\ array of units, lf-stamp-units, found through a hash table,
\ lf-stamp-table (lib/htab.fs), instead of in columns over every index of
\ the term store (constants and symbolic Sorts are about 1.4% of
\ Mathlib's nodes). A unit is made, zero, the first time its index is
\ asked for, and keeps what was written as a column unit did: a rollback
\ or reset of the term store leaves it, and a reused index gets new
\ stamps when its node is made, so a stale node never matches. When the
\ map cannot grow (no heap), a spare zero unit stands in: what is written
\ there is lost, so the node reads as unstamped and every audit refuses
\ it (fail-closed).

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ./diagnostics.fs
require ./levels.fs
require ./symbolic-session.fs
require ./tagged-sort-boundary.fs
require ./terms.fs

lf-walk-room context-walk: lf-href-walker

begin-structure /lf-stamp
  field: lf-stamp-term       \ the term index
  field: lf-stamp-own        \ the node's own identity, stamped when made
  field: lf-stamp-level      \ a symbolic Sort's level identity
end-structure
\ A constant's unit holds its reference's identity where a Sort's holds
\ its level's (constant-term-boundary.fs; compact-store plan step S4).
: lf-stamp-ref ( unit -- addr ) lf-stamp-level ;
/lf-stamp context-slab: lf-stamp-units
/htab context-record: lf-stamp-table
/lf-stamp context-record: lf-stamp-spare
: lf-stamp-unit ( n -- unit ) lf-stamp-units slab-at ;
: lf-stamp-rehash ( n htab -- h ) drop lf-stamp-unit lf-stamp-term @ hash-fmix ;
: lf-stamp-same ( n key htab -- flag ) drop swap lf-stamp-unit lf-stamp-term @ = ;
create lf-stamp-hooks /htab-hooks allot
' lf-stamp-rehash ' lf-stamp-same lf-stamp-hooks htab-hooks!
: lf-stamp-table-make ( -- ) 4 lf-stamp-hooks lf-stamp-table htab-init drop ;
' lf-stamp-table-make context-setup
:noname ( -- ) lf-stamp-table htab-free ; context-teardown
: lf-stamp-none ( index -- unit ) drop lf-stamp-spare dup /lf-stamp erase ;
: lf-stamp-find ( index -- n true | slot false ) dup hash-fmix lf-stamp-table htab-find ;
\ A new zero unit for index, entered at the empty slot the find gave.
: lf-stamp-fill ( index n -- unit )
  lf-stamp-unit dup /lf-stamp erase tuck lf-stamp-term ! ;
: lf-stamp-new ( index slot -- unit )
  1 lf-stamp-units slab-claim ok? 0= if 2drop lf-stamp-none exit then
  tuck swap lf-stamp-table htab-put lf-stamp-fill ;
\ An input node of a term view (terms.fs) has no unit: it is sealed, its
\ own stamp is its identity and its level's or reference's the one the
\ importer gave it (lf-term-leaf-stamp), so a unit of those is filled in
\ a spare of its own; what is written there is lost.
/lf-stamp context-record: lf-stamp-input
: lf-stamp-of-input ( index -- unit )
  lf-stamp-input >r dup r@ lf-stamp-term ! dup lf-term-input-identity r@ lf-stamp-own !
  lf-term-leaf-stamp r@ lf-stamp-level ! r> ;
\ The stamp unit of a term index, made when first asked for.
: lf-term-stamps ( index -- unit )
  dup lf-term-input? if lf-stamp-of-input exit then
  lf-stamp-table htab-ready ok? 0= if lf-stamp-none exit then
  dup lf-stamp-find if nip lf-stamp-unit exit then lf-stamp-new ;

\ Stamp cells at a valid term index: the node's own identity (a symbolic
\ Sort's; constant-term-boundary.fs's constant nodes) and a Sort's level
\ identity.
: lf-term-own-stamp ( index -- addr ) lf-term-stamps lf-stamp-own ;
: lf-hsort-level-stamp ( index -- addr ) lf-term-stamps lf-stamp-level ;

\ The fuel the last audit left, under its established name.
: lf-href-fuel ( -- addr ) lf-href-walker walk-fuel ;

\ A pair names a live slot with that identity. Level pairs say nothing about
\ shape or scope; term pairs also need the session to be current. A handle
\ is where a pass takes a node from outside, so these are checked roots:
\ they check the store's whole header (terms.fs), the reads after them
\ only the index.
: lf-hlevel-id? ( index identity -- flag )
  swap lf-level-identity if = else drop false then ;
: lf-hlevel-valid? ( index identity -- flag )
  lf-level-count-valid? if lf-hlevel-id? else 2drop false then ;
: lf-hterm-id? ( index identity -- flag )
  swap lf-term-identity if = else drop false then ;
\ The session's check covers both stores' headers (symbolic-session.fs).
: lf-hterm-valid? ( index identity -- flag )
  lf-ssession-current? if lf-hterm-id? else 2drop false then ;
: lf-hterms-valid? ( left lid right rid -- flag )
  lf-hterm-valid? >r lf-hterm-valid? r> and ;

\ Turn an allocator's result into a handle.
: lf-hlevel-result ( index true | false -- index identity true | false )
  if dup lf-level-identity dup 0= if nip then else false then ;
: lf-hterm-result ( index true | false -- index identity true | false )
  if dup lf-term-identity dup 0= if nip then else false then ;

\ Level handles: zero, an opaque parameter, or the successor of a live level.
\ Parameters must still be in the session context when checked.
: lf-hlevel-zero ( -- index identity true | false )
  0 lf-level-root? if 0 dup lf-level-identity else false then ;
: lf-hlevel-param ( name-id -- index identity true | false )
  lf-level-param lf-hlevel-result ;
: lf-hlevel-succ ( index identity -- index identity true | false )
  2dup lf-hlevel-valid? if drop lf-level-succ lf-hlevel-result else 2drop false then ;

\ Symbolic Sort from a live level handle while the session is current; the
\ stamps tie the new term to both identities. Level scope is checked later.
: lf-hsort-stamp ( level-identity term-index term-identity -- )
  over lf-term-own-stamp ! lf-hsort-level-stamp ! ;
: lf-hsort-source? ( level-index level-identity -- flag )
  lf-hlevel-valid? lf-ssession-current? and ;
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
: lf-hterm-app ( left lid right rid -- index identity true | false )
  lf-tag-app lf-hterm-binary ;
: lf-hterm-lam ( domain did body bid -- index identity true | false )
  lf-tag-lam lf-hterm-binary ;
: lf-hterm-pi ( domain did body bid -- index identity true | false )
  lf-tag-pi lf-hterm-binary ;

\ Audit of a structurally checked term: each symbolic Sort must carry the
\ stamps of this exact term allocation and a level that still has the
\ stamped identity. Children point backwards, so a count rollback cannot
\ keep a parent while removing its child. Raw mutation is excluded.
\ Whether the node still has the identity it was stamped with.
: lf-term-stamped? ( node -- flag )
  dup lf-term-identity if swap lf-term-own-stamp @ = else drop false then ;
: lf-hsort-level-ok? ( level node -- flag )
  swap lf-level-identity if swap lf-hsort-level-stamp @ = else drop false then ;
: lf-hsort-stamped? ( level node -- flag )
  dup lf-term-stamped? if lf-hsort-level-ok? else 2drop false then ;
: lf-href-sort ( first second walk -- outcome )
  nip walk-node @ lf-hsort-stamped? flag>outcome ;
: lf-href-dispatch ( first second walk tag -- outcome )
  ['] lf-href-sort lf-symbolic-dispatch ;
: lf-href-visit ( walk -- outcome ) ['] lf-href-dispatch lf-term-visit ;
\ Internal: audit an already structurally checked root. Negative fuel is
\ invalid.
: lf-href-site ( -- site ) c" generation-handles lf-hterm-check" ;
: lf-href-run ( root -- status )
  ['] lf-href-visit lf-href-walker lf-href-site lf-diag-run ;
: lf-href-check ( root fuel -- status )
  lf-href-walker walk-budget if lf-href-run else drop-invalid then ;

\ Check a live handle's reachable syntax, levels and Sort stamps with one
\ budget. Structural and level-scope evidence only: binder scope, typing and
\ theorem validity are not checked.
: lf-hterm-check ( index identity fuel -- status )
  >r 2dup lf-hterm-valid? 0= if 2drop r> drop outcome-invalid exit then
  drop dup r> lf-ssession-check ok-then? if lf-ssession-fuel @ lf-href-check then ;
