\ Bounded storage for symbolic Lean-style universe level syntax: zero,
\ successor, max, imax and parameters. Untrusted. This module does not decide
\ level equality, validate parameter scope, check declarations or confer
\ theorem validity. Parameter identifiers are opaque positive cell values,
\ not a complete Lean name representation.
\ Each level is a tagged node (lib/node.fs) in a heap store
\ (lib/store.fs) whose record 0 is always the zero level, growing up to a
\ capacity that is a setting of each context, as for terms (terms.fs):
\ lf-level-capacity reads it, lf-level-capacity! sets it, a new context
\ starts with lf-level-default. Per-level side data of other modules lives
\ in columns of the group lf-level-columns (lib/store-columns.fs). Level
\ graphs have no fixed depth (plan task 6.2.0): lf-level-walk-room is
\ only the room a level walk starts with.
\
\ Hash-consing (ADR 0016 C1, C4; compact-store plan step S4), as for
\ terms (terms.fs): lf-level-add looks the record (tag, first, second)
\ up in a hash table of the context and gives back the equal level it
\ finds, else appends a new one and enters it, so equal level syntax is
\ one index for the levels a context makes while sharing (Lean's
\ operator== on levels). The zero level, record 0, is entered at every
\ reset. Sharing follows the context's switch for terms
\ (lf-term-sharing?): a context that keeps data per node turns both off.
\ A hash is only a hint; an entry is equal only when its allocated record
\ is, field by field, so no answer depends on the table (C8). A rollback
\ (lf-level-rollback, which the joint scratch marks of
\ core/scratch-marks.fs and the level passes' own marks use) takes the
\ entries of the records it gives back out of the table by Knuth's
\ Algorithm R, as lib/cons.fs does; a reset empties it.
\ State: the store header lf-levels, the hash table lf-level-table and
\ the candidate record lf-level-key, members of the checker context
\ (lib/context.fs) whose blocks are on the heap, made and reset by set-up
\ words in every context and freed by their teardown words; single-threaded
\ within one context. A reset invalidates all indices. The cell layout is
\ host-specific and must never be serialized directly.

require ../lib/lib.fs
require ../lib/u32.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ./diagnostics.fs
require ./terms.fs
require ../lib/store-columns.fs
require ./scratch-meter.fs

64 constant lf-level-default
64 constant lf-level-walk-room   \ a level walk's first room
0 constant lf-level-tag-zero
1 constant lf-level-tag-succ
2 constant lf-level-tag-max
3 constant lf-level-tag-imax
4 constant lf-level-tag-param

store-header context-record: lf-levels
: lf-levels-make ( -- )
  lf-level-default /node 1 lf-levels store-heap-init ok? 0= abort" levels: no heap" ;
' lf-levels-make context-setup
:noname ( -- ) lf-levels store-heap-free ; context-teardown
\ The capacity setting of this context, and setting it (as for terms).
: lf-level-capacity ( -- n ) lf-levels store-limit @ ;
: lf-level-capacity! ( n -- outcome ) lf-levels store-limit! ;

\ The store's fields under their established names; other modules roll the
\ store back through marks (core/scratch-marks.fs, or a level-store mark),
\ and tests corrupt these cells to check fail-closed behavior.
: lf-level-count ( -- addr ) lf-levels store-count ;
: lf-level-generation ( -- addr ) lf-levels store-generation ;
: lf-level-serial ( -- addr ) lf-levels store-serial ;
: lf-level-identities ( -- addr ) lf-levels store-identities ;
\ Node address; the index must already be validated.
: lf-level-slot ( index -- addr ) lf-levels store-slot ;

\ ---------------------------------------------------------------------------
\ The hash-consing table (see the header): its hooks hash record n from
\ its fields and tell whether allocated record n equals the record sought.
/htab context-record: lf-level-table
/lf-sought context-record: lf-level-key   \ the record sought (terms.fs)
: lf-level-rehash ( n htab -- h ) drop lf-level-slot node@ lf-fields-hash ;
\ Whether level n may be given for a record made equal to it: a hook, by
\ default always; kernel/check-declaration.fs sets it so that in a check a
\ level made before it is given only once the check reached it, as for
\ terms (terms.fs's lf-term-findable?; agent PF, ADR 0014 Amendment 7).
defer lf-level-findable? ( n -- flag )
:noname ( n -- flag ) drop true ; is lf-level-findable?
: lf-level-same ( n key htab -- flag )
  drop over lf-levels store-at? 0= if 2drop false exit then
  over lf-level-findable? 0= if 2drop false exit then
  >r lf-level-slot node@ r> lf-sought= ;
create lf-level-hooks /htab-hooks allot
' lf-level-rehash ' lf-level-same lf-level-hooks htab-hooks!
: lf-level-table-make ( -- ) 4 lf-level-hooks lf-level-table htab-init drop ;
' lf-level-table-make context-setup
:noname ( -- ) lf-level-table htab-free ; context-teardown
: lf-level-key@ ( -- tag first second ) lf-level-key lf-sought@ ;
: lf-level-find ( tag first second -- n true | i false )
  lf-level-key lf-sought-hash! lf-level-table htab-find ;
\ Enter the new record index at the empty slot i the find gave.
: lf-level-enter ( i index true | i false -- index true | false )
  if tuck swap lf-level-table htab-put true else drop false then ;
\ Take record index out of the table, if it is there (a record made while
\ sharing was off, or that the table could not take, is not), and every
\ record from count up to the store's count.
: lf-level-forget ( index -- )
  dup lf-level-slot node@ lf-fields-hash lf-level-table htab-remove drop ;
: lf-level-unlist ( count -- )
  lf-level-table htab-live? 0= if drop exit then
  lf-level-count @ swap ?do i lf-level-forget loop ;
\ The zero level into the table (one that cannot take it only costs
\ sharing).
: lf-level-enter-zero ( -- )
  lf-level-table htab-ready ok? 0= if exit then
  0 lf-level-slot node@ lf-level-find if drop else 0 swap lf-level-table htab-put then ;
\ Empty the table, back to 16 slots when it had grown large.
: lf-level-table-empty ( -- ) lf-level-table ['] lf-level-table-make htab-renew ;

\ Discard every level and claim record 0 as the zero level with a fresh
\ identity. Unchecked: the serial must not be spent; lf-level-reset checks.
: lf-level-restart ( -- ) 0 lf-level-count ! lf-levels store-claim lf-level-slot /node erase ;
\ Reset to the zero level alone and advance the generation. A spent identity
\ serial poisons the store instead of reusing an identity. The table then
\ holds the zero level alone.
: lf-level-reset ( -- )
  lf-level-table-empty
  lf-levels store-spent? if lf-levels store-poison exit then
  lf-level-restart lf-levels store-epoch+ lf-level-enter-zero ;
\ Roll the store back to a mark of it (lib/store.fs's store-mark): ok,
\ the records made since and their table entries given back; or invalid
\ with nothing changed for a mark that store-rollback refuses.
: lf-level-rollback ( mark -- outcome )
  dup lf-levels store-mark-valid? if dup mark-count @ lf-level-unlist then
  lf-levels store-rollback ;

\ Count and index checks; a valid store always holds the zero level. They
\ cannot detect stale indices reused after a reset, or corrupted fields.
\ As for terms (terms.fs, compact-store plan step S2), the whole header
\ is checked at a pass's root (lf-level-count-valid?, lf-level-root?,
\ lf-level-pair-valid? or a handle), and every read after that only
\ checks that the index is allocated (store-at?).
: lf-level-count-valid? ( -- flag ) lf-levels store-count-valid? ;
: lf-level-root? ( index -- flag ) lf-levels store-valid? ;
: lf-level-valid? ( index -- flag ) lf-levels store-at? ;
\ A live node's identity, including the zero level's; never repeats.
: lf-level-identity ( index -- identity true | false )
  dup lf-level-valid? if lf-levels store-identity @ true else drop false then ;
\ A level node with its identity, 0 when it is not live.
: lf-level-handle ( index -- index identity ) dup lf-level-identity 0= if 0 then ;

\ Append a node whose tag and fields the caller validated; a failed
\ allocation (no room, or past a check's memory limit: scratch-meter.fs)
\ returns false, changes nothing and is recorded as a diagnostic.
: lf-level-site ( -- site ) c" levels lf-level-add" ;
: lf-level-refused ( -- false )
  lf-levels lf-level-site lf-diag-levels-full lf-diag-store false ;
' lf-levels column-group: lf-level-columns
1 cells context-record: lf-level-covered   \ capacity the columns last covered
\ The usual case first: a free record and columns that cover the store.
: lf-level-steady? ( -- flag )
  lf-levels dup store-filled? 0= swap store-capacity @ lf-level-covered @ = and ;
: lf-level-room? ( -- flag )
  lf-level-steady? if true exit then
  lf-levels store-ready ok? if lf-level-covered lf-level-columns columns-ready else false then ;
\ Whether a universe parameter occurs in a level (Lean's has_param_univ),
\ kept per level in a column when the level is made, from its children's
\ (compact-store plan step S3: the term store's data words read it,
\ core/terms.fs). A record changed in place later (only tests do that)
\ keeps the flag it was made with; a child that is not allocated (a raw
\ caller's) counts as none.
/slab context-record: lf-level-param-flags
1 cells ' lf-level-param-flags lf-level-columns column-add
: lf-level-params? ( level -- flag ) lf-level-param-flags column-at @ 0<> ;
: lf-level-child-params? ( child -- flag )
  dup lf-level-valid? if lf-level-params? else drop false then ;
: lf-level-params-of ( tag first second -- flag )
  rot case lf-level-tag-param of 2drop true endof
    lf-level-tag-succ of drop lf-level-child-params? endof
    lf-level-tag-max of lf-level-child-params? swap lf-level-child-params? or endof
    lf-level-tag-imax of lf-level-child-params? swap lf-level-child-params? or endof
    >r 2drop false r> endcase ;
\ A new level is charged to a check's memory limit here, where it is made,
\ never one found shared (review rvRS F4).
: lf-level-new ( tag first second -- index true | false )
  lf-meter-level? 0= if 2drop drop lf-level-refused exit then
  2 pick 2 pick 2 pick lf-level-params-of >r lf-levels node-new
  if r> over lf-level-param-flags column-at ! true else r> drop lf-level-refused then ;
\ Hash-consed: the equal level, given only where an allocation would be
\ allowed (store-open?, as for terms), or a new level entered at the
\ empty slot the find gave. A table that cannot grow only costs sharing.
: lf-level-found ( n -- n true | false )
  lf-levels store-open? if true else drop lf-level-refused then ;
: lf-level-cons ( tag first second -- index true | false )
  lf-level-table htab-ready ok? 0= if lf-level-new exit then
  lf-level-find if lf-level-found exit then lf-level-key@ lf-level-new lf-level-enter ;
\ At most 2^32 - 2 records, so that a table slot holds every index plus one.
: lf-level-numbered? ( -- flag ) lf-level-count @ u32-mask 1- u< ;
: lf-level-make ( tag first second -- index true | false )
  lf-term-sharing? if lf-level-cons else lf-level-new then ;
: lf-level-add ( tag first second -- index true | false )
  lf-level-room? lf-level-numbered? and
  if lf-level-make else 2drop drop lf-level-refused then ;

\ Successor of an existing level; the second field is unused.
: lf-level-succ ( child -- index true | false )
  dup lf-level-valid? if lf-level-tag-succ swap 0 lf-level-add else drop false then ;
\ Parameter carrying an opaque, positive name identifier.
: lf-level-param ( name-id -- index true | false )
  dup 0> if lf-level-tag-param swap 0 lf-level-add else drop false then ;

\ max or imax of two existing levels, stored as syntax without simplifying
\ or asserting any equality. The tag range relies on imax = max + 1.
lf-level-tag-imax lf-level-tag-max 1+ <>
[if] .( levels.fs: max and imax tags must be consecutive) cr abort [then]
: lf-level-binary-tag? ( tag -- flag ) lf-level-tag-max lf-level-tag-imax 1+ within ;
\ Two checked roots with one header check (and a new node's children).
: lf-level-pair-valid? ( left right -- flag ) lf-levels store-pair-valid? ;
: lf-level-binary ( left right tag -- index true | false )
  >r 2dup lf-level-pair-valid? r@ lf-level-binary-tag? and
  if r> -rot lf-level-add else r> drop 2drop false then ;
: lf-level-max ( left right -- index true | false ) lf-level-tag-max lf-level-binary ;
: lf-level-imax ( left right -- index true | false ) lf-level-tag-imax lf-level-binary ;

\ Read an allocated node. A valid index alone does not authenticate fields;
\ the header is the root's to check.
: lf-level-read ( index -- tag first second true | false ) lf-levels node-read ;
\ One field of a node. Unchecked: the index must already be validated,
\ for instance by an earlier lf-level-read of the same node, under a
\ checked root.
: lf-level-tag@ ( index -- tag ) lf-level-slot node-tag @ ;
: lf-level-first@ ( index -- first ) lf-level-slot node-first @ ;
: lf-level-second@ ( index -- second ) lf-level-slot node-second @ ;

\ Every context starts with the zero level alone, and with its columns.
' lf-level-reset context-setup
:noname ( -- ) lf-level-columns columns-setup ; context-setup
:noname ( -- ) lf-level-columns columns-free ; context-teardown
