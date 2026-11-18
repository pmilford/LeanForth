\ Building terms for the authoring words (ADR 0017 §6, §10): nodes in the
\ existing term, level, name and constant-reference stores, each with its
\ source position in the presentation side table. While the term store
\ holds 64 nodes, identical nodes are shared: an application, variable,
\ Sort or constant equal to an existing node is that node, which keeps
\ the position where it was first written. Binder nodes are never shared
\ (each carries its own name, kind and position), and neither is a node
\ with a label or note: a step that gets one is first given a node of its
\ own (lfa-own), so a label never appears at two places. Levels and
\ constant references are shared by content. Store exhaustion stops the
\ authoring run with an error. Untrusted authoring code: a wrong node is a
\ different term, which the checker checks as it is and the printer shows.
\ State: two scratch records in the checker context, lfa-sought (the node
\ a lookup seeks) and lfa-sought-ref (the constant reference sought),
\ passed by address to the lookups.

require ../lib/lib.fs
require ../lib/find.fs
require ../lib/memo.fs
require ../lib/slab.fs
require ../core/terms.fs
require ../core/literals.fs
require ../core/projections.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/generation-handles.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../present/binder-table.fs
require ../present/note-table.fs
require ./errors.fs

/node context-record: lfa-sought

\ Fill the node sought.
: lfa-seek ( tag first second -- node ) lfa-sought dup >r node! r> ;
: lfa-same? ( node slot -- flag )
  2dup node-tag @ swap node-tag @ = >r 2dup node-first @ swap node-first @ = >r
  node-second @ swap node-second @ = r> r> and and ;
: lfa-shareable? ( term -- flag ) lf-note-any? 0= ;
\ A term's fields as the node sought holds them: a literal's value and
\ count, its limbs being kept apart (core/literals.fs).
: lfa-lit-fields ( term -- tag value count )
  lf-tag-lit over lf-lit-cell rot lf-term-second@ ;
: lfa-term-fields ( term -- tag first second )
  dup lf-lit-leaf? if lfa-lit-fields else lf-term-slot lf-term-fields@ then ;

\ The index of the terms a node may be shared with (review reuse-front-a
\ finding 1: a linear scan of the term store for each new node grew as
\ the cube of a statement's arrows once a declaration's values had no
\ limit). A memo (lib/memo.fs) maps a term's fields, as lfa-term-fields
\ gives them, to the chain of the terms that have them, oldest first:
\ links (term, identity, next) in a slab (lib/slab.fs). Only the tags
\ that a lookup seeks are entered (lfa-sought-tags: those lfa-copy
\ shares). The index follows the term store lazily: a lookup first
\ enters the terms made since the last one (lfa-shares-follow), and it
\ tells a rollback or reset by identities (core/terms.fs: a record's
\ identity is a serial that never repeats and grows with its number, so
\ a record made since the newest one entered has a newer identity). The
\ links of terms given back stay in their chains, stale, and a lookup
\ passes over them; once stale links outnumber live ones the index is
\ made again. A lookup answers the first live term of its chain that has
\ no label or note: the first term number that a scan of the whole store
\ would find, so sharing is as it was. Cost: a hash lookup and a link or
\ two per node; per entered term a link of three cells and, per distinct
\ fields, a memo entry of five. A heap that refuses the memo or a link
\ stops the run as a full term store (60), never with another node.
lf-tag-app lf-tag-bit lf-tag-projection lf-tag-bit or lf-tag-bvar lf-tag-bit or
lf-tag-symbolic-sort lf-tag-bit or lf-tag-constant lf-tag-bit or lf-tag-lit lf-tag-bit or
lf-tag-proj lf-tag-bit or constant lfa-sought-tags
begin-structure /lfa-link
  field: lfa-link-term
  field: lfa-link-identity   \ the term's identity when it was entered
  field: lfa-link-next       \ the next link of the chain, numbered from 1; 0 at the end
end-structure
begin-structure /lfa-shares
  /memo +field lfa-shares-memo   \ fields -> chain: first and last link (from 1)
  /slab +field lfa-shares-links
  field: lfa-shares-done         \ terms 0 .. done-1 are entered
  field: lfa-shares-last         \ the newest identity entered
  field: lfa-shares-stale        \ terms given back since the index was made
end-structure
/lfa-shares context-record: lfa-shares
/node context-record: lfa-share-key
: lfa-memo ( -- memo ) lfa-shares lfa-shares-memo ;
: lfa-links ( -- slab ) lfa-shares lfa-shares-links ;
: lfa-done ( -- a-addr ) lfa-shares lfa-shares-done ;
: lfa-stale ( -- a-addr ) lfa-shares lfa-shares-stale ;
: lfa-link ( n -- addr ) 1- lfa-links slab-at ;
:noname ( -- ) lfa-memo memo-free lfa-links slab-free ; context-teardown
: lfa-room ( outcome -- ) ok? lfa-e-terms-full lfa-must ;
: lfa-unentered ( -- ) 0 lfa-done ! 0 lfa-stale ! ;
: lfa-shares-make ( -- )
  lfa-unentered lfa-links slab-free 3 2 lfa-memo memo-init lfa-room
  /lfa-link dup slab-limit-max lfa-links slab-init lfa-room ;
: lfa-shares-ready ( -- ) lfa-memo memo-live? 0= if lfa-shares-make then ;
: lfa-renew ( -- ) lfa-memo memo-empty lfa-links slab-clear lfa-unentered ;

\ Entering term t: a link at the end of its fields' chain.
: lfa-identity ( term -- identity ) lf-term-identity 0= if 0 then ;
: lfa-link! ( term addr -- )
  2dup lfa-link-term ! swap lfa-identity over lfa-link-identity ! 0 swap lfa-link-next ! ;
: lfa-link-new ( term -- n ) 1 lfa-links slab-claim lfa-room 1+ tuck lfa-link lfa-link! ;
: lfa-chain+ ( n a-addr -- )
  dup @ if 2dup cell+ @ lfa-link lfa-link-next ! else 2dup ! then cell+ ! ;
: lfa-key ( term -- key ) lfa-term-fields lfa-share-key dup >r node! r> ;
: lfa-sought-tag? ( key -- flag ) node-tag @ lf-tag-bit lfa-sought-tags and 0<> ;
: lfa-enter-key ( term key -- )
  lfa-memo memo-put lfa-room swap lfa-link-new swap lfa-chain+ ;
: lfa-enter ( term -- ) dup lfa-key dup lfa-sought-tag? if lfa-enter-key else 2drop then ;
: lfa-entered ( term -- )
  dup lfa-enter dup lfa-identity lfa-shares lfa-shares-last ! 1+ lfa-done ! ;

\ Following the store: the terms below k that are the records entered
\ (no newer identity), the rest given back, and the terms made since.
: lfa-count ( -- n ) lf-term-count @ ;
: lfa-kept? ( k -- flag ) 1- lfa-identity lfa-shares lfa-shares-last @ > 0= ;
: lfa-kept ( -- k )
  lfa-done @ lfa-count min begin dup while dup lfa-kept? 0= while 1- repeat then ;
: lfa-forget ( k -- ) lfa-done @ over - lfa-stale +! lfa-done ! ;
: lfa-stale? ( -- flag ) lfa-stale @ lfa-done @ > ;
: lfa-shares-follow ( -- )
  lfa-shares-ready lfa-kept lfa-forget lfa-stale? if lfa-renew lfa-shares-ready then
  lfa-count lfa-done @ ?do i lfa-entered loop ;

\ A lookup: the first link whose term is the record entered, within the
\ store's count, and has no label or note.
: lfa-link-live? ( addr -- flag )
  dup lfa-link-term @ dup lfa-count < if lfa-identity swap lfa-link-identity @ =
  else 2drop false then ;
: lfa-link-hit? ( n -- flag )
  lfa-link dup lfa-link-live? if lfa-link-term @ lfa-shareable? else drop false then ;
: lfa-chain-next ( n -- n' ) lfa-link lfa-link-next @ ;
: lfa-chain-find ( n -- term true | false )
  begin dup while dup lfa-link-hit? 0= while lfa-chain-next repeat
    lfa-link lfa-link-term @ true then ;
\ An existing term equal to the node sought, without labels or notes.
: lfa-find ( node -- term true | false )
  lfa-shares-follow lfa-memo memo-find dup if @ lfa-chain-find then ;

\ New nodes; a refused allocation stops the run (the term store is full).
: lfa-made ( index true | false -- term ) 0= if lfa-e-terms-full lfa-fail then ;
\ An application, or a projection when f is a projection leaf
\ (core/projections.fs): the authors' $ applies a leaf to its term.
: lfa-app-tag ( f -- tag ) lf-proj-leaf? if lf-tag-projection else lf-tag-app then ;
: lfa-new-app ( f a -- term ) over lfa-app-tag lf-term-binary lfa-made ;
: lfa-new-bvar ( i -- term ) lf-term-bvar lfa-made ;
: lfa-new-sort ( level -- term )
  dup lf-level-identity drop lf-hterm-sort if drop else lfa-e-terms-full lfa-fail then ;
: lfa-new-const ( cref identity -- term )
  lf-cterm-new if drop else lfa-e-terms-full lfa-fail then ;
: lfa-span ( term pos -- term ) over swap lf-pres-source! drop ;

: lfa-new-lit ( u -- term ) lf-hterm-cell if drop else lfa-e-terms-full lfa-fail then ;
: lfa-new-proj ( name idx -- term )
  lf-hterm-proj if drop else lfa-e-terms-full lfa-fail then ;

\ Shared nodes: the term and true when it is new, false when it existed.
: lfa-app ( f a pos -- term fresh )
  >r 2dup over lfa-app-tag -rot lfa-seek lfa-find if nip nip r> drop false exit then
  lfa-new-app r> lfa-span true ;
: lfa-bvar ( i pos -- term fresh )
  >r lf-tag-bvar over 0 lfa-seek lfa-find if nip r> drop false exit then
  lfa-new-bvar r> lfa-span true ;
: lfa-sort ( level pos -- term fresh )
  >r lf-tag-symbolic-sort over 0 lfa-seek lfa-find if nip r> drop false exit then
  lfa-new-sort r> lfa-span true ;
: lfa-const ( cref identity pos -- term fresh )
  >r over lf-tag-constant swap 0 lfa-seek lfa-find if nip nip r> drop false exit then
  lfa-new-const r> lfa-span true ;

\ A literal leaf of one cell's value, and a projection leaf (name, index).
: lfa-lit ( u pos -- term fresh )
  >r lf-tag-lit over dup 0<> 1 and lfa-seek lfa-find if nip r> drop false exit then
  lfa-new-lit r> lfa-span true ;
: lfa-proj ( name idx pos -- term fresh )
  >r 2dup lf-tag-proj -rot lfa-seek lfa-find if nip nip r> drop false exit then
  lfa-new-proj r> lfa-span true ;

\ Binder nodes, never shared: the node, then its name and kind. A kind
\ the heap has no room to record stops the run (60): the front end reads
\ kinds (rw's telescope, intro), so a lost one is no longer only a lost
\ name in printed text (fix-batch-2, review C4 of 2026-11-18).
: lfa-binder-node ( domain body tag -- term ) lf-term-binary lfa-made ;
: lfa-kind-kept ( outcome -- ) ok? 0= if lfa-e-terms-full lfa-fail then ;
: lfa-name! ( term name kind -- term ) 2>r dup 2r> lf-pres-binder! lfa-kind-kept ;

\ A node of its own for a step that gets a label or note: the term itself
\ when it was new, else a copy with the same fields and position.
: lfa-copy-source ( old new -- )
  swap lf-pres-source@ if lf-pres-source! drop else drop then ;
: lfa-copy-naming ( old new -- )
  swap lf-pres-binder@ if lf-pres-binder! lfa-kind-kept else drop then ;
: lfa-copy-entry ( old new -- ) 2dup lfa-copy-source lfa-copy-naming ;
: lfa-fields ( term -- first second ) dup lf-term-first@ swap lf-term-second@ ;
\ A CASE with one arm per tag that is ever shared; binder nodes are new.
: lfa-copy ( term -- term' )
  dup lf-term-tag@ case
    lf-tag-app of lfa-fields lfa-new-app endof
    lf-tag-projection of lfa-fields lfa-new-app endof
    lf-tag-bvar of lf-term-first@ lfa-new-bvar endof
    lf-tag-symbolic-sort of lf-term-first@ lfa-new-sort endof
    lf-tag-constant of lf-term-first@ dup lf-cref-current lfa-new-const endof
    lf-tag-lit of lf-lit-cell lfa-new-lit endof
    lf-tag-proj of lfa-fields lfa-new-proj endof
  endcase ;
: lfa-own ( term fresh -- term ) if exit then dup lfa-copy tuck lfa-copy-source ;

\ Levels, shared by content; the zero level is index 0.
: lfa-level-made ( index true | false -- level ) 0= if lfa-e-levels-full lfa-fail then ;
: lfa-level-is? ( node i -- node flag ) over swap lf-level-slot lfa-same? ;
: lfa-level-find ( node -- level true | false )
  lf-level-count @ ['] lfa-level-is? find-index ;
: lfa-succ ( level -- level' )
  lf-level-tag-succ over 0 lfa-seek lfa-level-find if nip exit then
  lf-level-succ lfa-level-made ;
: lfa-param ( name -- level )
  lf-level-tag-param over 0 lfa-seek lfa-level-find if nip exit then
  lf-level-param lfa-level-made ;
: lfa-binary-level ( a b tag -- level )
  >r 2dup r@ -rot lfa-seek lfa-level-find if nip nip r> drop exit then
  r> lf-level-binary lfa-level-made ;
: lfa-max ( a b -- level ) lf-level-tag-max lfa-binary-level ;
: lfa-imax ( a b -- level ) lf-level-tag-imax lfa-binary-level ;
: lfa-succs ( level n -- level' ) 0 ?do lfa-succ loop ;
\ The level n: n successors of zero. A level beyond the store's capacity
\ could never be built.
: lfa-level-number ( n -- level )
  dup lf-level-capacity < lfa-e-levels-full lfa-must 0 swap lfa-succs ;

\ Constant references, shared by name and levels. The reference sought is
\ a record: a name, a count and that many (index identity) level pairs.
begin-structure /lfa-ref
  field: lfa-ref-name
  field: lfa-ref-count
end-structure
/lfa-ref context-record: lfa-sought-ref
\ Its level pairs, as many as the reference has (no fixed limit).
2 cells context-slab: lfa-ref-pair-cells
: lfa-ref-pairs ( ref -- addr ) drop 0 lfa-ref-pair-cells slab-at ;

: lfa-cref-at ( i -- index identity ) dup lf-cref-slot lf-crec-identity @ ;
: lfa-ref-head? ( ref i -- flag )
  lfa-cref-at lf-cref-read 0= if drop false exit then
  nip >r over lfa-ref-name @ = swap lfa-ref-count @ r> = and ;
: lfa-ref-levels? ( ref i -- flag )
  lfa-cref-at lf-cref-levels 0= if drop false exit then rot lfa-ref-pairs swap
    2* cells= ;
: lfa-ref-match? ( ref i -- flag ) 2dup lfa-ref-head? if lfa-ref-levels? else 2drop false
  then ;
: lfa-ref-is? ( ref i -- ref flag ) over swap lfa-ref-match? ;
: lfa-ref-find ( ref -- index identity true | false )
  lf-cref-count @ ['] lfa-ref-is? find-index if lfa-cref-at true else false then ;
: lfa-ref-new ( ref -- index identity )
  dup lfa-ref-name @ lf-name-generation @ rot dup lfa-ref-pairs swap lfa-ref-count @
  lf-cref-new 0= if lfa-e-references-full lfa-fail then ;
: lfa-cref ( ref -- index identity ) dup lfa-ref-find if rot drop else lfa-ref-new then ;

\ Shifting for A B ->: B's variables that point outside B (index at least
\ cutoff) point one binder further out. Unchanged subterms stay the same
\ node; a rebuilt node takes over the old one's position, binder name and
\ kind, and labels and notes (on a node of its own). Recursion is as deep
\ as the term, at most the term store's capacity.
: lfa-rebuilt ( old new fresh -- new' )
  rot dup lf-note-any? if -rot lfa-own tuck lf-note-move else 2drop then ;
: lfa-source-of ( term -- pos ) lf-pres-source@ 0= if 0 then ;
defer lfa-shift ( term cutoff -- term' )
: lfa-children ( term cutoff -- first' second' )
  over lf-term-first@ over lfa-shift >r swap lf-term-second@ swap lfa-shift r> swap ;
: lfa-binder-children ( term cutoff -- domain' body' )
  over lf-term-first@ over lfa-shift >r 1+ swap lf-term-second@ swap lfa-shift r> swap ;
: lfa-unchanged? ( term first' second' -- flag )
  rot dup lf-term-second@ rot = swap lf-term-first@ rot = and ;
: lfa-shift-var ( term cutoff -- term' )
  over lf-term-first@ swap < if exit then
  dup lf-term-first@ 1+ over lfa-source-of lfa-bvar lfa-rebuilt ;
: lfa-shift-app ( term cutoff -- term' )
  over swap lfa-children 2>r dup 2r@ lfa-unchanged? if 2r> 2drop exit then
  2r> 2 pick lfa-source-of lfa-app lfa-rebuilt ;
: lfa-shift-binder ( term cutoff -- term' )
  over swap lfa-binder-children 2>r dup 2r@ lfa-unchanged? if 2r> 2drop exit then
  dup lf-term-tag@ 2r> rot lfa-binder-node 2dup lfa-copy-entry true lfa-rebuilt ;
\ A CASE with one arm per tag that can hold a variable.
: lfa-shift-node ( term cutoff -- term' )
  over lf-term-tag@ case
    lf-tag-bvar of lfa-shift-var endof
    lf-tag-app of lfa-shift-app endof  lf-tag-projection of lfa-shift-app endof
    lf-tag-lam of lfa-shift-binder endof
    lf-tag-pi of lfa-shift-binder endof
    >r drop r> endcase ;
' lfa-shift-node is lfa-shift

\ A B ->: the Pi over A whose anonymous, explicit binder B does not use.
: lfa-arrow ( a b pos -- term )
  >r 0 lfa-shift lf-tag-pi lfa-binder-node 0 lf-binder-default lfa-name! r> lfa-span ;
