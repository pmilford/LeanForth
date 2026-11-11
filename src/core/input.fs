\ The input of a checking run (ADR 0012, E1): the declarations the
\ importer decoded, in input order, each with its name, kind, safety,
\ universe parameters, type and value roots and reducibility hint. They
\ point into the term, level, name and constant-reference stores, which
\ hold the decoded terms. Declaration i is the i-th added, counting from 0.
\
\ The importer (in phase 2 a test-only transport) adds declarations with
\ lf-input-add and ends loading with lf-input-end, which marks every input
\ store (store-mark). From then on nothing may be added or written below
\ the marks: a check allocates its scratch above them, and
\ lf-input-rollback returns the stores to the marks after each check,
\ whatever its outcome. lf-input-intact? tells whether the input is still
\ as loading left it, as far as counts and identities show: every mark
\ still valid (no reset, nothing rolled back below it) and the name bytes
\ still there (their count not below the count when loading ended).
\ Records below the marks are never written again by any word; tests
\ check that with a digest. lf-input-add checks each record's ranges and
\ that its references are live, not its typing or scope.
\
\ Per context, for now. ADR 0012 (E1) makes the input one shared, read-only
\ tier; today the term, level, name and reference stores are members of
\ the checker context (lib/context.fs), so the input lives in the context
\ that loaded it, and so do its declarations and marks. A check can run
\ only in a context holding the input. lf-input-end records a fingerprint
\ of the input region: every input store's records, identities, count and
\ generation below its mark, then the name bytes in use and their count.
\ Two contexts that loaded the same input from a fresh start have the
\ same fingerprint, and an environment (kernel/environment.fs) is bound to
\ the fingerprint it was made over, so a context holding no input or a
\ different one fails closed.
\
\ The fingerprint's limits (ADR 0012, amended 2026-11-02): it guards
\ against mistakes, such as checking in a context that loaded another
\ input, not against forgery: FNV-style mixing is not a cryptographic
\ hash, and two different inputs can share one. It is computed once, when
\ loading ends; later changes are caught by lf-input-intact? as far as
\ counts and identities show, never by the fingerprint. Plan task 7.2.1
\ splits the stores into a shared input tier and per-context scratch.
\ Seal only after every context member is declared: a marked store whose
\ context moves no longer matches its mark.
\
\ Untrusted [import] data; part of the first checker's [kernel] path, not
\ yet through the review gate. A declaration may have any number of
\ universe parameters (plan task 6.2.0; Mathlib's most is 30): an
\ importer's record points at its own array of them, and lf-input-add
\ copies them into the input's cells (lf-input-more); lf-param-capacity,
\ 64, is no limit: only the number run records 0.1 report. The number of
\ declarations is a capacity setting (lf-input-capacity!). The
\ fingerprint also covers the references' universe arguments (their
\ pool) and, under a name view (names.fs), every input name's hash.
\ State: the declaration store lf-inputs (a heap store), the name index
\ lf-input-names and the inductive data lf-input-more (heap slabs) and one
\ record, lf-input-state, all members of the checker context; written only
\ while loading and by
\ lf-input-reset, then read by every check in that context. The layout is
\ host-specific and never serialized.

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/store-columns.fs
require ../lib/bytes.fs
require ./terms.fs
require ./levels.fs
require ./names.fs
require ./constant-references.fs

32 constant lf-input-default
64 constant lf-param-capacity

\ Declaration kinds, as Lean's ConstantInfo; 0 is no kind.
1 constant lf-kind-definition
2 constant lf-kind-theorem
3 constant lf-kind-axiom
4 constant lf-kind-opaque
5 constant lf-kind-quotient
6 constant lf-kind-inductive
7 constant lf-kind-constructor
8 constant lf-kind-recursor
9 constant lf-kind-block         \ an empty inductive block (ADR 0016 amendment 1)
\ Safety and reducibility hints, coded as the NDJSON reader codes them.
0 constant lf-safety-safe
1 constant lf-safety-unsafe
2 constant lf-safety-partial
0 constant lf-hint-opaque
1 constant lf-hint-abbrev
2 constant lf-hint-regular

begin-structure /lf-idecl
  field: lf-idecl-name      \ name ID, not anonymous
  field: lf-idecl-kind      \ lf-kind-...
  field: lf-idecl-safety    \ lf-safety-...
  field: lf-idecl-type      \ term index of the type
  field: lf-idecl-value     \ term index of the value, or -1 for none
  field: lf-idecl-hint      \ lf-hint-...; opaque for every kind but a definition
  field: lf-idecl-height    \ a regular hint's height, else 0
  field: lf-idecl-arity     \ number of universe parameters
  field: lf-idecl-params    \ an importer's record: the address of their name
                            \ IDs, in order (unused in the input's copy)
  field: lf-idecl-param-at  \ set by lf-input-add: where it put them, the
                            \ first of arity cells of lf-input-more
  field: lf-idecl-prev      \ set by lf-input-add: the declaration before it
                            \ of the same name, plus one; 0 for none
  field: lf-idecl-more      \ an inductive type, constructor or recursor: its
                            \ data's first cell in lf-input-more, plus one; else 0
  field: lf-idecl-block     \ a member of an inductive block: the block's
                            \ header cell in lf-input-more, plus one; else 0
end-structure

\ The declarations: a heap store growing up to a capacity that is a
\ setting of each context, as for terms (terms.fs); a new context starts
\ with lf-input-default.
store-header context-record: lf-inputs
: lf-inputs-make ( -- )
  lf-input-default /lf-idecl 0 lf-inputs store-heap-init ok? 0= abort" input: no heap" ;
' lf-inputs-make context-setup
:noname ( -- ) lf-inputs store-heap-free ; context-teardown
: lf-input-capacity ( -- n ) lf-inputs store-limit @ ;
: lf-input-capacity! ( n -- outcome ) lf-inputs store-limit! ;

\ The name index (ADR 0016 C4; ADR 0012 E5): for each name ID, the newest
\ declaration of that name plus one (0 for none), and in each declaration
\ the one before it of the same name (lf-idecl-prev); lf-input-add fills
\ both. When names are interned in a shared input tier (a name view,
\ names.fs), the declarations named n are exactly n's chain, so the
\ environment reads the chain instead of scanning every earlier
\ declaration (lf-input-indexed?); tests check that both agree. A heap
\ slab of cells, a member of the checker context with a teardown word.
/slab context-record: lf-input-names
: lf-input-names-make ( -- ) 1 cells max-n 1 cells / lf-input-names slab-init drop ;
' lf-input-names-make context-setup
:noname ( -- ) lf-input-names slab-free ; context-teardown
: lf-input-newest-cell ( name -- addr ) lf-input-names column-at ;
: lf-input-indexed? ( -- flag ) lf-name-viewed? ;

\ Inductive data (ADR 0015 B1; plan task 5.2.1a): the exported fields of
\ inductive types, constructors and recursors that the declaration record
\ has no room for, and each inductive block's header, as cells of one
\ heap slab, lf-input-more, written only while loading. A declaration's
\ lf-idecl-more and lf-idecl-block give its first cell and its block's
\ header (plus one; 0 for none). Lists are a count followed by the items.
\   block header  first member's declaration index, types, constructors,
\                 recursors (the members follow it in input order)
\   type          numParams numIndices numNested flags (bit 0 isRec, bit 1
\                 isReflexive) | all: count, names | ctors: count, names
\   constructor   induct cidx numParams numFields
\   recursor      numParams numIndices numMotives numMinors k (true or
\                 false) | all: count, names | rules: count, then per rule
\                 its constructor's name, nfields and right side (a term)
\ The numbers are the file's, never trusted: the checker of a block
\ computes its own and compares where Lean's replay compares (ADR 0015 B3,
\ B4). A heap slab of cells, a member of the checker context.
/slab context-record: lf-input-more
: lf-input-more-make ( -- ) 1 cells max-n 1 cells / lf-input-more slab-init drop ;
' lf-input-more-make context-setup
:noname ( -- ) lf-input-more slab-free ; context-teardown
0 constant lf-hdr-first   1 constant lf-hdr-types   2 constant lf-hdr-ctors
3 constant lf-hdr-recs    4 constant /lf-hdr
0 constant lf-ity-params  1 constant lf-ity-indices  2 constant lf-ity-nested
3 constant lf-ity-flags   4 constant lf-ity-all
0 constant lf-ict-induct  1 constant lf-ict-cidx  2 constant lf-ict-params
3 constant lf-ict-fields  4 constant /lf-ict
0 constant lf-irc-params  1 constant lf-irc-indices  2 constant lf-irc-motives
3 constant lf-irc-minors  4 constant lf-irc-k  5 constant lf-irc-all
3 constant /lf-rule
1 constant lf-ity-rec-bit
2 constant lf-ity-reflexive-bit
\ Reading. Unchecked: the offsets are those lf-input-add accepted.
: lf-more-count ( -- n ) lf-input-more slab-count ;
: lf-more-cell ( k -- addr ) lf-input-more slab-at ;
: lf-more@ ( k -- x ) lf-more-cell @ ;
\ A declaration's data and its block's header: the address of the first
\ cell, or 0 for none.
: lf-idecl-data ( decl -- addr|0 ) lf-idecl-more @ ?dup if 1- lf-more-cell else 0 then ;
: lf-idecl-header ( decl -- addr|0 )
  lf-idecl-block @ ?dup if 1- lf-more-cell else 0 then ;
\ Field k of a data record, and a list at addr: its items and count.
: lf-more-field ( addr k -- x ) cells + @ ;
: lf-more-list ( addr -- items n ) dup cell+ swap @ ;
\ The list after the one at addr.
: lf-more-next ( addr -- addr' ) dup @ 1+ cells + ;
\ A type's lists: all, then ctors; a recursor's all, then its rules.
: lf-ity-all@ ( data -- items n ) lf-ity-all cells + lf-more-list ;
: lf-ity-ctors@ ( data -- items n ) lf-ity-all cells + lf-more-next lf-more-list ;
: lf-irc-all@ ( data -- items n ) lf-irc-all cells + lf-more-list ;
: lf-irc-rules@ ( data -- rules n ) lf-irc-all cells + lf-more-next lf-more-list ;
\ Rule k of a rules list: its constructor's name, nfields and right side.
: lf-irc-rule ( rules k -- addr ) /lf-rule * cells + ;
\ A rule's three cells: its constructor's name, its fields, its right side.
: lf-irule-ctor ( rule -- name ) @ ;
: lf-irule-nfields ( rule -- n ) cell+ @ ;
: lf-irule-rhs ( rule -- root ) 2 cells + @ ;

5 constant lf-input-stores#
begin-structure /lf-inrec
  field: lf-inrec-sealed        \ true once loading has ended
  field: lf-inrec-name-bytes    \ name bytes in use when it ended
  field: lf-inrec-fingerprint   \ the input region's fingerprint then
  lf-input-stores# /store-mark * +field lf-inrec-marks
end-structure
/lf-inrec context-record: lf-input-state

\ The input stores, in the order of their marks.
create lf-input-stores ' lf-terms , ' lf-levels , ' lf-names , ' lf-crefs , ' lf-inputs ,
: lf-input-store ( k -- store ) cells lf-input-stores + @ execute ;
: lf-input-mark ( k -- mark ) /store-mark * lf-input-state lf-inrec-marks + ;
\ Its count, as a value: objects of input store k lie below it (for
\ readers such as the derivation log, which may not hold an address).
: lf-input-mark-count ( k -- n ) lf-input-mark mark-count @ ;
\ Whether test ( mark store -- flag ) holds for every input store.
: lf-input-all? ( test -- flag )
  true lf-input-stores# 0 ?do over i lf-input-mark i lf-input-store rot execute and loop
  nip ;
: lf-input-bytes ( -- addr ) lf-input-state lf-inrec-name-bytes ;
: lf-input-sealed? ( -- flag ) lf-input-state lf-inrec-sealed @ true = ;

\ The fingerprint: cells, then bytes, mixed in order with lib/bytes.fs's
\ fnv-step and bytes-mix (within one host only; never compared across
\ machines or written out).
: lf-fp-cells ( h addr n -- h' ) 0 ?do dup @ rot swap fnv-step swap cell+ loop drop ;
: lf-fp-width ( store -- n ) store-width @ 1 cells / ;
: lf-fp-records ( h count store -- h' )
  tuck lf-fp-width * swap store-records swap lf-fp-cells ;
: lf-fp-identities ( h count store -- h' ) store-identities swap lf-fp-cells ;
: lf-fp-state ( h store -- h' )
  dup store-count @ rot swap fnv-step swap store-generation @ fnv-step ;
\ One store below count, with its count and generation.
: lf-fp-store ( h count store -- h' )
  rot over lf-fp-state -rot 2dup 2>r lf-fp-records 2r> lf-fp-identities ;
: lf-input-marked ( k -- count store )
  dup lf-input-mark mark-count @ swap lf-input-store ;
\ The name bytes in use when loading ended, and their count. Unchecked:
\ the count is within the pool (lf-input-end checks it).
: lf-fp-names ( h -- h' ) lf-input-bytes @ tuck fnv-step lf-name-bytes rot bytes-mix ;
\ The universe arguments of the references, in their pool, and under a
\ name view the count and stored hash of every name.
: lf-fp-pool ( h -- h' ) 0 lf-cref-pool slab-at lf-cref-top 2* lf-fp-cells ;
: lf-fp-view-names ( h -- h' )
  lf-name-numbers tuck fnv-step swap 0 ?do i lf-name-hash fnv-step loop ;
: lf-fp-view ( h -- h' ) lf-name-viewed? if lf-fp-view-names then ;
\ The inductive data: its count, then its cells.
: lf-fp-more ( h -- h' )
  lf-more-count tuck fnv-step swap ?dup if 0 lf-more-cell swap lf-fp-cells then ;
: lf-input-print ( -- h )
  0 lf-input-stores# 0 ?do i lf-input-marked lf-fp-store loop lf-fp-names lf-fp-pool
  lf-fp-view lf-fp-more ;
\ The fingerprint recorded when loading ended; 0 before.
: lf-input-fingerprint ( -- h ) lf-input-state lf-inrec-fingerprint @ ;

\ Reading declarations. Unchecked: i is a valid index.
: lf-input-count ( -- n ) lf-inputs store-count @ ;
: lf-input-decl ( i -- decl ) lf-inputs store-slot ;
: lf-input-name ( i -- name ) lf-input-decl lf-idecl-name @ ;
: lf-param@ ( params k -- name ) cells + @ ;
\ An added declaration's parameters (in lf-input-more, which grows only
\ while loading).
: lf-idecl-params@ ( decl -- params n )
  dup lf-idecl-param-at @ lf-more-cell swap lf-idecl-arity @ ;
: lf-input-params ( i -- params n ) lf-input-decl lf-idecl-params@ ;
\ The newest declaration named name, and the one named alike before d;
\ -1 for none. Unchecked: a valid name, d a valid index.
: lf-input-newest ( name -- d|-1 )
  dup lf-input-names slab-capacity u< if lf-input-newest-cell @ 1- else drop -1 then ;
: lf-input-before ( d -- d'|-1 ) lf-input-decl lf-idecl-prev @ 1- ;

\ Whether the input is as loading left it (see above).
: lf-input-intact? ( -- flag )
  lf-input-sealed? ['] store-mark-valid? lf-input-all? and
  lf-name-used @ lf-input-bytes @ >= and ;
\ Checked: declaration i of an intact input.
: lf-input-read ( i -- decl outcome )
  lf-input-intact? over lf-inputs store-valid? and
  if lf-input-decl outcome-ok else drop 0 outcome-invalid then ;

\ Checks of a record before it is added: ranges, and live references.
: lf-input-name-ok? ( decl -- flag ) lf-idecl-name @ dup 0> swap lf-name-valid? and ;
: lf-input-kind-ok? ( decl -- flag )
  lf-idecl-kind @ lf-kind-definition lf-kind-recursor between? ;
: lf-input-safety-ok? ( decl -- flag ) lf-idecl-safety @ lf-safety-partial upto? ;
\ A regular hint has a height of at least 0; the others have height 0.
: lf-hint-ok? ( hint height -- flag )
  over lf-hint-regular = if nip 0< 0= else 0= swap lf-hint-abbrev upto? and then ;
: lf-input-hint-ok? ( decl -- flag )
  dup lf-idecl-hint @ over lf-idecl-height @ lf-hint-ok?
  over lf-idecl-kind @ lf-kind-definition = rot lf-idecl-hint @ lf-hint-opaque = or and ;
: lf-param-ok? ( name -- flag ) dup 0> swap lf-name-valid? and ;
: lf-params-ok? ( params n -- flag )
  0 ?do dup i lf-param@ lf-param-ok? 0= if drop false unloop exit then loop drop true ;
: lf-input-params-ok? ( decl -- flag )
  dup lf-idecl-arity @ dup 0< 0=
  if swap lf-idecl-params @ swap lf-params-ok? else 2drop false then ;
: lf-input-value-ok? ( value -- flag ) dup -1 = if drop true else lf-term-root? then ;
: lf-input-roots-ok? ( decl -- flag )
  dup lf-idecl-type @ lf-term-root? swap lf-idecl-value @ lf-input-value-ok? and ;
\ The inductive data, when present: a record of the declaration's kind
\ that lies wholly within lf-input-more, its lists' counts nonnegative;
\ the block header likewise. Nothing else about the data is checked here.
: lf-more-span? ( k n -- flag ) over 0< 0= -rot + lf-more-count upto? and ;
\ A list at cell k that fits: the cell after it, or -1.
: lf-more-list-end ( k -- k' )
  dup 1 lf-more-span? 0= if drop -1 exit then
  dup lf-more@ dup 0< if 2drop -1 exit then
  1+ 2dup lf-more-span? if + else 2drop -1 then ;
: lf-more-rules-end ( k -- k' )
  dup 1 lf-more-span? 0= if drop -1 exit then
  dup lf-more@ dup 0< if 2drop -1 exit then /lf-rule * 1+ 2dup lf-more-span?
  if + else 2drop -1 then ;
: lf-more-type? ( k -- flag )
  lf-ity-all + lf-more-list-end dup 0< if drop false exit then lf-more-list-end 0< 0= ;
: lf-more-ctor? ( k -- flag ) /lf-ict lf-more-span? ;
: lf-more-rec? ( k -- flag )
  lf-irc-all + lf-more-list-end dup 0< if drop false exit then lf-more-rules-end 0< 0= ;
: lf-more-kind? ( k kind -- flag )
  over 0< if 2drop false exit then
  case lf-kind-inductive of lf-more-type? endof
    lf-kind-constructor of lf-more-ctor? endof
    lf-kind-recursor of lf-more-rec? endof nip false swap endcase ;
: lf-input-more-ok? ( decl -- flag )
  dup lf-idecl-more @ ?dup if 1- swap lf-idecl-kind @ lf-more-kind? else drop true then ;
: lf-input-block-ok? ( decl -- flag )
  lf-idecl-block @ ?dup if 1- /lf-hdr lf-more-span? else true then ;
\ An empty inductive block (lf-kind-block): the one declaration of an
\ inductive record with no type, constructor or recursor, which Lean's
\ kernel rejects (emptyBlock); the importer adds it so that the checker
\ can say so (ADR 0016 amendment 1). No name, no universe parameter, no
\ type, no value, no data; safe; a member of its block, whose header it
\ points at.
: lf-input-empty-ok? ( decl -- flag )
  dup lf-idecl-name @ 0= over lf-idecl-arity @ 0= and over lf-idecl-type @ -1 = and
  over lf-idecl-value @ -1 = and over lf-idecl-more @ 0= and
  over lf-idecl-safety @ lf-safety-safe = and over lf-input-hint-ok? and
  over lf-idecl-block @ 0<> and swap lf-input-block-ok? and ;
: lf-input-decl-ok? ( decl -- flag )
  dup lf-idecl-kind @ lf-kind-block = if lf-input-empty-ok? exit then
  dup lf-input-name-ok? over lf-input-kind-ok? and over lf-input-safety-ok? and
  over lf-input-hint-ok? and over lf-input-params-ok? and over lf-input-roots-ok? and
  over lf-input-more-ok? and swap lf-input-block-ok? and ;

\ Loading. lf-input-add copies a /lf-idecl record the importer filled and
\ gives its index: ok; invalid, adding nothing, after loading has ended or
\ for a record that fails the checks above; full when the store has no
\ room. lf-input-end marks every input store and ends loading: ok; or
\ invalid, still loading, when loading had already ended, the name store
\ or its byte count is out of range, or a store is invalid.
\ The offset the next cell of lf-input-more gets, and appending a cell
\ there: ok, or full when the slab has no room.
: lf-more-here ( -- k ) lf-more-count ;
: lf-more-append ( x -- outcome )
  1 lf-input-more slab-claim dup ok? if drop lf-more-cell ! outcome-ok else nip nip then ;
\ Room in the name index for decl's name (the test hook of lib/store.fs is
\ asked before it grows, as for the store's own block), and the links of
\ declaration i.
: lf-input-index-room ( decl -- outcome )
  lf-idecl-name @ 1+ dup lf-input-names slab-capacity > 0= if drop outcome-ok exit then
  lf-inputs store-grow-refused? if drop outcome-full exit then
  lf-input-names column-reserve ;
: lf-input-link ( i -- )
  dup lf-input-name lf-input-newest-cell 2dup @ swap lf-input-decl lf-idecl-prev !
  swap 1+ swap ! ;
\ The record's parameters appended to lf-input-more: where they begin, and
\ ok or full.
: lf-input-param, ( params i -- params outcome ) over swap lf-param@ lf-more-append ;
: lf-input-params, ( decl -- k outcome )
  lf-more-here swap dup lf-idecl-params @ swap lf-idecl-arity @ 0 ?do
    i lf-input-param, dup ok? 0= if nip unloop exit then drop
  loop drop outcome-ok ;
\ The copy keeps where its parameters are, never the importer's address
\ (which differs from context to context and would change the input's
\ fingerprint).
: lf-input-placed ( k decl i -- i )
  nip tuck lf-input-decl tuck lf-idecl-param-at ! 0 swap lf-idecl-params ! ;
: lf-input-copy ( decl -- i outcome )
  dup lf-input-index-room dup ok? 0= if nip -1 swap exit then drop
  dup lf-input-params, dup ok? 0= if nip nip -1 swap exit then drop swap
  lf-inputs store-ready drop
  lf-inputs store-new-slot 0= if 2drop -1 outcome-full exit then
  >r over swap /lf-idecl move r> lf-input-placed dup lf-input-link outcome-ok ;
: lf-input-add ( decl -- i outcome )
  lf-input-sealed? if drop -1 outcome-invalid exit then
  dup lf-input-decl-ok? if lf-input-copy else drop -1 outcome-invalid then ;
\ Inductive data, while loading (see lf-input-more above): appending a
\ cell (lf-more-here gives its offset): ok; invalid once loading has
\ ended; full when the slab has no room. A declaration that refers to
\ the data is added after it.
: lf-more, ( x -- outcome )
  lf-input-sealed? if drop outcome-invalid else lf-more-append then ;
: lf-mark-ok? ( mark store -- flag ) store-mark ok? ;
: lf-input-seal ( -- )
  lf-name-used @ lf-input-bytes ! lf-input-print lf-input-state lf-inrec-fingerprint !
  true lf-input-state lf-inrec-sealed ! ;
: lf-input-end ( -- outcome )
  lf-input-sealed? lf-name-state-valid? 0= or if outcome-invalid exit then
  ['] lf-mark-ok? lf-input-all? if lf-input-seal outcome-ok else outcome-invalid then ;

\ After a check: every input store back to its mark and the name bytes
\ back to their count; ok, or invalid with nothing changed when the input
\ is not intact. The terms go back through lf-term-rollback, which takes
\ their entries out of the hash-consing table too (terms.fs).
: lf-store-back ( mark store -- outcome )
  dup lf-terms = if drop lf-term-rollback else store-rollback then ;
: lf-mark-back ( mark store -- flag ) lf-store-back ok? ;
: lf-input-rollback ( -- outcome )
  lf-input-intact? 0= if outcome-invalid exit then
  ['] lf-mark-back lf-input-all? lf-input-bytes @ lf-name-used ! flag>outcome ;

\ Start loading a new input in this context: forget every declaration and
\ end the sealed state. Every environment made over the old input then
\ fails closed: its fingerprint covers the declarations' identities, which
\ never repeat.
: lf-input-reset ( -- )
  lf-inputs store-clear lf-input-state /lf-inrec erase lf-input-names column-erase
  lf-input-more slab-clear ;
