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
\ still there. Records below the marks are never written again by any
\ word; tests check that with a digest. lf-input-add checks each record's
\ ranges and that its references are live, not its typing or scope.
\
\ Per context, for now. ADR 0012 (E1) makes the input one shared, read-only
\ tier; today the term, level, name and reference stores are members of
\ the checker context (lib/context.fs), so the input lives in the context
\ that loaded it, and so do its declarations and marks. A check can run
\ only in a context holding the input. lf-input-end records a fingerprint
\ of the input region (every input store's records, identities, count and
\ generation below its mark; not the name bytes, which are text); two
\ contexts that loaded the same input from a fresh start have the same
\ fingerprint, and an environment (kernel/environment.fs) is bound to the
\ fingerprint it was made over, so a context holding no input or another
\ one fails closed. Plan task 7.2.1 splits the stores into a shared input
\ tier and per-context scratch. Seal only after every context member is
\ declared: a marked store whose context moves no longer matches its mark.
\
\ Untrusted [import] data; part of the first checker's [kernel] path, not
\ yet through the review gate. Up to lf-param-capacity universe
\ parameters per declaration (Mathlib uses up to 30 universe arguments:
\ a phase-2 limit, like the eight levels of a constant reference).
\ State: the declaration store lf-inputs and one record, lf-input-state,
\ both members of the checker context; written only while loading and by
\ lf-input-reset, then read by every check in that context. The layout is
\ host-specific and never serialized.

require ../lib/lib.fs
require ./terms.fs
require ./levels.fs
require ./names.fs
require ./constant-references.fs

32 constant lf-input-capacity
8 constant lf-param-capacity

\ Declaration kinds, as Lean's ConstantInfo; 0 is no kind.
1 constant lf-kind-definition
2 constant lf-kind-theorem
3 constant lf-kind-axiom
4 constant lf-kind-opaque
5 constant lf-kind-quotient
6 constant lf-kind-inductive
7 constant lf-kind-constructor
8 constant lf-kind-recursor
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
  lf-param-capacity cells +field lf-idecl-params   \ their name IDs, in order
end-structure

lf-input-capacity /lf-idecl 0 context-store: lf-inputs

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
\ Whether test ( mark store -- flag ) holds for every input store.
: lf-input-all? ( test -- flag )
  true lf-input-stores# 0 ?do over i lf-input-mark i lf-input-store rot execute and loop
  nip ;
: lf-input-bytes ( -- addr ) lf-input-state lf-inrec-name-bytes ;
: lf-input-sealed? ( -- flag ) lf-input-state lf-inrec-sealed @ true = ;

\ The fingerprint: cells mixed in order (FNV-style, within one host only;
\ never compared across machines or written out).
: lf-fp-mix ( h x -- h' ) xor 16777619 um* drop ;
: lf-fp-cells ( h addr n -- h' ) 0 ?do dup @ rot swap lf-fp-mix swap cell+ loop drop ;
: lf-fp-width ( store -- n ) store-width @ 1 cells / ;
: lf-fp-records ( h count store -- h' )
  tuck lf-fp-width * swap store-records swap lf-fp-cells ;
: lf-fp-identities ( h count store -- h' ) store-identities swap lf-fp-cells ;
: lf-fp-state ( h store -- h' )
  dup store-count @ rot swap lf-fp-mix swap store-generation @ lf-fp-mix ;
\ One store below count, with its count and generation.
: lf-fp-store ( h count store -- h' )
  rot over lf-fp-state -rot 2dup 2>r lf-fp-records 2r> lf-fp-identities ;
: lf-input-marked ( k -- count store )
  dup lf-input-mark mark-count @ swap lf-input-store ;
: lf-input-print ( -- h ) 0 lf-input-stores# 0 ?do i lf-input-marked lf-fp-store loop ;
\ The fingerprint recorded when loading ended; 0 before.
: lf-input-fingerprint ( -- h ) lf-input-state lf-inrec-fingerprint @ ;

\ Reading declarations. Unchecked: i is a valid index.
: lf-input-count ( -- n ) lf-inputs store-count @ ;
: lf-input-decl ( i -- decl ) lf-inputs store-slot ;
: lf-input-name ( i -- name ) lf-input-decl lf-idecl-name @ ;
: lf-param@ ( params k -- name ) cells + @ ;
: lf-idecl-params@ ( decl -- params n ) dup lf-idecl-params swap lf-idecl-arity @ ;
: lf-input-params ( i -- params n ) lf-input-decl lf-idecl-params@ ;

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
  dup lf-idecl-arity @ dup lf-param-capacity upto?
  if swap lf-idecl-params swap lf-params-ok? else 2drop false then ;
: lf-input-value-ok? ( value -- flag ) dup -1 = if drop true else lf-term-valid? then ;
: lf-input-roots-ok? ( decl -- flag )
  dup lf-idecl-type @ lf-term-valid? swap lf-idecl-value @ lf-input-value-ok? and ;
: lf-input-decl-ok? ( decl -- flag )
  dup lf-input-name-ok? over lf-input-kind-ok? and over lf-input-safety-ok? and
  over lf-input-hint-ok? and over lf-input-params-ok? and swap lf-input-roots-ok? and ;

\ Loading. lf-input-add copies a /lf-idecl record the importer filled and
\ gives its index: ok; invalid, adding nothing, after loading has ended or
\ for a record that fails the checks above; full when the store has no
\ room. lf-input-end marks every input store and ends loading: ok; or
\ invalid, still loading, when loading had already ended or a store is
\ invalid.
: lf-input-copy ( decl -- i outcome )
  lf-inputs store-new-slot 0= if drop -1 outcome-full exit then
  >r /lf-idecl move r> outcome-ok ;
: lf-input-add ( decl -- i outcome )
  lf-input-sealed? if drop -1 outcome-invalid exit then
  dup lf-input-decl-ok? if lf-input-copy else drop -1 outcome-invalid then ;
: lf-mark-ok? ( mark store -- flag ) store-mark ok? ;
: lf-input-seal ( -- )
  lf-name-used @ lf-input-bytes ! lf-input-print lf-input-state lf-inrec-fingerprint !
  true lf-input-state lf-inrec-sealed ! ;
: lf-input-end ( -- outcome )
  lf-input-sealed? if outcome-invalid exit then
  ['] lf-mark-ok? lf-input-all? if lf-input-seal outcome-ok else outcome-invalid then ;

\ After a check: every input store back to its mark and the name bytes
\ back to their count; ok, or invalid with nothing changed when the input
\ is not intact.
: lf-mark-back ( mark store -- flag ) store-rollback ok? ;
: lf-input-rollback ( -- outcome )
  lf-input-intact? 0= if outcome-invalid exit then
  ['] lf-mark-back lf-input-all? lf-input-bytes @ lf-name-used ! flag>outcome ;

\ Start loading a new input in this context: forget every declaration and
\ end the sealed state. Every environment made over the old input then
\ fails closed: its fingerprint covers the declarations' identities, which
\ never repeat.
: lf-input-reset ( -- ) lf-inputs store-clear lf-input-state /lf-inrec erase ;
