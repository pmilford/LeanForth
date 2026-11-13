\ Elaboration data (plan rows FE1d and FE1e1; ADR 0021 D10): the reader of
\ the file scripts/export-elab.sh writes with pinned Lean for a Lean
\ export -- classes with their out-parameters; instances with their class,
\ priority, synthesis order, discrimination-tree keys and rank in Lean's
\ instance tree, and the values of that tree the export lacks; default
\ instances with their rank; reducibility; the induction and cases
\ eliminators; the tags the elaborator and Meta's whnf read; matchers and
\ projection functions -- checked against the export's names and kept for
\ the elaborator (FE1e: instances; FE1g: eliminators; FE1d2: whnf). Format
\ version 2, one JSON object per line: docs/programming/ELABORATION_DATA.md
\ and schemas/elab-data-2.schema.json; a version 1 file is refused as
\ another format version. Untrusted and fail-closed: the data never
\ reaches the kernel, and nothing it holds can make a declaration
\ accepted; it can change what a statement means. What is checked here is
\ the file's form, its export's SHA-256, the names and kinds of the
\ declarations it names, that keys make one term, that ranks under each
\ root key are 0, 1, 2, ... and that matchers and projections fit their
\ declarations' types (below). The rest is pinned Lean's output taken on
\ trust, bound to the export only by that unkeyed hash: that an instance
\ belongs to the class its record names and has those keys (plan row
\ FE1e3 checks both against the instance's type), ranks, priorities,
\ synthesis orders, out-parameter positions, the default instances,
\ reducibility statuses, tags, matcher alternatives and which eliminator a
\ type has; every statement is printed back as the guard for it.
\ LeanForth-specific (Lean's attributes, the importer stage's names).
\ Requires: lib/bytes.fs, json.fs, sha256.fs, htab.fs, hash32.fs,
\ front/elab-keys.fs, and import/stage.fs (and through it
\ import/manifest.fs's JSON helpers and core/compact-exprs.fs).
\
\ elab-read ( c-addr u stage sha -- outcome ) reads the file c-addr u
\ against a stage that holds the library export, read and not yet sealed
\ (its names are looked up without adding any), and sha, the address of
\ that export's 32-byte SHA-256. The first line must be the header: this
\ format and version, the pinned Lean, the export's SHA-256 equal to sha,
\ the number of records of each kind and the SHA-256 of every later line
\ with its line feed. Every later line is one record of a known kind with
\ exactly its members; every name in it (a JSON array of string and
\ natural-number parts, root first) is the name of exactly one
\ declaration of the stage, of the right kind: a class an inductive type;
\ an instance, eliminator, tagged declaration or projection function not
\ one; a matcher a definition; a projection's constructor a constructor;
\ a reducibility's declaration, an eliminator's target types and a
\ constant key any declaration. An instance's or default instance's class
\ has a class record before it. A left-out instance's name, when it is
\ not_exported, is no declaration of the library, and a constant of its
\ keys that no declaration has is kept as a foreign key. No declaration
\ is named twice as one kind, no tag twice, no two eliminators of one
\ kind have the same target types, no two values under one root key the
\ same rank, no two default instances of a class the same rank. At the
\ end the records of each kind and the SHA-256 must equal the header's,
\ so a file cut off between two lines, or changed, is refused, and the
\ ranks under each root key must have no gap.
\
\ Outcomes (ADR 0008): ok; invalid for anything malformed, unknown,
\ duplicated, of the wrong kind or differing from the header or from the
\ export, an unreadable file, a sealed stage, or a call while a read is in
\ progress; unsupported for another format version or Lean version, a
\ number beyond 2^32 - 1 (no Lean library has one; plan row FE3 lifts it
\ if one appears) and a smart-unfolding record (format 2 has the kind;
\ plan row FE1d2 reads it); full when the heap has no room or a line
\ passes elab-line-limit bytes. A read that is not ok keeps nothing: every
\ table is empty afterwards, as after elab-reset.
\ elab-error ( -- line c-addr u ) gives the line of the failure (1 the
\ header; after the last line, the number of lines read; 0 before the
\ file is open) and why: elab-error-line, elab-error-code (stable, 1-38)
\ and elab-error-why apart. elab-unhashed ( outcome -- outcome ) refuses
\ for a caller that could not hash the export (error 26).
\
\ The data kept, numbered from 0 in file order, its declarations the
\ stage's declaration numbers: elab-count ( kind -- n );
\ elab-instance@ ( i -- d class priority ), elab-instance-order
\ ( i -- addr n ) (cells), elab-instance-keys ( i -- k n ) (keys of
\ front/elab-keys.fs), elab-instance-rank ( i -- rank ), elab-instance-of
\ ( d -- i true | false ); elab-left-out@ ( j -- priority rank reason ),
\ elab-left-out-keys ( j -- k n ); elab-default@ ( i -- class d priority ),
\ elab-default-rank ( i -- rank ); elab-class-of ( d -- k true | false ),
\ elab-class@ ( k -- d ), elab-class-out-params and elab-class-out-levels
\ ( k -- addr n ) (cells); elab-status ( d -- status ) (elab-semireducible
\ when no record names d); elab-tagged? ( d tag -- flag ); elab-eliminator@
\ ( i -- kind d ), elab-eliminator-types ( i -- addr n ) (cells),
\ elab-eliminator-for ( d kind -- i true | false ) (the eliminator whose
\ one target type is d); elab-matcher-of ( d -- m true | false ),
\ elab-matcher@ ( m -- d params discrs ), elab-matcher-elim
\ ( m -- pos true | false ), elab-matcher-alts ( m -- a n ), elab-alt@
\ ( a -- fields overlaps thunk? ); elab-projection-of ( d -- p true |
\ false ), elab-projection@ ( p -- ctor params idx ), elab-projection-decl
\ ( p -- d ), elab-projection-class? ( p -- flag ). elab-loaded? says
\ whether the last read was ok. Unchecked: the words that take a record
\ number read that record whatever it is; it must be below elab-count of
\ its kind (an alternative a below the sum of the matchers' alternatives).
\ The elab-* words are the interface; helpers, fields and tables are named
\ ed-*.
\
\ Example (the export read but not sealed, its manifest checked):
\   create lib /stage allot   12 lib stage-init drop
\   s" tests/author/init-slice.ndjson" lib stage-read drop
\   s" tests/front/init-slice.elab.ndjson" lib
\   lib stage-manifest manifest-digest elab-read .   \ 0, ok
\   elab-instance elab-count .                        \ 3
\
\ State: one context record, elab (the read in progress: its reader,
\ JSON view and SHA-256, the header's numbers and the key-reading mode;
\ the eliminators' and the ranks' hash tables and their probes), and
\ eleven context slabs: elab-facts (a record per declaration of the
\ stage), the instances, the numbers of synthesis orders and
\ out-parameters, the default instances, the eliminators and their target
\ types, the left-out instances, the classes, the matchers, their
\ alternatives and the projections; the keys are front/elab-keys.fs's.
\ One read at a time per context; the reader and the view hold heap memory
\ only during a read, the tables and the slabs until the context is freed.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json.fs
require ../lib/sha256.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ../import/stage.fs
require ./elab-keys.fs

\ Record kinds, numbered (the file orders them otherwise: class first).
0 constant elab-instance   1 constant elab-default
2 constant elab-reducibility   3 constant elab-eliminator   4 constant elab-left-out
5 constant elab-class   6 constant elab-tag   7 constant elab-matcher
8 constant elab-projection   9 constant elab-sunfold   10 constant elab-kinds
\ Reducibility statuses (Lean's ReducibilityStatus; 0 is the default).
0 constant elab-semireducible   1 constant elab-reducible   2 constant elab-irreducible
3 constant elab-implicit-reducible   4 constant elab-instance-reducible
\ Eliminator kinds: @[induction_eliminator] and @[cases_eliminator].
0 constant elab-induction   1 constant elab-cases
\ Tags: elab_as_elim, elab_without_expected_type, isAuxRecursor,
\ isNoConfusion, isCasesOnRecursor, isRecOnRecursor, isBRecOnRecursor.
0 constant elab-tag-as-elim   1 constant elab-tag-no-expected
2 constant elab-tag-aux-recursor   3 constant elab-tag-no-confusion
4 constant elab-tag-cases-on   5 constant elab-tag-rec-on   6 constant elab-tag-brec-on
\ Why a value of the instance tree is no instance record.
0 constant elab-erased   1 constant elab-not-exported
1048576 constant elab-line-limit   \ longest line, in bytes
8 constant elab-depth-limit        \ deepest JSON nesting of a line
65536 constant elab-token-limit    \ most JSON tokens in one line

\ ---- State.
\ A value of the instance tree: its keys k .. k+n-1 and its rank.
begin-structure /ed-value
  field: ed-value-keys   field: ed-value-keys#   field: ed-value-rank
end-structure
begin-structure /ed-inst
  /ed-value +field ed-inst-value
  field: ed-inst-decl   field: ed-inst-class   field: ed-inst-priority
  field: ed-inst-order   field: ed-inst-order#   \ its synthesis order in elab-orders
end-structure
begin-structure /ed-left
  /ed-value +field ed-left-value
  field: ed-left-priority   field: ed-left-reason
end-structure
begin-structure /ed-dflt
  field: ed-dflt-class   field: ed-dflt-decl
  field: ed-dflt-priority   field: ed-dflt-rank
end-structure
begin-structure /ed-elim
  field: ed-elim-kind   field: ed-elim-decl
  field: ed-elim-types   field: ed-elim-types#   \ its target types in elab-types
end-structure
begin-structure /ed-class
  field: ed-class-decl
  field: ed-class-params   field: ed-class-params#   \ its out-parameters in elab-orders
  field: ed-class-levels   field: ed-class-levels#   \ its out-level parameters
end-structure
begin-structure /ed-match
  field: ed-match-decl   field: ed-match-params   field: ed-match-discrs
  field: ed-match-elim                   \ the elimination universe's place, or -1
  field: ed-match-alts   field: ed-match-alts#     \ its alternatives in elab-alts
end-structure
begin-structure /ed-alt
  field: ed-alt-fields   field: ed-alt-overlaps   field: ed-alt-thunk
end-structure
begin-structure /ed-proj
  field: ed-proj-decl   field: ed-proj-ctor   field: ed-proj-params   field: ed-proj-idx
  field: ed-proj-class                             \ true: the structure is a class
end-structure
\ What the data says of one declaration of the stage.
begin-structure /ed-fact
  field: ed-fact-bits      \ bits 0-2 its status, 3 a default instance, 4-10 its tags
  field: ed-fact-inst      \ its instance's number + 1, or 0
  field: ed-fact-class     \ its class's number + 1, or 0
  field: ed-fact-matcher   \ its matcher's number + 1, or 0
  field: ed-fact-proj      \ its projection's number + 1, or 0
end-structure
\ An eliminator's key, kind and target types (cells), as the table
\ compares it; ed-key-one holds the type of a key made for one type.
begin-structure /ed-key
  field: ed-key-kind   field: ed-key-types   field: ed-key-types#   field: ed-key-one
end-structure
begin-structure /elab
  /reader +field elab-reader
  /json +field elab-json
  /sha256 +field elab-sha
  /htab +field elab-table            \ eliminators by kind and target types
  /ed-key +field elab-elim-key       \ the eliminator key looked up
  /ed-key +field elab-elim-probe     \ the hooks' key of an entry
  /htab +field elab-ranks            \ the instance tree's values by root key and rank
  /ed-value +field elab-ranked       \ the root key and rank looked up
  field: elab-stage                  \ during a read: the stage
  field: elab-export                 \ during a read: the export's SHA-256
  field: elab-reading                \ true during a read
  field: elab-loaded                 \ true: the last read was ok
  field: elab-foreign                \ true: keys being read may name foreign constants
  field: elab-code                   \ why it failed: an error code, or 0
  field: elab-at                     \ the line it failed at
  elab-kinds cells +field elab-counts     \ records read of each kind
  elab-kinds cells +field elab-expected   \ the header's numbers
  sha-digest-bytes chars +field elab-digest
  sha-digest-bytes 2* chars +field elab-hex       \ a SHA-256 as text
  sha-digest-bytes 2* chars +field elab-records   \ the header's records_sha256
end-structure
/elab context-record: elab
/ed-fact context-slab: elab-facts
/ed-inst context-slab: elab-insts
1 cells context-slab: elab-orders
/ed-dflt context-slab: elab-dflts
/ed-elim context-slab: elab-elims
1 cells context-slab: elab-types
/ed-left context-slab: elab-lefts
/ed-class context-slab: elab-classes
/ed-match context-slab: elab-matches
/ed-alt context-slab: elab-alts
/ed-proj context-slab: elab-projs

: ed-view ( -- view ) elab elab-json ;
: ed-stage ( -- stage ) elab elab-stage @ ;
: elab-count ( kind -- n ) cells elab elab-counts + @ ;
: elab-loaded? ( -- flag ) elab elab-loaded @ ;

\ Failing: an error code, stable (docs/programming/ELABORATION_DATA.md,
\ "Errors"; ed-messages holds each one's text, 0 none), at the current
\ line, with the outcome given.
1 constant ed-e-file   2 constant ed-e-line   3 constant ed-e-long
4 constant ed-e-json   5 constant ed-e-header   6 constant ed-e-format
7 constant ed-e-version   8 constant ed-e-lean   9 constant ed-e-export
10 constant ed-e-malformed   11 constant ed-e-kind   12 constant ed-e-unknown
13 constant ed-e-several   14 constant ed-e-wrong-kind   15 constant ed-e-instance
16 constant ed-e-default   17 constant ed-e-reducibility
18 constant ed-e-eliminator   19 constant ed-e-number   20 constant ed-e-count
21 constant ed-e-sha   22 constant ed-e-room   23 constant ed-e-lookup
24 constant ed-e-sealed   25 constant ed-e-busy   26 constant ed-e-hash
27 constant ed-e-no-class   28 constant ed-e-class   29 constant ed-e-tag
30 constant ed-e-term   31 constant ed-e-rank   32 constant ed-e-gap
33 constant ed-e-default-rank   34 constant ed-e-left-out   35 constant ed-e-matcher
36 constant ed-e-projection   37 constant ed-e-unfit   38 constant ed-e-later
create ed-messages
  s" none" counted,
  s" file missing or unreadable" counted,
  s" no line, or a line without its line feed" counted,
  s" a line longer than the limit" counted,
  s" not one JSON value within the limits" counted,
  s" no header" counted,
  s" not elaboration data" counted,
  s" another format version" counted,
  s" another Lean version" counted,
  s" elaboration data of another export" counted,
  s" malformed line" counted,
  s" unknown record kind" counted,
  s" unknown name" counted,
  s" a name several declarations have" counted,
  s" a declaration of the wrong kind" counted,
  s" an instance named twice" counted,
  s" a default instance named twice" counted,
  s" a reducibility named twice" counted,
  s" two eliminators for the same types" counted,
  s" a number beyond 2^32 - 1" counted,
  s" records differ in number from the header" counted,
  s" records differ from their SHA-256" counted,
  s" no room" counted,
  s" name lookup failed" counted,
  s" the library's stage is sealed: its names cannot be looked up" counted,
  s" a read in progress" counted,
  s" the library's export could not be hashed" counted,
  s" a class without its class record before it" counted,
  s" a class named twice" counted,
  s" a tag named twice" counted,
  s" keys that are not one term" counted,
  s" two values of one root key with one rank" counted,
  s" ranks of a root key with a gap" counted,
  s" two default instances of one class with one rank" counted,
  s" a left-out instance the library has" counted,
  s" a matcher named twice" counted,
  s" a projection named twice" counted,
  s" numbers that do not fit the declaration's type" counted,
  s" a record kind this reader does not read yet" counted,
  0 0 counted,
: ed-message ( code -- c-addr u ) ed-messages swap 0 ?do key-next loop count ;
: ed-line ( -- n ) elab elab-reader reader-position nip nip ;
: ed-fail ( code outcome -- outcome ) ed-line elab elab-at ! swap elab elab-code ! ;
: ed-bad ( code -- outcome ) outcome-invalid ed-fail ;
: ed-malformed ( -- outcome ) ed-e-malformed ed-bad ;
: ed-or-bad ( flag why -- outcome ) swap if drop outcome-ok else ed-bad then ;
: ed-or-other ( flag why -- outcome )
  swap if drop outcome-ok else outcome-unsupported ed-fail then ;
: ed-roomed ( outcome -- outcome ) dup ok? 0= if ed-e-room swap ed-fail then ;
: elab-error-line ( -- line ) elab elab-at @ ;
: elab-error-code ( -- code ) elab elab-code @ ;
: elab-error-why ( -- c-addr u ) elab-error-code ed-message ;
: elab-error ( -- line c-addr u ) elab-error-line elab-error-why ;

\ ---- Facts per declaration of the stage.
7 constant ed-facts-status   8 constant ed-facts-default   4 constant ed-tag-shift
: ed-fact ( d -- addr ) elab-facts slab-at ;
\ A fact field of d (xt gives the field's address), 0 for a d beyond them.
: ed-fact@ ( d xt -- x )
  over elab-facts slab-count u< if swap ed-fact swap execute @ else 2drop 0 then ;
: ed-fact! ( d i xt -- ) rot ed-fact swap execute swap 1+ swap ! ;
: ed-facts-made ( n -- outcome )
  dup elab-facts slab-claim ed-roomed ok-then? if ed-fact swap /ed-fact * erase outcome-ok
  else nip then ;
: ed-bits@ ( d -- x ) ['] ed-fact-bits ed-fact@ ;
: elab-status ( d -- status ) ed-bits@ ed-facts-status and ;
: elab-instance-of ( d -- i true | false ) ['] ed-fact-inst ed-fact@ +1>number ;
: elab-class-of ( d -- k true | false ) ['] ed-fact-class ed-fact@ +1>number ;
: elab-matcher-of ( d -- m true | false ) ['] ed-fact-matcher ed-fact@ +1>number ;
: elab-projection-of ( d -- p true | false ) ['] ed-fact-proj ed-fact@ +1>number ;
: ed-tag-bit ( tag -- mask ) ed-tag-shift + 1 swap lshift ;
: elab-tagged? ( d tag -- flag ) ed-tag-bit swap ed-bits@ and 0<> ;

\ ---- The records kept.
: ed-inst ( i -- addr ) elab-insts slab-at ;
: ed-left ( j -- addr ) elab-lefts slab-at ;
: ed-dflt ( i -- addr ) elab-dflts slab-at ;
: ed-elim ( i -- addr ) elab-elims slab-at ;
: ed-class ( k -- addr ) elab-classes slab-at ;
: ed-match ( m -- addr ) elab-matches slab-at ;
: ed-alt ( a -- addr ) elab-alts slab-at ;
: ed-proj ( p -- addr ) elab-projs slab-at ;
: ed-types ( first n -- addr n ) swap elab-types slab-at swap ;
\ A span: two fields, the first number and the count, of numbers in elab-orders.
: ed-span@ ( span -- addr n ) dup @ elab-orders slab-at swap cell+ @ ;
: ed-keys@ ( value -- k n ) dup ed-value-keys @ swap ed-value-keys# @ ;
: elab-instance@ ( i -- d class priority )
  ed-inst dup ed-inst-decl @ over ed-inst-class @ rot ed-inst-priority @ ;
: elab-instance-order ( i -- addr n ) ed-inst ed-inst-order ed-span@ ;
: elab-instance-keys ( i -- k n ) ed-inst ed-inst-value ed-keys@ ;
: elab-instance-rank ( i -- rank ) ed-inst ed-inst-value ed-value-rank @ ;
: elab-left-out@ ( j -- priority rank reason )
  ed-left dup ed-left-priority @ over ed-left-value ed-value-rank @ rot ed-left-reason @ ;
: elab-left-out-keys ( j -- k n ) ed-left ed-left-value ed-keys@ ;
: elab-default@ ( i -- class d priority )
  ed-dflt dup ed-dflt-class @ over ed-dflt-decl @ rot ed-dflt-priority @ ;
: elab-default-rank ( i -- rank ) ed-dflt ed-dflt-rank @ ;
: elab-class@ ( k -- d ) ed-class ed-class-decl @ ;
: elab-class-out-params ( k -- addr n ) ed-class ed-class-params ed-span@ ;
: elab-class-out-levels ( k -- addr n ) ed-class ed-class-levels ed-span@ ;
: elab-eliminator@ ( i -- kind d ) ed-elim dup ed-elim-kind @ swap ed-elim-decl @ ;
: elab-eliminator-types ( i -- addr n )
  ed-elim dup ed-elim-types @ swap ed-elim-types# @ ed-types ;
: elab-matcher@ ( m -- d params discrs )
  ed-match dup ed-match-decl @ over ed-match-params @ rot ed-match-discrs @ ;
: elab-matcher-elim ( m -- pos true | false ) ed-match ed-match-elim @ 1+ +1>number ;
: elab-matcher-alts ( m -- a n ) ed-match dup ed-match-alts @ swap ed-match-alts# @ ;
: elab-alt@ ( a -- fields overlaps thunk? )
  ed-alt dup ed-alt-fields @ over ed-alt-overlaps @ rot ed-alt-thunk @ ;
: elab-projection@ ( p -- ctor params idx )
  ed-proj dup ed-proj-ctor @ over ed-proj-params @ rot ed-proj-idx @ ;
: elab-projection-decl ( p -- d ) ed-proj ed-proj-decl @ ;
: elab-projection-class? ( p -- flag ) ed-proj ed-proj-class @ ;

\ ---- The eliminators' table (lib/htab.fs): entries are eliminator
\ numbers, keyed by kind and target types; the hooks make an entry's key
\ in elab-elim-probe, never in the key being looked up.
: ed-key! ( i key -- )
  >r dup elab-eliminator@ drop r@ ed-key-kind ! elab-eliminator-types r@ ed-key-types# !
  r> ed-key-types ! ;
: ed-key-cells ( key -- addr u ) dup ed-key-types @ swap ed-key-types# @ cells ;
: ed-key-hash ( key -- h )
  dup ed-key-kind @ hash-fmix swap ed-key-cells bounds ?do i @ hash-step 1 cells +loop ;
: ed-same-kind? ( key1 key2 -- flag ) ed-key-kind @ swap ed-key-kind @ = ;
: ed-same-key? ( key1 key2 -- flag )
  2dup ed-same-kind? >r ed-key-cells rot ed-key-cells compare 0= r> and ;
: ed-probe ( n -- key ) elab elab-elim-probe tuck ed-key! ;
: ed-rehash ( n htab -- h ) drop ed-probe ed-key-hash ;
: ed-same ( n key htab -- flag ) drop swap ed-probe ed-same-key? ;
create ed-hooks /htab-hooks allot  ' ed-rehash ' ed-same ed-hooks htab-hooks!
\ The ranks' table: entries are the instance tree's values, instance i as
\ 2i and left-out instance j as 2j + 1, keyed by root key and rank; a
\ key looked up is a value record (elab-ranked, or the value itself).
: ed-value ( e -- value )
  2 /mod swap if ed-left ed-left-value else ed-inst ed-inst-value then ;
: ed-root ( value -- k ) ed-value-keys @ ;
: ed-value-hash ( value -- h ) dup ed-root elab-key-hash swap ed-value-rank @ hash-step ;
: ed-same-value? ( value1 value2 -- flag )
  2dup ed-value-rank @ swap ed-value-rank @ = if ed-root swap ed-root elab-key= exit then
  2drop false ;
: ed-rank-rehash ( e htab -- h ) drop ed-value ed-value-hash ;
: ed-rank-same ( e value htab -- flag ) drop swap ed-value ed-same-value? ;
create ed-rank-hooks /htab-hooks allot
' ed-rank-rehash ' ed-rank-same ed-rank-hooks htab-hooks!
\ The tables are made by the first read, so that a context holds no heap
\ block for them until then, and emptied by every later one.
: ed-table ( -- htab ) elab elab-table ;
: ed-ranks ( -- htab ) elab elab-ranks ;
:noname ( -- ) ed-table htab-free ed-ranks htab-free ; context-teardown
: ed-table? ( -- flag ) ed-table htab-live? ;
: ed-htab-ready ( hooks htab -- outcome )
  dup htab-live? if nip htab-clear outcome-ok exit then 4 -rot htab-init ;
: ed-tables-ready ( -- outcome )
  ed-hooks ed-table ed-htab-ready dup ok? 0= if exit then
  drop ed-rank-hooks ed-ranks ed-htab-ready ;
: ed-key-find ( key -- n true | i false ) dup ed-key-hash ed-table htab-find ;
: ed-rank-find ( value -- e true | i false ) dup ed-value-hash ed-ranks htab-find ;
: elab-eliminator-for ( d kind -- i true | false )
  ed-table? 0= if 2drop false exit then
  elab elab-elim-key tuck ed-key-kind ! tuck ed-key-one !
  dup ed-key-one over ed-key-types !
  1 over ed-key-types# ! ed-key-find dup 0= if nip then ;

\ ---- Forgetting: every table empty, the counts zero, nothing loaded.
: ed-slabs-clear ( -- )
  elab-facts slab-clear elab-insts slab-clear elab-orders slab-clear
  elab-dflts slab-clear elab-elims slab-clear elab-types slab-clear elab-lefts slab-clear
  elab-classes slab-clear elab-matches slab-clear elab-alts slab-clear
  elab-projs slab-clear ;
: ed-tables-clear ( -- )
  ed-table? if ed-table htab-clear then
  ed-ranks dup htab-live? if htab-clear else drop then ;
: elab-reset ( -- )
  ed-slabs-clear elab-keys-clear ed-tables-clear false elab elab-loaded !
  elab elab-counts elab-kinds cells erase ;
\ A caller that could not compute the export's SHA-256 refuses the data
\ with error 26 at line 0, its outcome kept; nothing is loaded.
: elab-unhashed ( outcome -- outcome ) elab-reset ed-e-hash swap ed-fail ;

\ ---- Tables of keys: counted strings ending with an empty one
\ (import/manifest.fs's exact-keys? reads them). ed-key-index finds a
\ text's place in one.
: ed-key-index ( c-addr u table -- k true | false )
  -rot 2>r 0 swap begin dup count nip while
    dup count 2r@ compare 0= if drop 2r> 2drop true exit then key-next swap 1+ swap
  repeat 2drop 2r> 2drop false ;
create ed-kind-names
  s" instance" counted, s" default_instance" counted, s" reducibility" counted,
  s" eliminator" counted, s" instance_left_out" counted, s" class" counted,
  s" tag" counted, s" matcher" counted, s" projection" counted, s" sunfold" counted,
  0 0 counted,
create ed-status-names
  s" reducible" counted, s" irreducible" counted, s" implicit_reducible" counted,
  s" instance_reducible" counted, 0 0 counted,
create ed-elim-names  s" induction" counted, s" cases" counted, 0 0 counted,
create ed-tag-names
  s" elab_as_elim" counted, s" elab_without_expected_type" counted,
  s" aux_recursor" counted, s" no_confusion" counted, s" cases_on" counted,
  s" rec_on" counted, s" brec_on" counted, 0 0 counted,
create ed-reason-names  s" erased" counted, s" not_exported" counted, 0 0 counted,
: ed-kind-name ( kind -- c-addr ) ed-kind-names swap 0 ?do key-next loop ;

\ ---- Members of the object value: shape? holds when it has exactly the
\ table's keys; ed-member gives a key's value, -1 when absent.
: ed-member ( value key -- index ) swap ed-view json-find 0= if -1 then ;
: ed-shape? ( value table -- flag ) swap ed-view exact-keys? ;
: ed-text ( index -- c-addr u true | false ) ed-view string-value ;
: ed-text= ( index c-addr u -- flag ) rot ed-text if compare 0= else 2drop false then ;
: ed-array? ( index -- flag ) json-array ed-view json-items-of dup if nip then ;
: ed-null? ( index -- flag ) ed-view json-kind-at json-null = ;
\ A natural number of at most 32 bits; one or none (null, -1); a boolean.
: ed-u32 ( index -- u outcome )
  ed-view json-u 0= if 0 ed-malformed exit then
  dup u32-mask u> if ed-e-number outcome-unsupported ed-fail exit then
  outcome-ok ;
: ed-u32-or-none ( index -- u outcome )
  dup ed-null? if drop -1 outcome-ok exit then ed-u32 ;
: ed-bool ( index -- flag outcome )
  ed-view json-bool if outcome-ok else 0 ed-malformed then ;
\ One of the table's texts: its place.
: ed-choice ( index table -- k outcome )
  >r ed-text if r> ed-key-index if outcome-ok exit then else r> drop then 0 ed-malformed ;
\ xt ( item -- outcome ) on each element of an array in turn, while ok.
: ed-next ( item -- item' ) ed-view json-next ;
: ed-items ( end first xt -- outcome )
  >r begin 2dup > while
    dup r@ execute ok-then? 0= if nip r> drop exit then ed-next
  repeat 2drop r> drop outcome-ok ;
: ed-array-items ( index xt -- outcome )
  over ed-array? 0= if 2drop ed-malformed exit then
  swap ed-view json-contents rot ed-items ;

\ ---- Names: a JSON array of parts, root first, each a string or a
\ natural number, looked up in the stage's tier without adding anything
\ (-1: no such name; a part beyond 32 bits names none).
: ed-tier ( -- tier ) ed-stage stage-tier ;
: ed-looked ( n outcome -- n outcome )
  dup ok? 0= if ed-e-lookup swap ed-fail then ;
: ed-part-text ( prefix item -- n outcome )
  ed-view json-text@ ed-tier name-seek-str ed-looked ;
: ed-part-number ( prefix item -- n outcome )
  ed-view json-u 0= if drop -1 ed-malformed exit then
  dup u32-mask u> if 2drop -1 outcome-ok exit then ed-tier name-seek-num ed-looked ;
: ed-part ( prefix item -- n outcome )
  dup ed-view json-kind@ json-string = if ed-part-text exit then
  dup ed-view json-kind@ json-integer = if ed-part-number exit then
  2drop -1 ed-malformed ;
\ The parts from first to end in turn, each under the name before it.
: ed-parts ( end first -- n outcome )
  0 -rot begin 2dup > while
    rot over ed-part ok-then? 0= if nip nip -1 swap exit then
    dup 0< if nip nip outcome-ok exit then -rot ed-next
  repeat 2drop outcome-ok ;
: ed-name-array? ( index -- flag )
  json-array ed-view json-items-of if 0> else false then ;
: ed-name ( index -- n outcome )
  dup ed-name-array? 0= if drop -1 ed-malformed exit then ed-view json-contents ed-parts ;
\ A name's form alone, every part: a string or a natural number.
: ed-part-shape ( item -- outcome )
  dup ed-view json-kind@ json-string = if drop outcome-ok exit then
  ed-view json-natural if 2drop outcome-ok else ed-malformed then ;
: ed-name-shape ( index -- outcome )
  dup ed-name-array? if ['] ed-part-shape ed-array-items else drop ed-malformed then ;
\ The one declaration of tier name n.
: ed-decls ( n -- u true | false )
  dup 0< if drop false exit then ed-stage 2dup stage-by-name slab-count u<
  if resolution else 2drop false then ;
: ed-name-decl ( n -- d outcome )
  ed-decls 0= if 0 ed-e-unknown ed-bad exit then
  +1>number if outcome-ok else 0 ed-e-several ed-bad then ;
: ed-decl ( index -- d outcome ) ed-name dup ok? if drop ed-name-decl then ;
\ The same, of the kind wanted: an inductive type, or any but one; a
\ definition, a constructor.
: ed-type? ( d -- flag ) ed-stage staged-kind@ kind-type = ;
: ed-kind-bad ( d -- d outcome ) ed-e-wrong-kind ed-bad ;
: ed-a-type ( index -- d outcome )
  ed-decl dup ok? 0= if exit then drop dup ed-type? if outcome-ok else ed-kind-bad then ;
: ed-no-type ( index -- d outcome )
  ed-decl dup ok? 0= if exit then drop dup ed-type? if ed-kind-bad else outcome-ok then ;
: ed-of-kind ( d kind -- d outcome )
  over ed-stage staged-kind@ = if outcome-ok else ed-kind-bad then ;
: ed-a-def ( index -- d outcome ) ed-decl dup ok? if drop kind-def ed-of-kind then ;
: ed-a-ctor ( index -- d outcome ) ed-decl dup ok? if drop kind-ctor ed-of-kind then ;
\ A class: an inductive type with a class record read before.
: ed-a-class ( index -- d outcome )
  ed-a-type dup ok? 0= if exit then drop
  dup elab-class-of if drop outcome-ok else ed-e-no-class ed-bad then ;

\ ---- Fields. A record's fields are steps ( value i -- outcome ), run in
\ turn while ok; ed-put stores x in a field of record addr when ok.
: ed-step ( value i outcome xt -- value i outcome )
  over ok? 0= if drop exit then nip >r 2dup r> execute ;
: ed-steps ( value i table -- outcome )
  outcome-ok swap begin dup @ while dup cell+ >r @ ed-step r> repeat drop nip nip ;
: ed-put ( addr x outcome xt -- outcome )
  over ok? 0= if drop nip nip exit then nip rot swap execute ! outcome-ok ;
: ed-claim ( slab -- i outcome ) 1 swap slab-claim ed-roomed ;
: ed-push ( x slab -- outcome )
  tuck ed-claim ok-then? if rot slab-at ! outcome-ok else nip nip then ;
\ A span's first number and count, the units of slab claimed between.
: ed-span-open ( span slab -- ) slab-count swap ! ;
: ed-span-close ( span slab -- ) slab-count over @ - swap cell+ ! ;
\ An array of naturals of 32 bits into elab-orders, as the span at addr.
: ed-number-item ( item -- outcome ) ed-u32 ok-then? if elab-orders ed-push then ;
: ed-numbers ( span index -- outcome )
  over elab-orders ed-span-open ['] ed-number-item ed-array-items
  swap elab-orders ed-span-close ;

\ ---- Keys (front/elab-keys.fs): "star", "other", "arrow", or an object
\ of one of four forms. A constant no declaration has is, while
\ elab-foreign is set, a foreign key whose text is its name's parts,
\ each a byte s and a 32-bit length and the bytes, or n and the number.
create ed-word-names  s" star" counted, s" other" counted, s" arrow" counted, 0 0 counted,
create ed-word-tags  elab-key-star , elab-key-other , elab-key-arrow ,
: ed-key-word ( item -- outcome )
  ed-word-names ed-choice ok-then? if cells ed-word-tags + @ elab-key-new nip then ;
: ed-text-byte ( c -- outcome ) 1 elab-text-room ok-then? if c! outcome-ok else nip then ;
: ed-text-u32 ( u -- outcome )
  4 elab-text-room ok-then? if u32-le! outcome-ok else nip then ;
: ed-text-bytes ( c-addr u -- outcome )
  dup elab-text-room ok-then? if swap move outcome-ok else nip nip then ;
: ed-foreign-text ( item -- outcome )
  ed-view json-text@ [char] s ed-text-byte ok-then2? 0= if exit then
  dup ed-text-u32 ok-then2? if ed-text-bytes then ;
: ed-foreign-number ( item -- outcome )
  ed-u32 ok-then? 0= if exit then [char] n ed-text-byte ok-then? if ed-text-u32 then ;
: ed-foreign-part ( item -- outcome )
  dup ed-view json-kind@ json-string = if ed-foreign-text exit then ed-foreign-number ;
: ed-foreign-key ( index -- k outcome )
  elab-key-foreign elab-key-new ok-then? 0= if nip no-result exit then
  dup elab-key-text-start swap ['] ed-foreign-part ed-array-items
  ok-then? if dup elab-key-text-end outcome-ok else no-result then ;
: ed-foreign? ( n -- flag ) ed-decls if drop false else elab elab-foreign @ then ;
\ A key naming declaration d.
: ed-decl-key ( d tag -- k outcome )
  elab-key-new ok-then? if tuck elab-key-ref! outcome-ok else nip no-result then ;
: ed-const-key ( index -- k outcome )
  dup ed-name ok-then? 0= if nip no-result exit then
  dup ed-foreign? if drop ed-foreign-key exit then
  nip ed-name-decl ok-then? if elab-key-const ed-decl-key else no-result then ;
: ed-key-arity ( k value -- outcome )
  c" arity" ed-member ed-u32 ok-then? if swap elab-key-arity! outcome-ok else nip then ;
: ed-key-idx ( k value -- k outcome )
  c" idx" ed-member ed-u32 ok-then? if over elab-key-idx! outcome-ok then ;
: ed-key-const ( value -- outcome )
  dup c" const" ed-member ed-const-key ok-then? if swap ed-key-arity else nip then ;
: ed-proj-key ( value -- k outcome )
  c" proj" ed-member ed-a-type ok-then? if elab-key-proj ed-decl-key else no-result then ;
: ed-key-proj ( value -- outcome )
  dup ed-proj-key ok-then? 0= if nip exit then
  over ed-key-idx ok-then? if swap ed-key-arity else nip then ;
\ A texted key: its text kept first, then the key.
: ed-text-key ( c-addr u tag -- outcome )
  elab-key-new ok-then? 0= if nip nip exit then
  dup elab-key-text-start -rot ed-text-bytes
  ok-then? if elab-key-text-end outcome-ok then ;
: ed-digits ( index -- c-addr u outcome )
  ed-text if 2dup canonical-natural? if outcome-ok exit then 2drop then 0 0 ed-malformed ;
: ed-key-lit ( value -- outcome )
  c" lit" ed-member ed-digits ok-then2? if elab-key-lit ed-text-key then ;
: ed-key-str ( value -- outcome )
  c" lit_str" ed-member ed-text if elab-key-str ed-text-key else ed-malformed then ;
create ed-const-members  s" arity" counted, s" const" counted, 0 0 counted,
create ed-proj-key-members
  s" arity" counted, s" idx" counted, s" proj" counted, 0 0 counted,
create ed-lit-members  s" lit" counted, 0 0 counted,
create ed-str-members  s" lit_str" counted, 0 0 counted,
create ed-key-forms
  ed-const-members , ed-proj-key-members , ed-lit-members , ed-str-members ,
create ed-key-readers  ' ed-key-const , ' ed-key-proj , ' ed-key-lit , ' ed-key-str ,
4 constant ed-key-forms#
: ed-key-shape? ( value i -- flag ) cells ed-key-forms + @ ed-shape? ;
: ed-key-form ( value -- i true | false )
  ed-key-forms# 0 do dup i ed-key-shape? if drop i true unloop exit then loop drop false ;
: ed-key-object ( value -- outcome )
  dup ed-key-form if cells ed-key-readers + @ execute else drop ed-malformed then ;
: ed-key-item ( item -- outcome )
  dup ed-view json-kind@ json-string = if ed-key-word exit then ed-key-object ;
\ A value's keys: kept in order, one term.
: ed-one-term ( value -- outcome ) ed-keys@ elab-one-term? ed-e-term ed-or-bad ;
: ed-keys-read ( value index -- outcome )
  over elab-keys# swap ed-value-keys ! ['] ed-key-item ed-array-items
  ok-then? 0= if exit then dup elab-keys# over ed-value-keys @ - swap ed-value-keys# !
  ed-one-term ;
: ed-value-rank! ( value index -- outcome ) ed-u32 ['] ed-value-rank ed-put ;
\ A value into the ranks' table, unless one of its root key and rank is there.
: ed-place ( e -- outcome )
  ed-ranks htab-ready ed-roomed dup ok? 0= if nip exit then drop
  dup ed-value ed-rank-find
  if 2drop ed-e-rank ed-bad else ed-ranks htab-put outcome-ok then ;

\ ---- Instances: name, class, priority, synthesis order, keys, rank.
create ed-inst-keys
  s" class" counted, s" keys" counted, s" name" counted, s" priority" counted,
  s" rank" counted, s" synth_order" counted, 0 0 counted,
: ed-inst-fact ( d i -- outcome )
  over elab-instance-of if 2drop drop ed-e-instance ed-bad exit then
  ['] ed-fact-inst ed-fact! outcome-ok ;
: ed-inst-named ( i d -- i d outcome ) 2dup swap ed-inst-fact ;
: ed-inst-decl! ( value i -- outcome )
  swap c" name" ed-member ed-no-type dup ok? if drop ed-inst-named then
  rot ed-inst -rot ['] ed-inst-decl ed-put ;
: ed-inst-class! ( value i -- outcome )
  ed-inst swap c" class" ed-member ed-a-class ['] ed-inst-class ed-put ;
: ed-inst-priority! ( value i -- outcome )
  ed-inst swap c" priority" ed-member ed-u32 ['] ed-inst-priority ed-put ;
: ed-inst-order! ( value i -- outcome )
  ed-inst ed-inst-order swap c" synth_order" ed-member ed-numbers ;
: ed-inst-path! ( value i -- outcome )
  ed-inst ed-inst-value swap c" keys" ed-member ed-keys-read ;
: ed-inst-rank! ( value i -- outcome )
  ed-inst ed-inst-value swap c" rank" ed-member ed-value-rank! ;
: ed-inst-place ( value i -- outcome ) nip 2* ed-place ;
create ed-inst-steps
  ' ed-inst-decl! , ' ed-inst-class! , ' ed-inst-priority! , ' ed-inst-order! ,
  ' ed-inst-path! , ' ed-inst-rank! , ' ed-inst-place , 0 ,
: ed-on-instance ( value -- outcome )
  dup ed-inst-keys ed-shape? 0= if drop ed-malformed exit then
  elab-insts ed-claim ok-then? if ed-inst-steps ed-steps else nip then ;

\ ---- Instances left out: why, name, priority, keys (foreign constants
\ allowed), rank.
create ed-left-members
  s" keys" counted, s" name" counted, s" priority" counted, s" rank" counted,
  s" reason" counted, 0 0 counted,
: ed-has? ( n -- flag ) ed-decls dup if nip then ;
: ed-left-has? ( reason n -- flag ) ed-has? swap elab-not-exported = and ;
: ed-left-name ( reason index -- outcome )
  dup ed-name-shape dup ok? 0= if nip nip exit then drop
  ed-name ok-then? if ed-left-has? 0= ed-e-left-out ed-or-bad else nip then ;
: ed-left-reason! ( value j -- outcome )
  ed-left swap c" reason" ed-member ed-reason-names ed-choice ['] ed-left-reason ed-put ;
: ed-left-name! ( value j -- outcome )
  ed-left ed-left-reason @ swap c" name" ed-member ed-left-name ;
: ed-left-priority! ( value j -- outcome )
  ed-left swap c" priority" ed-member ed-u32 ['] ed-left-priority ed-put ;
: ed-left-path! ( value j -- outcome )
  true elab elab-foreign ! ed-left ed-left-value swap c" keys" ed-member ed-keys-read
  false elab elab-foreign ! ;
: ed-left-rank! ( value j -- outcome )
  ed-left ed-left-value swap c" rank" ed-member ed-value-rank! ;
: ed-left-place ( value j -- outcome ) nip 2* 1+ ed-place ;
create ed-left-steps
  ' ed-left-reason! , ' ed-left-name! , ' ed-left-priority! , ' ed-left-path! ,
  ' ed-left-rank! , ' ed-left-place , 0 ,
: ed-on-left-out ( value -- outcome )
  dup ed-left-members ed-shape? 0= if drop ed-malformed exit then
  elab-lefts ed-claim ok-then? if ed-left-steps ed-steps else nip then ;

\ ---- Default instances: class, name, priority, rank (one per class).
create ed-dflt-keys
  s" class" counted, s" name" counted, s" priority" counted, s" rank" counted,
  0 0 counted,
: ed-dflt-fact ( d -- d outcome )
  dup ed-fact ed-fact-bits dup @ ed-facts-default and
  if drop ed-e-default ed-bad exit then
  dup @ ed-facts-default or swap ! outcome-ok ;
: ed-dflt-decl! ( value i -- outcome )
  ed-dflt swap c" name" ed-member ed-no-type dup ok? if drop ed-dflt-fact then
  ['] ed-dflt-decl ed-put ;
: ed-dflt-class! ( value i -- outcome )
  ed-dflt swap c" class" ed-member ed-a-class ['] ed-dflt-class ed-put ;
: ed-dflt-priority! ( value i -- outcome )
  ed-dflt swap c" priority" ed-member ed-u32 ['] ed-dflt-priority ed-put ;
: ed-dflt-rank! ( value i -- outcome )
  ed-dflt swap c" rank" ed-member ed-u32 ['] ed-dflt-rank ed-put ;
\ Default instances are few (34 in Init): each is compared with those before.
: ed-dflt-key ( i -- class rank ) ed-dflt dup ed-dflt-class @ swap ed-dflt-rank @ ;
: ed-dflt-same? ( i j -- flag ) ed-dflt-key rot ed-dflt-key d= ;
: ed-dflt-new? ( i -- flag )
  dup 0 ?do dup i ed-dflt-same? if drop unloop false exit then loop drop true ;
: ed-dflt-once ( value i -- outcome ) nip ed-dflt-new? ed-e-default-rank ed-or-bad ;
create ed-dflt-steps
  ' ed-dflt-decl! , ' ed-dflt-class! , ' ed-dflt-priority! , ' ed-dflt-rank! ,
  ' ed-dflt-once , 0 ,
: ed-on-default ( value -- outcome )
  dup ed-dflt-keys ed-shape? 0= if drop ed-malformed exit then
  elab-dflts ed-claim ok-then? if ed-dflt-steps ed-steps else nip then ;

\ ---- Reducibility: name, status; no declaration twice.
create ed-red-keys  s" name" counted, s" status" counted, 0 0 counted,
: ed-status-fact ( d status -- outcome )
  over elab-status if 2drop ed-e-reducibility ed-bad exit then
  swap ed-fact ed-fact-bits +! outcome-ok ;
: ed-on-reducibility ( value -- outcome )
  dup ed-red-keys ed-shape? 0= if drop ed-malformed exit then
  dup c" name" ed-member ed-decl ok-then? 0= if nip exit then
  swap c" status" ed-member ed-status-names ed-choice
  ok-then? if 1+ ed-status-fact else nip then ;

\ ---- Eliminators: kind, name, target types; one per kind and types.
create ed-elim-keys  s" kind" counted, s" name" counted, s" types" counted, 0 0 counted,
: ed-elim-kind! ( value i -- outcome )
  ed-elim swap c" kind" ed-member ed-elim-names ed-choice ['] ed-elim-kind ed-put ;
: ed-elim-decl! ( value i -- outcome )
  ed-elim swap c" name" ed-member ed-no-type ['] ed-elim-decl ed-put ;
: ed-type-item ( item -- outcome ) ed-decl ok-then? if elab-types ed-push then ;
: ed-types-span ( addr -- )
  elab-types slab-count over ed-elim-types @ - swap ed-elim-types# ! ;
: ed-elim-types! ( value i -- outcome )
  ed-elim elab-types slab-count over ed-elim-types ! swap c" types" ed-member
  ['] ed-type-item ed-array-items swap ed-types-span ;
create ed-elim-steps  ' ed-elim-kind! , ' ed-elim-decl! , ' ed-elim-types! , 0 ,
\ Eliminator i into the table, unless one of its key is there.
: ed-twice ( i n -- outcome ) 2drop ed-e-eliminator ed-bad ;
: ed-elim-insert ( i -- outcome )
  ed-table htab-ready ed-roomed dup ok? 0= if nip exit then drop
  dup elab elab-elim-key tuck ed-key! ed-key-find
  if ed-twice else ed-table htab-put outcome-ok then ;
: ed-on-eliminator ( value -- outcome )
  dup ed-elim-keys ed-shape? 0= if drop ed-malformed exit then
  elab-elims ed-claim ok-then? 0= if nip exit then tuck ed-elim-steps ed-steps
  ok-then? if ed-elim-insert then ;

\ ---- Classes: name (an inductive type, once), out-parameters.
create ed-class-members
  s" name" counted, s" out_level_params" counted, s" out_params" counted, 0 0 counted,
: ed-class-fact ( d k -- outcome )
  over elab-class-of if 2drop drop ed-e-class ed-bad exit then
  ['] ed-fact-class ed-fact! outcome-ok ;
: ed-class-named ( k d -- k d outcome ) 2dup swap ed-class-fact ;
: ed-class-decl! ( value k -- outcome )
  swap c" name" ed-member ed-a-type dup ok? if drop ed-class-named then
  rot ed-class -rot ['] ed-class-decl ed-put ;
: ed-class-params! ( value k -- outcome )
  ed-class ed-class-params swap c" out_params" ed-member ed-numbers ;
: ed-class-levels! ( value k -- outcome )
  ed-class ed-class-levels swap c" out_level_params" ed-member ed-numbers ;
create ed-class-steps  ' ed-class-decl! , ' ed-class-params! , ' ed-class-levels! , 0 ,
: ed-on-class ( value -- outcome )
  dup ed-class-members ed-shape? 0= if drop ed-malformed exit then
  elab-classes ed-claim ok-then? if ed-class-steps ed-steps else nip then ;

\ ---- Tags: name (not an inductive type), tag; no tag of a declaration twice.
create ed-tag-members  s" name" counted, s" tag" counted, 0 0 counted,
: ed-tag-fact ( d tag -- outcome )
  2dup elab-tagged? if 2drop ed-e-tag ed-bad exit then
  ed-tag-bit swap ed-fact ed-fact-bits +! outcome-ok ;
: ed-on-tag ( value -- outcome )
  dup ed-tag-members ed-shape? 0= if drop ed-malformed exit then
  dup c" name" ed-member ed-no-type ok-then? 0= if nip exit then
  swap c" tag" ed-member ed-tag-names ed-choice ok-then? if ed-tag-fact else nip then ;

\ ---- Types, as far as the checks below read them: the leading Pi
\ binders of a declaration's type, written out (no unfolding), and its
\ universe parameters.
: ed-pi? ( e -- flag ) ed-tier expr-tag@ tag-pi dup 4 + within ;
: ed-pis ( e -- n )
  0 swap begin dup ed-pi? while ed-tier expr-b@ swap 1+ swap repeat drop ;
: ed-type-pis ( d -- n ) ed-stage staged-type@ ed-pis ;
: ed-levels ( d -- n ) ed-stage staged-params@ ed-stage stage-tuples tuple-length ;

\ ---- Matchers: name (a definition, once), parameters, discriminants,
\ elimination universe, alternatives, the discriminants' names (read for
\ their form, not kept). It fits when its type has a Pi binder for each
\ parameter, the motive, each discriminant and each alternative, and the
\ elimination universe is one of its universe parameters.
create ed-match-members
  s" alt_infos" counted, s" discr_names" counted, s" name" counted,
  s" num_discrs" counted, s" num_params" counted, s" u_elim_pos" counted, 0 0 counted,
create ed-alt-members
  s" has_unit_thunk" counted, s" num_fields" counted, s" num_overlaps" counted,
  0 0 counted,
: ed-match-fact ( d m -- outcome )
  over elab-matcher-of if 2drop drop ed-e-matcher ed-bad exit then
  ['] ed-fact-matcher ed-fact! outcome-ok ;
: ed-match-named ( m d -- m d outcome ) 2dup swap ed-match-fact ;
: ed-match-decl! ( value m -- outcome )
  swap c" name" ed-member ed-a-def dup ok? if drop ed-match-named then
  rot ed-match -rot ['] ed-match-decl ed-put ;
: ed-match-params! ( value m -- outcome )
  ed-match swap c" num_params" ed-member ed-u32 ['] ed-match-params ed-put ;
: ed-match-discrs! ( value m -- outcome )
  ed-match swap c" num_discrs" ed-member ed-u32 ['] ed-match-discrs ed-put ;
: ed-match-elim! ( value m -- outcome )
  ed-match swap c" u_elim_pos" ed-member ed-u32-or-none ['] ed-match-elim ed-put ;
: ed-alt-fields! ( value a -- outcome )
  ed-alt swap c" num_fields" ed-member ed-u32 ['] ed-alt-fields ed-put ;
: ed-alt-overlaps! ( value a -- outcome )
  ed-alt swap c" num_overlaps" ed-member ed-u32 ['] ed-alt-overlaps ed-put ;
: ed-alt-thunk! ( value a -- outcome )
  ed-alt swap c" has_unit_thunk" ed-member ed-bool ['] ed-alt-thunk ed-put ;
create ed-alt-steps  ' ed-alt-fields! , ' ed-alt-overlaps! , ' ed-alt-thunk! , 0 ,
: ed-alt-item ( item -- outcome )
  dup ed-alt-members ed-shape? 0= if drop ed-malformed exit then
  elab-alts ed-claim ok-then? if ed-alt-steps ed-steps else nip then ;
: ed-match-alts! ( value m -- outcome )
  ed-match ed-match-alts dup elab-alts ed-span-open swap c" alt_infos" ed-member
  ['] ed-alt-item ed-array-items swap elab-alts ed-span-close ;
\ The discriminants' names: as many as discriminants, each a name or null.
: ed-discr-item ( item -- outcome )
  dup ed-null? if drop outcome-ok exit then ed-name-shape ;
: ed-discrs? ( n index -- flag )
  json-array ed-view json-items-of if = else drop false then ;
: ed-discr-names ( value -- index ) c" discr_names" ed-member ;
: ed-match-names! ( value m -- outcome )
  ed-match ed-match-discrs @ over ed-discr-names ed-discrs?
  0= if drop ed-malformed exit then
  ed-discr-names ['] ed-discr-item ed-array-items ;
: ed-match-arity ( m -- n )
  ed-match dup ed-match-params @ over ed-match-discrs @ + 1+ swap ed-match-alts# @ + ;
: ed-elim-fits? ( m -- flag )
  dup elab-matcher-elim if swap elab-matcher@ 2drop ed-levels < else drop true then ;
: ed-match-fits? ( m -- flag )
  dup ed-match-arity over elab-matcher@ 2drop ed-type-pis > 0= swap ed-elim-fits? and ;
: ed-match-fit ( value m -- outcome ) nip ed-match-fits? ed-e-unfit ed-or-bad ;
create ed-match-steps
  ' ed-match-decl! , ' ed-match-params! , ' ed-match-discrs! , ' ed-match-elim! ,
  ' ed-match-alts! , ' ed-match-names! , ' ed-match-fit , 0 ,
: ed-on-matcher ( value -- outcome )
  dup ed-match-members ed-shape? 0= if drop ed-malformed exit then
  elab-matches ed-claim ok-then? if ed-match-steps ed-steps else nip then ;

\ ---- Projection functions: name (not an inductive type, once), the
\ constructor, the structure's parameters, the field, whether a class.
\ It fits when the function takes the parameters and the structure and
\ the constructor has the field.
create ed-proj-members
  s" ctor" counted, s" from_class" counted, s" idx" counted, s" name" counted,
  s" num_params" counted, 0 0 counted,
: ed-proj-fact ( d p -- outcome )
  over elab-projection-of if 2drop drop ed-e-projection ed-bad exit then
  ['] ed-fact-proj ed-fact! outcome-ok ;
: ed-proj-named ( p d -- p d outcome ) 2dup swap ed-proj-fact ;
: ed-proj-decl! ( value p -- outcome )
  swap c" name" ed-member ed-no-type dup ok? if drop ed-proj-named then
  rot ed-proj -rot ['] ed-proj-decl ed-put ;
: ed-proj-ctor! ( value p -- outcome )
  ed-proj swap c" ctor" ed-member ed-a-ctor ['] ed-proj-ctor ed-put ;
: ed-proj-params! ( value p -- outcome )
  ed-proj swap c" num_params" ed-member ed-u32 ['] ed-proj-params ed-put ;
: ed-proj-idx! ( value p -- outcome )
  ed-proj swap c" idx" ed-member ed-u32 ['] ed-proj-idx ed-put ;
: ed-proj-class! ( value p -- outcome )
  ed-proj swap c" from_class" ed-member ed-bool ['] ed-proj-class ed-put ;
: ed-proj-takes? ( p -- flag )
  ed-proj dup ed-proj-params @ swap ed-proj-decl @ ed-type-pis < ;
: ed-proj-field? ( p -- flag )
  ed-proj dup ed-proj-params @ over ed-proj-idx @ + swap ed-proj-ctor @ ed-type-pis < ;
: ed-proj-fit ( value p -- outcome )
  nip dup ed-proj-takes? swap ed-proj-field? and ed-e-unfit ed-or-bad ;
create ed-proj-steps
  ' ed-proj-decl! , ' ed-proj-ctor! , ' ed-proj-params! , ' ed-proj-idx! ,
  ' ed-proj-class! , ' ed-proj-fit , 0 ,
: ed-on-projection ( value -- outcome )
  dup ed-proj-members ed-shape? 0= if drop ed-malformed exit then
  elab-projs ed-claim ok-then? if ed-proj-steps ed-steps else nip then ;

\ ---- Smart-unfolding bodies (_sunfold, plan row FE1d2): the kind is in
\ format 2, so that data with them needs no new version, but this reader
\ does not read them yet: unsupported.
: ed-on-sunfold ( value -- outcome ) drop ed-e-later outcome-unsupported ed-fail ;

\ ---- Lines. Each is one JSON object with one member: the header's key
\ elab_data, or a record kind, whose value is an object.
create ed-kind-handlers
  ' ed-on-instance , ' ed-on-default , ' ed-on-reducibility , ' ed-on-eliminator ,
  ' ed-on-left-out , ' ed-on-class , ' ed-on-tag , ' ed-on-matcher , ' ed-on-projection ,
  ' ed-on-sunfold ,
: ed-one-member? ( -- flag ) 0 json-object ed-view json-items-of if 1 = else false then ;
: ed-object-value? ( -- flag ) 2 ed-view json-kind-at json-object = ;
: ed-wrapped? ( -- flag ) ed-one-member? if ed-object-value? else false then ;
: ed-tally ( kind -- ) cells elab elab-counts + 1 swap +! ;
: ed-dispatch ( value kind -- outcome ) dup ed-tally cells ed-kind-handlers + @ execute ;
: ed-on-record ( -- outcome )
  ed-wrapped? 0= if ed-malformed exit then
  1 ed-view json-text@ ed-kind-names ed-key-index
  0= if ed-e-kind ed-bad exit then
  2 swap ed-dispatch ;

\ ---- The header: its format and version first, so that another version
\ is told as such, then its shape, Lean, the export and the numbers.
create ed-head-keys
  s" export_sha256" counted, s" format" counted, s" format_version" counted,
  s" lean_githash" counted, s" lean_version" counted, s" modules" counted,
  s" records" counted, s" records_sha256" counted, 0 0 counted,
: ed-head-format ( value i -- outcome )
  drop c" format" ed-member s" leanforth-elab-data" ed-text=
  ed-e-format ed-or-bad ;
: ed-head-version ( value i -- outcome )
  drop c" format_version" ed-member ed-view natural-at if s" 2" compare 0= else false then
  ed-e-version ed-or-other ;
: ed-head-shape ( value i -- outcome )
  drop ed-head-keys ed-shape? ed-e-malformed ed-or-bad ;
: ed-head-lean ( value i -- outcome )
  drop dup c" lean_version" ed-member pinned-lean-version ed-text=
  swap c" lean_githash" ed-member pinned-lean-githash ed-text= and
  ed-e-lean ed-or-other ;
: ed-export-hex ( -- c-addr u )
  elab elab-export @ elab elab-hex sha256-hex elab elab-hex sha-digest-bytes 2* ;
: ed-head-export ( value i -- outcome )
  drop c" export_sha256" ed-member ed-export-hex ed-text=
  ed-e-export ed-or-bad ;
: ed-expected ( kind -- addr ) cells elab elab-expected + ;
: ed-expect ( object kind -- outcome )
  tuck ed-kind-name ed-member ed-view json-u if swap ed-expected ! outcome-ok
  else drop ed-malformed then ;
: ed-head-records ( value i -- outcome )
  drop c" records" ed-member dup ed-kind-names ed-shape? 0= if drop ed-malformed exit then
  elab-kinds 0 do dup i ed-expect dup ok? 0= if nip unloop exit then drop loop
  drop outcome-ok ;
: ed-head-hash ( value i -- outcome )
  drop c" records_sha256" ed-member ed-text 0= if ed-malformed exit then
  2dup sha-digest-bytes 2* hex-text? 0= if 2drop ed-malformed exit then
  elab elab-records swap move outcome-ok ;
: ed-module-item ( item -- outcome )
  ed-view json-kind@ json-string = if outcome-ok else ed-malformed then ;
: ed-head-modules ( value i -- outcome )
  drop c" modules" ed-member ['] ed-module-item ed-array-items ;
create ed-head-steps
  ' ed-head-format , ' ed-head-version , ' ed-head-shape , ' ed-head-lean ,
  ' ed-head-export , ' ed-head-records , ' ed-head-hash , ' ed-head-modules , 0 ,
: ed-head-key? ( -- flag ) 1 ed-view json-text@ s" elab_data" compare 0= ;
: ed-on-header ( -- outcome )
  ed-wrapped? if ed-head-key? else false then 0= if ed-e-header ed-bad exit then
  2 0 ed-head-steps ed-steps ;

\ ---- The file, line by line; each record line hashed before it is
\ parsed (parsing decodes its strings in place). A line that cannot be
\ read is the one after the last line read.
: ed-line-why ( outcome -- why )
  outcome-full = if ed-e-long exit then
  ed-e-line ;
: ed-unread ( outcome -- outcome ) dup ed-line-why swap ed-fail 1 elab elab-at +! ;
: ed-next-line ( -- c-addr u outcome )
  elab elab-reader reader-line dup ok? 0= if ed-unread then ;
: ed-parse ( c-addr u -- outcome )
  ed-view json-parse dup ok? 0= if ed-e-json swap ed-fail
  then ;
: ed-header ( -- outcome )
  ed-next-line ok-then2? if ed-parse dup ok? if drop ed-on-header then then ;
: ed-record-line ( c-addr u -- outcome )
  2dup elab elab-sha sha256-line ed-parse dup ok? if drop ed-on-record then ;
: ed-more? ( -- flag ) elab elab-reader reader-more? ;
: ed-records ( -- outcome )
  begin ed-more? while
    ed-next-line ok-then2? 0= if exit then ed-record-line dup ok? 0= if exit then drop
  repeat outcome-ok ;
\ At the end: the records of each kind and their SHA-256, as the header
\ says; then the ranks under each root key without a gap (each value of
\ rank r > 0 has one of rank r - 1 beside it).
: ed-counts-same? ( -- flag )
  elab elab-counts elab-kinds cells elab elab-expected over compare 0= ;
: ed-hash-same? ( -- flag )
  elab elab-digest elab elab-sha sha256-final elab elab-digest elab elab-hex sha256-hex
  elab elab-hex sha-digest-bytes 2* elab elab-records over compare 0= ;
: ed-rank-probe ( k rank -- value )
  elab elab-ranked tuck ed-value-rank ! tuck ed-value-keys ! ;
: ed-gapless? ( e -- flag )
  ed-value dup ed-value-rank @ ?dup 0= if drop true exit then
  1- swap ed-root swap ed-rank-probe ed-rank-find nip ;
: ed-values-gapless? ( n odd -- flag )
  swap 0 ?do i 2* over + ed-gapless? 0= if drop unloop false exit then loop drop true ;
: ed-kind-gapless? ( kind odd -- flag ) swap elab-count swap ed-values-gapless? ;
: ed-ranks-whole ( -- outcome )
  elab-instance 0 ed-kind-gapless? elab-left-out 1 ed-kind-gapless? and
  ed-e-gap ed-or-bad ;
: ed-ends ( -- outcome )
  ed-counts-same? 0= if ed-e-count ed-bad exit then
  ed-hash-same? 0= if ed-e-sha ed-bad exit then ed-ranks-whole ;
: ed-open ( c-addr u -- outcome )
  elab elab-reader reader-open
  dup ok? 0= if ed-e-file swap ed-fail then ;
: ed-steps-all ( c-addr u -- outcome )
  ed-open dup ok? if drop ed-header then dup ok? if drop ed-records then
  dup ok? if drop ed-ends then ;

\ ---- The read: started with every table empty, its reader and view
\ freed on every path (a THROW passes on after that), and everything
\ forgotten when it is not ok.
: ed-views ( -- outcome )
  4096 elab-line-limit elab elab-reader reader-init dup ok? 0= if exit then drop
  elab-depth-limit ed-view json-init
  dup ok? if elab-token-limit ed-view json-token-limit ! then ;
: ed-sealed ( stage -- outcome )
  drop ed-e-sealed ed-bad ;
\ After an ok outcome, xt ( -- outcome ); no room is told as such.
: ed-then ( outcome xt -- outcome ) over ok? if nip execute ed-roomed else drop then ;
: ed-start ( stage sha -- outcome )
  elab-reset 0 elab elab-code ! 0 elab elab-at ! false elab elab-foreign !
  elab elab-export ! dup elab elab-stage !
  elab elab-sha sha256-init dup stage-sealed? if ed-sealed exit then
  stage-decls ed-facts-made ['] ed-tables-ready ed-then ['] ed-views ed-then ;
: ed-close ( outcome -- outcome )
  elab elab-reader dup reader-close drop reader-free ed-view json-free
  false elab elab-reading ! dup ok? dup elab elab-loaded ! 0= if elab-reset then ;
: ed-caught ( c-addr u -- outcome code )
  ['] ed-steps-all catch dup if nip nip outcome-invalid swap then ;
: ed-busy ( c-addr u stage sha -- outcome ) 2drop 2drop ed-e-busy ed-bad ;
: elab-read ( c-addr u stage sha -- outcome )
  elab elab-reading @ if ed-busy exit then
  ed-start ok-then2? if true elab elab-reading ! ed-caught else 0 then
  >r ed-close r> throw ;

base !   \ the BASE this file was loaded with
