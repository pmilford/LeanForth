\ Elaboration data (plan rows FE1d and FE1e1; ADR 0021 D10): the reader of
\ the file scripts/export-elab.sh writes with pinned Lean for a Lean
\ export -- classes with their out-parameters; instances with their class,
\ priority, synthesis order, discrimination-tree keys and rank in Lean's
\ instance tree, and the values of that tree the export lacks; default
\ instances with their rank; reducibility; the induction and cases
\ eliminators; the tags the elaborator and Meta's whnf read; matchers and
\ projection functions; the smart-unfolding bodies (f._sunfold) -- checked
\ against the export's names and kept for the elaborator (FE1e: instances;
\ FE1g: eliminators; FE1d2 and plan S2: whnf). Format version 3, 3.1
\ (MATHLIB_FRONT.md O1: format 3 and inert nodes, metadata LeanForth does
\ not carry, whose body is then not usable) or 3.2 (plan FE1c-bk: also
\ Lean's own binder kinds of a declaration whose export gives others,
\ elab-binder-kinds-of ( d -- b true | false ), elab-binder-kinds ( b --
\ addr n ), elab-binder-domain ( b k -- addr n ), elab-binder-decl ( b --
\ d ); their numbers checked against the export's type), one JSON object per line:
\ docs/programming/ELABORATION_DATA.md and schemas/elab-data-3.schema.json;
\ a version 1 or 2 file is refused as another format version (a format-2
\ file says "sunfold":0 for a library whose definitions have bodies), an
\ inert node in a format-3 file as malformed. Untrusted and fail-closed:
\ the data never reaches the kernel, and nothing it holds can make a declaration
\ accepted; it can change what a statement means. What is checked here is
\ the file's form, its export's SHA-256, the names and kinds of the
\ declarations it names, that keys make one term, that ranks under each
\ root key are 0, 1, 2, ..., that matchers and projections fit their
\ declarations' types and that a smart-unfolding body is a closed term of
\ its definition's universe parameters (below). The rest is pinned Lean's
\ output taken on
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
\ with its line feed, which must be the one elab-bind! named, if any
\ (error 39: the export's manifest names other data). Every later line
\ is one record of a known kind with
\ exactly its members; every name in it (a JSON array of string and
\ natural-number parts, root first) is the name of exactly one
\ declaration of the stage, of the right kind: a class an inductive type;
\ an instance, eliminator, tagged declaration or projection function not
\ one; a matcher a definition; a projection's constructor a constructor;
\ a reducibility's declaration, an eliminator's target types and a
\ constant key any declaration; a smart-unfolding body's definition a
\ definition, its constants any declaration or none (the record is then
\ foreign: kept, and unsupported where it would be used), a projection's
\ structure an inductive type or none. An instance's or default instance's class
\ has a class record before it. A left-out instance's name, when it is
\ not_exported, is no declaration of the library, and a constant of its
\ keys that no declaration has is kept as a foreign key. No declaration
\ is named twice as one kind (a default instance may be, of one class at
\ two ranks, as Lean keeps it), no tag twice, no two eliminators of one
\ kind have the same target types, no two values under one root key the
\ same rank, no two default instances of a class the same rank. At the
\ end the records of each kind and the SHA-256 must equal the header's,
\ so a file cut off between two lines, or changed, is refused, and the
\ ranks under each root key must have no gap.
\
\ Outcomes (ADR 0008): ok; invalid for anything malformed, unknown,
\ duplicated, of the wrong kind or differing from the header or from the
\ export, a default instance's rank beyond elab-default-rank-most
\ (65,535: error 40), a smart-unfolding body given twice, with an entry
\ that names a later one, a loose bound variable at its root or universe
\ parameters other than its definition's (errors 41-44), an unreadable
\ file, a sealed stage, or a call while a read is in progress;
\ unsupported for another format version or Lean version, a number
\ beyond 2^32 - 1 (no Lean library has one; plan row FE3 lifts it if one
\ appears) and an annotation other than Lean's three or an inert node's
\ key other than its three (error 45); full
\ when the heap has no room or a line
\ passes elab-line-limit bytes. A read that is not ok keeps nothing: every
\ table is empty afterwards, as after elab-reset.
\ elab-error ( -- line c-addr u ) gives the line of the failure (1 the
\ header; after the last line, the number of lines read; 0 before the
\ file is open) and why: elab-error-line, elab-error-code (stable, 1-45)
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
\ ( p -- d ), elab-projection-class? ( p -- flag ); elab-sunfold-of
\ ( d -- s true | false ), elab-sunfold-decl ( s -- d ),
\ elab-sunfold-value ( s -- n ) (its root node), elab-sunfold-rec-arg
\ ( s -- k true | false ), elab-sunfold-foreign? ( s -- flag ) (a node
\ names a constant the library lacks), elab-sunfold-inert? ( s -- flag )
\ (it holds an inert node), elab-sunfold-usable? ( s -- flag ) (neither:
\ front/lib-decode.fs decodes no other); its nodes, numbered across
\ records: elab-node-kind ( n -- kind ) (elab-node-bvar .. -have, below)
\ and elab-node-a, -b, -c, -d ( n -- x ) as the table below says,
\ elab-node-levels ( n -- addr k ) a constant's levels (cells); its
\ levels: elab-level-kind ( l -- kind ), elab-level-a, -b ( l -- x ).
\ elab-loaded? says
\ whether the last read was ok; elab-generation ( -- n ) changes with
\ every read and every reset, so a user that keeps results about the
\ data (front/instances.fs) can tell they are of another read;
\ elab-read-against? ( stage -- flag )
\ whether it was, against that stage; elab-decl-of ( name -- d true |
\ false ) a name's declaration in that stage, elab-decl-name ( d -- name )
\ the name of one. Unchecked: the words that take a
\ record number read that record whatever it is; it must be below
\ elab-count of its kind (an alternative a below the sum of the matchers'
\ alternatives). The elab-* words are the interface; helpers, fields and
\ tables are named ed-*.
\
\ Format 4 (the number 4; plan FE9, slice SD-a of docs/design/TACTIC_SIMP.md
\ and SIMP_DATA.md section 3): format 3.2's kinds (inert nodes and binder
\ kinds allowed), the tag defeq (elab-tag-defeq: a theorem Lean holds to
\ be proved by rfl; its declaration must be a theorem, error 14; in an
\ older format it is malformed) and the kinds other files add, every kind
\ counted in the header. A file adds a kind while the modules load:
\ elab-add-kind ( form clear c-addr u -- kind ), the kind's key c-addr u
\ (the record's), its records read by elab-on-form with form, its clear
\ ( -- ) run by every reset; it aborts after context-new, on a key another
\ kind has, and with no room. The kinds number
\ from elab-kinds on, at most elab-kinds-most in all, and are read in
\ format 4 alone (else error 11). A reader reads its record's members with
\ the words elab-member .. elab-type-pis below, the elab- faces of this
\ file's own (front/simp-data.fs reads the congr kind with them: errors 47
\ and 48 are its). elab-format4? ( -- flag ): the data read is of format
\ 4 or 4.1; elab-tag-count ( tag -- n ): its declarations with that tag.
\ Format 4.1 (the text "4.1"; slice SD-b): format 4 and the kinds added by
\ elab-add-kind41 ( form clear c-addr u -- kind ), each after every kind
\ format 4 reads (else it aborts), read in a format-4.1 file alone (in
\ format 4 unknown, error 11, and not counted in its header);
\ elab-format41? ( -- flag ): the data read is of format 4.1.
\
\ Example (the export read but not sealed, its manifest checked):
\   create lib /stage allot   12 lib stage-init drop
\   s" tests/author/init-slice.ndjson" lib stage-read drop
\   s" tests/front/init-slice.elab.ndjson" lib
\   lib stage-manifest manifest-digest elab-read .   \ 0, ok
\   elab-instance elab-count .                        \ 3
\
\ State: one context record, elab (the read in progress: its reader,
\ JSON view and SHA-256, the header's numbers, the key-reading mode and
\ the kind of the record being read; the eliminators' and the ranks' hash
\ tables and their probes), and fourteen context slabs: elab-facts (a
\ record per declaration of the stage), the instances, the numbers of
\ synthesis orders, out-parameters, universe parameters and a constant
\ node's levels, the default instances, the eliminators and their target
\ types, the left-out instances, the classes, the matchers, their
\ alternatives, the projections, the smart-unfolding bodies, their nodes
\ and their levels; the keys are front/elab-keys.fs's (a node's literal,
\ string and binder name among them, for their texts).
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
require ../lib/find.fs
require ../lib/name-table.fs
require ../lib/text-run.fs
require ../lib/decimal.fs
require ../import/stage.fs
require ./elab-keys.fs

\ Record kinds, numbered (the file orders them otherwise: class first).
0 constant elab-instance   1 constant elab-default
2 constant elab-reducibility   3 constant elab-eliminator   4 constant elab-left-out
5 constant elab-class   6 constant elab-tag   7 constant elab-matcher
8 constant elab-projection   9 constant elab-sunfold   10 constant elab-binders
11 constant elab-kinds
\ Reducibility statuses (Lean's ReducibilityStatus; 0 is the default).
0 constant elab-semireducible   1 constant elab-reducible   2 constant elab-irreducible
3 constant elab-implicit-reducible   4 constant elab-instance-reducible
\ Eliminator kinds: @[induction_eliminator] and @[cases_eliminator].
0 constant elab-induction   1 constant elab-cases
\ Tags: elab_as_elim, elab_without_expected_type, isAuxRecursor,
\ isNoConfusion, isCasesOnRecursor, isRecOnRecursor, isBRecOnRecursor,
\ match_pattern.
0 constant elab-tag-as-elim   1 constant elab-tag-no-expected
2 constant elab-tag-aux-recursor   3 constant elab-tag-no-confusion
4 constant elab-tag-cases-on   5 constant elab-tag-rec-on   6 constant elab-tag-brec-on
7 constant elab-tag-match-pattern   \ Lean's @[match_pattern] (hasMatchPatternAttribute)
8 constant elab-tag-defeq           \ Lean's @[defeq] (defeqAttr; format 4)
16 constant elab-kinds-most         \ kinds with those other files add
\ Why a value of the instance tree is no instance record.
0 constant elab-erased   1 constant elab-not-exported
\ A smart-unfolding body's nodes (Lean's Expr; fields a, b, c, d) and levels.
\   bvar: a its index         sort: a its level      app: a the function, b the argument
\   lam, forall: a the name (a key), b the type, c the body, d the binder info
\   let, have: a the name, b the type, c the value, d the body (have: non_dep)
\   lit, str: a a key of its digits or bytes     const: a its declaration (-1 when
\   the library has none), its levels by elab-node-levels
\   proj: a the structure (-1: none), b the field, c the term
\   mdata: a the annotation (elab-sunfold-match, -match-alt, elab-borrowed, or
\   elab-inert: format 3.1's inert node, its body unusable), c the term
0 constant elab-node-bvar   1 constant elab-node-sort   2 constant elab-node-app
3 constant elab-node-lam   4 constant elab-node-forall   5 constant elab-node-let
6 constant elab-node-lit   7 constant elab-node-str   8 constant elab-node-proj
9 constant elab-node-mdata   10 constant elab-node-const   11 constant elab-node-have
0 constant elab-sunfold-match   1 constant elab-sunfold-match-alt
2 constant elab-borrowed   3 constant elab-inert
\ Levels: zero; succ (a); max, imax (a, b); param (a its place among the
\ definition's universe parameters).
0 constant elab-level-zero   1 constant elab-level-succ   2 constant elab-level-max
3 constant elab-level-imax   4 constant elab-level-param
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
begin-structure /ed-sun
  field: ed-sun-decl
  field: ed-sun-params   field: ed-sun-params#     \ its universe parameters' names
  field: ed-sun-levels   field: ed-sun-levels#     \ its levels in elab-levels
  field: ed-sun-nodes    field: ed-sun-nodes#      \ its nodes in elab-nodes
  field: ed-sun-value                              \ the root, a node number
  field: ed-sun-rec                                \ the recursion argument, or -1
  field: ed-sun-foreign                            \ true: a name the library lacks
  field: ed-sun-inert                              \ true: an inert node (format 3.1)
end-structure
\ A node, or a level (kind, a and b alone).
begin-structure /ed-node
  field: ed-node-kind   field: ed-node-a   field: ed-node-b   field: ed-node-c
  field: ed-node-d
  field: ed-node-loose     \ 1 + its largest loose bound variable, or 0
end-structure
\ What the data says of one declaration of the stage.
begin-structure /ed-fact
  field: ed-fact-bits      \ bits 0-2 its status, 4-12 its tags
  field: ed-fact-inst      \ its instance's number + 1, or 0
  field: ed-fact-class     \ its class's number + 1, or 0
  field: ed-fact-matcher   \ its matcher's number + 1, or 0
  field: ed-fact-proj      \ its projection's number + 1, or 0
  field: ed-fact-sun       \ its smart-unfolding body's number + 1, or 0
  field: ed-fact-bk        \ its binder kinds' number + 1, or 0
end-structure
\ Lean's binder kinds of a declaration (format 3.2): its type's leading Pi
\ binders' kinds, a span of elab-orders, and each one's domain's, spans
\ in elab-bk-doms from ed-bk-doms on.
begin-structure /ed-bk
  field: ed-bk-decl   2 cells +field ed-bk-kinds   field: ed-bk-doms
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
  field: elab-kind                   \ the kind of the record being read
  field: elab-code                   \ why it failed: an error code, or 0
  field: elab-gen                    \ resets so far (each read starts with one)
  field: elab-at                     \ the line it failed at
  elab-kinds-most cells +field elab-counts     \ records read of each kind
  elab-kinds-most cells +field elab-expected   \ the header's numbers
  sha-digest-bytes chars +field elab-digest
  sha-digest-bytes 2* chars +field elab-hex       \ a SHA-256 as text
  sha-digest-bytes 2* chars +field elab-records   \ the header's records_sha256
  sha-digest-bytes 2* chars +field elab-bound     \ the records_sha256 elab-bind! named
  field: elab-bound-length           \ its length: 0 when none is named
  field: elab-modules#               \ the header's modules: how many
  field: elab-inits#                 \ and how many are Init
  field: elab-v31                    \ true: the header says format 3.1 or 3.2
  field: elab-v32                    \ true: it says 3.2 (binder kinds) or 4
  field: elab-v4                     \ true: it says 4 (the kinds other files add)
  field: elab-v41                    \ true: it says 4.1 (also elab-add-kind41's)
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
/ed-sun context-slab: elab-suns
/ed-node context-slab: elab-nodes
/ed-node context-slab: elab-levels
/ed-bk context-slab: elab-bks
2 cells context-slab: elab-bk-doms

\ Kinds other files add (format 4), written only while the modules load
\ (ed-added-open; elab-add-kind below) and read in place afterwards, as
\ runs and workers do: a table of their names (lib/name-table.fs), each
\ entry's data an /ed-kind, then how many there are and their entries in
\ the order added; kind elab-kinds + i is entry i.
begin-structure /ed-kind
  field: ed-kind-number  \ elab-kinds + its place
  field: ed-kind-form    \ the record's form, read by ed-on-form
  field: ed-kind-clear   \ ( -- ), run by every reset
  field: ed-kind-v41     \ true: read in format 4.1 alone (elab-add-kind41)
end-structure
elab-kinds-most elab-kinds - constant ed-added-most
begin-structure /ed-added
  2 cells +field ed-added-names   \ the table of names
  field: ed-added-n
  ed-added-most cells +field ed-added-entries
end-structure
create ed-added  /ed-added allot  ed-added /ed-added erase
: ed-added-open ( -- ) context-sealed? abort" elab-data: a kind added after context-new" ;
: ed-added# ( -- n ) ed-added ed-added-n @ ;
: ed-added-room ( -- )
  ed-added# ed-added-most < 0= abort" elab-add-kind: no room for another kind" ;
: ed-names ( -- table ) ed-added ed-added-names ;
: ed-added-slot ( i -- a-addr ) cell ed-added ed-added-entries record-at ;
: ed-added-push ( entry -- kind )
  ed-added# ed-added-slot !  1 ed-added ed-added-n +!  ed-added# 1- elab-kinds + ;
: ed-kind-data ( kind -- a-addr ) elab-kinds - ed-added-slot @ name-entry-data ;
: ed-clear-entry ( entry -- ) name-entry-data ed-kind-clear @ execute ;
: ed-added-clears ( -- ) ed-names ['] ed-clear-entry name-table-each ;
: ed-v4? ( -- flag ) elab elab-v4 @ ;
: ed-v41? ( -- flag ) elab elab-v41 @ ;
\ The added kinds format 4 reads: those before the first of format 4.1.
: ed-v41-kind? ( x i -- x flag ) elab-kinds + ed-kind-data ed-kind-v41 @ ;
: ed-added-v4# ( -- n )
  0 ed-added# ['] ed-v41-kind? find-index 0= if ed-added# then ;
\ The added kinds the file's format reads: all of them in 4.1, else
\ those of format 4 (the difference added under 4.1's flag).
: ed-added-read# ( -- n ) ed-added-v4# ed-added# over - ed-v41? and + ;

: ed-view ( -- view ) elab elab-json ;
: ed-stage ( -- stage ) elab elab-stage @ ;
: elab-count ( kind -- n ) cells elab elab-counts + @ ;
: elab-loaded? ( -- flag ) elab elab-loaded @ ;
: elab-read-against? ( stage -- flag ) elab elab-stage @ = elab-loaded? and ;
\ The declaration of a name (of the stage tier's names, which a fed
\ context's input shares) in the stage the data was read against.
: elab-decl-of ( name -- d true | false ) ed-stage stage-find ;
: elab-decl-name ( d -- name ) ed-stage staged-name@ ;

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
36 constant ed-e-projection   37 constant ed-e-unfit
39 constant ed-e-bound   40 constant ed-e-dflt-most   41 constant ed-e-sunfold
42 constant ed-e-order   43 constant ed-e-loose   44 constant ed-e-params
45 constant ed-e-annotation   46 constant ed-e-binders
47 constant elab-e-congr-twice   48 constant elab-e-congr-order   \ front/simp-data.fs's
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
  s" a default instance of two classes" counted,
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
  s" other records than the export's manifest names" counted,
  s" a default instance's rank beyond 65535" counted,
  s" a smart-unfolding body named twice" counted,
  s" an index to no earlier entry" counted,
  s" a loose bound variable" counted,
  s" universe parameters other than the definition's" counted,
  s" an annotation this reader does not know" counted,
  s" binder kinds named twice" counted,
  s" a congruence lemma named twice" counted,
  s" congruence lemmas out of their function's order" counted,
  0 0 counted,
: ed-message ( code -- c-addr u ) ed-messages swap counted-nth count ;
: ed-line ( -- n ) elab elab-reader reader-line# ;
: ed-fail ( code outcome -- outcome ) ed-line elab elab-at ! swap elab elab-code ! ;
: ed-bad ( code -- outcome ) outcome-invalid ed-fail ;
: ed-malformed ( -- outcome ) ed-e-malformed ed-bad ;
: ed-or-bad ( flag why -- outcome ) swap if drop outcome-ok else ed-bad then ;
: ed-or-other ( flag why -- outcome )
  swap if drop outcome-ok else outcome-unsupported ed-fail then ;
\ A failed outcome recorded with its code, an ok one passed on.
: ed-failed ( outcome code -- outcome ) over ok? if drop else swap ed-fail then ;
: ed-roomed ( outcome -- outcome ) ed-e-room ed-failed ;
: elab-error-line ( -- line ) elab elab-at @ ;
: elab-error-code ( -- code ) elab elab-code @ ;
: elab-error-why ( -- c-addr u ) elab-error-code ed-message ;
: elab-error ( -- line c-addr u ) elab-error-line elab-error-why ;

\ ---- Facts per declaration of the stage.
7 constant ed-facts-status   4 constant ed-tag-shift
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
: elab-sunfold-of ( d -- s true | false ) ['] ed-fact-sun ed-fact@ +1>number ;
: elab-binder-kinds-of ( d -- b true | false ) ['] ed-fact-bk ed-fact@ +1>number ;
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
: ed-keys@ ( value -- k n ) ed-value-keys cell-pair@ ;
: elab-instance@ ( i -- d class priority )
  ed-inst ed-inst-decl cell-triple@ ;
: elab-instance-order ( i -- addr n ) ed-inst ed-inst-order ed-span@ ;
: elab-instance-keys ( i -- k n ) ed-inst ed-inst-value ed-keys@ ;
: elab-instance-rank ( i -- rank ) ed-inst ed-inst-value ed-value-rank @ ;
: elab-left-out@ ( j -- priority rank reason )
  ed-left dup ed-left-priority @ over ed-left-value ed-value-rank @ rot ed-left-reason @ ;
: elab-left-out-keys ( j -- k n ) ed-left ed-left-value ed-keys@ ;
: elab-default@ ( i -- class d priority )
  ed-dflt ed-dflt-class cell-triple@ ;
: elab-default-rank ( i -- rank ) ed-dflt ed-dflt-rank @ ;
: elab-class@ ( k -- d ) ed-class ed-class-decl @ ;
: elab-class-out-params ( k -- addr n ) ed-class ed-class-params ed-span@ ;
: elab-class-out-levels ( k -- addr n ) ed-class ed-class-levels ed-span@ ;
: elab-eliminator@ ( i -- kind d ) ed-elim ed-elim-kind cell-pair@ ;
: elab-eliminator-types ( i -- addr n )
  ed-elim dup ed-elim-types @ swap ed-elim-types# @ ed-types ;
: elab-matcher@ ( m -- d params discrs )
  ed-match ed-match-decl cell-triple@ ;
: elab-matcher-elim ( m -- pos true | false ) ed-match ed-match-elim @ 1+ +1>number ;
: elab-matcher-alts ( m -- a n ) ed-match ed-match-alts cell-pair@ ;
: elab-alt@ ( a -- fields overlaps thunk? )
  ed-alt ed-alt-fields cell-triple@ ;
: elab-projection@ ( p -- ctor params idx )
  ed-proj ed-proj-ctor cell-triple@ ;
: elab-projection-decl ( p -- d ) ed-proj ed-proj-decl @ ;
: elab-projection-class? ( p -- flag ) ed-proj ed-proj-class @ ;
: ed-sun ( s -- addr ) elab-suns slab-at ;
: ed-node ( n -- addr ) elab-nodes slab-at ;
: ed-level ( l -- addr ) elab-levels slab-at ;
: elab-sunfold-decl ( s -- d ) ed-sun ed-sun-decl @ ;
: elab-sunfold-value ( s -- n ) ed-sun ed-sun-value @ ;
: elab-sunfold-rec-arg ( s -- k true | false ) ed-sun ed-sun-rec @ 1+ +1>number ;
: elab-sunfold-foreign? ( s -- flag ) ed-sun ed-sun-foreign @ ;
: elab-sunfold-inert? ( s -- flag ) ed-sun ed-sun-inert @ ;
: elab-sunfold-usable? ( s -- flag )
  dup elab-sunfold-foreign? swap elab-sunfold-inert? or 0= ;
: elab-node-kind ( n -- kind ) ed-node ed-node-kind @ ;
: elab-node-a ( n -- x ) ed-node ed-node-a @ ;
: elab-node-b ( n -- x ) ed-node ed-node-b @ ;
: elab-node-c ( n -- x ) ed-node ed-node-c @ ;
: elab-node-d ( n -- x ) ed-node ed-node-d @ ;
: elab-node-levels ( n -- addr k ) ed-node ed-node-b ed-span@ ;
: elab-level-kind ( l -- kind ) ed-level ed-node-kind @ ;
: elab-level-a ( l -- x ) ed-level ed-node-a @ ;
: elab-level-b ( l -- x ) ed-level ed-node-b @ ;
: ed-bk ( b -- addr ) elab-bks slab-at ;
: elab-binder-decl ( b -- d ) ed-bk ed-bk-decl @ ;
: elab-binder-kinds ( b -- addr n ) ed-bk ed-bk-kinds ed-span@ ;
\ The kinds of binder k's domain's leading binders; none for k beyond them.
: ed-bk-dom ( b k -- span ) swap ed-bk ed-bk-doms @ + elab-bk-doms slab-at ;
: elab-binder-domain ( b k -- addr n )
  over elab-binder-kinds nip over u> if ed-bk-dom ed-span@ else 2drop 0 0 then ;

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
: ed-bodies-clear ( -- )
  elab-suns slab-clear elab-nodes slab-clear elab-levels slab-clear ;
: ed-slabs-clear ( -- )
  elab-facts slab-clear elab-insts slab-clear elab-orders slab-clear
  elab-dflts slab-clear elab-elims slab-clear elab-types slab-clear elab-lefts slab-clear
  elab-classes slab-clear elab-matches slab-clear elab-alts slab-clear
  elab-projs slab-clear ed-bodies-clear elab-bks slab-clear elab-bk-doms slab-clear ;
: ed-tables-clear ( -- )
  ed-table? if ed-table htab-clear then
  ed-ranks dup htab-live? if htab-clear else drop then ;
: ed-head-clear ( -- )
  elab elab-counts elab-kinds-most cells erase
  elab elab-expected elab-kinds-most cells erase
  0 elab elab-modules# ! 0 elab elab-inits# ! false elab elab-v41 !
  false elab elab-v31 ! false elab elab-v32 ! false elab elab-v4 ! ed-added-clears ;
: elab-reset ( -- )
  ed-slabs-clear elab-keys-clear ed-tables-clear false elab elab-loaded !
  ed-head-clear 1 elab elab-gen +! ;
: elab-generation ( -- n ) elab elab-gen @ ;
\ A caller that could not compute the export's SHA-256 refuses the data
\ with error 26 at line 0, its outcome kept; nothing is loaded.
: elab-unhashed ( outcome -- outcome ) elab-reset ed-e-hash swap ed-fail ;

\ ---- Tables of keys: counted strings ending with an empty one
\ (import/manifest.fs's exact-keys? reads them). ed-key-index finds a
\ text's place in one.
: ed-key-index ( c-addr u table -- k true | false )
  -rot 2>r 0 swap begin dup count nip while
    dup count 2r@ compare 0= if drop 2r> 2drop true exit then counted-next swap 1+ swap
  repeat 2drop 2r> 2drop false ;
create ed-kind-names
  s" instance" counted, s" default_instance" counted, s" reducibility" counted,
  s" eliminator" counted, s" instance_left_out" counted, s" class" counted,
  s" tag" counted, s" matcher" counted, s" projection" counted, s" sunfold" counted,
  s" binder_kinds" counted, 0 0 counted,
create ed-status-names
  s" reducible" counted, s" irreducible" counted, s" implicit_reducible" counted,
  s" instance_reducible" counted, 0 0 counted,
create ed-elim-names  s" induction" counted, s" cases" counted, 0 0 counted,
create ed-tag-names
  s" elab_as_elim" counted, s" elab_without_expected_type" counted,
  s" aux_recursor" counted, s" no_confusion" counted, s" cases_on" counted,
  s" rec_on" counted, s" brec_on" counted, s" match_pattern" counted, s" defeq" counted,
  0 0 counted,
create ed-reason-names  s" erased" counted, s" not_exported" counted, 0 0 counted,
\ An added kind's key, the counted name of its entry (name-entry-name
\ is that name's COUNT).
: ed-added-key ( i -- c-addr ) ed-added-slot @ name-entry-name drop 1- ;
: ed-added-name ( kind -- c-addr ) elab-kinds - ed-added-key ;
: ed-kind-name ( kind -- c-addr )
  dup elab-kinds u< if ed-kind-names swap counted-nth else ed-added-name then ;
\ An added kind by its key.
: ed-added-index ( c-addr u -- kind true | false )
  ed-names name-table-find dup if name-entry-data ed-kind-number @ true then ;
: ed-kind-index ( c-addr u -- kind true | false )
  2dup ed-kind-names ed-key-index if nip nip true else ed-added-index then ;
\ A load-time word: a kind whose key ( c-addr u ) no other kind has, read
\ by form, cleared by clear; aborts after context-new or with no room.
: ed-kind-new ( c-addr u -- c-addr u )
  2dup ed-kind-index dup if nip then abort" elab-add-kind: a kind spelt twice" ;
: ed-entry, ( form clear c-addr u -- c-addr u )
  2dup ed-names name-entry  ed-added# elab-kinds + ,  2swap swap , ,  false , ;
\ The entry just laid down, found by its key, takes the next place.
: ed-added-file ( c-addr u -- kind ) ed-names name-table-find ed-added-push ;
: ed-add ( form clear c-addr u -- kind )
  ed-added-open ed-added-room ed-kind-new ed-entry, ed-added-file ;
: elab-add-kind ( form clear c-addr u -- kind )
  ed-added-v4# ed-added# <> abort" elab-add-kind: format 4 after a 4.1 kind" ed-add ;
: elab-add-kind41 ( form clear c-addr u -- kind )
  ed-add true over ed-kind-data ed-kind-v41 ! ;
\ The kinds of formats 3 and 3.1, which have no binder_kinds: the table's
\ entries before it, copied when loaded.
: ed-table-copy, ( addr u -- ) here swap dup allot move ;
create ed-v3-kinds
  ed-kind-names elab-binders ed-kind-name over - ed-table-copy, 0 0 counted,

\ ---- Members of the object value: shape? holds when it has exactly the
\ table's keys; ed-member gives a key's value, -1 when absent.
: ed-member ( value key -- index ) swap ed-view json-find 0= if -1 then ;
: ed-shape? ( value table -- flag ) swap ed-view exact-keys? ;
: ed-text ( index -- c-addr u true | false ) ed-view json-string-of ;
: ed-text= ( index c-addr u -- flag ) rot ed-text if compare 0= else 2drop false then ;
: ed-array? ( index -- flag ) json-array ed-view json-items-of dup if nip then ;
: ed-null? ( index -- flag ) ed-view json-null json-kind-at? ;
: ed-string? ( index -- flag ) ed-view json-string-at? ;
\ A natural number of at most 32 bits; one or none (null, -1); a boolean.
: ed-u32 ( index -- u outcome )
  ed-view json-u 0= if 0 ed-malformed exit then
  dup u32-mask u> if ed-e-number outcome-unsupported ed-fail exit then
  outcome-ok ;
: ed-u32-or-none ( index -- u outcome )
  dup ed-null? if drop -1 outcome-ok exit then ed-u32 ;
: ed-bool ( index -- flag outcome )
  ed-view json-bool if outcome-ok else 0 ed-malformed then ;
\ One of the table's texts: its place (ed-choice: else malformed).
: ed-text-index ( index table -- k true | false )
  >r ed-text r> swap if ed-key-index else drop false then ;
: ed-choice ( index table -- k outcome )
  ed-text-index if outcome-ok else 0 ed-malformed then ;
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
: ed-looked ( n outcome -- n outcome ) ed-e-lookup ed-failed ;
: ed-part-text ( prefix item -- n outcome )
  ed-view json-text@ ed-tier name-seek-str ed-looked ;
: ed-part-number ( prefix item -- n outcome )
  ed-view json-u 0= if drop -1 ed-malformed exit then
  dup u32-mask u> if 2drop -1 outcome-ok exit then ed-tier name-seek-num ed-looked ;
: ed-part ( prefix item -- n outcome )
  dup ed-string? if ed-part-text exit then
  dup ed-view json-integer json-kind-at? if ed-part-number exit then
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
  dup ed-string? if drop outcome-ok exit then
  ed-view json-natural if 2drop outcome-ok else ed-malformed then ;
: ed-name-shape ( index -- outcome )
  dup ed-name-array? if ['] ed-part-shape ed-array-items else drop ed-malformed then ;
\ The one declaration of tier name n.
: ed-decls ( n -- u true | false )
  dup 0< if drop false exit then ed-stage 2dup stage-by-name slab-count u<
  if resolution else 2drop false then ;
: ed-one-decl ( u -- d outcome ) +1>number if outcome-ok else 0 ed-e-several ed-bad then ;
: ed-name-decl ( n -- d outcome )
  ed-decls if ed-one-decl else 0 ed-e-unknown ed-bad then ;
: ed-decl ( index -- d outcome ) ed-name ['] ed-name-decl ok-and ;
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
  over ok? 0= if drop exit then nip 2dup-under execute ;
: ed-steps ( value i table -- outcome )
  outcome-ok swap begin dup @ while dup cell+ >r @ ed-step r> repeat drop nip nip ;
: ed-put ( addr x outcome xt -- outcome )
  over ok? 0= if drop nip nip exit then nip rot swap execute ! outcome-ok ;
: ed-claim ( slab -- i outcome ) 1 swap slab-claim ed-roomed ;
: ed-push ( x slab -- outcome )
  tuck ed-claim ok-then? if rot slab-at ! outcome-ok else nip nip then ;
\ x pushed when the outcome before it is ok, else that outcome.
: ed-push-ok ( x outcome slab -- outcome ) swap ok-then? if ed-push else nip then ;
\ A record form: a table of its members' names (ed-shape?), the slab its
\ records go to (an xt), then its steps, as ed-steps reads them;
\ ed-on-form reads one record of the form into a unit claimed for it.
begin-structure /ed-form
  field: ed-form-keys      \ the table of its members' names
  field: ed-form-slab      \ xt ( -- slab ) of the slab its records go to
  0 +field ed-form-steps   \ its steps, from here to the 0 that ends them
end-structure
: ed-form-claim ( form -- i outcome ) ed-form-slab @ execute ed-claim ;
: ed-on-form ( value form -- outcome )
  2dup ed-form-keys @ ed-shape? 0= if 2drop ed-malformed exit then
  dup ed-form-claim ok-then? if swap ed-form-steps ed-steps else nip nip then ;
\ A span's first number and count, the units of slab claimed between.
: ed-span-open ( span slab -- ) slab-count swap ! ;
: ed-span-close ( span slab -- ) over @ swap slab-since swap cell+ ! ;
\ An array of naturals of 32 bits into elab-orders, as the span at addr.
: ed-number-item ( item -- outcome ) ed-u32 elab-orders ed-push-ok ;
\ The items of an array read by xt ( item -- outcome ), each pushing its
\ number to elab-orders, as the span at addr.
: ed-span-items ( span index xt -- outcome )
  >r over elab-orders ed-span-open r> ed-array-items swap elab-orders ed-span-close ;
: ed-numbers ( span index -- outcome ) ['] ed-number-item ed-span-items ;
\ Whether every number of the span is below limit.
: ed-below? ( span limit -- flag )
  swap ed-span@ cells bounds ?do dup i @ u> 0= if drop unloop false exit then
  1 cells +loop drop true ;

\ ---- Types, as far as the checks below read them: the leading Pi
\ binders of a declaration's type, written out (no unfolding), and its
\ universe parameters.
: ed-pi? ( e -- flag ) ed-tier expr-pi? ;
: ed-let? ( e -- flag ) ed-tier expr-tag@ let-tag? ;
\ The telescope words of core/compact-exprs.fs on the stage's tier:
\ ed-lead, a type's leading Pis (the binders binder kinds describe);
\ ed-pis+ adds them to n and leaves the first other node; ed-pis, its
\ parameters, where a let (a matcher's type may hold lets among its
\ parameters: 13 of Init's) counts none and its body follows.
: ed-pi-next ( n e -- n+1 e' ) ed-tier expr-b@ swap 1+ swap ;
: ed-lead ( e -- n ) ed-tier expr-pis ;
: ed-pis+ ( n e -- n' e' ) tuck ed-lead + swap ed-tier expr-pi-end ;
: ed-pis ( e -- n )
  0 swap begin ed-pis+ dup ed-let? while ed-tier expr-body@ repeat drop ;
: ed-type@ ( d -- e ) ed-stage staged-type@ ;   \ the declaration's type
: ed-type-pis ( d -- n ) ed-type@ ed-pis ;
: ed-levels ( d -- n ) ed-stage staged-params@ ed-stage stage-tuples tuple-length ;

\ ---- Keys (front/elab-keys.fs): "star", "other", "arrow", or an object
\ of one of four forms. A constant no declaration has is, while
\ elab-foreign is set, a foreign key whose text is its name's parts, each
\ as 32-bit fields (lib/u32.fs's u32-le!): 0, the length and the bytes of
\ a string, or 1 and the number.
create ed-word-names  s" star" counted, s" other" counted, s" arrow" counted, 0 0 counted,
create ed-word-tags  elab-key-star , elab-key-other , elab-key-arrow ,
: ed-key-word ( item -- outcome )
  ed-word-names ed-choice ok-then? if cells ed-word-tags + @ elab-key-new nip then ;
: ed-text-u32 ( u -- outcome )
  4 elab-text-room ok-then? if u32-le! outcome-ok else nip then ;
: ed-text-bytes ( c-addr u -- outcome )
  dup elab-text-room ok-then? if swap move outcome-ok else nip nip then ;
: ed-foreign-text ( item -- outcome )
  ed-view json-text@ 0 ed-text-u32 ok-then2? 0= if exit then
  dup ed-text-u32 ok-then2? if ed-text-bytes then ;
: ed-foreign-number ( item -- outcome )
  ed-u32 ok-then? 0= if exit then 1 ed-text-u32 ok-then? if ed-text-u32 then ;
: ed-foreign-part ( item -- outcome )
  dup ed-string? if ed-foreign-text exit then ed-foreign-number ;
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
\ A projection of a structure no declaration has (while elab-foreign is
\ set): a foreign key whose text is 2, the field and the structure's
\ parts, and whose arity field is Lean's Key.arity, one more than its
\ arguments.
: ed-idx-text ( value -- outcome ) c" idx" ed-member ed-u32 ok-then? if ed-text-u32 then ;
: ed-proj-text ( value -- outcome )
  2 ed-text-u32 ok-then? 0= if exit then dup ed-idx-text ok-then? 0= if exit then
  c" proj" ed-member ['] ed-foreign-part ed-array-items ;
: ed-proj-arity ( k value -- outcome )
  c" arity" ed-member ed-u32 ok-then? 0= if nip exit then
  1+ swap elab-key-arity! outcome-ok ;
: ed-foreign-proj ( value -- outcome )
  elab-key-foreign elab-key-new ok-then? 0= if nip exit then
  dup elab-key-text-start over ed-proj-text ok-then? 0= if nip exit then
  dup elab-key-text-end swap ed-proj-arity ;
: ed-foreign-name? ( index -- flag )
  ed-name ok-then? if ed-foreign? else drop false then ;
: ed-key-proj ( value -- outcome )
  dup c" proj" ed-member ed-foreign-name? if ed-foreign-proj exit then
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
  dup ed-string? if ed-key-word exit then ed-key-object ;
\ A value's keys: kept in order, one term.
: ed-one-term ( value -- outcome ) ed-keys@ elab-one-term? ed-e-term ed-or-bad ;
: ed-keys-read ( value index -- outcome )
  over elab-keys# swap ed-value-keys ! ['] ed-key-item ed-array-items
  ok-then? 0= if exit then dup elab-keys# over ed-value-keys @ - swap ed-value-keys# !
  ed-one-term ;
: ed-value-rank! ( value index -- outcome ) ed-u32 ['] ed-value-rank ed-put ;
\ Members several records share, read for ed-put ( value addr -- addr x
\ outcome ): the priority, the class, the parameter count; the rank into
\ the record's value ( value addr -- outcome ).
: ed-priority-at ( value addr -- addr u outcome )
  swap c" priority" ed-member ed-u32 ;
: ed-class-at ( value addr -- addr d outcome ) swap c" class" ed-member ed-a-class ;
: ed-params-at ( value addr -- addr u outcome ) swap c" num_params" ed-member ed-u32 ;
: ed-rank-into ( value addr -- outcome ) swap c" rank" ed-member ed-value-rank! ;
\ A value into the ranks' table, unless one of its root key and rank is there.
: ed-place ( e -- outcome )
  ed-ranks htab-ready ed-roomed dup ok? 0= if nip exit then drop
  dup ed-value ed-rank-find
  if 2drop ed-e-rank ed-bad else ed-ranks htab-put outcome-ok then ;

\ ---- A record's own declaration, its member name: read by the kind's
\ reader, named by one record of the kind at most (a second: the kind's
\ error), kept in the declaration's fact and in the record. ed-owns
\ gives each kind's descriptor (0: its name is not its own): the reader
\ ( index -- d outcome ), the fact field, the error, the record ( i --
\ addr ) and its declaration field.
begin-structure /ed-own
  field: ed-own-reader   field: ed-own-fact   field: ed-own-why
  field: ed-own-rec      field: ed-own-field
end-structure
create ed-inst-own
  ' ed-no-type , ' ed-fact-inst , ed-e-instance , ' ed-inst , ' ed-inst-decl ,
create ed-class-own
  ' ed-a-type , ' ed-fact-class , ed-e-class , ' ed-class , ' ed-class-decl ,
create ed-match-own
  ' ed-a-def , ' ed-fact-matcher , ed-e-matcher , ' ed-match , ' ed-match-decl ,
create ed-proj-own
  ' ed-no-type , ' ed-fact-proj , ed-e-projection , ' ed-proj , ' ed-proj-decl ,
create ed-sun-own  ' ed-a-def , ' ed-fact-sun , ed-e-sunfold , ' ed-sun , ' ed-sun-decl ,
create ed-bk-own  ' ed-decl , ' ed-fact-bk , ed-e-binders , ' ed-bk , ' ed-bk-decl ,
create ed-owns   \ by kind (elab-instance .. elab-binders)
  ed-inst-own , 0 , 0 , 0 , 0 , ed-class-own , 0 , ed-match-own , ed-proj-own ,
  ed-sun-own , ed-bk-own ,
: ed-own ( -- own ) elab elab-kind @ cells ed-owns + @ ;
: ed-own-once ( d i -- outcome )
  over ed-own ed-own-fact @ ed-fact@ if 2drop ed-own ed-own-why @ ed-bad exit then
  ed-own ed-own-fact @ ed-fact! outcome-ok ;
: ed-own-named ( i d -- i d outcome ) 2dup swap ed-own-once ;
: ed-own-read ( index -- d outcome ) ed-own ed-own-reader @ execute ;
: ed-own-record ( i -- addr ) ed-own ed-own-rec @ execute ;
: ed-own-decl! ( value i -- outcome )
  swap c" name" ed-member ed-own-read dup ok? if drop ed-own-named then
  rot ed-own-record -rot ed-own ed-own-field @ ed-put ;

\ ---- Instances: name, class, priority, synthesis order, keys, rank.
create ed-inst-keys
  s" class" counted, s" keys" counted, s" name" counted, s" priority" counted,
  s" rank" counted, s" synth_order" counted, 0 0 counted,
: ed-inst-class! ( value i -- outcome ) ed-inst ed-class-at ['] ed-inst-class ed-put ;
: ed-inst-priority! ( value i -- outcome )
  ed-inst ed-priority-at ['] ed-inst-priority ed-put ;
: ed-inst-order! ( value i -- outcome )
  ed-inst ed-inst-order swap c" synth_order" ed-member ed-numbers ;
: ed-inst-path! ( value i -- outcome )
  ed-inst ed-inst-value swap c" keys" ed-member ed-keys-read ;
: ed-inst-rank! ( value i -- outcome ) ed-inst ed-inst-value ed-rank-into ;
: ed-inst-place ( value i -- outcome ) nip 2* ed-place ;
create ed-inst-form  ed-inst-keys , ' elab-insts ,
  ' ed-own-decl! , ' ed-inst-class! , ' ed-inst-priority! , ' ed-inst-order! ,
  ' ed-inst-path! , ' ed-inst-rank! , ' ed-inst-place , 0 ,
: ed-on-instance ( value -- outcome ) ed-inst-form ed-on-form ;

\ ---- Instances left out: why, name, priority, keys (foreign constants
\ allowed), rank.
create ed-left-members
  s" keys" counted, s" name" counted, s" priority" counted, s" rank" counted,
  s" reason" counted, 0 0 counted,
: ed-has? ( n -- flag ) ed-decls dup if nip then ;
: ed-left-has? ( reason n -- flag ) ed-has? swap elab-not-exported = and ;
: ed-left-name ( reason index -- outcome )
  dup ed-name-shape ok-then2? 0= if exit then
  ed-name ok-then? if ed-left-has? 0= ed-e-left-out ed-or-bad else nip then ;
: ed-left-reason! ( value j -- outcome )
  ed-left swap c" reason" ed-member ed-reason-names ed-choice ['] ed-left-reason ed-put ;
: ed-left-name! ( value j -- outcome )
  ed-left ed-left-reason @ swap c" name" ed-member ed-left-name ;
: ed-left-priority! ( value j -- outcome )
  ed-left ed-priority-at ['] ed-left-priority ed-put ;
: ed-left-path! ( value j -- outcome )
  true elab elab-foreign ! ed-left ed-left-value swap c" keys" ed-member ed-keys-read
  false elab elab-foreign ! ;
: ed-left-rank! ( value j -- outcome ) ed-left ed-left-value ed-rank-into ;
: ed-left-place ( value j -- outcome ) nip 2* 1+ ed-place ;
create ed-left-form  ed-left-members , ' elab-lefts ,
  ' ed-left-reason! , ' ed-left-name! , ' ed-left-priority! , ' ed-left-path! ,
  ' ed-left-rank! , ' ed-left-place , 0 ,
: ed-on-left-out ( value -- outcome ) ed-left-form ed-on-form ;

\ ---- Default instances: class, name, priority, rank (one per class and
\ rank). An instance may be named twice, of one class at two ranks, as
\ Lean keeps it (addDefaultInstanceEntry conses each attribute onto the
\ class's list: Mathlib makes instHSMul a default instance a second time);
\ named again with another class it is refused (error 16).
create ed-dflt-keys
  s" class" counted, s" name" counted, s" priority" counted, s" rank" counted,
  0 0 counted,
\ A record's member name, a declaration that is no inductive type, into
\ field xt of addr (default instances' and eliminators').
: ed-decl-into ( addr value xt -- outcome )
  swap c" name" ed-member ed-no-type rot ed-put ;
: ed-dflt-decl! ( value i -- outcome ) ed-dflt swap ['] ed-dflt-decl ed-decl-into ;
: ed-dflt-class! ( value i -- outcome ) ed-dflt ed-class-at ['] ed-dflt-class ed-put ;
: ed-dflt-priority! ( value i -- outcome )
  ed-dflt ed-priority-at ['] ed-dflt-priority ed-put ;
\ A default instance's rank is at most elab-default-rank-most, so that
\ FE1e3's answer, a cell per rank, stays small (ELABORATION_DATA.md; no
\ Lean library has a class with that many default instances).
65535 constant elab-default-rank-most
: ed-rank-most ( u outcome -- u outcome )
  over elab-default-rank-most u> over ok? and if drop ed-e-dflt-most ed-bad then ;
: ed-dflt-rank! ( value i -- outcome )
  ed-dflt swap c" rank" ed-member ed-u32 ed-rank-most ['] ed-dflt-rank ed-put ;
\ Default instances are few (34 in Init, 52 in Mathlib): record i is
\ compared with each record k before it (lib's any?).
: ed-dflt-decl@ ( i -- d ) ed-dflt ed-dflt-decl @ ;
: ed-dflt-class@ ( i -- class ) ed-dflt ed-dflt-class @ ;
: ed-dflt-rank@ ( i -- rank ) ed-dflt ed-dflt-rank @ ;
: ed-same-decl? ( i j -- flag ) ed-dflt-decl@ swap ed-dflt-decl@ = ;
: ed-same-class? ( i j -- flag ) ed-dflt-class@ swap ed-dflt-class@ = ;
: ed-same-rank? ( i j -- flag ) ed-dflt-rank@ swap ed-dflt-rank@ = ;
\ One class and one rank; one instance of two classes.
: ed-same-slot? ( i j -- flag )
  2dup ed-same-rank? 0= if 2drop false exit then ed-same-class? ;
: ed-clash? ( i j -- flag )
  2dup ed-same-decl? if ed-same-class? 0= else 2drop false then ;
\ The tests any? runs, record i kept below.
: ed-dflt-same? ( i k -- i flag ) over swap ed-same-slot? ;
: ed-dflt-clash? ( i k -- i flag ) over swap ed-clash? ;
\ After the rank: no earlier record of the instance with another class
\ (error 16), none of the class with this rank (error 33).
: ed-dflt-once ( value i -- outcome )
  nip dup ['] ed-dflt-clash? any? if drop ed-e-default ed-bad exit then
  dup ['] ed-dflt-same? any? nip 0= ed-e-default-rank ed-or-bad ;
create ed-dflt-form  ed-dflt-keys , ' elab-dflts ,
  ' ed-dflt-decl! , ' ed-dflt-class! , ' ed-dflt-priority! , ' ed-dflt-rank! ,
  ' ed-dflt-once , 0 ,
: ed-on-default ( value -- outcome ) ed-dflt-form ed-on-form ;

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
: ed-elim-decl! ( value i -- outcome ) ed-elim swap ['] ed-elim-decl ed-decl-into ;
: ed-type-item ( item -- outcome ) ed-decl elab-types ed-push-ok ;
: ed-types-span ( addr -- )
  dup ed-elim-types @ elab-types slab-since swap ed-elim-types# ! ;
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

\ ---- Classes: name (an inductive type, once), out-parameters. They fit
\ when each out-parameter is one of the class's parameters (the Pi
\ binders of its type) and each out-level one of its universe parameters.
create ed-class-members
  s" name" counted, s" out_level_params" counted, s" out_params" counted, 0 0 counted,
: ed-class-params! ( value k -- outcome )
  ed-class ed-class-params swap c" out_params" ed-member ed-numbers ;
: ed-class-levels! ( value k -- outcome )
  ed-class ed-class-levels swap c" out_level_params" ed-member ed-numbers ;
: ed-class-fits? ( k -- flag )
  ed-class dup ed-class-params over ed-class-decl @ ed-type-pis ed-below?
  swap dup ed-class-levels swap ed-class-decl @ ed-levels ed-below? and ;
: ed-class-fit ( value k -- outcome ) nip ed-class-fits? ed-e-unfit ed-or-bad ;
create ed-class-form  ed-class-members , ' elab-classes ,
  ' ed-own-decl! , ' ed-class-params! , ' ed-class-levels! , ' ed-class-fit , 0 ,
: ed-on-class ( value -- outcome ) ed-class-form ed-on-form ;

\ ---- Tags: name (not an inductive type), tag; no tag of a declaration twice.
create ed-tag-members  s" name" counted, s" tag" counted, 0 0 counted,
: ed-tag-fact ( d tag -- outcome )
  2dup elab-tagged? if 2drop ed-e-tag ed-bad exit then
  ed-tag-bit swap ed-fact ed-fact-bits +! outcome-ok ;
\ The defeq tag: format 4 alone (before, an unknown tag), of a theorem.
: ed-defeq-fits ( d tag -- d tag outcome )
  dup elab-tag-defeq <> if outcome-ok exit then
  ed-v4? 0= if ed-malformed exit then over kind-thm ed-of-kind nip ;
: ed-tag-read ( d tag -- outcome )
  ed-defeq-fits dup ok? if drop ed-tag-fact else nip nip then ;
: ed-on-tag ( value -- outcome )
  dup ed-tag-members ed-shape? 0= if drop ed-malformed exit then
  dup c" name" ed-member ed-no-type ok-then? 0= if nip exit then
  swap c" tag" ed-member ed-tag-names ed-choice ok-then? if ed-tag-read else nip then ;

\ ---- Matchers: name (a definition, once), parameters, discriminants,
\ elimination universe, alternatives, the discriminants' names (read for
\ their form, not kept). It fits when its type has exactly a Pi binder for
\ each parameter, the motive, each discriminant and each alternative (the
\ motive applied is its conclusion; all 2,553 of Init's fit), and the
\ elimination universe is one of its universe parameters.
create ed-match-members
  s" alt_infos" counted, s" discr_names" counted, s" name" counted,
  s" num_discrs" counted, s" num_params" counted, s" u_elim_pos" counted, 0 0 counted,
create ed-alt-members
  s" has_unit_thunk" counted, s" num_fields" counted, s" num_overlaps" counted,
  0 0 counted,
: ed-match-params! ( value m -- outcome )
  ed-match ed-params-at ['] ed-match-params ed-put ;
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
create ed-alt-form  ed-alt-members , ' elab-alts ,
  ' ed-alt-fields! , ' ed-alt-overlaps! , ' ed-alt-thunk! , 0 ,
: ed-alt-item ( item -- outcome ) ed-alt-form ed-on-form ;
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
  dup ed-match-arity over elab-matcher@ 2drop ed-type-pis = swap ed-elim-fits? and ;
: ed-match-fit ( value m -- outcome ) nip ed-match-fits? ed-e-unfit ed-or-bad ;
create ed-match-form  ed-match-members , ' elab-matches ,
  ' ed-own-decl! , ' ed-match-params! , ' ed-match-discrs! , ' ed-match-elim! ,
  ' ed-match-alts! , ' ed-match-names! , ' ed-match-fit , 0 ,
: ed-on-matcher ( value -- outcome ) ed-match-form ed-on-form ;

\ ---- Projection functions: name (not an inductive type, once), the
\ constructor, the structure's parameters, the field, whether a class.
\ It fits when the function takes the parameters and the structure and
\ the constructor has the field.
create ed-proj-members
  s" ctor" counted, s" from_class" counted, s" idx" counted, s" name" counted,
  s" num_params" counted, 0 0 counted,
: ed-proj-ctor! ( value p -- outcome )
  ed-proj swap c" ctor" ed-member ed-a-ctor ['] ed-proj-ctor ed-put ;
: ed-proj-params! ( value p -- outcome )
  ed-proj ed-params-at ['] ed-proj-params ed-put ;
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
create ed-proj-form  ed-proj-members , ' elab-projs ,
  ' ed-own-decl! , ' ed-proj-ctor! , ' ed-proj-params! , ' ed-proj-idx! ,
  ' ed-proj-class! , ' ed-proj-fit , 0 ,
: ed-on-projection ( value -- outcome ) ed-proj-form ed-on-form ;

\ ---- Smart-unfolding bodies (plan S2, format 3; S2_INTERFACE.md §3): the
\ definition f, the record's own; the universe parameters of f._sunfold,
\ f's in order (error 44); a table of levels and one of nodes, each entry
\ naming only earlier ones (error 42); the root, a node with no loose
\ bound variable (error 43); f's structural recursion argument or null
\ (a place among an application's arguments, which Lean compares with
\ their number where it uses it, WHNF.lean:900: f's type may be a
\ definition that unfolds to more binders, as Nat.decidableExistsLT's
\ DecidablePred, so no arity is checked here). A node's constant, or a projection's
\ structure, that no declaration of the library has makes the record
\ foreign: kept, and unsupported where it would be used (25 of Init's
\ 387 name a `_proof_` lemma the export lacks). An annotation is one
\ entry, sunfoldMatch, sunfoldMatchAlt or borrowed, true; any other is
\ unsupported (error 45). An inert node (format 3.1) makes the record
\ inert: kept, and unsupported where it would be used, like a foreign
\ one. A binder's name may be anonymous ([]). A node's literal, string
\ and binder name are keys of front/elab-keys.fs, for their texts (a
\ name's parts as a foreign key's). The entry being read is the newest
\ of its slab.
create ed-sun-members
  s" level_params" counted, s" levels" counted, s" name" counted, s" nodes" counted,
  s" rec_arg" counted, s" value" counted, 0 0 counted,
: ed-sun-now ( -- addr ) elab-suns slab-count 1- ed-sun ;
: ed-nd ( -- addr ) elab-nodes slab-last ;
: ed-nd-kind! ( kind -- ) ed-nd ed-node-kind ! ;
: ed-lv ( -- addr ) elab-levels slab-last ;
: ed-nodes-first ( -- n ) ed-sun-now ed-sun-nodes @ ;
: ed-levels-first ( -- l ) ed-sun-now ed-sun-levels @ ;
\ An entry of the record's table at index (from first) below the limit
\ (a number): its number. The index is checked against the room left
\ (limit - first), so first + index cannot wrap.
: ed-entry-in ( first room n -- n' outcome )
  tuck swap index? if + outcome-ok else drop ed-e-order ed-bad then ;
: ed-entry-below ( index first limit -- n outcome )
  over - rot ed-u32 ['] ed-entry-in ok-apply3 ;
\ An earlier node or level of the record; its root; any of its levels.
: ed-node-ref ( index -- n outcome )
  ed-nodes-first elab-nodes slab-count 1- ed-entry-below ;
: ed-root-ref ( index -- n outcome ) ed-nodes-first elab-nodes slab-count ed-entry-below ;
: ed-level-ref ( index -- l outcome )
  ed-levels-first elab-levels slab-count 1- ed-entry-below ;
: ed-level-all ( index -- l outcome )
  ed-levels-first elab-levels slab-count ed-entry-below ;
\ A new entry of a slab of nodes or levels, every field 0.
: ed-entry-new ( slab -- outcome )
  dup ed-claim ok-then? if swap slab-at /ed-node erase outcome-ok else nip then ;
\ Arrays of two, and the first item of an array.
: ed-items? ( index n -- flag )
  swap json-array ed-view json-items-of if = else drop false then ;
: ed-first-item ( index -- item ) ed-view json-contents nip ;
\ The two entries of an array of two, each read by xt ( item -- n outcome ).
: ed-two-refs ( value xt -- n1 n2 outcome )
  over 2 ed-items? 0= if 2drop 0 0 ed-malformed exit then
  swap ed-first-item 2dup swap execute ok-then? 0= if nip nip 0 0 rot exit then
  -rot ed-next swap execute ;
: ed-ab! ( n1 n2 outcome addr -- outcome )
  swap dup ok? 0= if nip nip nip exit then drop tuck ed-node-b ! ed-node-a ! outcome-ok ;
\ An object of one member whose key is in table: the member's value and
\ the key's place.
: ed-sole? ( index -- flag ) json-object ed-view json-items-of if 1 = else false then ;
: ed-sole ( value table -- value' k true | false )
  over ed-sole? 0= if 2drop false exit then
  swap ed-first-item dup 1+ -rot ed-view json-text@ rot ed-key-index dup 0= if nip then ;

\ The universe parameters: their names in elab-orders, each f's next one.
: ed-sun-decl@ ( -- d ) ed-sun-now ed-sun-decl @ ;
: ed-params-read ( -- k ) ed-sun-now ed-sun-params @ elab-orders slab-since ;
: ed-f-param ( k -- n )
  ed-sun-decl@ ed-stage staged-params@ ed-stage stage-tuples tuple-item ;
: ed-next-param? ( n -- flag )
  ed-params-read dup ed-sun-decl@ ed-levels < if ed-f-param = else 2drop false then ;
: ed-param-item ( item -- outcome )
  ed-name ok-then? 0= if exit then
  dup ed-next-param? if elab-orders ed-push else drop ed-e-params ed-bad then ;
: ed-sun-params! ( value s -- outcome )
  ed-sun ed-sun-params swap c" level_params" ed-member ['] ed-param-item ed-span-items ;
: ed-param-place ( n -- i true | false ) ed-sun-now ed-sun-params ed-span@ cells-index ;

\ The levels: "zero", or {"succ": L}, {"max": [L, L]}, {"imax": [L, L]},
\ {"param": NAME}, each L an earlier level's place.
create ed-level-names
  s" succ" counted, s" max" counted, s" imax" counted, s" param" counted, 0 0 counted,
: ed-lv-succ ( value -- outcome ) ed-lv swap ed-level-ref ['] ed-node-a ed-put ;
: ed-lv-pair ( value -- outcome ) ['] ed-level-ref ed-two-refs ed-lv ed-ab! ;
: ed-lv-param ( value -- outcome )
  ed-name ok-then? 0= if exit then ed-param-place 0= if ed-e-params ed-bad exit then
  ed-lv swap outcome-ok ['] ed-node-a ed-put ;
create ed-level-readers  ' ed-lv-succ , ' ed-lv-pair , ' ed-lv-pair , ' ed-lv-param ,
: ed-lv-form ( value k -- outcome )
  dup 1+ ed-lv ed-node-kind ! cells ed-level-readers + @ execute ;
: ed-lv-object ( item -- outcome )
  ed-level-names ed-sole if ed-lv-form else ed-malformed then ;
: ed-lv-zero ( item -- outcome ) s" zero" ed-text= ed-e-malformed ed-or-bad ;
: ed-level-item ( item -- outcome )
  elab-levels ed-entry-new dup ok? 0= if nip exit then drop
  dup ed-string? if ed-lv-zero else ed-lv-object then ;
: ed-sun-levels! ( value s -- outcome )
  ed-sun ed-sun-levels dup elab-levels ed-span-open swap c" levels" ed-member
  ['] ed-level-item ed-array-items swap elab-levels ed-span-close ;

\ The nodes' fields (the table at elab-node-bvar). ed-nd-put stores x,
\ when ok, in the field xt of the newest node; ed-nd-ref! there the place
\ of an earlier node, member key of value.
: ed-nd-put ( x outcome xt -- outcome ) ed-nd swap execute swap ok-store ;
: ed-nd-ref! ( value key xt -- outcome ) >r ed-member ed-node-ref r> ed-nd-put ;
: ed-nd-bvar ( value -- outcome ) ed-u32 ['] ed-node-a ed-nd-put ;
: ed-nd-sort ( value -- outcome ) ed-level-all ['] ed-node-a ed-nd-put ;
: ed-nd-app ( value -- outcome ) ['] ed-node-ref ed-two-refs ed-nd ed-ab! ;
: ed-nd-name ( value -- outcome )
  c" name" ed-member ed-foreign-key ['] ed-node-a ed-nd-put ;
: ed-nd-type ( value -- outcome ) c" type" ['] ed-node-b ed-nd-ref! ;
: ed-nd-body ( value -- outcome ) c" body" ['] ed-node-c ed-nd-ref! ;
create ed-info-names
  s" default" counted, s" implicit" counted, s" strict" counted, s" inst" counted,
  0 0 counted,
: ed-nd-info ( value -- outcome )
  c" info" ed-member ed-info-names ed-choice ['] ed-node-d ed-nd-put ;
create ed-binder-members
  s" body" counted, s" info" counted, s" name" counted, s" type" counted, 0 0 counted,
\ A form: its members' table, then its steps ( value -- outcome ), run
\ in turn when the value has exactly those members.
create ed-binder-form
  ed-binder-members , ' ed-nd-name , ' ed-nd-type , ' ed-nd-body , ' ed-nd-info , 0 ,
: ed-nd-steps ( value form -- outcome )
  2dup @ ed-shape? if cell+ outcome-steps else 2drop ed-malformed then ;
: ed-nd-binder ( value -- outcome ) ed-binder-form ed-nd-steps ;
: ed-nd-value ( value -- outcome ) c" value" ['] ed-node-c ed-nd-ref! ;
: ed-nd-let-body ( value -- outcome ) c" body" ['] ed-node-d ed-nd-ref! ;
: ed-nd-non-dep ( value -- outcome )
  c" non_dep" ed-member ed-bool ok-then? if if elab-node-have ed-nd-kind! then
  outcome-ok then ;
create ed-let-members
  s" body" counted, s" name" counted, s" non_dep" counted, s" type" counted,
  s" value" counted, 0 0 counted,
create ed-let-form  ed-let-members ,
  ' ed-nd-name , ' ed-nd-type , ' ed-nd-value , ' ed-nd-let-body , ' ed-nd-non-dep , 0 ,
: ed-nd-let ( value -- outcome ) ed-let-form ed-nd-steps ;
: ed-texted ( c-addr u tag -- k outcome ) ed-text-key elab-keys# 1- swap ;
: ed-nd-lit ( value -- outcome )
  ed-digits ok-then2? if elab-key-lit ed-texted else no-result then
  ['] ed-node-a ed-nd-put ;
: ed-nd-str ( value -- outcome )
  ed-text if elab-key-str ed-texted else 0 ed-malformed then
  ['] ed-node-a ed-nd-put ;
\ A constant, or a projection's structure: the one declaration of the
\ name, or -1 when none has it (the record foreign).
: ed-body-decl ( n -- d outcome )
  ed-decls if ed-one-decl else true ed-sun-now ed-sun-foreign ! -1 outcome-ok then ;
: ed-type-or-none ( d -- d outcome )
  dup 0< if outcome-ok exit then dup ed-type? if outcome-ok else ed-kind-bad then ;
: ed-body-name ( index -- d outcome )
  ed-name ['] ed-body-decl ok-apply ;
: ed-nd-struct ( value -- outcome )
  c" struct" ed-member ed-body-name
  ['] ed-type-or-none ok-apply ['] ed-node-a ed-nd-put ;
: ed-nd-idx ( value -- outcome ) c" idx" ed-member ed-u32 ['] ed-node-b ed-nd-put ;
: ed-nd-expr ( value -- outcome ) c" expr" ['] ed-node-c ed-nd-ref! ;
create ed-proj-node-members
  s" expr" counted, s" idx" counted, s" struct" counted, 0 0 counted,
create ed-proj-node-form
  ed-proj-node-members , ' ed-nd-struct , ' ed-nd-idx , ' ed-nd-expr , 0 ,
: ed-nd-proj ( value -- outcome ) ed-proj-node-form ed-nd-steps ;
\ An annotation: [[KEY, {"bool": true}]], KEY one of Lean's three.
create ed-annotation-names
  s" sunfoldMatch" counted, s" sunfoldMatchAlt" counted, s" borrowed" counted,
  0 0 counted,
create ed-bool-members  s" bool" counted, 0 0 counted,
: ed-true? ( index -- flag )
  dup ed-bool-members ed-shape? if c" bool" ed-member ed-view json-bool 0= if false then
  else drop false then ;
: ed-annotation ( key -- k true | false )
  dup 1 ed-items? 0= if drop false exit then
  ed-first-item ed-annotation-names ed-text-index ;
: ed-unknown-mark ( -- k outcome ) 0 ed-e-annotation outcome-unsupported ed-fail ;
\ A mark's place, or error 45.
: ed-known ( k true | false -- k outcome ) if outcome-ok else ed-unknown-mark then ;
: ed-entry ( entry -- k outcome )
  dup 2 ed-items? 0= if drop 0 ed-malformed exit then
  ed-first-item dup ed-next ed-true? if ed-annotation else drop false then ed-known ;
: ed-nd-entries ( value -- outcome )
  c" entries" ed-member dup 1 ed-items? if ed-first-item ed-entry
  else drop 0 ed-malformed then ['] ed-node-a ed-nd-put ;
create ed-mdata-members  s" entries" counted, s" expr" counted, 0 0 counted,
create ed-mdata-form  ed-mdata-members , ' ed-nd-entries , ' ed-nd-expr , 0 ,
: ed-nd-mdata ( value -- outcome ) ed-mdata-form ed-nd-steps ;
\ An inert node (format 3.1 alone; in a format-3 file malformed, as the
\ readers of format 3 had it): {"expr":i,"key":KEY}, KEY one of three
\ kinds of metadata LeanForth does not carry; any other text is error 45,
\ a KEY that is no text malformed (review L3 of MF1). An mdata node of
\ elab-inert; the body holding it is not usable.
create ed-inert-names
  s" save_info" counted, s" noImplicitLambda" counted, s" congrHole" counted, 0 0 counted,
: ed-inert-key ( value -- k outcome )
  c" key" ed-member dup ed-string? 0= if drop 0 ed-malformed exit then
  ed-inert-names ed-text-index ed-known ;
: ed-inert-mark ( -- outcome )
  true ed-sun-now ed-sun-inert ! elab-inert outcome-ok ['] ed-node-a ed-nd-put ;
: ed-nd-key ( value -- outcome ) ed-inert-key ok-then? if drop ed-inert-mark then ;
create ed-inert-members  s" expr" counted, s" key" counted, 0 0 counted,
create ed-inert-form  ed-inert-members , ' ed-nd-key , ' ed-nd-expr , 0 ,
: ed-v31? ( -- flag ) elab elab-v31 @ ;
: ed-nd-inert ( value -- outcome )
  ed-v31? 0= if drop ed-malformed exit then
  elab-node-mdata ed-nd-kind! ed-inert-form ed-nd-steps ;
: ed-node-level ( item -- outcome ) ed-level-all elab-orders ed-push-ok ;
: ed-nd-levels ( value -- outcome )
  ed-nd ed-node-b swap c" levels" ed-member ['] ed-node-level ed-span-items ;
\ A constant: its declaration (-1: foreign), then its levels, as many as
\ the declaration has universe parameters (a foreign one's: any number).
: ed-nd-levels# ( -- n ) ed-nd ed-node-b ed-span@ nip ;
: ed-nd-arity? ( -- flag )
  ed-nd ed-node-a @ dup 0< if drop true else ed-levels ed-nd-levels# = then ;
: ed-nd-fits ( -- outcome ) ed-nd-arity? ed-e-unfit ed-or-bad ;
: ed-nd-const ( value -- outcome )
  dup c" const" ed-member ed-body-name ['] ed-node-a ed-nd-put
  ok-then? if ed-nd-levels dup ok? if drop ed-nd-fits then then ;

\ Loose bound variables: 1 + the largest, from the fields of the newest node.
: ed-loose ( n -- k ) ed-node ed-node-loose @ ;
: ed-under ( n -- k ) ed-loose 1- 0 max ;
: ed-lo-none ( addr -- k ) drop 0 ;
: ed-lo-bvar ( addr -- k ) ed-node-a @ 1+ ;
: ed-lo-app ( addr -- k ) dup ed-node-a @ ed-loose swap ed-node-b @ ed-loose max ;
: ed-lo-binder ( addr -- k ) dup ed-node-b @ ed-loose swap ed-node-c @ ed-under max ;
: ed-lo-let ( addr -- k )
  dup ed-node-b @ ed-loose over ed-node-c @ ed-loose max swap ed-node-d @ ed-under max ;
: ed-lo-term ( addr -- k ) ed-node-c @ ed-loose ;   \ proj's and mdata's
create ed-loose-of   \ by node kind
  ' ed-lo-bvar , ' ed-lo-none , ' ed-lo-app , ' ed-lo-binder , ' ed-lo-binder ,
  ' ed-lo-let , ' ed-lo-none , ' ed-lo-none , ' ed-lo-term , ' ed-lo-term ,
  ' ed-lo-none , ' ed-lo-let ,
: ed-loose-xt ( addr -- xt ) ed-node-kind @ cells ed-loose-of + @ ;
: ed-loose! ( -- ) ed-nd dup dup ed-loose-xt execute swap ed-node-loose ! ;

\ A node: {"const": NAME, "levels": [L...]}, or an object of one member
\ whose key names its kind.
create ed-node-names
  s" bvar" counted, s" sort" counted, s" app" counted, s" lam" counted,
  s" forall" counted, s" let" counted, s" lit" counted, s" str" counted,
  s" proj" counted, s" mdata" counted, s" inert" counted, 0 0 counted,
create ed-node-readers
  ' ed-nd-bvar , ' ed-nd-sort , ' ed-nd-app , ' ed-nd-binder , ' ed-nd-binder ,
  ' ed-nd-let , ' ed-nd-lit , ' ed-nd-str , ' ed-nd-proj , ' ed-nd-mdata , ' ed-nd-inert ,
create ed-const-node-members  s" const" counted, s" levels" counted, 0 0 counted,
\ A name's place is its node kind (elab-node-bvar .. -mdata), except
\ inert's, 10: stored for a moment as elab-node-const, until ed-nd-inert
\ makes the node an mdata (or the read fails).
: ed-nd-form ( value k -- outcome ) dup ed-nd-kind! cells ed-node-readers + @ execute ;
: ed-nd-read ( item -- outcome )
  dup ed-const-node-members ed-shape? if elab-node-const ed-nd-kind! ed-nd-const exit then
  ed-node-names ed-sole if ed-nd-form else ed-malformed then ;
: ed-node-item ( item -- outcome )
  elab-nodes ed-entry-new dup ok? 0= if nip exit then drop
  ed-nd-read dup ok? if ed-loose! then ;
: ed-sun-nodes! ( value s -- outcome )
  ed-sun ed-sun-nodes dup elab-nodes ed-span-open swap c" nodes" ed-member
  ['] ed-node-item ed-array-items swap elab-nodes ed-span-close ;

\ The root and the recursion argument; then the record fits f.
: ed-sun-value! ( value s -- outcome )
  ed-sun swap c" value" ed-member ed-root-ref ['] ed-sun-value ed-put ;
: ed-sun-rec! ( value s -- outcome )
  ed-sun swap c" rec_arg" ed-member ed-u32-or-none ['] ed-sun-rec ed-put ;
: ed-sun-closed? ( addr -- flag ) ed-sun-value @ ed-loose 0= ;
: ed-sun-all-params? ( addr -- flag )
  dup ed-sun-params# @ swap ed-sun-decl @ ed-levels = ;
: ed-sun-fit ( value s -- outcome )
  nip ed-sun dup ed-sun-all-params? 0= if drop ed-e-params ed-bad exit then
  ed-sun-closed? ed-e-loose ed-or-bad ;
create ed-sun-steps
  ' ed-own-decl! , ' ed-sun-params! , ' ed-sun-levels! , ' ed-sun-nodes! ,
  ' ed-sun-value! , ' ed-sun-rec! , ' ed-sun-fit , 0 ,
: ed-on-sunfold ( value -- outcome )
  dup ed-sun-members ed-shape? 0= if drop ed-malformed exit then
  elab-suns ed-claim ok-then? 0= if nip exit then
  dup ed-sun /ed-sun erase ed-sun-steps ed-steps ;

\ ---- Binder kinds (format 3.2 alone; plan FE1c-bk): a declaration's name
\ and one text per leading Pi binder of its type, its kind's digit (Lean's
\ BinderInfo: 0 default, 1 implicit, 2 strict implicit, 3 instance) and
\ then its domain's leading binders'. Their numbers must be the export's
\ type's (error 37); a declaration has one record at most (error 46).
: ed-v32? ( -- flag ) elab elab-v32 @ ;
: ed-not-kind? ( char -- flag ) [char] 0 - 4 u< 0= ;
: ed-kinds? ( c-addr u -- flag ) dup if ['] ed-not-kind? text-any? 0= else nip then ;
: ed-kind-text ( item -- c-addr u true | false )
  ed-text 0= if false exit then 2dup ed-kinds? dup 0= if nip nip then ;
: ed-kind@ ( c-addr -- kind ) 1 decimal>u ;
: ed-bk-lead ( item -- outcome )
  ed-kind-text if drop ed-kind@ elab-orders ed-push else ed-malformed then ;
: ed-bk-kinds! ( value b -- outcome )
  ed-bk ed-bk-kinds swap c" kinds" ed-member ['] ed-bk-lead ed-span-items ;
: ed-dom-digit ( c-addr k -- c-addr outcome ) over + ed-kind@ elab-orders ed-push ;
: ed-dom-digits ( c-addr u -- outcome ) 1 /string ['] ed-dom-digit ok-each nip ;
\ A domain's digits, after its kind's: the item's text is not checked
\ again, ed-bk-kinds! (run first, ed-bk-steps) refused any item that is
\ no text of digits 0-3 (ed-kind-text), so ed-text's flag is dropped.
: ed-dom-span ( item span -- outcome )
  dup elab-orders ed-span-open swap ed-text drop ed-dom-digits
  swap elab-orders ed-span-close ;
: ed-dom-item ( item -- outcome )
  elab-bk-doms ed-claim ok-then? if elab-bk-doms slab-at ed-dom-span else nip then ;
: ed-bk-doms! ( value b -- outcome )
  elab-bk-doms slab-count over ed-bk ed-bk-doms ! drop
  c" kinds" ed-member ed-view json-contents ['] ed-dom-item ed-items ;
\ The fit: as many leading Pis as kinds (ed-lead), each domain's as its
\ own: the record's domain spans (from b's first, span) walked beside the
\ type's leading Pis (ed-pi-next), once ed-lead-fits? holds.
: ed-dom-fit? ( span e -- flag )
  ed-tier expr-a@ ed-lead swap elab-bk-doms slab-at ed-span@ nip = ;
: ed-doms-fit? ( b e -- flag )
  swap ed-bk ed-bk-doms @ swap begin dup ed-pi? while
    2dup ed-dom-fit? 0= if 2drop false exit then ed-pi-next repeat 2drop true ;
: ed-lead-fits? ( b e -- flag ) ed-lead swap elab-binder-kinds nip tuck = swap 0<> and ;
: ed-bk-fit ( value b -- outcome )
  nip dup elab-binder-decl ed-type@
  2dup ed-lead-fits? if ed-doms-fit? else 2drop false then ed-e-unfit ed-or-bad ;
create ed-bk-members  s" kinds" counted, s" name" counted, 0 0 counted,
create ed-bk-steps  ' ed-own-decl! , ' ed-bk-kinds! , ' ed-bk-doms! , ' ed-bk-fit , 0 ,
: ed-on-binder-kinds ( value -- outcome )
  ed-v32? 0= if drop ed-e-kind ed-bad exit then
  dup ed-bk-members ed-shape? 0= if drop ed-malformed exit then
  elab-bks ed-claim ok-then? if ed-bk-steps ed-steps else nip then ;

\ ---- Lines. Each is one JSON object with one member: the header's key
\ elab_data, or a record kind, whose value is an object.
create ed-kind-handlers
  ' ed-on-instance , ' ed-on-default , ' ed-on-reducibility , ' ed-on-eliminator ,
  ' ed-on-left-out , ' ed-on-class , ' ed-on-tag , ' ed-on-matcher , ' ed-on-projection ,
  ' ed-on-sunfold , ' ed-on-binder-kinds ,
: ed-one-member? ( -- flag ) 0 ed-sole? ;
: ed-object-value? ( -- flag ) 2 ed-view json-object json-kind-at? ;
: ed-wrapped? ( -- flag ) ed-one-member? if ed-object-value? else false then ;
: ed-tally ( kind -- ) elab elab-counts cell-tally ;
\ A record of an added kind, read by its form's reader in format 4 alone.
: ed-added-read? ( kind -- flag ) elab-kinds - ed-added-read# < ed-v4? and ;
: ed-on-added ( value -- outcome )
  elab elab-kind @ ed-added-read? 0= if drop ed-e-kind ed-bad exit then
  elab elab-kind @ ed-kind-data ed-kind-form @ ed-on-form ;
: ed-handler ( kind -- xt )
  dup elab-kinds u< if cells ed-kind-handlers + @ else drop ['] ed-on-added then ;
: ed-dispatch ( value kind -- outcome )
  dup elab elab-kind ! dup ed-tally ed-handler execute ;
: ed-on-record ( -- outcome )
  ed-wrapped? 0= if ed-malformed exit then
  1 ed-view json-text@ ed-kind-index
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
\ Format 3 (the number), or 3.1 (the text; an inert node allowed:
\ elab-v31), or 3.2 (also binder kinds: elab-v32, plan FE1c-bk).
: ed-head-v32 ( index -- flag ) s" 3.2" ed-text= dup elab elab-v32 ! ;
: ed-head-v31 ( index -- flag )
  dup ed-head-v32 swap s" 3.1" ed-text= or dup elab elab-v31 ! ;
: ed-natural= ( index c-addr u -- flag )
  rot ed-view natural-at if compare 0= else 2drop false then ;
: ed-head-v3? ( index -- flag ) s" 3" ed-natural= ;
\ Format 4 (the number): 3.2's kinds and inert nodes, the added kinds;
\ 4.1 (the text) also elab-add-kind41's.
: ed-v4! ( flag -- ) dup elab elab-v4 ! dup elab elab-v31 ! elab elab-v32 ! ;
: ed-head-v4 ( index -- flag ) s" 4" ed-natural= dup ed-v4! ;
: ed-head-v4-or-3 ( index -- flag ) dup ed-head-v4 swap ed-head-v3? or ;
: ed-head-v41 ( index -- flag ) s" 4.1" ed-text= dup elab elab-v41 ! ;
: ed-head-v4x ( index -- flag )
  dup ed-head-v41 if drop true dup ed-v4! else ed-head-v4-or-3 then ;
: ed-head-version ( value i -- outcome )
  drop c" format_version" ed-member dup ed-head-v4x if drop true else ed-head-v31 then
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
\ Format 3.2 counts every kind; 3 and 3.1 all but binder_kinds (none).
: ed-kinds-named ( -- table n )
  ed-v32? if ed-kind-names elab-kinds else ed-v3-kinds elab-binders then ;
: ed-kinds# ( -- n )
  ed-v4? if elab-kinds ed-added-read# + else ed-kinds-named nip then ;
\ Format 4 counts the kinds of 3.2 and every added one.
: ed-added-counted? ( object i -- object flag ) ed-added-key over swap ed-member 0< 0= ;
: ed-all-added? ( object -- flag )
  ed-added-read# ['] ed-added-counted? count-index ed-added-read# = ;
: ed-v4-shaped? ( object -- flag )
  ed-kinds# over ed-view members? 0= if drop false exit then
  dup ed-kind-names swap ed-view all-keys? swap ed-all-added? and ;
: ed-records-shaped? ( object -- flag )
  ed-v4? if ed-v4-shaped? exit then ed-kinds-named drop ed-shape? ;
: ed-expect-k ( object k -- object outcome ) over swap ed-expect ;
: ed-head-records ( value i -- outcome )
  drop c" records" ed-member dup ed-records-shaped? 0= if drop ed-malformed exit then
  ed-kinds# ['] ed-expect-k ok-each nip ;
\ M6 (S1 note): the records SHA-256 the export's manifest names, if any,
\ must be the header's (the records are then checked against it).
: ed-bound ( -- c-addr u ) elab elab-bound elab elab-bound-length @ ;
: ed-bound-same? ( c-addr u -- flag )
  ed-bound dup if compare 0= else 2drop 2drop true then ;
: ed-records-keep ( c-addr u -- outcome )
  2dup ed-bound-same? 0= if 2drop ed-e-bound ed-bad exit then
  elab elab-records swap move outcome-ok ;
: ed-head-hash ( value i -- outcome )
  drop c" records_sha256" ed-member ed-text 0= if ed-malformed exit then
  2dup sha-digest-bytes 2* hex-text? 0= if 2drop ed-malformed exit then ed-records-keep ;
\ (Counted for elab-init-only?: S2's unification hints.)
: ed-module-count ( item -- )
  1 elab elab-modules# +! s" Init" ed-text= if 1 elab elab-inits# +! then ;
: ed-module-item ( item -- outcome )
  dup ed-string? if ed-module-count outcome-ok else drop
    ed-malformed
  then ;
: ed-head-modules ( value i -- outcome )
  drop 0 elab elab-modules# ! 0 elab elab-inits# !
  c" modules" ed-member ['] ed-module-item ed-array-items ;
\ The data is of Lean's Init alone (its header's modules: Init), whose
\ unification hints are known (front/defeq.fs's isDefEqOnFailure).
: elab-init-only? ( -- flag )
  elab-loaded? elab dup elab-modules# @ 1 = swap elab-inits# @ 1 = and and ;
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
: ed-added-cells ( addr -- addr' u ) elab-kinds cells + ed-added# cells ;
: ed-added-same? ( -- flag )
  elab elab-counts ed-added-cells elab elab-expected ed-added-cells compare 0= ;
: ed-ends ( -- outcome )
  ed-counts-same? ed-added-same? and 0= if ed-e-count ed-bad exit then
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
  reader-strict elab elab-reader reader-rules!
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
  0 elab elab-bound-length !
  elab elab-reader dup reader-close drop reader-free ed-view json-free
  false elab elab-reading ! dup ok? dup elab elab-loaded ! 0= if elab-reset then ;
: ed-caught ( c-addr u -- outcome code )
  ['] ed-steps-all catch dup if nip nip outcome-invalid swap then ;
: ed-busy ( c-addr u stage sha -- outcome ) 2drop 2drop ed-e-busy ed-bad ;
\ Name the records SHA-256 (64 hexadecimal digits, as text) the next
\ elab-read must find in the header, or 0 0 for none: the export
\ manifest's elab_records_sha256 (manifest-elab-sha). Used by that read only.
: elab-bind! ( c-addr u -- )
  sha-digest-bytes 2* min dup elab elab-bound-length ! elab elab-bound swap move ;
: elab-read ( c-addr u stage sha -- outcome )
  elab elab-reading @ if ed-busy exit then
  ed-start ok-then2? if true elab elab-reading ! ed-caught else 0 then
  >r ed-close r> throw ;

\ ---- For the kinds other files add (elab-add-kind): this file's own
\ record-reading words under elab- names, with their stack effects. A
\ form for elab-on-form is the address of three or more cells: a table of
\ the record's members (counted strings ending with an empty one), an xt
\ ( -- slab ) of the slab a record is claimed in, then its steps ( value
\ i -- outcome ), run in turn while ok, ended by 0.
synonym elab-member ed-member            ( value key -- index )
synonym elab-u32 ed-u32                  ( index -- u outcome )
synonym elab-decl ed-decl                ( index -- d outcome )
synonym elab-of-kind ed-of-kind          ( d kind -- d outcome )
synonym elab-refuse ed-bad               ( code -- outcome )
synonym elab-malformed ed-malformed      ( -- outcome )
synonym elab-roomed ed-roomed            ( outcome -- outcome ) \ a failure: error 22
synonym elab-e-unfit ed-e-unfit          ( -- 37 )
synonym elab-put ed-put                  ( addr x outcome xt -- outcome )
synonym elab-on-form ed-on-form          ( value form -- outcome )
synonym elab-array-items ed-array-items  ( index xt -- outcome )
synonym elab-type-pis ed-type-pis        ( d -- n )
synonym elab-numbers ed-numbers          ( span index -- outcome ) \ u32s into elab-orders
synonym elab-span@ ed-span@              ( span -- addr n )
synonym elab-text= ed-text=              ( index c-addr u -- flag )
synonym elab-tier ed-tier                ( -- tier ) \ the stage's names and terms
synonym elab-type@ ed-type@              ( d -- e )
: elab-format4? ( -- flag ) elab-loaded? ed-v4? and ;
: elab-format41? ( -- flag ) elab-format4? ed-v41? and ;
: ed-tagged-at? ( tag d -- tag flag ) over elab-tagged? ;
: elab-tag-count ( tag -- n ) elab-facts slab-count ['] ed-tagged-at? count-index ;

base !   \ the BASE this file was loaded with
