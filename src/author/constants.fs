\ The declarations of an authoring run (ADR 0017 §8): one record per
\ theorem, def, axiom or import stub, in the order they ended. Each is a
\ constant later declarations can name: the record holds what the term
\ printer's Forth mode prints (kind, name, universe parameters, type and
\ value, print-forth.fs) and where its labels and notes are. A constant of
\ the library a checked run names (library.fs; plan task 8.2.1d) gets a
\ record of kind lfa-decl-library when first named: its name, its number
\ of universe parameters and its definition height, no type or value; the
\ printer never prints one and the export never writes one. Untrusted
\ authoring code; the checker receives terms, never these records.
\ State: the store lfa-decls, in the checker context (ADR 0009).

require ../lib/lib.fs
require ../present/binder-table.fs
require ../present/print-forth.fs
require ./errors.fs

lf-pres-declaration-capacity constant lfa-decl-capacity
\ The kind of a library constant's record, after print-forth.fs's kinds.
lf-decl-stub 1+ constant lfa-decl-library

begin-structure /lfa-decl
  /lf-fdecl +field lfa-decl-print   \ the printer's view; first, so a record is one
  field: lfa-decl-notes             \ index of its first label or note
  field: lfa-decl-notes-end         \ index after its last one
  field: lfa-decl-at                \ position of its declaration word
  field: lfa-decl-height            \ a library definition's height (Lean's hint), else 0
end-structure
lfa-decl-capacity /lfa-decl 0 context-store: lfa-decls

: lfa-decl ( i -- decl ) lfa-decls store-slot ;
: lfa-decl-count ( -- n ) lfa-decls store-count @ ;
\ A new, zeroed record; too many declarations stop the run.
: lfa-decl-new ( -- i )
  lfa-decls store-new lfa-e-entries-full lfa-must dup lfa-decl /lfa-decl erase ;
: lfa-decl-name ( i -- name ) lfa-decl lf-fdecl-name @ ;
: lfa-decl-universes ( i -- n ) lfa-decl lf-fdecl-universes @ ;
: lfa-decl-kind ( i -- kind ) lfa-decl lf-fdecl-kind @ ;
: lfa-library? ( i -- flag ) lfa-decl-kind lfa-decl-library = ;
\ The record of name, the file's or the library's: one at most, as no
\ declaration takes a name declared before (error 28), the library's too.
: lfa-decl-named? ( name i -- name flag ) lfa-decl-name over = ;
: lfa-decl-find ( name -- i true | false ) lfa-decl-count ['] lfa-decl-named? find-index ;
