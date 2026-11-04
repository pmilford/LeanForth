\ The declarations of an authoring run (ADR 0017 §8): one record per
\ theorem, def, axiom or import stub, in the order they ended. Each is a
\ constant later declarations can name: the record holds what the term
\ printer's Forth mode prints (kind, name, universe parameters, type and
\ value, print-forth.fs) and where its labels and notes are. Untrusted
\ authoring code; the checker receives terms, never these records.
\ State: the store lfa-decls, in the checker context (ADR 0009).

require ../lib/lib.fs
require ../present/binder-table.fs
require ../present/print-forth.fs
require ./errors.fs

lf-pres-declaration-capacity constant lfa-decl-capacity

begin-structure /lfa-decl
  /lf-fdecl +field lfa-decl-print   \ the printer's view; first, so a record is one
  field: lfa-decl-notes             \ index of its first label or note
  field: lfa-decl-notes-end         \ index after its last one
  field: lfa-decl-at                \ position of its declaration word
end-structure
lfa-decl-capacity /lfa-decl 0 context-store: lfa-decls

: lfa-decl ( i -- decl ) lfa-decls store-slot ;
: lfa-decl-count ( -- n ) lfa-decls store-count @ ;
\ A new, zeroed record; too many declarations stop the run.
: lfa-decl-new ( -- i )
  lfa-decls store-new lfa-e-entries-full lfa-must dup lfa-decl /lfa-decl erase ;
: lfa-decl-name ( i -- name ) lfa-decl lf-fdecl-name @ ;
: lfa-decl-universes ( i -- n ) lfa-decl lf-fdecl-universes @ ;
