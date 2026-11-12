\ The library a checked run may name (plan task 8.2.1d; ADR 0017
\ Amendment 1, A4, and its Amendment 2): a Lean export the command line
\ has read (leanforth check --env EXPORT FILE.lf), whose constants the text
\ names by their Lean names. The run asks a finder its caller gives,
\ finder ( name -- universes height true | false ): whether one
\ declaration of the library has the full name name (an ID of the run's
\ name store, interned from the text: a candidate that is no name of the
\ library stays in the store, unused), its number of universe parameters,
\ and its height when it is a definition with regular hints (else 0). A
\ text that is not a name stops as such (error 30). A constant named for
\ the first time gets a
\ record in lfa-decls (constants.fs, kind lfa-decl-library), kept for the
\ run, so that it resolves as a file's constant does (namespaces.fs), with
\ two rules of its own:
\ - the export does not say which constants are protected, so a name of
\   one part that would reach a library constant through a namespace stops
\   with error 55, "write the full name": a temporary refusal where Lean
\   decides, until the export pipeline records protected (plan 8.2.1d);
\ - no declaration of the text may take a library constant's name (error
\   28, Lean's "already declared").
\ A checked run (lf-author-checked!) refuses import-stub (error 48, at the
\ word): a stub declares a constant no one checks. Every word of the
\ library's names is made by the runner's look-ahead (runner.fs). Untrusted
\ authoring code: a finder that answers wrongly makes the words build a
\ different term, which the checker checks as it is.
\ State: one context record, lfa-library (the finder, or 0, and whether
\ the run is checked).

require ../lib/lib.fs
require ./declarations.fs

begin-structure /lfa-library
  field: lfa-library-finder     \ xt ( c-addr u -- universes height true | false ), or 0
  field: lfa-library-checked    \ true: import-stub is refused
end-structure
/lfa-library context-record: lfa-library

\ Settings, kept until changed; a new context has neither.
: lf-author-library! ( finder|0 -- ) lfa-library lfa-library-finder ! ;
: lf-author-checked! ( flag -- ) lfa-library lfa-library-checked ! ;
: lfa-checked? ( -- flag ) lfa-library lfa-library-checked @ ;
: lfa-library-on? ( -- flag ) lfa-library lfa-library-finder @ 0<> ;

\ The record of the library constant of name, if one was made.
: lfa-library-is? ( name i -- flag )
  dup lfa-library? if lfa-decl-name = else 2drop false then ;
: lfa-library-decl? ( name -- decl true | false )
  lfa-decl-count 0 ?do dup i lfa-library-is? if drop i true unloop exit then loop
  drop false ;
\ A new record: the name, the number of universe parameters, the height.
: lfa-library-fields ( name universes height decl -- )
  tuck lfa-decl-height ! tuck lf-fdecl-universes ! tuck lf-fdecl-name !
  lfa-decl-library over lf-fdecl-kind ! -1 over lf-fdecl-type ! -1 swap lf-fdecl-value ! ;
: lfa-library-new ( name universes height -- decl )
  lfa-decl-new dup >r lfa-decl lfa-library-fields r> ;
\ The library's constant of full name c-addr u, its record made when new.
: lfa-library-found ( name -- universes height true | false )
  lfa-library lfa-library-finder @ execute ;
: lfa-library-new? ( name -- decl true | false )
  dup lfa-library-found if lfa-library-new true else drop false then ;
: lfa-library-lookup ( c-addr u -- decl true | false )
  lfa-library-on? 0= if 2drop false exit then
  lfa-intern dup lfa-library-decl? if nip true else lfa-library-new? then ;
' lfa-library-lookup is lfa-library-named
