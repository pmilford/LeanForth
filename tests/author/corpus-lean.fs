\ The round trip over terms that Lean exported (plan task 8.1.2): reads a
\ pinned fixture's printer transport from stdin (tests/present/
\ fixture-read.fs, fed by check_author.py), prints every declaration as
\ LeanForth words, runs them in a new context and compares, as report.fs
\ does, the terms (binder names and kinds included; a Pi printed as ->
\ keeps no hygienic name, the stated exception) and the printed text.
\ Usage: python3 tests/present/present_transport.py FIXTURE.ndjson |
\        gforth tests/author/corpus-lean.fs
\ Test-only; not a public interface.
require ../present/fixture-read.fs
require ./report.fs

\ The reader's declarations as the printer's records.
create fdecls slots /lf-fdecl * allot
: fdecl ( i -- addr ) /lf-fdecl * fdecls + ;
: >kind ( reader-kind -- kind ) if lf-decl-theorem else lf-decl-def then ;
: fdecl-head! ( d f -- )
  false over lf-fdecl-protected !
  over decl-kind @ >kind over lf-fdecl-kind ! swap decl-name @ swap lf-fdecl-name ! ;
: fdecl-terms! ( d f -- )
  over decl-type @ over lf-fdecl-type ! swap decl-value @ swap lf-fdecl-value ! ;
: fdecl-universes! ( d f -- )
  over decl-params# @ over lf-fdecl-universes ! swap decl-params swap lf-fdecl-universe
  4 cells move ;
: fdecl! ( i -- )
  dup decl swap fdecl 2dup fdecl-head! 2dup fdecl-terms! fdecl-universes! ;

create blank-line 10 c,
: print-one ( i -- outcome )
  dup if blank-line 1 lf-pp-emit then fdecl print-fuel lf-print-forth-decl ;
: print-fdecls ( -- outcome )
  to-capture decls# @ 0 ?do i print-one dup ok? 0= if unloop exit then drop loop outcome-ok ;
: dump-fdecls ( -- ) decls# @ 0 ?do i fdecl dump-decl loop ;
: fdecls! ( -- ) decls# @ 0 ?do i fdecl! loop ;
: lean-trip ( -- ) fdecls! ['] print-fdecls ['] dump-fdecls round-trip-of ;

fresh read-names read-levels read-terms read-decls at-end
lean-trip
bye
