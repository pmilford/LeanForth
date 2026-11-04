\ The Forth side of the inductive table's differential (plan task 5.2.1a;
\ ADR 0015 §13, test plan 1): tests/core/inductive-table.py writes each
\ case of tests/reference/inductive-expected.lean as the lean4export file
\ Lean's run printed, then a script that includes this file and runs
\ `s" FILE" table-case` for each. A case's file is staged (without a
\ manifest) and fed to the checker (src/import/feed.fs), every
\ declaration checked in a new environment by check-declaration (which
\ checks an inductive block with check-block.fs), and printed:
\   feed TAB outcome                    when the feed refuses the file;
\   check TAB d TAB code TAB step       after each check (d its first
\                                       declaration; code the diagnostic,
\                                       step check-block's for a block);
\   decl TAB d TAB name TAB outcome     for every declaration, afterwards;
\   case-end
\ A check that throws spends the main context (env-publish.fs, G-P6):
\ then "spent" is printed and Gforth ends, and the Python side starts a
\ new Gforth at the next case. The Python side compares the outcome of
\ each case's own declarations with the table. Test-only; nothing here
\ accepts anything.
require ../../src/import/feed.fs
require ../../src/kernel/check-declaration.fs

create table-stage /stage allot
create table-feed /feed allot
1000000 constant table-fuel
4096 constant table-deps
: table-must ( flag -- ) 0= abort" inductive-table: refused" ;
: tab ( -- ) 9 emit ;
\ A name as Lean prints it without escapes: components joined by dots.
: table-name ( id -- )
  dup 0= if drop exit then
  dup lf-name-prefix@ ?dup if recurse [char] . emit then
  dup lf-name-tag@ lf-name-tag-str = if lf-name-text type else lf-name-payload 0 .r then ;
\ The check of every declaration, reporting its diagnostic and step.
: table-check ( -- )
  lf-check-declaration
  ." check" tab lf-env-limit 0 .r tab lf-diag-code@ 0 .r tab lf-block-step@ 0 .r cr ;
: table-decl ( d -- )
  ." decl" tab dup 0 .r tab dup lf-input-name table-name tab
  lf-env-outcome outcome-text type cr ;
: table-decls ( -- ) lf-env-view drop lf-input-count 0 ?do i table-decl loop ;
: table-run ( -- )
  table-fuel lf-check-budget table-deps lf-env-new ok? table-must
  dup lf-env-use ok? table-must
  ['] table-check ['] lf-check-no-maker lf-env-run drop table-decls lf-env-free drop ;
: table-fed? ( -- flag )
  table-stage table-feed lf-feed dup ok? if drop true exit then
  ." feed" tab outcome-text type cr false ;
: table-case ( c-addr u -- )
  16 table-stage stage-init ok? table-must table-stage stage-load-unchecked
  dup ok? if drop table-fed? if table-run then
  else ." feed" tab outcome-text type cr then
  lf-name-viewed? if lf-name-detach then table-stage stage-free ." case-end" cr
  lf-env-spent? if ." spent" cr bye then ;
