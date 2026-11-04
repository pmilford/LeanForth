\ The proof outline from the command line (plan task 2.4.4; ADR 0013 L7):
\ read a lean4export NDJSON file with the test-only transport
\ (tests/support/ndjson-input.fs), check each declaration in turn with
\ check-declaration and the derivation log at level terms, and print each
\ one's proof outline (src/present/proof-outline.fs) or, with detail, every
\ step of its log. Used by `make print EXPORT=file.ndjson [DETAIL=1]`:
\   gforth tests/support/print-outline.fs -e 's" file" 0 po-file bye'
\ Binder names and kinds, each declaration's line in the file and each
\ constant's declared type go into the presentation side table
\ (src/present/binder-table.fs), which the checker never reads, in a third
\ pass over the file. Test-only transport, like make run-record: phase 3
\ (plan task 3.2.2) replaces it with the Forth importer and `leanforth print`.
\ State: the transport's (global, test-only), the declarations' lines
\ (po-lines) and the declaration counter of the third pass.

require ./ndjson-input.fs
require ../../src/present/proof-outline.fs

100000 constant po-fuel
create po-lines lf-input-capacity cells allot
variable po-decls

\ The third pass: names and kinds of binders, sources of expressions,
\ lines and declared types of declarations.
: po-binder ( record -- outcome )
  dup record-index @ ni-root over binder-name @ ni-name rot binder-info @ lf-pres-binder! ;
: po-expr ( record -- outcome ) dup record-index @ ni-root swap record-index @ lf-pres-source! ;
: po-bound ( record -- outcome )
  dup po-expr ok? 0= if drop outcome-ok exit then po-binder drop outcome-ok ;
: po-source ( record -- outcome ) po-expr drop outcome-ok ;
: po-decl ( record -- outcome )
  po-decls @ dup lf-input-capacity < 0= if 2drop outcome-full exit then
  over record-line @ swap cells po-lines + ! 1 po-decls +!
  dup decl-name @ ni-name swap decl-type @ ni-root lf-pres-declare drop outcome-ok ;
create po-third
  ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler ,
  ' ok-handler , ' po-source , ' po-source , ' po-source , ' po-source , ' po-bound ,
  ' po-bound , ' po-source , ' po-source , ' po-source , ' po-source , ' po-source ,
  ' po-decl , ' po-decl , ' po-decl , ' po-decl , 0 , 0 , 0 , 0 , 0 ,
: po-present ( c-addr u -- outcome )
  0 po-decls ! lf-pres-reset ni-export export-init dup ok? 0= if nip nip exit then drop
  po-third ni-pass ni-export export-free ;

\ Check declaration i with the log on, then print its outline (detail:
\ every step) from a view of the environment.
: po-line ( i -- line ) cells po-lines + @ ;
: po-step ( i -- fault? ) ['] lf-check-declaration swap lf-env-step nip ;
\ The verdict of declaration i, read in a view of the environment: its
\ outcome and, when accepted, its axiom set (-1 otherwise).
: po-verdict ( i -- outcome axioms )
  lf-env-view drop dup lf-env-outcome swap lf-env-axioms ok? 0= if drop -1 then ;
: po-print ( c-addr u i detail -- )
  >r dup >r po-line lf-outline-source r> po-verdict r> lf-outline ;
: po-each ( c-addr u detail -- )
  lf-input-count 0 ?do i po-step if ." the run stopped" cr leave then
    2 pick 2 pick i 3 pick po-print loop drop 2drop ;
: po-run ( c-addr u detail env -- ) >r po-each r> lf-env-free drop ;
\ Read the export file c-addr u and print every declaration's outline,
\ or with detail true every step of its log, with the log options as they
\ are (a level other than off; tests set limits or level steps).
: po-run-file ( c-addr u detail -- )
  >r 2dup ni-read ok? 0= abort" print-outline: not read"
  2dup po-present ok? 0= abort" print-outline: names not read"
  po-fuel lf-check-budget
  64 lf-env-new ok? 0= abort" print-outline: no environment"
  dup lf-env-use drop r> swap po-run ;
\ The same with the log at level terms and every limit at its capacity,
\ which a complete outline needs.
: po-file ( c-addr u detail -- )
  lf-log-terms lf-log-set lf-log-capacities lf-log-limits po-run-file ;
\ The same, then leave Gforth with status 0 (make print); a file that
\ cannot be read aborts first (status 1 with no terminal input).
: po-exit ( c-addr u detail -- ) po-file 0 (bye) ;
