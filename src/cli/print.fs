\ Proof outlines from a Lean export (plan task 2.4.4; ADR 0013 L7): the
\ words behind `leanforth print` (cli/leanforth.fs) and make print
\ (tests/support/print-outline.fs). After the export is read into the
\ checker's input (import/checker-input.fs), pr-present reads it once more
\ and puts binder names and kinds, each expression's source and each
\ declaration's line and declared type into the presentation side table
\ (present/binder-table.fs), which the checker never reads; with the
\ manifest checked, that read checks it again, so names come from the
\ bytes checked; without it (--no-manifest), the file could change between
\ the two reads and binder names (only names) could come from other bytes.
\ Then each declaration is checked in turn, through the checked
\ environment's serial step (lf-env-step) with the derivation log at
\ level terms and every limit at its capacity, and its outline
\ (present/proof-outline.fs) printed right after its check, while its log
\ is still in the context.
\
\ Untrusted presentation code: nothing here decides or changes a verdict;
\ the verdict printed is the published slot's (lf-env-outcome), with its
\ label and axioms, and the log is the checker's; the outline printer
\ itself refuses a log that does not agree with that verdict, a
\ declaration not accepted, and a log truncated or kept without formulas.
\ The printer's scratch between checks advances the stores' identity
\ serials, so a diagnostic whose numbers are identities or serials (codes
\ 8, 21, 25, 27) can differ from check's for a later declaration; no
\ verdict depends on them.
\ State: one record in the checker context, print-state: the line of each
\ declaration in the file, the declarations the extra read counted, and
\ the text of a declaration's name being compared.

require ../lib/lib.fs
require ../core/input.fs
require ../core/derivation-log.fs
require ../kernel/environment.fs
require ../kernel/env-publish.fs
require ../kernel/check-declaration.fs
require ../import/ndjson.fs
require ../import/checker-input.fs
require ../present/binder-table.fs
require ../present/print-names.fs
require ../present/proof-outline.fs

256 constant pr-text-capacity
begin-structure /pr
  field: pr-decls                       \ declarations the extra read counted
  field: pr-text-used                   \ bytes of the name text
  lf-input-default cells +field pr-lines   \ each declaration's line in the file
  pr-text-capacity +field pr-text
end-structure
/pr context-record: print-state

\ The extra read: binders' names and kinds, sources of expressions, lines
\ and declared types of declarations (checker-input's tables give the
\ indices). Every other record passes; a side-table refusal only leaves a
\ name out.
: pr-binder ( record -- outcome )
  dup record-index @ cin-root over binder-name @ cin-name rot binder-info @
  lf-pres-binder! ;
: pr-expr ( record -- outcome )
  dup record-index @ cin-root swap record-index @ lf-pres-source! ;
: pr-bound ( record -- outcome )
  dup pr-expr ok? 0= if drop outcome-ok exit then pr-binder drop outcome-ok ;
: pr-source ( record -- outcome ) pr-expr drop outcome-ok ;
: pr-line! ( line k -- ) cells print-state pr-lines + ! ;
: pr-decl ( record -- outcome )
  print-state pr-decls @ dup lf-input-default < 0= if 2drop outcome-full exit then
  over record-line @ swap pr-line! 1 print-state pr-decls +!
  dup decl-name @ cin-name swap decl-type @ cin-root lf-pres-declare drop outcome-ok ;
create pr-handlers
  ' cin-pass-by , ' cin-pass-by , ' cin-pass-by , ' cin-pass-by , ' cin-pass-by ,
  ' cin-pass-by , ' cin-pass-by , ' pr-source , ' pr-source , ' pr-source ,
  ' pr-source , ' pr-bound , ' pr-bound , ' pr-source , ' pr-source ,
  ' pr-source , ' pr-source , ' pr-source , ' pr-decl , ' pr-decl ,
  ' pr-decl , ' pr-decl , ' cin-pass-by , ' cin-pass-by , 0 , 0 , 0 ,
pr-handlers cin-table-check
: pr-reader ( checked? -- xt ) if ['] cin-checked else ['] cin-plain then ;
: pr-read ( c-addr u checked? -- outcome )
  pr-reader pr-handlers cin-handlers execute ;
\ Read the export c-addr u again into the side table, its manifest
\ checked when checked? is true: ok, or the reader's outcome.
: pr-reset ( -- ) 0 print-state pr-decls ! lf-pres-reset ;
: pr-present ( c-addr u checked? -- outcome )
  pr-reset cin-init dup ok? 0= if nip nip nip cin-done exit then drop pr-read cin-done ;

\ A declaration's name as text, and the declaration named by a text.
: pr-used ( -- addr ) print-state pr-text-used ;
: pr-put ( c-addr u -- )
  pr-used @ over + pr-text-capacity > if 2drop exit then
  tuck print-state pr-text pr-used @ + swap move pr-used +! ;
: pr-name ( i -- c-addr u )
  0 pr-used ! lf-input-name ['] pr-put lf-pp-name-to print-state pr-text pr-used @ ;
\ The first declaration named c-addr u: (i true), or false.
: pr-find ( c-addr u -- i true | false )
  lf-input-count 0 ?do 2dup i pr-name compare 0= if 2drop i true unloop exit then loop
  2drop false ;

\ Checking declaration i (lf-env-step): whether the run must stop, as
\ check's does: a fault, or a THROW in the check (the context spent).
: pr-step ( i -- fault? )
  ['] lf-check-declaration swap lf-env-step nip lf-env-spent? or ;
\ Whether declaration i is still to check: not already published by the
\ check of its inductive block's first member (as the environment's own
\ run skips it, lf-env-next), whose log and outline cover the block.
: pr-due? ( i -- flag ) lf-env-published? 0= ;
\ Its verdict, read in a view of the environment: the outcome and, when
\ accepted, the axiom set (-1 otherwise); invalid when no view can be had.
: pr-verdict ( i -- outcome axioms )
  lf-env-view ok? 0= if drop outcome-invalid -1 exit then
  dup lf-env-outcome swap lf-env-axioms ok? 0= if drop -1 then ;
: pr-line ( i -- line )
  dup print-state pr-decls @ < if cells print-state pr-lines + @ else drop 0 then ;
\ Print the outline of declaration i of the export c-addr u (detail:
\ every step of its log), right after its check; its outcome.
: pr-print ( c-addr u i detail -- outcome )
  >r dup >r pr-line lf-outline-source r> pr-verdict over r> swap >r lf-outline r> ;
\ The log every later check writes: level terms, every limit at its
\ capacity, which a complete outline needs (set outside jobs).
: pr-log-on ( -- ) lf-log-terms lf-log-set lf-log-capacities lf-log-limits ;
