\ Proof outlines from a Lean export in a Forth session (plan task 2.4.4;
\ ADR 0013 L7), for the outline's golden test (tests/present/outline-cases.fs)
\ and the user page's example (docs/user/PROOF_OUTLINE.md): the words of
\ src/cli/print.fs, which `leanforth print` uses too, without the command
\ line's manifest check and exit codes. po-file prints every declaration's
\ outline (detail: every step of its log) with the log at level terms;
\ po-run-file with the log options as they are, so that a test can set a
\ limit or level steps; po-check-file checks every declaration with the
\ log at level terms and prints nothing, leaving the last one's log. The
\ export is staged and fed as `leanforth check` does it, with print's hooks
\ (binder names and declaration lines); the stage and the input stay until
\ the next po-load or po-reload (ck-start frees the last run), so that a log
\ can be printed against its input after the environment is freed.
\ A file that cannot be read, or an environment that cannot be made, used
\ or freed, aborts. Test support.
\ State: none of its own (print.fs's and check-run.fs's).

require ../../src/cli/print.fs

100000 constant po-fuel
: po-one ( c-addr u detail i -- fault? )
  dup pr-step if 2drop 2drop true exit then swap pr-print drop false ;
: po-each ( c-addr u detail -- )
  lf-input-count 0 ?do i pr-due? if
    2 pick 2 pick 2 pick i po-one if ." the run stopped" cr leave then then
  loop drop 2drop ;
\ The export staged and fed (a new input, the last run's freed), without an
\ environment.
: po-reload ( c-addr u -- )
  po-fuel ck-start false pr-load ok? 0= abort" print-outline: not read" ;
\ The same, then an environment to check it in, made current.
: po-load ( c-addr u -- env )
  po-reload
  po-fuel lf-check-budget lf-env-pool-max lf-env-new ok? 0= abort" print-outline: no environment"
  dup lf-env-use ok? 0= abort" print-outline: environment not used" ;
: po-free ( env -- ) lf-env-free ok? 0= abort" print-outline: environment not freed" ;
: po-run-file ( c-addr u detail -- )
  >r 2dup po-load r> swap >r po-each r> po-free ;
: po-file ( c-addr u detail -- ) pr-log-on po-run-file ;
: po-check-file ( c-addr u -- )
  pr-log-on po-load lf-input-count 0 ?do i pr-due? if i pr-step if leave then then loop
  po-free ;
