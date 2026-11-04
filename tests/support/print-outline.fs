\ Proof outlines from a Lean export in a Forth session (plan task 2.4.4;
\ ADR 0013 L7), for the outline's golden test (tests/present/outline-cases.fs)
\ and the user page's example (docs/user/PROOF_OUTLINE.md): the words of
\ src/cli/print.fs, which `leanforth print` uses too, without the command
\ line's manifest check and exit codes. po-file prints every declaration's
\ outline (detail: every step of its log) with the log at level terms;
\ po-run-file with the log options as they are, so that a test can set a
\ limit or level steps; po-check-file checks every declaration with the
\ log at level terms and prints nothing, leaving the last one's log. A
\ file that cannot be read, or an environment that cannot be made, used
\ or freed, aborts. Test support.
\ State: none of its own (print.fs's and checker-input's).

require ../../src/cli/print.fs

100000 constant po-fuel
: po-each ( c-addr u detail -- )
  lf-input-count 0 ?do i pr-step if ." the run stopped" cr leave then
    2 pick 2 pick i 3 pick pr-print drop loop drop 2drop ;
\ The export read (and read again for names) and an environment to check
\ it in, made current.
: po-load ( c-addr u -- env )
  2dup cin-read ok? 0= abort" print-outline: not read"
  false pr-present ok? 0= abort" print-outline: names not read"
  po-fuel lf-check-budget 64 lf-env-new ok? 0= abort" print-outline: no environment"
  dup lf-env-use ok? 0= abort" print-outline: environment not used" ;
: po-free ( env -- ) lf-env-free ok? 0= abort" print-outline: environment not freed" ;
: po-run-file ( c-addr u detail -- )
  >r 2dup po-load r> swap >r po-each r> po-free ;
: po-file ( c-addr u detail -- ) pr-log-on po-run-file ;
: po-check-file ( c-addr u -- )
  pr-log-on po-load lf-input-count 0 ?do i pr-step if leave then loop po-free ;
