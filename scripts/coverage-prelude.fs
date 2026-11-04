\ Block coverage for make coverage (plan task 1.4.1; scripts/coverage.py).
\ scripts/coverage-gforth.sh loads this file before a test's own files.
\ It loads Gforth 1.0's coverage.fs, which puts a counter on every basic
\ block of the code compiled after it, and makes Gforth write every
\ counter, as .cover-raw prints it (one line "file:line:column: count" per
\ block), to the file that the environment variable LF_COVERAGE_OUT names,
\ however the run ends:
\ - BYE, which Gforth also runs at the end of its input;
\ - (BYE), redefined for the code compiled after this file;
\ - each later command-line argument (a file or -e) runs under CATCH, so
\   that a THROW out of it, ABORT's -1 too (which Gforth then ends with
\   silently), first writes the counts and then passes on unchanged;
\ - DOERROR, which reports an uncaught THROW.
\ An error in writing is ignored on the error paths. The last write wins.
\ Without LF_COVERAGE_OUT nothing is written. It prints nothing itself.
\ Gforth 1.0 only: 0.7.3 has no coverage.fs. A development tool, never
\ loaded by src/main.fs. One variable holds the argument's word: Gforth
\ processes its arguments one at a time, in the main task.
require coverage.fs
: lf-cover-file ( -- c-addr u ) s" LF_COVERAGE_OUT" getenv ;
: lf-cover-write ( c-addr u -- )
  w/o create-file throw >r ['] .cover-raw r@ outfile-execute r> close-file throw ;
: lf-cover-save ( -- ) lf-cover-file dup if lf-cover-write else 2drop then ;
: lf-cover-saved ( -- ) ['] lf-cover-save catch drop ;
:noname ( -- ) lf-cover-save defers bye ; is bye
warnings @ warnings off
: (bye) ( n -- ) lf-cover-saved (bye) ;   \ the inner (bye) is the kernel's
warnings !
:noname ( throw-code -- ) lf-cover-saved defers DoError ; is DoError
variable lf-cover-option   \ the xt that processes the current argument
: lf-cover-run ( i*x -- j*x ) lf-cover-option @ catch ?dup if lf-cover-saved throw then ;
:noname ( c-addr u -- xt | 0 )
  defers process-option dup if lf-cover-option ! ['] lf-cover-run then ; is process-option
