\ Test support for the printer: build terms with binder names, constants
\ and levels directly, and capture what the printer sends to its sink.
\ Not a parser and not a public interface. Each word aborts the test run
\ when a constructor fails, so a test never prints a half-built term.
require ../support/tester.fs
require ../../src/present/term-printer.fs

: must ( flag -- ) 0= abort" build: constructor failed" ;
: must-ok ( outcome -- ) ok? must ;

\ A fresh session: empty names, levels, terms, references and side table.
\ Binder names are kept per node, so the term store's hash-consing
\ (compact-store plan step S3) is off, as it is for the print command.
: fresh ( -- )
  false lf-term-sharing!
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-pres-reset lf-ssession-begin must ;

\ Names: one more string component under a prefix; or a name read as Lean
\ reads one, a component per dot (HAdd.hAdd is HAdd, then hAdd), since
\ the printer writes a component holding a dot between « ».
: nm. ( prefix c-addr u -- id ) lf-name-str must ;
: nm-head# ( c-addr u -- n ) tuck [char] . byte-scan nip - ;
: nm-cut ( c u n -- c n c' u' ) >r over r@ 2swap r> 1+ /string ;
: nm-split ( prefix c-addr u -- id )
  begin 2dup nm-head# 2dup > while nm-cut 2>r nm. 2r> repeat drop nm. ;
: nm ( c-addr u -- id ) 0 -rot nm-split ;
: nm# ( prefix n -- id ) lf-name-num must ;

\ Terms. Binders take their name and kind from the side table.
: t-sort ( n -- t ) lf-term-sort must ;
: t-prop ( -- t ) 0 t-sort ;
: t-var ( i -- t ) lf-term-bvar must ;
: t-app ( f a -- t ) lf-term-app must ;
: t-lam ( dom body -- t ) lf-term-lam must ;
: t-pi ( dom body -- t ) lf-term-pi must ;
: named ( t kind c-addr u -- t ) nm swap 2 pick -rot lf-pres-binder! must-ok ;
: ex. ( t c-addr u -- t ) lf-binder-default -rot named ;
: im. ( t c-addr u -- t ) lf-binder-implicit -rot named ;
: si. ( t c-addr u -- t ) lf-binder-strict -rot named ;
: in. ( t c-addr u -- t ) lf-binder-instance -rot named ;

\ Levels and symbolic Sorts.
: lzero ( -- l ) 0 ;
: lsucc ( l -- l ) lf-level-succ must ;
: lparam ( c-addr u -- l ) nm lf-level-param must ;
: lmax ( l l -- l ) lf-level-max must ;
: limax ( l l -- l ) lf-level-imax must ;
: ssort ( l -- t ) lf-term-symbolic-sort must ;

\ Constants: a name and up to 8 universe arguments.
create cargs 16 cells allot
variable cargc
: args{ ( -- ) 0 cargc ! ;
: uarg ( l -- ) dup lf-level-identity must swap cargc @ 2* cells cargs + 2! 1 cargc +! ;
: t-const ( c-addr u -- t )
  nm lf-name-generation @ cargs cargc @ lf-cref-new must lf-cterm-new must drop ;
: declare ( t c-addr u -- ) nm swap lf-pres-declare must-ok ;

\ Capturing output.
create cap-buf 4096 allot
variable cap-len
: cap-reset ( -- ) 0 cap-len ! ;
: cap-sink ( c-addr u -- )
  dup cap-len @ + 4096 > abort" capture overflow"
  tuck cap-buf cap-len @ + swap move cap-len +! ;
: cap ( -- c-addr u ) cap-buf cap-len @ ;
: mode ( options -- ) ['] cap-sink swap lf-print-setup ;

\ Compare the captured text with the expected text; on a difference print
\ both and fail the run.
: expect-text ( c-addr u -- )
  2dup cap compare 0= if 2drop exit then
  cr ." expected: " type cr ." printed:  " cap type cr -1 throw ;
\ Print a term (or a statement) with ample fuel and check the outcome.
10000 constant fuel
: shows ( t c-addr u -- ) rot cap-reset fuel lf-print-term must-ok expect-text ;
: states ( t c-addr u -- ) rot cap-reset fuel lf-print-statement must-ok expect-text ;
