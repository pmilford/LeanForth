\ Golden cases of the term printer. Each case builds one term with binder
\ names, kinds and levels exactly as tests/reference/printer-cases.lean
\ builds the same Lean expression, then prints it in the three modes as
\ lines mode<TAB>case<TAB>text. tests/present/check-golden.py compares the
\ output with print-cases.golden (make test); printer-differential.py
\ compares the unicode lines with Lean's own printing (make check).
require ./build.fs

: tab ( -- ) 9 emit ;
: mode-name ( options -- c-addr u )
  lf-print-mode-mask and case
    lf-print-ascii of s" ascii" endof lf-print-latex of s" latex" endof s" unicode" rot
  endcase ;
\ Print t with options as one line: mode, case name, text (or the outcome).
: line ( t c-addr u options -- )
  dup mode-name type tab mode type tab
  cap-reset fuel lf-print-term dup ok? 0=
  if ." outcome " . cr exit then drop cap type cr ;
\ Build a case with xt ( -- t ) in a fresh session, print it in each mode.
: run-case ( xt c-addr u options -- )
  >r 2>r fresh execute 2r> r>
  3 0 do 3 pick 3 pick 3 pick 3 pick i or line loop 2drop 2drop ;
: uni ( xt c-addr u -- ) 0 run-case ;
: univ ( xt c-addr u -- ) lf-print-universes run-case ;

include ./print-case-list.fs
bye
