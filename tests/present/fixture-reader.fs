\ Test-only reader of the printer transport (present_transport.py): reads
\ it with fixture-read.fs and prints every declaration as Lean's #print
\ does, in the Unicode, ASCII and LaTeX modes. Malformed or truncated
\ input aborts before anything is printed for it.
require ./fixture-read.fs

\ Printing as #print does: kind, name with universe parameters, type, value.
: print-ok ( outcome -- ) ok? 0= abort" fixture: print failed" ;
: print-params ( d -- )
  dup decl-params# @ ?dup 0= if drop exit then
  ." .{" 0 ?do i
  if ." , " then dup decl-params i cells + @ lf-print-name print-ok loop drop ." }" ;
: print-type ( d -- )
  dup decl-type @ fuel rot decl-kind @
  if lf-print-statement else lf-print-term then print-ok ;
: print-decl ( d -- )
  dup decl-kind @ if ." theorem " else ." def " then
  dup decl-name @ lf-print-name print-ok dup print-params ."  : " dup print-type ."  :="
  cr
  decl-value @ fuel lf-print-term print-ok cr ;
: print-mode ( options c-addr u -- )
  ." -- " type cr ['] type swap lf-print-setup decls# @ 0 ?do i decl print-decl loop ;

fresh read-names read-levels read-terms read-decls at-end
lf-print-unicode s" unicode" print-mode
lf-print-ascii s" ascii" print-mode
lf-print-latex s" latex" print-mode
bye
