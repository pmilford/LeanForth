\ Test driver for the whole-export LeanForth text (plan task 8.6.3): runs one
\ LeanForth file (written by `leanforth print --lf`) and prints, for
\ check_author.py, `ran: ok` and each declaration as the tree dump of dump.fs
\ with every line starting `term: `, or `ran: ` and the error. Unlike
\ report.fs it keeps no text, so it reads a file of any size.
\ Usage: gforth tests/author/terms.fs -e 's" FILE" terms-run bye'
\ Test-only; not a public interface.
require ../../src/author/runner.fs
require ./dump.fs

variable line-start
: term-out ( c-addr u -- )
  bounds ?do line-start @ if ." term: " then i 1 type i c@ 10 = line-start ! loop ;
: dump-all ( -- )
  ['] term-out is dump-out false dump-notes? ! true line-start !
  lf-author-count 0 ?do i lf-author-decl dump-decl loop ;
: room! ( -- )
  1000000 lf-term-capacity! drop 1000000 lf-level-capacity! drop 1000000 lf-name-capacity! drop
  1000000 lf-cref-capacity! drop ;
: terms-run ( c-addr u -- )
  room!
  ['] type lf-print-unicode lf-print-setup
  lf-author-begin lf-author-file dup ok?
  if drop ." ran: ok" cr dump-all exit then
  ." ran: " lf-author-error. ." ; outcome " outcome-text type cr ;
