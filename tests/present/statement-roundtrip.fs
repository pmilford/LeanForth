\ The proof outline's LeanForth statement runs to the identical term (plan
\ task 8.6.2; run by tests/present/check_outline.py on every pinned example).
\ Reads two lines from standard input: a Lean export (tests/reference/NAME.
\ ndjson) and a file of LeanForth words, the blocks the outlines of that
\ export printed, in declaration order. The export is read as `leanforth
\ print` reads it (with the binder names, for the side table); each
\ declaration's type is dumped as a tree, by dump.fs, which does not use the
\ term printer, as the axiom of its own name that the block states; then
\ the words run through the authoring words in a new checker context and
\ the declarations they make are dumped the same way. The two dumps (every
\ node, index, level, constant, universe argument, binder name and kind)
\ must be equal. Prints "round trip: same", or DIFFERENT with both dumps.
\ Test-only; not a public interface.
require ../support/print-outline.fs
require ../author/report.fs

create export-path 256 allot  variable export-len
create words-path 256 allot  variable words-len
: path-line ( buffer -- u ) 256 stdin read-line throw 0= abort" statement-roundtrip: no line" ;

\ The checker's side: the export read, then each declaration's type dumped
\ as the statement's axiom.
: load-export ( -- ) export-path export-len @ po-reload ;
: dump-statements ( -- )
  lf-input-count 0 ?do i lf-input-decl lf-sf-fdecl dump-decl loop ;

\ The words' side, in a new context (report.fs's in-new-context).
: words-text ( -- c-addr u ) words-path words-len @ slurp-file ;
: second-dump ( -- outcome )
  lf-author-begin words-text lf-author-text dup ok? 0= if exit then drop
  dump2 dump2# capture-into dump-all outcome-ok ;

: report-trip ( outcome -- )
  dup ok? 0= if ." round trip: the words did not run (" outcome-text type ." )" cr
    lf-author-error. cr exit then drop
  dump1 dump1# @ dump2 dump2# @ same?
  if ." round trip: same" cr else ." round trip: DIFFERENT" cr ." checker:" cr
    dump1 dump1# @ type cr ." words:" cr dump2 dump2# @ type cr then ;

export-path path-line export-len !
words-path path-line words-len !
load-export
dump1 dump1# capture-into
' capture is dump-out
dump-statements
' second-dump in-new-context report-trip
bye
