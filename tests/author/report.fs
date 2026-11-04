\ Test driver for the authoring words (plan task 8.1.2): runs one LeanForth
\ file and reports, for check_author.py,
\   ran: ok, or the error and its outcome;
\   lean: each theorem, def and axiom as Lean's #print shows it (the term
\     printer's Unicode mode), compared with pinned Lean by check_author.py;
\   type: each import stub's type, in the same notation;
\   note: each note with the label of its step and its line;
\   words: every declaration printed as LeanForth words (print-forth.fs);
\   round trip: the printed words run again, in a new checker context,
\     and printed again: the terms (with binder names and kinds, levels,
\     constants and universe arguments, labels and notes, compared by an
\     independent tree dump, dump.fs) and the text must be the same.
\ Usage: gforth tests/author/report.fs -e 's" FILE" report bye'
\ The corpus tests (corpus-cases.fs, corpus-lean.fs) reuse its round trip.
\ Test-only; not a public interface.
require ../../src/author/runner.fs
require ./dump.fs

100000 constant print-fuel
: ok! ( outcome -- ) dup ok? if drop else ." (print failed: " outcome-text type ." )" then ;

\ The Lean notation, as #print shows it.
: .universes ( decl -- )
  dup lf-fdecl-universes @ ?dup 0= if drop exit then
  ." .{" 0 ?do i if ." , " then dup lf-fdecl-universe i cells + @ lf-print-name ok! loop drop
  ." }" ;
: .kind ( decl -- )
  lf-fdecl-kind @ case lf-decl-theorem of ." theorem" endof lf-decl-def of ." def" endof
    lf-decl-axiom of ." axiom" endof ." import-stub" endcase ;
: .type ( decl -- )
  dup lf-fdecl-type @ print-fuel rot lf-fdecl-kind @ lf-decl-theorem =
  if lf-print-statement else lf-print-term then ok! ;
: .head ( decl -- ) dup .kind space dup lf-fdecl-name @ lf-print-name ok! .universes ;
: .lean ( decl -- )
  ." lean: " dup .head ."  : " dup .type
  dup lf-fdecl-value @ 0< if drop cr exit then
  ."  :=" cr ." lean: " lf-fdecl-value @ print-fuel lf-print-term ok! cr ;
: .stub ( decl -- )
  dup lf-fdecl-type @ 0< if drop exit then
  ." type: " dup lf-fdecl-name @ lf-print-name ok! dup .universes ."  : " .type cr ;
: .declaration ( decl -- )
  dup lf-fdecl-kind @ lf-decl-stub = if .stub else .lean then ;

\ Notes: step NAME/LABEL (line L), by a person or an AI: TEXT.
: label-of ( term -- c-addr u )
  lf-note-count 0 ?do dup i lf-note-on? i lf-note-kind@ lf-note-label = and
    if drop i lf-note-text@ unloop exit then loop drop s" -" ;
: .who ( kind -- ) lf-note-person = if ." a person" else ." an AI" then ;
: .note ( decl i -- )
  ." note: " swap lf-fdecl-name @ lf-print-name ok! ." /" dup lf-note-term@ label-of type
  ."  (line " dup lf-note-source@ lfa-pos> drop 0 .r ." ), by " dup lf-note-kind@ .who ." : "
  lf-note-text@ type cr ;
: .notes ( i -- )
  dup lf-author-decl swap lf-author-notes swap ?do
    i lf-note-kind@ lf-note-label <> if dup i .note then loop drop ;

\ Captured text: the printed words and the dump, of the first run and of
\ the second.
16384 constant text-max
create words1 text-max allot  variable words1#
create words2 text-max allot  variable words2#
create dump1 text-max allot  variable dump1#
create dump2 text-max allot  variable dump2#
variable into   variable into#
: capture ( c-addr u -- )
  dup into# @ @ + text-max > abort" report: capture full"
  tuck into @ into# @ @ + swap move into# @ +! ;
: capture-into ( buffer count -- ) 0 over ! into# ! into ! ;
' capture is dump-out
: to-capture ( -- ) ['] capture lf-print-unicode lf-print-setup ;
: print-words ( -- outcome ) to-capture print-fuel lf-author-print ;
: dump-all ( -- ) lf-author-count 0 ?do i lf-author-decl dump-decl loop ;

\ The round trip, in a new context: the words of the first run (words1)
\ run there; they are printed and dumped again (words2, dump2). Each
\ context has its own printer settings, so the sink is set in both.
variable trip
: second-run ( -- outcome )
  lf-author-begin words1 words1# @ lf-author-text dup ok? 0= if exit then drop
  words2 words2# capture-into print-words dup ok? 0= if exit then drop
  dump2 dump2# capture-into dump-all outcome-ok ;
: in-new-context ( xt -- outcome )
  context-new throw dup trip ! context-use execute context-main context-use
  trip @ context-free throw ;
: same? ( a1 u1 a2 u2 -- flag ) compare 0= ;
: .same ( flag -- ) if ." same" else ." DIFFERENT" then ;
: .trip ( -- )
  ['] second-run in-new-context ['] type lf-print-unicode lf-print-setup
  dup ok? 0= if ." round trip: the printed words did not run (" outcome-text type ." )" cr
    exit then drop
  ." round trip: terms, names, kinds, labels and notes "
  dump1 dump1# @ dump2 dump2# @ same? .same
  ." ; printed text " words1 words1# @ words2 words2# @ same? .same cr ;
\ The round trip of what print-xt ( -- outcome ) prints and dump-xt ( -- )
\ dumps in the current context.
: round-trip-of ( print-xt dump-xt -- )
  >r words1 words1# capture-into execute dup ok? 0= if r> drop ['] type lf-print-unicode
    lf-print-setup ." round trip: the words could not be printed (" outcome-text type ." )"
    cr exit then drop
  dump1 dump1# capture-into r> execute .trip ;
: round-trip ( -- ) ['] print-words ['] dump-all round-trip-of ;

: .printed ( -- )
  ." words:" cr ['] type lf-print-unicode lf-print-setup print-fuel lf-author-print dup ok?
  if drop else cr ok! cr then ;
: report-run ( -- )
  ['] type lf-print-unicode lf-print-setup
  lf-author-count 0 ?do i lf-author-decl .declaration i .notes loop .printed round-trip ;
: report ( c-addr u -- )
  lf-author-begin lf-author-file dup ok?
  if drop ." ran: ok" cr report-run exit then
  ." ran: " lf-author-error. ." ; outcome " outcome-text type cr ;
