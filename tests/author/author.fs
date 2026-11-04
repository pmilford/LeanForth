\ Unit tests of the LeanForth authoring words (plan task 8.1.2): every
\ error code that a proof can reach, with its line and column (and the
\ second position where there is one); names that differ only in case;
\ Forth's own words invisible in proof text; namespaces, open and the
\ ambiguity error; var# and root:; source positions on nodes; labels and
\ notes; the runner restoring the caller's settings; the note table and
\ the printer's Forth mode on their own. The 19 example files and their
\ round trips are in check_author.py.
require ../support/tester.fs
require ../../src/author/runner.fs

: run ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: see-pos ( -- line col ) lfa-error lfa-err-see @ lfa-pos> ;
: fails ( c-addr u -- code line col ) run drop err ;

\ Text built by repeating a phrase, for the store limits.
create text 32768 allot  variable text#
: text0 ( -- ) 0 text# ! ;
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: times ( c-addr u n -- ) 0 ?do 2dup text+ loop 2drop ;
: text$ ( -- c-addr u ) text text# @ ;

\ A whole declaration runs; so do the example files (check_author.py).
T{ s" theorem t Prop explicit: p p := p end t" run -> outcome-ok }T
T{ lf-author-count -> 1 }T
T{ lf-author-code -> 0 }T

\ Forth's own words are invisible: each is an unknown name at its column.
T{ s" theorem t Prop explicit: p p dup := p end t" fails -> 1 1 30 }T
T{ s" theorem t Prop explicit: p p := p p + end t" fails -> 1 1 37 }T
T{ s" theorem t Prop explicit: p p := swap p end t" fails -> 1 1 33 }T
T{ s" : x ; theorem t" fails -> 1 1 1 }T
T{ s\" theorem t\n  CHAR Prop" fails -> 1 2 3 }T
\ Syntax words are case-sensitive too.
T{ s" theorem t PROP := Prop end t" fails -> 1 1 11 }T
T{ s" theorem t Prop explicit: p P := p end t" fails -> 1 1 28 }T

\ Names that differ only in case: x : X, a variable named prop, the
\ constants id and Id.
T{ s" def f 0 Type implicit: X X explicit: x X := x end f" run -> outcome-ok }T
T{ s" def f Prop explicit: prop Prop := prop end f" run -> outcome-ok }T
T{ s" import-stub id end id import-stub Id end Id def f id Id $ := Id end f" run
   -> outcome-ok }T
T{ s" import-stub Nat end Nat def f Prop explicit: nat Nat := nat end f" run
   -> outcome-ok }T

\ The error codes a proof can reach, each at its token.
T{ s" theorem t Prop explicit:" fails -> 2 1 16 }T
T{ s" theorem t $" fails -> 3 1 11 }T
T{ s" theorem t Prop Prop explicit: x $ fun" fails -> 3 1 33 }T
T{ s" Prop" fails -> 4 1 1 }T
T{ s" theorem t 0 1 level-max explicit: x" fails -> 5 1 25 }T
T{ s" theorem t Prop Type" fails -> 6 1 16 }T
T{ s" theorem t universe u u := u end t" fails -> 7 1 24 }T
T{ s" theorem t Prop explicit: x x Sort" fails -> 8 1 30 }T
T{ s" theorem t Prop 0 ^" fails -> 9 1 18 }T
: universes ( n -- ) 0 ?do s"  universe u" text+ i 0 <# #s #> text+ loop ;
text0 s" import-stub c" text+ 8 universes s"  end c theorem t c" text+ s"  0 ^" 9 times
T{ text$ fails -> 10 1 text# @ }T
T{ s\" def d universe u u Sort := u Sort end d\ntheorem t d Prop $ := Prop end t" fails
   -> 11 2 18 }T
T{ see-pos -> 2 11 }T
T{ s" theorem t Prop explicit: x Prop Prop fun" fails -> 12 1 38 }T
T{ see-pos -> 1 16 }T
T{ s" theorem t Prop fun" fails -> 13 1 16 }T
T{ s" theorem t Prop explicit: x Prop := x fun" fails -> 13 1 38 }T
T{ s" theorem t theorem u" fails -> 14 1 11 }T
T{ s" 0 theorem t" fails -> 15 1 3 }T
T{ s" theorem t Prop explicit: p universe u" fails -> 16 1 28 }T
T{ s" axiom a Prop :=" fails -> 17 1 14 }T
T{ s" :=" fails -> 17 1 1 }T
T{ s" theorem t :=" fails -> 18 1 11 }T
T{ s" theorem t Prop end t" fails -> 19 1 16 }T
T{ s" theorem t Prop := end t" fails -> 20 1 19 }T
T{ s" theorem t Prop := Prop explicit: x x end t" fails -> 21 1 38 }T
T{ see-pos -> 1 24 }T
T{ s" theorem t Prop := Prop end u" fails -> 22 1 24 }T
T{ s" namespace A end B" fails -> 22 1 13 }T
T{ s" end A" fails -> 23 1 1 }T
T{ s" theorem t namespace A" fails -> 24 1 11 }T
T{ s" theorem t open A" fails -> 24 1 11 }T
text0 s"  namespace A" lfa-space-capacity 1+ times
T{ text$ fails -> 25 1 lfa-space-capacity 1+ 12 * }T
T{ s" open Nope" fails -> 26 1 6 }T
T{ s" import-stub c end c import-stub A.c end A.c namespace A theorem t c" fails
   -> 27 1 67 }T
T{ s" import-stub A.c end A.c import-stub B.c end B.c open A open B theorem t c" fails
   -> 27 1 73 }T
T{ s" import-stub c end c import-stub c" fails -> 28 1 33 }T
T{ s" theorem t universe u universe u" fails -> 28 1 31 }T
T{ s" theorem t Prop label: a label: a" fails -> 29 1 32 }T
T{ s" theorem t Prop explicit: a..b" fails -> 30 1 26 }T
T{ s" theorem t Prop explicit: .a" fails -> 30 1 26 }T
T{ s" theorem t Prop explicit: a." fails -> 30 1 26 }T
T{ s" theorem t 5 var#" fails -> 31 1 13 }T
T{ s" theorem t Prop explicit: p p var#" fails -> 32 1 30 }T
T{ s" theorem t universe u u Prop level+" fails -> 32 1 29 }T
T{ s" theorem t Prop" fails -> 33 1 11 }T
T{ s" 7" fails -> 33 1 1 }T
T{ s" theorem t -5 Prop $" fails -> 34 1 19 }T
T{ s\" theorem t Prop note\" an open note" fails -> 37 1 16 }T
T{ s" theorem t root: c" fails -> 38 1 17 }T
T{ s" theorem t 5 Prop ->" fails -> 50 1 18 }T
T{ s" theorem t Prop let" fails -> 51 1 16 }T
T{ s" theorem t Prop explicit: x by" fails -> 51 1 28 }T
T{ s\" theorem t s\" text\"" fails -> 51 1 11 }T
T{ s" import Mathlib" fails -> 51 1 1 }T
T{ s" theorem t _" fails -> 52 1 11 }T
T{ s" theorem _root_.t" fails -> 53 1 9 }T
\ Outcomes: invalid for mistakes, unsupported for forms not built yet,
\ full for stores out of room.
T{ s" theorem t Prop let" run -> outcome-unsupported }T
T{ s" theorem t 999 Type" run -> outcome-full }T
T{ lf-author-code -> 61 }T
\ Out of room, one code per store or table.
text0 s" theorem t Prop" text+ s"  Prop ->" 64 times
T{ text$ fails drop drop -> 60 }T
text0 s" theorem t" text+ s"  Prop explicit: a" 65 times
T{ text$ fails drop drop -> 65 }T
text0 s" theorem t" text+ s"  Prop" 513 times
T{ text$ fails drop drop -> 64 }T
text0 s" theorem t Prop" text+ s\"  note\" n\"" 65 times
T{ text$ fails drop drop -> 67 }T
text0 s" import-stub c end c " 33 times
T{ text$ fails drop drop -> 28 }T
: stubs ( n -- ) 0 ?do s" import-stub c" text+ i 0 <# #s #> text+ s"  end c" text+
  i 0 <# #s #> text+ s"  " text+ loop ;
text0 33 stubs
T{ text$ fails drop drop -> 66 }T
: binders ( n -- ) 0 ?do s"  Prop explicit: x" text+ i 0 <# #s #> text+ s" .y" text+ loop ;
text0 s" theorem t" text+ 35 binders
T{ text$ fails drop drop -> 62 }T
: levels ( n -- ) 1+ 1 ?do s"  c " text+ i 0 <# #s #> text+ s"  ^ $" text+ loop ;
text0 s" import-stub c universe u end c theorem t c 0 ^" text+ 32 levels
T{ text$ fails drop drop -> 63 }T
\ A file that cannot be opened.
T{ lf-author-begin s" tests/author/no-such-file.lf" lf-author-file -> outcome-invalid }T
T{ lf-author-code -> 40 }T
\ A floating-point number is not a LeanForth value.
[defined] fdepth [if]
T{ s" theorem t 1e Prop := Prop end t" fails -> 35 1 27 }T
[then]
\ A LeanForth word run other than by the text interpreter.
lf-author-begin
T{ s" Prop" lf-words search-wordlist drop ' execute catch nip -> lf-author-throw }T
T{ lf-author-code -> 36 }T

\ Namespaces and open: full names, short names inside, open, the
\ namespace of a constant's prefix, dotted namespace names.
T{ s" namespace A import-stub c end c end A theorem t A.c := A.c end t" run
   -> outcome-ok }T
T{ s" import-stub A.c end A.c open A theorem t c := c end t" run -> outcome-ok }T
T{ s" namespace A.B import-stub c end c end A.B theorem t A.B.c := A.B.c end t" run
   -> outcome-ok }T
T{ s" namespace A.B theorem t Prop := Prop end t end A.B namespace A theorem u B.t := B.t end u"
   run -> outcome-ok }T
T{ s" namespace A.B end A" fails -> 22 1 15 }T
T{ s" namespace A import-stub c end c namespace B theorem t c := c end t end B end A" run
   -> outcome-ok }T
T{ s" import-stub A.B.c end A.B.c namespace A open B theorem t c := c end t end A" run
   -> outcome-ok }T

\ var# and root:.
T{ s" def f Prop explicit: x Prop explicit: x 1 var# fun fun := Prop end f" run
   -> outcome-ok }T
T{ s" import-stub x end x def f Prop explicit: x root: x := x end f" run -> outcome-ok }T

\ Source positions: line times 65536 plus column, on every node.
T{ s\" theorem t\n  Prop explicit: p\n  p\n:=\n  p\nend t" run -> outcome-ok }T
: type@ ( -- term ) 0 lf-author-decl lf-fdecl-type @ ;
T{ type@ lf-pres-source@ -> 2 lfa-line-unit * 8 + true }T
T{ type@ lf-term-first@ lf-pres-source@ -> 2 lfa-line-unit * 3 + true }T
T{ type@ lf-term-second@ lf-pres-source@ -> 3 lfa-line-unit * 3 + true }T

\ Labels and notes: kept on the step, with its kind and position; a
\ shared node is given a node of its own first.
T{ s\" theorem t Prop explicit: p p := p label: a ai-note\" why\" end t" run -> outcome-ok }T
T{ lf-note-count -> 2 }T
T{ 0 lf-note-kind@ 1 lf-note-kind@ -> lf-note-label lf-note-ai }T
T{ 0 lf-note-text@ s" a" compare -> 0 }T
T{ 0 lf-note-term@ 1 lf-note-term@ = -> true }T
T{ 0 lf-author-decl lf-fdecl-value @ lf-term-second@ 0 lf-note-term@ = -> true }T
T{ 0 lf-author-decl lf-fdecl-type @ lf-term-second@ 0 lf-note-term@ = -> false }T
T{ 0 lf-note-source@ lfa-pos> -> 1 35 }T
T{ 0 lf-author-notes -> 0 2 }T

\ The runner restores the caller's BASE, search order and wordlist, also
\ after an error; in hexadecimal, a stays a name.
hex
T{ s" def f Prop explicit: a a := a end f" run -> outcome-ok }T
T{ base @ -> 10 }T
decimal
: order# ( -- n ) get-order dup >r 0 ?do drop loop r> ;
: first-wid ( -- wid ) get-order over >r 0 ?do drop loop r> ;
: order-pair ( -- n wid ) order# first-wid ;
: same-order? ( -- f1 f2 ) order-pair s" Prop" run drop order-pair rot = >r = r> ;
T{ same-order? -> true true }T
T{ get-current s" theorem t" run drop get-current = -> true }T

\ The note table on its own.
lf-author-begin
T{ 0 lf-term-sort drop -> 0 }T
T{ s" x" lf-note-person 0 lf-note-add -> 0 outcome-ok }T
T{ s" x" 7 0 lf-note-add -> -1 outcome-invalid }T
T{ s" x" lf-note-person 5 lf-note-add -> -1 outcome-invalid }T
T{ 0 lf-note-live? 0 lf-note-any? -> true true }T
T{ 0 lf-term-sort drop dup 0 swap lf-note-move lf-note-any? -> true }T
T{ 0 lf-note-any? -> false }T
T{ s" y" lf-note-label 1 lf-note-add -> 1 outcome-ok }T
T{ s" y" 0 lf-note-label? s" y" 2 lf-note-label? s" z" 0 lf-note-label? -> true false false }T
lf-term-reset
T{ 0 lf-note-live? -> false }T
lf-note-reset
T{ lf-note-count -> 0 }T

\ The printer's Forth mode for a term on its own.
create fout 256 allot  variable fout#
: fout+ ( c-addr u -- ) tuck fout fout# @ + swap move fout# +! ;
: forth-text ( term -- c-addr u outcome )
  0 fout# ! ['] fout+ lf-print-unicode lf-print-setup 1000 lf-print-forth-term >r fout fout# @ r> ;
T{ s" def f Prop explicit: x x fun := Prop end f" run -> outcome-ok }T
T{ 0 lf-author-decl lf-fdecl-type @ forth-text rot rot s" Prop explicit: x x fun" compare
   -> outcome-ok 0 }T
T{ 0 lf-author-decl lf-fdecl-type @ -1 lf-print-forth-term -> outcome-invalid }T
T{ 0 lf-author-decl lf-fdecl-type @ 1 lf-print-forth-term -> outcome-exhausted }T
T{ 99 1000 lf-print-forth-term -> outcome-invalid }T
' type lf-print-unicode lf-print-setup

cr .( author.fs: all tests passed) cr
bye
