\ Unit tests of the LeanForth authoring words (plan task 8.1.2): every
\ error code that a proof can reach, with its line and column (and the
\ second position where there is one); names that differ only in case;
\ Forth's own words forth-word-in-proof in proof text; numbers only as plain
\ decimals, the same tokens refused on every host; values used once;
\ names never number-like; namespaces, open and which constant a name
\ means, as Lean resolves it; var# and root:; source positions on nodes;
\ labels and notes; the runner restoring the caller's settings; the note
\ table and the printer's Forth mode on their own, which refuses labels
\ and notes it cannot spell. The 21 example files, their round trips and
\ the comparison with Lean are in check_author.py.
require ../support/tester.fs
require ../../src/author/runner.fs

: run ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: see-pos ( -- line col ) lfa-error lfa-err-see @ lfa-pos> ;
: fails ( c-addr u -- code line col ) run drop err ;

\ Text built by repeating a phrase, for the store limits.
131072 constant text-max
create text text-max allot  variable text#
: text0 ( -- ) 0 text# ! ;
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: times ( c-addr u n -- ) 0 ?do 2dup text+ loop 2drop ;
: text$ ( -- c-addr u ) text text# @ ;

\ A whole declaration runs; so do the example files (check_author.py).
T{ s" theorem t Prop explicit: p p := p end t" run -> outcome-ok }T
T{ lf-author-count -> 1 }T
T{ lf-author-code -> 0 }T

\ Forth's own words are forth-word-in-proof: each is an unknown name at its column.
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
T{ s" import-stub c end c import-stub X.c end X.c open X theorem t c" fails -> 27 1 62 }T
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
T{ s" theorem t -5 Prop $" fails -> 35 1 11 }T
T{ s\" theorem t Prop note\" an open note" fails -> 37 1 16 }T
T{ s" theorem t root: c" fails -> 38 1 17 }T
T{ s" theorem t 5 Prop ->" fails -> 50 1 18 }T
T{ s" theorem t Prop let" fails -> 51 1 16 }T
T{ s" theorem t Prop explicit: x by" fails -> 51 1 28 }T
T{ s\" theorem t s\" text\"" fails -> 51 1 11 }T
T{ s" import Mathlib" fails -> 51 1 1 }T
T{ s" theorem t _" fails -> 52 1 11 }T
T{ s" theorem _root_.t" fails -> 53 1 9 }T
\ A ( comment must close on its line, as a note must.
T{ s" theorem t Prop ( no close" fails -> 42 1 16 }T
T{ s\" theorem t\n  Prop ( the binder\n  explicit: p )\n  p := p end t" fails -> 42 2 8 }T
\ Names that are numbers: no universe, declaration or namespace name is
\ number-like as a whole token, so no word shadows a number; a numeric part
\ after the first is Name.num (no word is made for a part); a binder may
\ have a number-like name but gets no word.
T{ s" def big universe 1 2 Type := 1 Type end big" fails -> 30 1 18 }T
T{ s" def 0 Prop := Prop end 0" fails -> 30 1 5 }T
T{ s" def x.01 Prop := Prop end x.01" fails -> 30 1 5 }T
T{ s" namespace 1" fails -> 30 1 11 }T
T{ s" namespace -x" fails -> 30 1 11 }T
T{ s" def 1.x Prop := Prop end 1.x" fails -> 30 1 5 }T
T{ s" def a Prop explicit: 1 Prop := Prop end a def b 2 Type := 1 Type end b" run
   -> outcome-ok }T
T{ 1 lf-author-decl lf-fdecl-value @ lf-term-first@ -> 0 lfa-succ lfa-succ }T
T{ s" def c 2 Type := 1 Type end c" run -> outcome-ok }T
T{ s" def f Prop explicit: 1 1 := Prop end f" fails -> 50 1 26 }T
\ A numeric part is Name.num, a string part of digits (between guillemets) a
\ string; both stay distinct, and 0, 1 and -1 are still numbers afterwards.
: n1 ( -- name ) 0 s" N" lf-name-str drop ;
: n0 ( -- name ) n1 0 lf-name-num drop ;
: ns0 ( -- name ) n1 s" 0" lf-name-str drop ;
T{ s\" def N.0.f Prop := Prop end N.0.f def N.\xC2\xAB0\xC2\xBB.f Prop := Prop end N.\xC2\xAB0\xC2\xBB.f"
   run -> outcome-ok }T
T{ 0 lf-author-decl lf-fdecl-name @ lf-name-prefix@ -> n0 }T
T{ 1 lf-author-decl lf-fdecl-name @ lf-name-prefix@ -> ns0 }T
T{ n0 ns0 = -> false }T
T{ s" def a.0 Prop := Prop end a.0 def b 2 Type := 1 Type end b" run -> outcome-ok }T
T{ 1 lf-author-decl lf-fdecl-value @ lf-term-first@ -> 0 lfa-succ lfa-succ }T
T{ s" def a.0 Prop := Prop end a.0 def b -1 Type := Prop end b" fails -> 35 1 36 }T
\ A guillemet part holds only digits.
T{ s\" def N.\xC2\xAB0x\xC2\xBB.f Prop := Prop end N.\xC2\xAB0x\xC2\xBB.f" fails
   -> 30 1 5 }T
\ Numeric name parts have no leading zero (x.01 and x.1 are one Lean name).
T{ s" def f Prop explicit: x.01 Prop := Prop end f" fails -> 30 1 22 }T
T{ s" def f Prop explicit: x.10 Prop := Prop end f" run -> outcome-ok }T
\ A value left below a parameter's binder: the statement is not one term.
T{ s\" theorem t\n  Prop implicit: A\n  A\n  A explicit: a\n  A\n:=\n  a\nend t" fails
   -> 18 6 1 }T
T{ see-pos -> 4 5 }T
T{ s" axiom t Prop implicit: A A A explicit: a A end t" fails -> 18 1 44 }T
T{ see-pos -> 1 30 }T
\ Outcomes: invalid for mistakes, unsupported for forms not built yet,
\ full for stores out of room.
T{ s" theorem t Prop let" run -> outcome-unsupported }T
T{ s" theorem t 999 Type" run -> outcome-full }T
T{ lf-author-code -> 61 }T
\ Out of room, one code per store or table.
text0 s" theorem t Prop" text+ s"  Prop ->" 64 times
T{ text$ fails drop drop -> 60 }T
\ Binders grow (plan task 6.2.0): 65 open binders are not too many (the
\ text then ends unfinished, 33). A binder store at its limit, a setting
\ (here 16), is.
text0 s" theorem t" text+ s"  Prop explicit: a" 65 times
T{ text$ fails drop drop -> 33 }T
lfa-scope-close  16 lfa-binders store-limit! drop
text0 s" theorem t" text+ s"  Prop explicit: a" 17 times
T{ text$ fails drop drop -> 65 }T
lfa-scope-close  lfa-binder-limit lfa-binders store-limit! drop
text0 s" theorem t" text+ s"  Prop" 513 times
T{ text$ fails drop drop -> 64 }T
text0 s" theorem t Prop" text+ s\"  note\" n\"" 65 times
T{ text$ fails drop drop -> 67 }T
text0 s" import-stub c end c " 33 times
T{ text$ fails drop drop -> 28 }T
: stubs ( n -- ) 0 ?do s" import-stub c" text+ i 0 <# #s #> text+ s"  end c" text+
  i 0 <# #s #> text+ s"  " text+ loop ;
variable saved-names  lf-name-capacity saved-names !  100000 lf-name-capacity! drop
text0 lfa-decl-capacity 1+ stubs
T{ text$ fails drop drop -> 66 }T
lf-author-begin saved-names @ lf-name-capacity! drop
: binders ( n -- ) 0 ?do s"  Prop explicit: x" text+ i 0 <# #s #> text+ s" .y" text+ loop ;
text0 s" theorem t" text+ 35 binders
T{ text$ fails drop drop -> 62 }T
: levels ( n -- ) 1+ 1 ?do s"  c " text+ i 0 <# #s #> text+ s"  ^ $" text+ loop ;
text0 s" import-stub c universe u end c theorem t c 0 ^" text+ 32 levels
T{ text$ fails drop drop -> 63 }T
\ A file that cannot be opened.
T{ lf-author-begin s" tests/author/no-such-file.lf" lf-author-file -> outcome-invalid }T
T{ lf-author-code -> 40 }T
\ A Forth exception: very many numbers overflow Forth's data stack (-3 on
\ Gforth 1.0 and 0.7.3, at their default sizes), reported at the last token
\ a word read. (A line of 1024 characters in a file, error 39, is the
\ fixture 17-long-line.lf.)
text0 s" theorem t" text+ s"  1" 40000 times
T{ text$ fails -> 41 1 9 }T
T{ lfa-error lfa-err-number @ -> -3 }T
\ Numbers are plain decimals of at most 9 digits: every other form a Forth
\ host may read as a number is refused at its token, the same on every
\ host (Gforth 1.0 recognizes more forms than 0.7.3); a token that is no
\ number form is an unknown name.
T{ s" theorem t 1e Prop := Prop end t" fails -> 35 1 11 }T
T{ s" theorem t $10 Type" fails -> 35 1 11 }T
T{ s" theorem t 0x3 Type" fails -> 35 1 11 }T
T{ s" theorem t %11 Type" fails -> 35 1 11 }T
T{ s" theorem t #1 Type" fails -> 35 1 11 }T
T{ s" theorem t +2 Type" fails -> 35 1 11 }T
T{ s" theorem t 1. Type" fails -> 35 1 11 }T
T{ s" theorem t 'a' Type" fails -> 35 1 11 }T
T{ s" theorem t 2p Type" fails -> 35 1 11 }T
T{ s" theorem t 1234567890 Type" fails -> 35 1 11 }T
T{ s" theorem t 0 Type 1foo" fails -> 35 1 18 }T
T{ s" theorem t 0 Type := 0 Type 1foo" fails -> 35 1 28 }T
T{ s\" theorem t Prop \"x\" foo" fails -> 1 1 16 }T
T{ s" theorem t Prop ${HOME} foo" fails -> 35 1 16 }T
T{ s" theorem t Prop explicit: x Prop := Prop ->x end t" fails -> 35 1 41 }T
T{ s" theorem t Prop explicit: x Prop := Prop 'x end t" fails -> 35 1 41 }T
T{ s" theorem t Prop explicit: x Prop := Prop forth:dup end t" fails -> 1 1 41 }T
T{ s" def a 123456789 Type := Prop end a" fails -> 61 1 17 }T
T{ s" def a 007 Type := 7 Type end a" run -> outcome-ok }T
\ A forged value: each value is used once, and a variable only inside its
\ binder (the text cannot write a negative number; these use the words).
: forged ( value -- code )
  lfa-error-reset ['] lfa>term catch if drop lf-author-code else drop 0 then ;
lf-author-begin
lfa-kind-term 0 true lfa-item-new constant v
T{ v lfa>term -> 0 }T
T{ v forged -> 34 }T
T{ -7 forged -> 34 }T
lfa-kind-name 0 -1 lfa-item-new constant w
T{ w forged -> 34 }T
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
\ Which constant a name means, as pinned Lean 4.35.0 resolves it: the
\ namespace around wins, innermost first, over the root and the opened
\ namespaces; a dotted declaration name puts its body in its namespace;
\ namespace A.B is two scopes; open N opens A.N inside A, and O.N for
\ every open O. Each case was run in Lean; make check compares the same
\ cases with Lean's terms (16-namespaces.lf).
: const-of ( term -- name )
  dup lf-term-first@ swap lf-term-second@ lf-cref-read 0= abort" ref" 2drop ;
: value-const ( i -- name ) lf-author-decl lf-fdecl-value @ const-of ;
: name1 ( c-addr u -- name ) 0 -rot lf-name-str drop ;
: name+ ( name c-addr u -- name' ) lf-name-str drop ;
: A.c ( -- name ) s" A" name1 s" c" name+ ;
: A.B.c ( -- name ) s" A" name1 s" B" name+ s" c" name+ ;
: stubs-c ( -- c-addr u )
  s" import-stub c end c import-stub A.c end A.c import-stub A.B.c end A.B.c " ;
create ns-text 512 allot  variable ns-text#
: with-stubs ( c-addr u -- outcome )
  stubs-c ns-text swap move stubs-c nip ns-text# !
  tuck ns-text ns-text# @ + swap move ns-text# +! ns-text ns-text# @ run ;
T{ s" namespace A def t Prop := c end t end A" with-stubs -> outcome-ok }T
T{ 3 value-const -> A.c }T
T{ s" def A.t Prop := c end A.t" with-stubs -> outcome-ok }T
T{ 3 value-const -> A.c }T
T{ s" namespace A def B.t Prop := c end B.t def u Prop := c end u end A" with-stubs
   -> outcome-ok }T
T{ 3 value-const 4 value-const -> A.B.c A.c }T
T{ s" namespace A.B def t Prop := c end t end B def u Prop := c end u end A" with-stubs
   -> outcome-ok }T
T{ 3 value-const 4 value-const -> A.B.c A.c }T
T{ s" import-stub X.c end X.c namespace A open X def t Prop := c end t end A" with-stubs
   -> outcome-ok }T
T{ 4 value-const -> A.c }T
T{ s" def t Prop := A.c end t namespace A def u Prop := A.c end u end A" with-stubs
   -> outcome-ok }T
T{ 3 value-const 4 value-const -> A.c A.c }T
: open-b ( -- )
  text0 s" import-stub B.e end B.e import-stub A.B.g end A.B.g " text+
  s" namespace A open B def t Prop := " text+ ;
open-b s" g end t end A" text+
T{ text$ run -> outcome-ok }T
open-b s" e end t end A" text+
T{ text$ fails -> 1 1 86 }T
T{ s" import-stub Y.Z.h end Y.Z.h open Y open Z def t Prop := h end t" run
   -> outcome-ok }T
T{ 1 value-const -> s" Y" name1 s" Z" name+ s" h" name+ }T
\ protected, as in Lean (ResolveName.lean, resolveQualifiedName): through
\ a namespace, around or open, a name of one part never finds a protected
\ constant; a dotted name and the root do. Lean's own terms for these
\ cases: 18-protected.lf.
: prot-stubs ( -- )
  text0 s" import-stub bar end bar protected import-stub N.bar end N.bar " text+ ;
prot-stubs s" namespace N def t Prop := bar end t end N" text+
T{ text$ run -> outcome-ok }T
T{ 2 value-const 1 lf-author-decl lf-fdecl-protected @ -> s" bar" name1 true }T
prot-stubs s" def N.t Prop := bar end N.t" text+
T{ text$ run -> outcome-ok }T
T{ 2 value-const -> s" bar" name1 }T
prot-stubs s" namespace N def t Prop := N.bar end t end N" text+
T{ text$ run -> outcome-ok }T
T{ 2 value-const -> s" N" name1 s" bar" name+ }T
prot-stubs s" namespace M open N def t Prop := bar end t end M" text+
T{ text$ run -> outcome-ok }T
T{ 2 value-const -> s" bar" name1 }T
T{ s" protected import-stub N.bar end N.bar namespace N def t Prop := bar end t end N" fails
   -> 1 1 65 }T
T{ s" protected namespace N" fails -> 43 1 11 }T
T{ s" protected" fails -> 2 1 1 }T
T{ s" protected def t Prop := Prop end t" fails -> 44 1 15 }T
T{ s" namespace N protected def t Prop := Prop end t end N" run -> outcome-ok }T
T{ 0 lf-author-decl lf-fdecl-protected @ -> true }T
T{ s" protected axiom N.a Prop end N.a protected theorem N.t Prop := Prop end N.t" run
   -> outcome-ok }T
T{ 0 lf-author-decl lf-fdecl-protected @ 1 lf-author-decl lf-fdecl-protected @ -> true true }T
\ export makes aliases, which Lean's resolution also searches: not built.
T{ s" export N (x)" fails -> 54 1 1 }T
T{ s" namespace B end A.B" fails -> 23 1 13 }T
T{ s" namespace A namespace B end A.B def t Prop := Prop end t" run -> outcome-ok }T
T{ 0 lf-author-decl lf-fdecl-name @ -> s" t" name1 }T

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
[defined] rec-forth [if]
\ On Gforth 1.0 the interpreter's recognizer is restored too.
T{ action-of rec-forth s" Prop" run drop action-of rec-forth = -> true }T
T{ action-of rec-forth s" theorem t valeu" run drop action-of rec-forth = -> true }T
[then]

\ ---- The rules for running in the checker's own Gforth (plan task
\ 8.2.1a; ADR 0017 Amendment 1, A5), from probes p01, p03, p04, p05, p07.
\ Forth's own words are unknown names, wherever they stand (p01).
: forth-word-in-proof ( c-addr u -- code line col )
  text0 s" theorem t Prop explicit: p p := " text+ text+ s"  p end t" text+ text$ fails ;
T{ s" bye" forth-word-in-proof -> 1 1 33 }T
T{ s" evaluate" forth-word-in-proof -> 1 1 33 }T
T{ s" included" forth-word-in-proof -> 1 1 33 }T
T{ s" immediate" forth-word-in-proof -> 1 1 33 }T
T{ s" postpone" forth-word-in-proof -> 1 1 33 }T
T{ s" ]" forth-word-in-proof -> 1 1 33 }T
T{ s" [" forth-word-in-proof -> 1 1 33 }T
T{ s" state" forth-word-in-proof -> 1 1 33 }T
T{ s" here" forth-word-in-proof -> 1 1 33 }T
T{ s" !" forth-word-in-proof -> 1 1 33 }T
T{ s" execute" forth-word-in-proof -> 1 1 33 }T
T{ s" quit" forth-word-in-proof -> 1 1 33 }T
T{ s" set-order" forth-word-in-proof -> 1 1 33 }T
T{ s" forth-wordlist" forth-word-in-proof -> 1 1 33 }T
T{ s" forth:bye" forth-word-in-proof -> 1 1 33 }T
\ More of the number forms one host or the other reads (p01).
T{ s" theorem t -3 Type" fails -> 35 1 11 }T
T{ s" theorem t &10 Type" fails -> 35 1 11 }T
T{ s" theorem t .5 Type" fails -> 1 1 11 }T
T{ s" theorem t 1_000 Type" fails -> 35 1 11 }T
T{ s" theorem t '' Type" fails -> 35 1 11 }T
T{ s" theorem t 1e3 Type" fails -> 35 1 11 }T
T{ s" theorem t `Prop Type" fails -> 1 1 11 }T
T{ s" theorem t <Prop> Type" fails -> 1 1 11 }T

\ STATE (p03): a run started while Forth compiles is refused before
\ anything runs (error 45), so nothing is compiled into the caller; and a
\ line that ends with Forth compiling is refused too.
variable during
: run-now ( -- ) s" theorem tc Prop explicit: q q := q end tc" run during ! ; immediate
: victim ( -- ) run-now ;
T{ during @ lf-author-code lf-author-count -> outcome-invalid 45 0 }T
T{ victim -> }T
: compiling-line-end ( -- code )
  lfa-error-reset s" x" lfa-line! -1 state ! ['] lfa-line-end catch 0 state ! drop
  lf-author-code ;
T{ compiling-line-end -> 45 }T

\ Characters a line may not hold (p07): refused at their column before
\ anything of the line runs (error 46); TAB separates tokens; letters
\ beyond ASCII are fine; a CR before the line end is the line end.
T{ s\" theorem t\x01" fails lf-author-count -> 46 1 10 0 }T
T{ s\" theorem t\vProp" fails -> 46 1 10 }T
T{ s\" theorem t\fProp" fails -> 46 1 10 }T
T{ s\" theorem t\rProp" fails -> 46 1 10 }T
T{ s\" theorem t\x7f" fails -> 46 1 10 }T
T{ s\" theorem t\x00" fails -> 46 1 10 }T
T{ s\" theorem t \xff" fails -> 46 1 11 }T
T{ s\" theorem t \xe2\x80\xae" fails -> 46 1 11 }T
T{ s\" theorem t \xe2\x80\x8b" fails -> 46 1 11 }T
T{ s\" def f\n  Prop\x1b := Prop end f" fails -> 46 2 7 }T
T{ s\" theorem\tt Prop explicit:\tp p := p end t" run -> outcome-ok }T
T{ s\" def \xce\xb1 Prop := Prop end \xce\xb1" run -> outcome-ok }T
T{ s\" def f Prop := Prop end f\r\n" run -> outcome-ok }T

\ A Forth exception on a line where no word has read a token yet names
\ the line's first token (p04): here the data stack overflows on line 2.
text0 s\" theorem t\n" text+ s"  1" 40000 times
T{ text$ fails -> 41 2 2 }T
T{ lfa-error lfa-err-token lfa-error lfa-err-length @ s" 1" compare -> 0 }T

\ Each text's lines count from 1, also when a second text runs in the
\ same run (the second text's PROP is on its line 1).
T{ lf-author-begin s\" def a\n Prop := Prop end a" lf-author-text
   s" def b PROP := Prop end b" lf-author-text err -> outcome-ok outcome-invalid 1 1 7 }T

\ Names that are Forth words become harmless group words (p04), and the
\ EVALUATE that makes a group sees only lfa-group:, so a word of that name
\ defined later, here in this file's word list, is never run.
variable hijacked  false hijacked !
: lfa-group: ( -- ) true hijacked ! ;
T{ s" axiom bye Prop end bye" run -> outcome-ok }T
T{ s" axiom ] Prop end ]" run -> outcome-ok }T
T{ s" axiom postpone Prop end postpone" run -> outcome-ok }T
T{ s" axiom lfa-group: Prop end lfa-group:" run -> outcome-ok }T
T{ s" theorem t Prop explicit: evaluate evaluate := evaluate end t" run -> outcome-ok }T
T{ s" axiom aNewNameForTheDefiner Prop end aNewNameForTheDefiner" run hijacked @
   -> outcome-ok false }T

[defined] rec-to [defined] traverse-wordlist and [if]
\ Gforth 1.0's -> recognizer writes a VALUE or DEFER it finds in the
\ search order (p01): the sealed lists must hold only CREATE ... DOES>
\ words, for which 0 ->NAME throws -21. Every word of the three lists,
\ the group words made by the runs above included, with Gforth's own
\ recognizers and that list alone in the search order.
create to-text 300 allot  variable to-wid  variable to-bad  variable to-count
create to-order 40 cells allot  variable to-order#
: to-save ( -- ) get-order dup to-order# ! 0 ?do to-order i cells + ! loop ;
: to-back ( -- ) to-order# @ 0 ?do to-order to-order# @ 1- i - cells + @ loop
  to-order# @ set-order ;
: to-line ( nt -- c-addr u )
  name>string 290 min >r s" 0 ->" to-text swap move to-text 4 + r@ move to-text r> 4 + ;
: to-try ( nt -- flag )
  to-line depth >r to-save to-wid @ 1 set-order ['] evaluate catch to-back
  depth r> - 1+ 0 max 0 ?do nip loop
  -21 <> if 1 to-bad +! then 1 to-count +! true ;
: to-list ( wid -- bad count )
  dup to-wid ! 0 to-bad ! 0 to-count ! ['] to-try swap traverse-wordlist
  to-bad @ to-count @ ;
T{ lf-words to-list nip 30 > -> true }T
T{ lf-words to-list drop lf-locals to-list drop lf-consts to-list drop -> 0 0 0 }T
[then]

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
\ Number literals and projections: n lit# and i proj# NAME build the leaves,
\ shared when equal, and print as the words that built them.
T{ s" import-stub Nat end Nat import-stub Prod end Prod def f Prod explicit: p Nat := 0 proj# Prod p $ end f def g Nat := 7 lit# end g def h Nat := 7 lit# end h"
   run -> outcome-ok }T
T{ 3 lf-author-decl lf-fdecl-value @ lf-lit-leaf? -> true }T
T{ 3 lf-author-decl lf-fdecl-value @ lf-lit-cell -> 7 }T
T{ 3 lf-author-decl lf-fdecl-value @ 4 lf-author-decl lf-fdecl-value @ = -> true }T
T{ 4 lf-author-decl lf-fdecl-value @ forth-text rot rot s" 7 lit#" compare -> outcome-ok 0 }T
T{ 2 lf-author-decl lf-fdecl-value @ forth-text rot rot s" Prod explicit: p 0 proj# Prod p $ fun" compare
   -> outcome-ok 0 }T
T{ s" import-stub Nat end Nat def f Nat := 0 proj# Missing end f" fails drop drop -> lfa-e-unknown-constant }T
\ A label or note the words cannot read back as itself (added through the
\ note table, not by the words) is refused, never printed as live words.
: noted ( c-addr u kind -- outcome )
  s" def f Prop := Prop end f" run drop 0 lf-author-decl lf-fdecl-value @ lf-note-add nip
  drop 0 lf-author-decl lf-fdecl-value @ forth-text nip nip ;
T{ s\" hi\" Prop" lf-note-person noted -> outcome-unsupported }T
T{ s\" two\nlines" lf-note-ai noted -> outcome-unsupported }T
T{ s" a b" lf-note-label noted -> outcome-unsupported }T
T{ s" " lf-note-label noted -> outcome-unsupported }T
T{ s" fine, (really)" lf-note-person noted -> outcome-ok }T
T{ s" a-b" lf-note-label noted -> outcome-ok }T
\ Both pass the text rule too: a bidirectional control would make the runner refuse the line.
T{ s\" a\xe2\x80\xaeb" lf-note-label noted -> outcome-unsupported }T
T{ s\" a\xe2\x80\xaeb" lf-note-person noted -> outcome-unsupported }T
' type lf-print-unicode lf-print-setup

\ A search order of more wordlists than a run can save is an outcome (error 47,
\ full), not an abort; the caller's order is left as it was.
: wid-push ( -- ) get-order forth-wordlist swap 1+ set-order ;
: wid-pop ( -- ) get-order swap drop 1- set-order ;
: wide-run ( c-addr u -- outcome ) 17 0 ?do wid-push loop run 17 0 ?do wid-pop loop ;
T{ s" Prop" wide-run -> outcome-full }T
T{ lf-author-code -> 47 }T
T{ same-order? -> true true }T
T{ s" theorem t Prop explicit: p p := p end t" run -> outcome-ok }T

\ Names the words cannot spell: a part between guillemets reads back as another
\ part, or stops the run (plan task 8.6.3), so the printer refuses it; a Zs space
\ in a name is spelt and read back exactly.
T{ s\" \xc2\xab1\xc2\xbb" lf-pf-plain? -> false }T
T{ s\" \xc2\xabab\xc2\xbb" lf-pf-plain? -> false }T
T{ s\" \xc2\xab\xc2\xbb" lf-pf-plain? -> true }T
T{ s\" \xc2\xabab" lf-pf-plain? -> true }T
T{ s\" a\xc2\xa0b" lf-pf-plain? -> true }T

\ The dictionary reserve (p05): with fewer than lfa-dictionary-reserve
\ address units unused, no group word is made (error 66, full), while
\ names that have one still work. Last in this file: the space taken here
\ is not given back.
unused lfa-dictionary-reserve - 1+ allot
T{ s" axiom aNameAfterTheReserve Prop end aNameAfterTheReserve" fails drop drop -> 66 }T
T{ lf-author-code lf-author-outcome -> outcome-full }T
T{ s" theorem t Prop explicit: p p := p end t" run -> outcome-ok }T

cr .( author.fs: all tests passed) cr
bye
