\ Unit tests of the LeanForth authoring words (plan task 8.1.2): every
\ error code that a proof can reach, with its line and column (and the
\ second position where there is one); names that differ only in case;
\ Forth's own words forth-word-in-proof in proof text; numbers only as plain
\ decimals, the same tokens refused on every host; values used once;
\ names never number-like; namespaces, open and which constant a name
\ means, as Lean resolves it; var# and root:; source positions on nodes;
\ labels and notes; the runner restoring the caller's settings; the note
\ table and the printer's Forth mode on their own, which refuses labels
\ and notes it cannot spell; the export's records (export.fs). The example
\ files, their round trips, their records and the comparison with Lean
\ are in check_author.py.
require ../support/tester.fs
require ../../src/author/runner.fs

: run ( c-addr u -- outcome ) lf-author-begin lf-author-kernel lf-author-text ;
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
T{ s" theorem t Prop explicit: p p := p p over end t" fails -> 1 1 37 }T
\ + is Lean's + (owner, 2026-11-12), a word of natural LeanForth only: in
\ kernel-form text it is refused at its column (error 58), never Forth's +.
T{ s" theorem t Prop explicit: p p := p p + end t" fails -> 58 1 37 }T
\ So are the notation words of slice S3a-ops (words.fs's
\ lfa-natural-words), their ASCII spellings too, never Forth's - or <=,
\ and \/ is a word, not the comment word \.
T{ s" theorem t Prop explicit: p p := p p - end t" fails -> 58 1 37 }T
T{ s" theorem t Prop explicit: p p := p p <= end t" fails -> 58 1 37 }T
T{ s" theorem t Prop explicit: p p := p p \/ end t" fails -> 58 1 37 }T
T{ s" theorem t Prop explicit: p p := p p ∧ end t" fails -> 58 1 37 }T
T{ s" theorem t Prop explicit: p p := swap p end t" fails -> 1 1 33 }T
T{ s" : x ; theorem t" fails -> 1 1 1 }T
T{ s\" theorem t\n  CHAR Prop" fails -> 1 2 3 }T
\ Syntax words are case-sensitive too.
T{ s" theorem t PROP := Prop end t" fails -> 1 1 11 }T
T{ s" theorem t Prop explicit: p P := p end t" fails -> 1 1 28 }T
\ A binder is never named by a reserved word, a syntax word or a tactic
\ file's word, which its variable would hide (78, at the name); a name
\ that only starts like one is a name, and so is _, as Lean's own _
\ binders are written (a match's Unit argument).
T{ s" theorem t Prop explicit: at: at: := at: end t" fails -> 78 1 26 }T
T{ s" theorem t Prop implicit: fun Prop := Prop end t" fails -> 78 1 26 }T
T{ s" theorem t Prop explicit: by-exact by-exact := by-exact end t" fails -> 78 1 26 }T
T{ s" def f Prop explicit: at Prop := at end f" run -> outcome-ok }T
T{ s" def f Prop explicit: x Prop explicit: _ Prop := x end f" run -> outcome-ok }T

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
\ Values grow too (the author review's R5): 513 values are not too many
\ (the text then ends unfinished); a value store at its limit, a setting
\ (here 16), is. The numerals: tests/front/front.fs.
text0 s" theorem t" text+ s"  Prop" 513 times
T{ text$ fails drop drop -> 33 }T
lfa-items-reset  16 lfa-items store-limit! drop
text0 s" theorem t" text+ s"  Prop" 17 times
T{ text$ fails drop drop -> 64 }T
lfa-items-reset  /lfa-item store-most lfa-items store-limit! drop
\ Sharing (build.fs's index, review reuse-front-a finding 1): a lookup
\ finds what a scan of the whole term store finds, the first term with the
\ node's fields and no label or note, after random statements with labels,
\ rollbacks of the store (one large enough to make the index again, one
\ that leaves stale links), terms made again at the numbers given back,
\ and a reset. The scan is the lookup before the index.
: scan-same? ( node term -- flag )
  lfa-term-fields 3 pick node-second @ = >r 2 pick node-first @ = >r
  over node-tag @ = nip r> r> and and ;
: scan-is? ( node term -- node flag ) 2dup scan-same? swap lfa-shareable? and ;
: scan-find ( node -- term true | false ) lf-term-count @ ['] scan-is? find-index ;
create probe /node allot
: probe-of ( term -- node ) lfa-term-fields probe node! probe ;
: found ( node xt -- term | -1 ) execute 0= if -1 then ;
: agree? ( node -- flag ) dup ['] scan-find found swap ['] lfa-find found = ;
: absent ( node -- node ) 1 over node-second +! ;
\ Every term of a tag a lookup seeks (a binder never is), and its fields
\ with the second one more, which mostly no term has.
: term-agrees? ( term -- flag ) dup probe-of agree? swap probe-of absent agree? and ;
create sought-tags  lf-tag-app , lf-tag-projection , lf-tag-bvar , lf-tag-symbolic-sort ,
  lf-tag-constant , lf-tag-lit , lf-tag-proj ,
: sought? ( term -- flag ) probe-of node-tag @ sought-tags 7 cells-has? ;
: all-agree? ( -- flag )
  true lf-term-count @ 0 ?do i sought? if i term-agrees? and then loop ;
variable share-seed  20261118 share-seed !
: share-rnd ( n -- u )
  share-seed @ 1103515245 * 12345 + 2147483647 and dup share-seed ! 16 rshift swap mod ;
variable depth#  variable label#
: num+ ( n -- ) 0 <# #s #> text+ ;
\ Leaves P, Q (variables), Prop (a Sort) and c (a constant); arrows and
\ applications.
create leaves  char P c, char Q c, char c c,
: leaf-text ( k -- c-addr u ) dup 3 = if drop s"  Prop" else s"  " text+ leaves + 1 then ;
: leaf ( -- ) 4 share-rnd leaf-text text+ 1 depth# +! ;
: arrow ( -- ) 3 share-rnd if s"  ->" else s"  $" then text+ -1 depth# +! ;
\ Labels, at most 60 in the run (the note table holds 64).
: label? ( -- flag ) 6 share-rnd 0= label# @ 60 < and ;
: label ( -- ) label? if s"  label: l" text+ label# @ num+ 1 label# +! then ;
: step ( -- ) depth# @ 2 < 3 share-rnd 0= or if leaf else arrow then label ;
: statement ( n -- ) 0 depth# ! 0 ?do step loop begin depth# @ 1 > while arrow repeat ;
: axiom-text ( k -- )
  s"  axiom a" text+ dup num+ s"  Prop explicit: P Prop explicit: Q" text+
  16 share-rnd 2 + statement s"  forall forall end a" text+ num+ ;
: stub ( k0 -- ) 0= if s" import-stub c end c" text+ then ;
: axioms ( k0 n -- outcome )
  text0 over stub bounds ?do i axiom-text loop text$ lf-author-text ;
create share-mark /store-mark allot
variable share-room  lf-term-capacity share-room !  1000000 lf-term-capacity! drop
variable share-names  lf-name-capacity share-names !  100000 lf-name-capacity! drop
lf-author-begin lf-author-kernel
T{ 0 40 axioms all-agree? -> outcome-ok true }T
T{ share-mark lf-terms store-mark -> outcome-ok }T
T{ 40 60 axioms all-agree? -> outcome-ok true }T
T{ share-mark lf-term-rollback all-agree? -> outcome-ok true }T
T{ lfa-shares lfa-shares-stale @ -> 0 }T
T{ 100 30 axioms all-agree? -> outcome-ok true }T
T{ share-mark lf-terms store-mark -> outcome-ok }T
variable kept-seed  share-seed @ kept-seed !
T{ 130 10 axioms all-agree? -> outcome-ok true }T
T{ share-mark lf-term-rollback all-agree? -> outcome-ok true }T
T{ lfa-shares lfa-shares-stale @ 0> -> true }T
\ The same statements again, one number later and with a term made before
\ any lookup: the stale links' numbers now hold other terms.
T{ share-mark lf-term-rollback 1000 lfa-new-bvar drop -> outcome-ok }T
kept-seed @ share-seed !
T{ 140 10 axioms all-agree? -> outcome-ok true }T
T{ 150 30 axioms all-agree? -> outcome-ok true }T
\ By hand: #2000 entered at number m, given back, then #2001 made at m and
\ #2000 at m + 1 with no lookup between: the stale link of m is passed
\ over (its identity is old), and m is entered again.
: bvar-sought ( i -- term true | false ) lf-tag-bvar swap 0 probe node! probe lfa-find ;
variable x-term  variable y-term  variable z-term
T{ share-mark lf-terms store-mark -> outcome-ok }T
T{ 2000 lfa-new-bvar x-term ! 2000 bvar-sought -> x-term @ true }T
T{ share-mark lf-term-rollback -> outcome-ok }T
2001 lfa-new-bvar y-term !  2000 lfa-new-bvar z-term !
T{ y-term @ x-term @ = 2000 bvar-sought -> true z-term @ true }T
T{ 2001 bvar-sought all-agree? -> y-term @ true true }T
T{ lf-author-begin all-agree? lf-term-count @ -> true 0 }T
\ The index out of room: a memo that admits no entry, or a slab of two
\ links, stops the run full (60), never with another node; a memo freed
\ is made again, with every term entered again.
: no-entry ( memo -- false ) drop false ;
: five ( -- c-addr u ) s" axiom a Prop explicit: P P P P P P -> -> -> -> forall end a" ;
: five-run ( -- outcome code ) five run lf-author-code ;
T{ five-run -> outcome-ok 0 }T
' no-entry lfa-memo memo-admit!
T{ five-run -> outcome-full 60 }T
0 lfa-memo memo-admit!  lfa-links slab-free  /lfa-link 2 lfa-links slab-init drop
T{ five-run -> outcome-full 60 }T
lfa-memo memo-free
T{ five-run lfa-links slab-count 2 > -> outcome-ok 0 true }T
T{ 0 1 axioms all-agree? -> outcome-ok true }T
lf-author-begin share-room @ lf-term-capacity! drop share-names @ lf-name-capacity! drop
\ A heap store refused at its start aborts (form.fs's lfa-heap-must).
T{ outcome-full ' lfa-heap-must catch nip outcome-ok ' lfa-heap-must catch -> -2 0 }T
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
T{ text$ fails -> 300 1 9 }T
T{ lfa-error lfa-err-number @ 300 lf-author-outcome -> -3 outcome-full }T
\ The class of a Forth exception (review N1 of 2026-11-18): a host stack,
\ the dictionary or the heap running out is full, error 300 (exit 3); any
\ other THROW is LeanForth's internal fault, error 41, whose outcome is
\ none of the vocabulary (exit 5), never the text's invalid (exit 4).
: thrown ( throw -- code outcome flag ) lfa-error-reset lfa-caught lf-author-code swap dup ok? ;
T{ -3 thrown -> 300 outcome-full false }T
T{ -5 thrown -> 300 outcome-full false }T
T{ -8 thrown -> 300 outcome-full false }T
T{ -59 thrown -> 300 outcome-full false }T
T{ -61 thrown -> 300 outcome-full false }T
T{ -4 thrown -> 41 lfa-internal false }T
T{ -9 thrown -> 41 lfa-internal false }T
T{ -6 thrown -> 41 lfa-internal false }T
T{ lfa-internal outcome? lfa-internal outcome-sane -> false outcome-invalid }T
T{ lfa-error lfa-err-number @ -> -6 }T
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
  lf-term-first@ dup lf-cref-current lf-cref-read 0= abort" ref" 2drop ;
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
\ ] is LeanForth's own word, which closes by-rw[ (a tactic: not supported
\ in kernel-form text, 72), never Forth's, which would start compiling.
T{ s" ]" forth-word-in-proof -> 72 1 33 }T
T{ state @ -> 0 }T
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
T{ text$ fails -> 300 2 2 }T
T{ lfa-error lfa-err-token lfa-error lfa-err-length @ s" 1" compare -> 0 }T

\ Each text's lines count from 1, also when a second text runs in the
\ same run (the second text's PROP is on its line 1).
T{ lf-author-begin lf-author-kernel s\" def a\n Prop := Prop end a" lf-author-text
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
\ Room (review FRP, B7): the table holds lf-note-capacity entries and the
\ pool lf-note-byte-capacity bytes; one more is full and changes nothing;
\ a malformed entry is invalid before a full table is full.
: notes-fill ( n -- ) 0 ?do s" n" lf-note-person 0 lf-note-add 2drop loop ;
create note-big lf-note-byte-capacity 1+ allot
: big-note ( u -- outcome ) note-big swap lf-note-person 0 lf-note-add nip ;
lf-note-reset
T{ lf-note-capacity notes-fill lf-note-count lf-note-used -> 64 64 }T
T{ s" x" lf-note-person 0 lf-note-add lf-note-count -> -1 outcome-full 64 }T
T{ s" x" 7 0 lf-note-add -> -1 outcome-invalid }T
lf-note-reset
T{ lf-note-byte-capacity 1+ big-note lf-note-count lf-note-used -> outcome-full 0 0 }T
T{ lf-note-byte-capacity big-note lf-note-used -> outcome-ok 4096 }T
T{ s" " lf-note-person 0 lf-note-add 1 big-note -> 1 outcome-ok outcome-full }T
T{ 0 lf-note-text@ nip 1 lf-note-text@ nip lf-note-count -> 4096 0 2 }T
lf-note-reset
T{ s" x" lf-note-person 0 lf-note-add s" y" lf-note-label 0 lf-note-add -> 0 outcome-ok 1 outcome-ok }T
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
\ A constant named like a notation word (slice S3a-ops) is written with
\ root:, which reads back as that constant, not the word.
T{ s" axiom ∧ Prop end ∧ def f Prop := root: ∧ end f" run -> outcome-ok }T
T{ 1 lf-author-decl lf-fdecl-value @ forth-text rot rot s" root: ∧" compare -> outcome-ok 0 }T
T{ s" axiom <= Prop end <= def f Prop := root: <= end f" run -> outcome-ok }T
T{ 1 lf-author-decl lf-fdecl-value @ forth-text rot rot s" root: <=" compare -> outcome-ok 0 }T
\ A term or level of a tag no step writes is invalid (refactor-present
\ review L3): a metavariable leaf, and a Sort of a metavariable level.
T{ 0 0 lf-mvar-leaf drop forth-text nip nip -> outcome-invalid }T
T{ 0 0 lf-level-mvar-leaf drop lf-term-symbolic-sort drop forth-text nip nip -> outcome-invalid }T
\ Corrupted tags (the item-2 review's L3): a term tag 0, 31, 32 or
\ 2^32 - 1, and a level tag 7, 8 or -1 under a symbolic Sort, are invalid,
\ inside or outside the Forth mode's tables. In a context of their own, so
\ the corrupted records go with it.
require ../support/store-faults.fs
context-new throw constant tags-context
tags-context context-use
: forth-tag ( tag -- outcome ) dup 1000 + lf-term-sort drop tuck term-tag! forth-text nip nip ;
: tag-level ( n -- level ) 0 swap 2000 + lf-name-num drop lf-level-param drop ;
: forth-level-tag ( tag -- outcome )
  dup tag-level tuck level-tag! lf-term-symbolic-sort drop forth-text nip nip ;
T{ 0 forth-tag 31 forth-tag -> outcome-invalid outcome-invalid }T
T{ 32 forth-tag -1 forth-tag -> outcome-invalid outcome-invalid }T
T{ 7 forth-level-tag 8 forth-level-tag -1 forth-level-tag
   -> outcome-invalid outcome-invalid outcome-invalid }T
context-main context-use  tags-context context-free throw
\ An import stub without a type prints as it was written (review N1).
: printed ( -- c-addr u outcome )
  0 fout# ! ['] fout+ lf-print-unicode lf-print-setup 1000 lf-author-print >r fout fout# @ r> ;
T{ s" import-stub X end X" run printed rot rot s\" import-stub X\nend X\n" compare
   -> outcome-ok outcome-ok 0 }T
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
\ A projection leaf is a term only as the function of $ (review M2): as a
\ proof, an argument, a binder's type, under -> or a label it stops the run
\ (error 56) at the word that takes it; applied, it is a projection.
T{ s" axiom S 0 Type end S def d 0 Type := 0 proj# S end d" fails -> 56 1 48 }T
T{ s" axiom S 0 Type end S def d 0 Type := Prop 0 proj# S $ end d" fails -> 56 1 53 }T
T{ s" axiom S 0 Type end S def d 0 proj# S explicit: x 0 Type := Prop end d" fails
   -> 56 1 38 }T
T{ s" axiom S 0 Type end S def d 0 Type := 0 proj# S Prop -> end d" fails -> 56 1 53 }T
T{ s" axiom S 0 Type end S def d 0 Type := 0 proj# S label: a end d" fails -> 56 1 55 }T
T{ lf-author-code lf-author-outcome -> outcome-invalid }T
T{ s" axiom S 0 Type end S def d S explicit: s 0 Type := 0 proj# S s $ end d" run
   -> outcome-ok }T
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
\ A wordlist's place in the copied search order (groups.fs, review
\ reuse-front-a finding 2): its index, or the count when it is not there,
\ so that no list is searched after it.
T{ lfa-order@ lfa-order# 0> 0 lfa-order-wid lfa-order-index -> true 0 }T
T{ lfa-order# 1- lfa-order-wid lfa-order-index -> lfa-order# 1- }T
T{ wordlist lfa-order-index -> lfa-order# }T

\ Names the words cannot spell: a part between guillemets reads back as another
\ part, or stops the run (plan task 8.6.3), so the printer refuses it; a Zs space
\ in a name is spelt and read back exactly.
T{ s\" \xc2\xab1\xc2\xbb" lf-pf-plain? -> false }T
T{ s\" \xc2\xabab\xc2\xbb" lf-pf-plain? -> false }T
T{ s\" \xc2\xab\xc2\xbb" lf-pf-plain? -> true }T
T{ s\" \xc2\xabab" lf-pf-plain? -> true }T
T{ s\" a\xc2\xa0b" lf-pf-plain? -> true }T
\ A token that could start a Forth number (a digit, or any of - + $ # % &
\ ' " .) is no word the printer writes: each of them, not only the first
\ (review reuse-out-2 rc3 B2); after the first character they are fine.
: token-starts ( -- n )
  0 s\" 7-+$#%&'\"." bounds ?do i c@ pad c! [char] x pad 1+ c! pad 2 lf-pf-token? 0= - loop ;
T{ token-starts -> 10 }T
T{ s" x+" lf-pf-token? s" x'" lf-pf-token? -> true true }T

\ The export of a run's declarations (export.fs, plan task 8.2.1c): one
\ export record a line to a sink, the metadata first; theorem t makes its
\ two names, four expressions and itself.
8192 constant lines-max
create lines lines-max allot  variable lines#  variable lines-n
: line-sink ( c-addr u -- outcome )
  dup lines# @ + lines-max > if 2drop outcome-full exit then
  tuck lines lines# @ + swap move lines# +! 1 lines-n +! outcome-ok ;
: export-now ( -- outcome ) 0 lines# ! 0 lines-n ! ['] line-sink lf-author-export ;
: exported ( c-addr u -- outcome ) run drop export-now ;
: holds? ( c-addr u -- flag ) lines lines# @ 2swap search nip nip ;
T{ s" theorem t Prop explicit: p p := p end t" exported lines-n @ -> outcome-ok 8 }T
T{ s\" \"name\":\"leanforth\"" holds? s\" {\"in\":1,\"str\":{\"pre\":0,\"str\":\"t\"}}" holds?
   -> true true }T
T{ s\" {\"thm\":{\"all\":[1],\"levelParams\":[],\"name\":1,\"type\":3,\"value\":2}}" holds?
   -> true }T
\ The names pass the full audit before any line is written (ADR 0005
\ Amendment 1): a name's kept hash rewritten after the kept audit passed
\ it, or its prefix pointed forward, refuses the export as invalid.
variable kept-cell
: spoil ( x addr -- ) dup @ kept-cell ! ! ;
: unspoil ( addr -- ) kept-cell @ swap ! ;
: name-1 ( -- entry ) 1 lf-name-slot ;
T{ s" theorem t Prop explicit: p p := p end t" run -> outcome-ok }T
T{ lf-name-storage-valid? 1 name-1 lf-entry-hash spoil export-now lines-n @ -> true outcome-invalid 0 }T
T{ name-1 lf-entry-hash unspoil 99 name-1 lf-entry-prefix spoil export-now lines-n @
   -> outcome-invalid 0 }T
T{ name-1 lf-entry-prefix unspoil export-now -> outcome-ok }T
\ Lean's heights: a definition one above the highest it names.
T{ s" def a 0 Type := Prop end a def b 0 Type := a end b" exported -> outcome-ok }T
T{ s\" \"hints\":{\"regular\":1}" holds? s\" \"hints\":{\"regular\":2}" holds? -> true true }T
\ Levels, universe parameters, literals and binder kinds as Lean writes them.
T{ s" def five 0 Type := 5 lit# end five" exported s\" \"natVal\":\"5\"" holds?
   -> outcome-ok true }T
T{ s" theorem k universe u u Sort implicit: x x := x end k" exported -> outcome-ok }T
T{ s\" {\"il\":1,\"param\":2}" holds? s\" \"binderInfo\":\"implicit\"" holds? -> true true }T
T{ s\" \"levelParams\":[2]" holds? -> true }T
\ Lean's key order and escapes (review S7): bvar, app, const and forallE
\ before "ie", the rest after; a name's non-ASCII bytes as they are.
T{ s" theorem t Prop explicit: p p := p end t" exported -> outcome-ok }T
T{ s\" {\"bvar\":0,\"ie\":1}" holds? s\" {\"ie\":0,\"sort\":0}" holds? -> true true }T
T{ s\" {\"forallE\":{\"binderInfo\":\"default\",\"body\":1,\"name\":2,\"type\":0},\"ie\":3}"
   holds? -> true }T
T{ s\" theorem \xce\xb1 Prop explicit: p p := p end \xce\xb1" exported -> outcome-ok }T
T{ s\" \"str\":\"\xce\xb1\"" holds? -> true }T
\ A tab, which no text's name holds (it splits tokens), put in the name
\ store by hand: \u0009 as Lean writes it, not \t.
T{ 0 s\" a\tb" lf-name-str nip export-now -> true outcome-ok }T
T{ s\" \"str\":\"a\\u0009b\"" holds? -> true }T
T{ s" def a 0 Type := Prop end a def b 0 Type := a end b" exported -> outcome-ok }T
T{ s\" {\"const\":{\"name\":1,\"us\":[]},\"ie\":" holds? -> true }T
T{ s" theorem t Prop explicit: f Prop explicit: x f x $ := Prop end t" exported
   s\" {\"app\":{\"arg\":" holds? -> outcome-ok true }T
\ The sink's refusal stops it at the line refused; a line past the writer's
\ limit is full; a node no record holds is unsupported.
variable calls
: refusing ( c-addr u -- outcome ) 2drop 1 calls +! outcome-invalid ;
T{ s" theorem t Prop explicit: p p := p end t" run 0 calls ! ' refusing lf-author-export
   calls @ -> outcome-ok outcome-invalid 1 }T
T{ 20 lfx lfx-writer jw-limit ! export-now -> outcome-full }T
lfx-line-capacity lfx lfx-writer jw-limit !
T{ 0 0 lf-tag-let lf-term-binary nip export-now -> true outcome-unsupported }T
\ A let and a have (the tactics' let and have, plan row TB2): Lean's letE
\ record with its nondep flag and its binder's name, after the record of
\ its binder's lambda: let k : Prop := Prop; Prop, k a name of its own.
: a-lam ( -- lam )
  0 lf-term-symbolic-sort drop dup lf-term-lam drop
  dup 0 s" k" lf-name-str drop lf-binder-default lf-pres-binder! drop ;
: a-let ( nondep -- flag outcome )
  >r 0 lf-term-symbolic-sort drop a-lam r> lf-let-make nip export-now ;
T{ s" theorem t Prop explicit: p p := p end t" run true a-let -> outcome-ok true outcome-ok }T
T{ s\" {\"in\":3,\"str\":{\"pre\":0,\"str\":\"k\"}}" holds? -> true }T
\ The whole line pinned: Lean's own form of it (keys and order as in
\ tests/core/check-declaration-cases/let-nondep.ndjson, line 8, made by
\ Lean 4.35.0: {"ie":3,"letE":{"body":2,"name":2,"nondep":true,"type":0,
\ "value":1}}), here value 4 (Prop), the lambda 6's type and body 5 and
\ its name 3 (k).
T{ s\" {\"ie\":7,\"letE\":{\"body\":5,\"name\":3,\"nondep\":true,\"type\":5,\"value\":4}}"
   holds? -> true }T
T{ s" theorem t Prop explicit: p p := p end t" run false a-let -> outcome-ok true outcome-ok }T
T{ s\" \"name\":3,\"nondep\":false,\"type\":5," holds? -> true }T
\ A projection, a binder without a recorded name (made by hand) and the
\ heights: an axiom named in a value counts 0, so does a constant whose
\ record is gone (renamed by hand), a definition its own height.
T{ s" axiom S 0 Type end S def d S explicit: s 0 Type := 0 proj# S s $ end d" exported
   s\" {\"ie\":3,\"proj\":{\"idx\":0,\"struct\":2,\"typeName\":1}}" holds? -> outcome-ok true }T
T{ 0 0 lf-tag-pi lf-term-binary nip export-now -> true outcome-ok }T
T{ s\" \"binderInfo\":\"default\",\"body\":0,\"name\":0,\"type\":0" holds? -> true }T
T{ s" axiom a 0 Type end a def b 0 Type := a end b" exported
   s\" \"hints\":{\"regular\":1}" holds? -> outcome-ok true }T
T{ s" def a 0 Type := Prop end a def b 0 Type := a end b" run -> outcome-ok }T
T{ 0 s" zz" lf-name-str drop 0 lfa-decl lf-fdecl-name ! export-now -> outcome-ok }T
T{ s\" \"hints\":{\"regular\":2}" holds? -> false }T
\ A numbering table the heap cannot give (lfx-tables's lib/blocks.fs):
\ full, the cell left 0.
variable no-block  0 no-block !
T{ max-n no-block block-zeroed no-block @ -> outcome-full 0 }T
\ A reference to a projection's leaf is refused, never written (review M2).
T{ s" theorem t Prop explicit: p p := p end t" exported -> outcome-ok }T
T{ 1 0 lf-hterm-proj drop drop 0 swap lf-tag-app lf-term-binary nip export-now
   -> true outcome-unsupported }T
T{ s" 18446744073709551615" holds? -> false }T
\ A level of a tag the format has no record for is refused (review S6).
T{ s" theorem t Prop explicit: p p := p end t" exported -> outcome-ok }T
T{ 7 0 0 lf-level-new nip export-now -> true outcome-unsupported }T
\ A metavariable anywhere in the stores (core/mvar-leaves.fs, ADR 0021 D2)
\ refuses the whole run before any line is written: invalid, elaboration
\ incomplete; a term one and a level one, each unreachable from any value.
T{ s" theorem t Prop explicit: p p := p end t" exported -> outcome-ok }T
T{ 0 0 lf-mvar-leaf nip export-now lines-n @ -> true outcome-invalid 0 }T
T{ s" theorem t Prop explicit: p p := p end t" exported -> outcome-ok }T
T{ 0 0 lf-level-mvar-leaf nip export-now lines-n @ -> true outcome-invalid 0 }T
\ And one inside the theorem's own proof, put there by hand.
T{ s" theorem t Prop explicit: p p := p end t" run -> outcome-ok }T
T{ 0 0 lf-mvar-leaf drop 0 lf-author-decl lf-fdecl-value ! export-now lines-n @
   -> outcome-invalid 0 }T
T{ lf-holes? -> true }T
T{ s" theorem t Prop explicit: p p := p end t" run lf-holes? -> outcome-ok false }T

\ A library (library.fs, plan task 8.2.1d): a finder that knows Lib.c,
\ Lib.k and Lib.m, of no universe parameters, definitions of height 3. Its
\ constant gets a record of kind library, which the export never writes.
: part= ( id c-addr u -- flag ) rot lf-name-text compare 0= ;
: c-or-k? ( name -- flag ) dup s" c" part= over s" k" part= or swap s" m" part= or ;
: lib-c? ( name -- flag )
  dup c-or-k? swap lf-name-prefix@ dup if s" Lib" part= else drop false then and ;
: lib-finder ( name -- universes height true | false ) lib-c? if 0 3 true else false then ;
: with-lib ( c-addr u -- outcome ) ['] lib-finder lf-author-library! run 0 lf-author-library! ;
: lib-fails ( c-addr u -- code line col ) with-lib drop err ;
T{ s" def d 0 Type := Lib.c end d" with-lib lf-author-count -> outcome-ok 2 }T
T{ 0 lfa-library? 1 lfa-library? 1 lfa-decl lfa-decl-height @ -> false true 3 }T
T{ ' lib-finder lf-author-library! export-now 0 lf-author-library! -> outcome-ok }T
T{ s\" \"hints\":{\"regular\":4}" holds? lines-n @ -> true 8 }T
\ Errors: an unknown name; a short name through a namespace (55); a name
\ the library has (28); a stub in a checked run (48, at the stub's word).
T{ s" def d 0 Type := Lib.d end d" lib-fails -> 1 1 17 }T
T{ s" namespace Lib def e 0 Type := c end e end Lib" lib-fails -> 55 1 31 }T
T{ lf-author-code lf-author-outcome -> outcome-unsupported }T
T{ s" def Lib.c 0 Type := Prop end Lib.c" lib-fails -> 28 1 5 }T
\ A name the text declared twice, with a library: its record is the
\ file's, not the library's, and the second declaration is refused.
T{ s" def x 0 Type := Prop end x def x 0 Type := Prop end x" lib-fails -> 28 1 32 }T
T{ true lf-author-checked! s" import-stub X end X" fails -> 48 1 1 }T
T{ s" protected import-stub N.x end N.x" fails false lf-author-checked! -> 48 1 11 }T
T{ s" import-stub X end X" run -> outcome-ok }T
\ The look-ahead: every token of a line up to a \ comment that has no word
\ gets a group word; a number-like one none, and it is still refused.
T{ s" def d 0 Type := Lib.c end d \ Zzz.q" with-lib -> outcome-ok }T
T{ s" Zzz.q" lf-consts search-wordlist s" Lib.c" lf-consts search-wordlist nip -> 0 -1 }T
T{ s" def d 0 Type := Lib.c $10 end d" lib-fails -> 35 1 23 }T
T{ s" -7" lf-consts search-wordlist -> 0 }T
\ The text of a ( comment and of notes is no token (review M1): it gets no
\ group word, a \ in it ends nothing (Lib.k, first named here, after one),
\ and a long word in it is no name (no error 62 or 66).
T{ s\" def d 0 Type := Lib.c ( Zzz.p ) note\" Zzz.n\" ai-note\" Zzz.a\" end d" with-lib
   -> outcome-ok }T
T{ s" Zzz.p" lf-consts search-wordlist s" Zzz.n" lf-consts search-wordlist
   s" Zzz.a" lf-consts search-wordlist -> 0 0 0 }T
T{ s\" def d 0 Type := ( a \\ b ) Lib.k note\" \\ \" end d" with-lib -> outcome-ok }T
: long-comment ( -- c-addr u )
  text0 s" def d 0 Type := Lib.c ( x" text+ s" y" 320 times s" ) end d" text+ text$ ;
T{ long-comment with-lib -> outcome-ok }T
T{ s\" def d 0 Type := Lib.c note\" ( Zzz.u end d" lib-fails -> 37 1 23 }T
\ An unclosed ( with a library stops at its word (error 42); a \ in an
\ ai-note" ends nothing either (Lib.m, first named here, after it).
T{ s" def d 0 Type := Lib.c ( Zzz.v end d" lib-fails -> 42 1 23 }T
T{ s\" def d 0 Type := Prop ai-note\" a \\ b\" Lib.m $ end d" with-lib -> outcome-ok }T

\ In natural form, with no front end loaded (src/front/), a name is not
\ supported yet (error 70).
T{ ' lib-finder lf-author-library! lf-author-begin s" def d Lib.c" lf-author-text drop err
   0 lf-author-library! -> 70 1 7 }T

\ The dictionary reserve (p05): with fewer than lfa-dictionary-reserve
\ address units unused, no group word is made (error 66, full), while
\ names that have one still work. Last in this file: the space taken here
\ is not given back.
unused lfa-dictionary-reserve - 1+ allot
T{ s" axiom aNameAfterTheReserve Prop end aNameAfterTheReserve" fails drop drop -> 66 }T
T{ lf-author-code lf-author-outcome -> outcome-full }T
T{ s" theorem t Prop explicit: p p := p end t" run -> outcome-ok }T
\ The look-ahead stops there too, at the token that needs a new group word.
T{ s" def t 0 Type := Lib.zz end t" lib-fails -> 66 1 17 }T
\ The visible binders inside binder j (lf-pf-inner#, count-index since
\ cleanup-families-1), a hidden one (a negative domain) not counted; in
\ scope, innermost first: 7, hidden, 5.
: pf-bind ( domain -- ) lf-pp-used @ lf-pp-bind drop ;
T{ lf-pp-clear 5 pf-bind -1 pf-bind 7 pf-bind 1 lf-pf-inner# 2 lf-pf-inner# 3 lf-pf-inner#
   -> 1 1 2 }T
lf-pp-clear

cr .( author.fs: all tests passed) cr
bye
