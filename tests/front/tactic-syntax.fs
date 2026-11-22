\ Unit tests of tactic proofs read (plan FE1g-2; src/front/tactic-syntax.fs,
\ design docs/design/FE1G_TACTICS.md section 3): the records of well-formed
\ proofs, which are handed to the runner (src/front/tactic-run.fs, whose
\ tests are tests/front/tactic-run.fs) and, with no statement elaborator
\ until plan FE1e, end not supported yet (error 71, never accepted), or
\ without the runner error 80;
\ every malformed shape with its code, line and column; the forms not
\ supported yet; hypotheses' scope and shadowing; tactic words in the
\ kernel form; the stores out of room and the heap refusing; nesting
\ 1,000 blocks deep; the same verdict after a failed run. The coverage
\ classes are docs/development/TEST_COVERAGE_REVIEW.md's. Every T{ }T
\ checks the data stack's depth. Nothing here checks or accepts a theorem.
include ../support/heap-watch.fs
require ../support/tester.fs
require ../../src/load/checker.fs
require ../../src/load/front.fs
require ../../src/cli/check-lf.fs
require ./tactic-dump.fs

: nrun ( c-addr u -- outcome ) lf-author-begin lf-author-text ;
: err ( -- code line col ) lf-author-code lfa-error lfa-err-at @ lfa-pos> ;
: see-at ( -- line col ) lfa-error lfa-err-see @ lfa-pos> ;
: nfails ( c-addr u -- code line col ) nrun drop err ;
: outcome ( -- outcome ) lf-author-code lf-author-outcome ;
: kind ( node -- k ) syn-kind@ ;
: named? ( id c-addr u -- flag ) lfa-intern = ;
: step ( i -- addr ) lf-tactic-step ;
: kind@ ( i -- kind ) step tac-kind @ ;
: parent@ ( i -- i' ) step tac-parent @ ;
: at@ ( i -- line col ) step tac-at @ lfa-pos> ;
: args@ ( i -- first count ) step dup tac-first @ swap tac-count @ ;
: arg-node ( i k -- node ) swap args@ drop + lf-tactic-arg drop ;
: arg-name ( i k -- id ) arg-node ;
\ Texts: a theorem with the variable n of type Nat whose statement is
\ 0 + n = n, then := by and the proof; its first proof token is at 1:43.
create text 32768 allot  variable text#
: text0 ( -- ) 0 text# ! ;
: text+ ( c-addr u -- ) tuck text text# @ + swap move text# +! ;
: text$ ( -- c-addr u ) text text# @ ;
: proof ( c-addr u -- c-addr' u' )
  text0 s" theorem t Nat explicit: n 0 n + n = := by " text+ text+ text$ ;

\ ---- 1. Pass: well-formed proofs are read whole and go to the runner,
\ which stops at end when no statement elaborator is set (71; the reader
\ alone here: src/front/elab-decl.fs's is tests/front/elab.fs's); never
\ ok. Without the runner (the hook's own default), end stops with 80 and
\ by as the second place.
' lfr-unelaborated is lf-front-by-statement
T{ s" n by-induction end t" proof nfails -> 71 1 58 }T
T{ outcome -> outcome-unsupported }T
T{ ' lft-unrun is lf-tactic-proof-end s" n by-induction end t" proof nfails see-at
   -> 80 1 58 1 40 }T
T{ outcome ' lfr-proof-end is lf-tactic-proof-end -> outcome-unsupported }T
T{ s" by-rfl end t" proof nfails -> 71 1 50 }T
\ An empty proof and a by-induction-with with no alternative: Lean parses
\ both (and refuses them when it runs them: unsolved goals, an
\ alternative not provided), so they are read.
T{ s" end t" proof nfails -> 71 1 43 }T
T{ s" n by-induction-with by-end end t" proof nfails -> 71 1 70 }T
T{ s" by-rw[ ] end t" proof nfails -> 71 1 52 }T
\ The main test's record (tests/front/01-zero-add-rw.lf, on one line).
T{ s" n by-induction-with | zero => by-rfl | succ k ih => by-rw[ ' Nat.add_succ ih ] by-end end t"
   proof nfails -> 71 1 129 }T
T{ lf-tactic-count lf-tactic-format -> 6 1 }T
T{ 0 kind@ 1 kind@ 2 kind@ 3 kind@ 4 kind@ 5 kind@
   -> tac-k-by tac-k-with tac-k-alt tac-k-rfl tac-k-alt tac-k-rw }T
T{ 0 parent@ 1 parent@ 2 parent@ 3 parent@ 4 parent@ 5 parent@ -> -1 0 1 2 1 4 }T
T{ 0 at@ 1 at@ 5 at@ -> 1 40 1 45 1 95 }T
T{ 2 step tac-name @ s" zero" named? 4 step tac-name @ s" succ" named? -> true true }T
T{ 2 step tac-arrow @ lfa-pos> 4 step tac-arrow @ lfa-pos> -> 1 70 1 92 }T
T{ 0 step tac-inner @ 1 step tac-inner @ 2 step tac-inner @ 4 step tac-inner @ -> 1 0 1 1 }T
\ Arguments: the target n (v0), the names k ih, the rules in order.
T{ 1 args@ nip 1 0 arg-node kind 1 0 arg-node syn-a@ -> 1 syn-k-var 0 }T
T{ 2 args@ nip 4 args@ nip -> 0 2 }T
T{ 4 0 arg-name s" k" named? 4 1 arg-name s" ih" named? -> true true }T
T{ 5 args@ nip 5 0 arg-node kind 5 1 arg-node kind -> 2 syn-k-const syn-k-hyp }T
T{ 5 0 arg-node syn-a@ lfa-decl-name s" Nat.add_succ" named? -> true }T
T{ 5 1 arg-node syn-a@ s" ih" named? 5 1 arg-node syn-at@ lfa-pos> -> true 1 117 }T
\ Its text: from just past the step before to just past its last word.
T{ 3 step tac-from @ lfa-pos> 3 step tac-to @ lfa-pos> -> 1 72 1 79 }T
T{ 5 step tac-from @ lfa-pos> 5 step tac-to @ lfa-pos> -> 1 94 1 121 }T
T{ 1 step tac-to @ lfa-pos> 0 step tac-to @ lfa-pos> -> 1 128 1 134 }T
\ The rules' order is kept (r1 first) and a numeral is a rule too.
T{ s" by-rewrite[ 1 n 2 ] end t" proof nfails -> 71 1 63 }T
T{ 1 kind@ 1 args@ nip 1 0 arg-node syn-a@ 1 2 arg-node syn-a@ -> tac-k-rewrite 3 1 2 }T
T{ 1 1 arg-node kind 1 2 arg-node syn-at@ lfa-pos> -> syn-k-var 1 59 }T

\ Nesting: cases inside an alternative, by-intro:, both bracket words.
s" n by-induction-with | zero => n by-induction by-case: zero => by-rfl by-end "
  proof 2drop
s" by-case: succ j hj => hj by-exact by-end | succ k ih => by-intro: h "
  text+ s" by-rewrite[ ih h ] by-rw[ ] by-end end t" text+
T{ text$ nfails drop drop -> 71 }T
T{ lf-tactic-count -> 12 }T
T{ 3 kind@ 4 kind@ 5 kind@ 6 kind@ 7 kind@ -> tac-k-induction tac-k-case tac-k-rfl tac-k-case
   tac-k-exact }T
T{ 3 parent@ 4 parent@ 5 parent@ 6 parent@ 7 parent@ -> 2 2 4 2 6 }T
T{ 8 kind@ 9 kind@ 10 kind@ 11 kind@ -> tac-k-alt tac-k-intro tac-k-rewrite tac-k-rw }T
T{ 8 parent@ 9 parent@ 10 parent@ 11 parent@ 2 step tac-inner @ 8 step tac-inner @
   -> 1 8 8 8 3 3 }T
T{ 7 0 arg-node kind 7 0 arg-node syn-a@ s" hj" named? -> syn-k-hyp true }T
T{ 9 0 arg-name s" h" named? 10 args@ nip 11 args@ nip -> true 2 0 }T
T{ 10 1 arg-node syn-a@ s" h" named? -> true }T

\ ---- 2. Malformed: each a stable code at its token; nothing checked.
\ by-end with no block, ] with no by-rw[, | outside by-induction-with.
T{ s" by-end end t" proof nfails -> 83 1 43 }T
T{ outcome -> outcome-invalid }T
T{ s" ] end t" proof nfails -> 83 1 43 }T
T{ s" | zero => by-rfl end t" proof nfails -> 83 1 43 }T
T{ s" n by-induction by-case: zero => | succ => by-rfl by-end end t" proof nfails
   -> 83 1 75 }T
\ A block left open at end: the error names end and the block by-end
\ would close (an alternative's is its by-induction-with).
T{ s" n by-induction-with | zero => by-rfl end t" proof nfails see-at -> 82 1 80 1 45 }T
T{ s" by-rw[ n end t" proof nfails see-at -> 82 1 52 1 43 }T
T{ s" n by-induction by-case: zero => by-case: succ => by-rfl by-end end t" proof nfails
   see-at -> 82 1 106 1 58 }T
T{ s" n by-induction by-case: zero => by-case: succ => by-rfl by-end by-end end t" proof
   nfails -> 71 1 113 }T
\ A tactic word inside by-rw[ ]: the word, and by-rw[.
T{ s" by-rw[ n by-rfl ] end t" proof nfails see-at -> 82 1 52 1 43 }T
T{ s" by-rewrite[ by-end end t" proof nfails see-at -> 82 1 55 1 43 }T
T{ s" by-rw[ | end t" proof nfails -> 82 1 50 }T
\ Headers: => without a tag, => alone, a word where a name is due, the
\ line ending before =>.
T{ s" n by-induction-with | => by-rfl by-end end t" proof nfails -> 84 1 65 }T
T{ s" => end t" proof nfails -> 84 1 43 }T
T{ s" n by-induction-with | zero by-rfl by-end end t" proof nfails -> 84 1 70 }T
T{ s" n by-induction-with | by-rfl => by-rfl by-end end t" proof nfails -> 84 1 65 }T
T{ s" n by-induction-with | succ by-rfl ih => by-rfl by-end end t" proof nfails
   -> 84 1 70 }T
T{ s\" theorem t Nat explicit: n 0 n + n =\n:= by n by-induction-with\n| succ k ih\n=> by-rfl"
   nfails -> 84 3 10 }T
T{ s\" theorem t Nat explicit: n 0 n + n =\n:= by n by-induction-with\n|\nzero =>" nfails
   -> 84 3 1 }T
T{ s" by-case: zero" proof nfails -> 84 1 52 }T
\ A tag or name that is no name: number-like (30); by-intro: with no name
\ on its line (2), or a word.
T{ s" n by-induction-with | succ 0 ih => by-rfl by-end end t" proof nfails -> 30 1 70 }T
T{ s" n by-induction-with | 0 => by-rfl by-end end t" proof nfails -> 30 1 65 }T
T{ s" by-intro:" proof nfails -> 2 1 43 }T
T{ s" by-intro: => end t" proof nfails -> 84 1 53 }T
\ An alternative or case block with no tactic, at the word that ends it,
\ and its => as the second place (where pinned Lean's parser reports it).
T{ s" n by-induction-with | zero => | succ k ih => by-rfl by-end end t" proof nfails
   see-at -> 85 1 73 1 70 }T
T{ s" n by-induction-with | zero => by-end end t" proof nfails see-at -> 85 1 73 1 70 }T
T{ s" n by-induction by-case: zero => by-end end t" proof nfails see-at -> 85 1 75 1 72 }T
\ Values: too few or too many for the word, left at a word that takes
\ none, at by-rw[, at | and at end.
T{ s" by-exact end t" proof nfails -> 86 1 43 }T
T{ s" n n by-exact end t" proof nfails -> 86 1 47 }T
T{ s" by-induction end t" proof nfails -> 86 1 43 }T
T{ s" n by-rfl end t" proof nfails -> 86 1 45 }T
T{ s" n by-rw[ ] end t" proof nfails -> 86 1 45 }T
T{ s" n end t" proof nfails -> 86 1 45 }T
T{ s" n by-induction-with | zero => by-rfl n | succ => by-rfl by-end end t" proof nfails
   -> 86 1 82 }T
T{ s" n by-induction-with | zero => by-rfl n by-end end t" proof nfails -> 86 1 82 }T
\ A tactic word in a statement, in a term proof, outside declarations.
T{ s" theorem t Nat explicit: n by-rfl 0 n + n = := by end t" nfails -> 81 1 27 }T
T{ s" theorem t Nat explicit: n 0 n + n = := n by-rfl end t" nfails -> 81 1 42 }T
T{ s" by-rfl" nfails -> 81 1 1 }T
T{ s" ]" nfails -> 81 1 1 }T
T{ s" =>" nfails -> 81 1 1 }T
\ A binder of a term left open at a tactic word or at ] (21, and the binder).
T{ s" Nat explicit: x by-rfl end t" proof nfails see-at -> 21 1 59 1 47 }T
T{ s" by-rw[ Nat explicit: x ] end t" proof nfails see-at -> 21 1 66 1 54 }T

\ ---- 1. Not supported yet (72): Lean's pre-tactic (with tac), its
\ wildcard, @ and several-tag forms; a hypothesis's argument count (87).
T{ s" n by-induction-with by-rfl | zero => by-rfl by-end end t" proof nfails -> 72 1 63 }T
T{ outcome -> outcome-unsupported }T
T{ s" n by-induction-with by-case: zero => by-rfl by-end by-end end t" proof nfails
   -> 72 1 63 }T
T{ s" n by-induction-with | _ => by-rfl by-end end t" proof nfails -> 72 1 65 }T
T{ s" n by-induction-with | @succ k ih => by-rfl by-end end t" proof nfails -> 72 1 65 }T
T{ s" n by-induction-with | zero | succ => by-rfl by-end end t" proof nfails -> 72 1 70 }T
\ (by-case: _ is read since tactic batch 2b, Lean's case _: by-case:'s @
\ form is still 72)
T{ s" by-case: @zero => by-rfl by-end end t" proof nfails -> 72 1 52 }T
\ Too many values where a hypothesis read since the last tactic word had
\ values below it, which it may take once tactics run: not supported yet
\ (87). One read first takes nothing (ih k by-exact: two values, 86); too
\ many for a word that takes none, or too few, stays a mistake whatever
\ a hypothesis takes.
T{ s\" theorem t Nat explicit: n 0 n + n =\n:= by n by-induction-with\n| succ k ih => n ih by-exact"
   nfails -> 87 3 21 }T
T{ outcome -> outcome-unsupported }T
T{ s" by-intro: h n h by-exact end t" proof nfails -> 87 1 59 }T
T{ s" n by-induction-with | succ k ih => k ih by-exact" proof nfails -> 87 1 83 }T
T{ s" n by-induction-with | succ k ih => ih n by-exact" proof nfails -> 86 1 83 }T
\ (k is a hypothesis too: in ih k by-exact it may take ih.)
T{ s" n by-induction-with | succ k ih => ih k by-exact" proof nfails -> 87 1 83 }T
\ Inside by-rw[ ] every value is a rule: a hypothesis takes nothing there,
\ so leaves no doubt after ]; one applied is written with $ (ih k $).
T{ s" n by-induction-with | succ k ih => by-rw[ ih ] n n by-exact" proof nfails -> 86 1 94 }T
T{ s" n by-induction-with | succ k ih => by-rw[ n ih ] n n by-exact" proof nfails
   -> 86 1 96 }T
T{ s" n by-induction-with | succ k ih => by-rw[ ih k $ ] by-end end t" proof nfails
   -> 71 1 101 }T
T{ 3 kind@ 3 args@ nip 3 0 arg-node kind 3 0 arg-node syn-a@ kind
   -> tac-k-rw 1 syn-k-app syn-k-hyp }T
T{ s" n by-induction-with | succ k ih => by-rw[ k ih ] by-end end t" proof nfails -> 71 1 99 }T
T{ 3 args@ nip 3 0 arg-node kind 3 1 arg-node kind -> 2 syn-k-hyp syn-k-hyp }T
T{ s" by-intro: h h by-rfl end t" proof nfails -> 86 1 57 }T
T{ s" by-intro: h h end t" proof nfails -> 86 1 57 }T
T{ s" by-intro: h by-exact end t" proof nfails -> 86 1 55 }T
\ The doubt ends with its tactic word: after k ih $ by-exact (ih read
\ with k below it), n n by-exact is a mistake again (review fe1g2 L-1).
T{ s" by-intro: h h by-exact n n by-exact end t" proof nfails -> 86 1 70 }T
T{ s" n by-induction-with | succ k ih => k ih $ by-exact n n by-exact" proof nfails
   -> 86 1 98 }T

\ ---- Hypotheses: their scope is their block (an alternative or case;
\ by-intro:'s, the block it is in); a hypothesis newer than a variable of
\ its spelling is read, an older one is not; dotted names; _.
T{ s" n by-induction-with | succ k ih => ih by-exact by-end ih end t" proof nfails -> 1 1 97 }T
T{ s" n by-induction-with | succ k ih => ih by-exact | zero => ih by-exact by-end end t" proof
   nfails -> 1 1 100 }T
T{ s" by-case: zero => by-intro: h h by-exact by-end h end t" proof nfails -> 1 1 90 }T
T{ s" by-intro: h by-case: zero => h by-exact by-end h by-exact end t" proof nfails
   -> 71 1 101 }T
T{ s" n by-induction-with | succ n ih => n by-exact | zero => n by-exact by-end end t" proof
   nfails -> 71 1 117 }T
T{ 3 0 arg-node kind 5 0 arg-node kind -> syn-k-hyp syn-k-var }T
T{ s" n by-induction-with | succ k ih => Nat explicit: ih ih by-exact" proof nfails
   -> 21 1 98 }T
T{ syn-count 1- kind -> syn-k-var }T
T{ s" n by-induction-with | succ a.b ih => ' a.b by-exact by-end end t" proof nfails
   -> 71 1 102 }T
T{ 3 0 arg-node dup kind swap syn-a@ s" a.b" named? -> syn-k-hyp true }T
T{ 2 0 arg-name s" a.b" named? 2 1 arg-name s" ih" named? -> true true }T
T{ s" n by-induction-with | succ _ ih => ih by-exact by-end end t" proof nfails -> 71 1 97 }T
T{ 2 0 arg-name 2 1 arg-name s" ih" named? -> 0 true }T
T{ s" by-intro: _ _ by-exact end t" proof nfails -> 52 1 55 }T
T{ 1 0 arg-name -> 0 }T
\ Names are case-sensitive: IH is not ih.
T{ s" n by-induction-with | succ k IH => ih by-exact by-end end t" proof nfails -> 1 1 78 }T

\ ---- 3. Interfaces: the kernel form keeps its meanings (72 for every
\ tactic word; by is not built there, 51); each code's outcome.
: kform ( c-addr u -- c-addr' u' )
  text0 s" kernel-form theorem t Prop explicit: p p := p " text+ text+ text$ ;
T{ s" by-end end t" kform nfails -> 72 1 47 }T
T{ s" | end t" kform nfails -> 72 1 47 }T
T{ s" ] end t" kform nfails -> 72 1 47 }T
T{ s" => end t" kform nfails -> 72 1 47 }T
T{ s" by-intro: h end t" kform nfails -> 72 1 47 }T
T{ s" by-rw[ end t" kform nfails -> 72 1 47 }T
T{ s" by-rewrite[ end t" kform nfails -> 72 1 47 }T
T{ s" by-induction-with end t" kform nfails -> 72 1 47 }T
T{ s" kernel-form theorem t Prop explicit: p p := by p end t" nfails -> 51 1 45 }T
T{ 80 lf-author-outcome 81 lf-author-outcome 82 lf-author-outcome 83 lf-author-outcome
   -> outcome-unsupported outcome-invalid outcome-invalid outcome-invalid }T
T{ 84 lf-author-outcome 85 lf-author-outcome 86 lf-author-outcome 87 lf-author-outcome
   88 lf-author-outcome
   -> outcome-invalid outcome-invalid outcome-invalid outcome-unsupported outcome-full }T
\ After a run no tactic proof is open, also when it failed inside one
\ (its block still open: outside the declaration, no proof is read); a
\ new run starts with no record.
T{ lf-tactic-proof? lf-author-begin lf-tactic-count -> false 0 }T
T{ s" n by-induction-with | zero => by-rfl end t" proof nfails drop drop -> 82 }T
T{ lf-tactic-proof? tac-read tac-read-open @ 0< -> false false }T

\ ---- 5. Resources: 1,000 nested by-case: blocks, one a line (heap
\ records, no host recursion); a store that may hold 3 steps stops the
\ run full at the fourth (88), an argument store at its first argument
\ too many; a heap that refuses to grow the steps' store, the same.
text0 s\" theorem t Nat explicit: n 0 n + n =\n:= by\n" text+
: cases ( n -- ) 0 ?do s\" by-case: a =>\n" text+ loop ;
: ends ( n -- ) 0 ?do s\" by-end\n" text+ loop ;
1000 cases s\" by-rfl\n" text+ 1000 ends s" end t" text+
T{ text$ nfails -> 71 2004 1 }T
T{ lf-tactic-count 1001 parent@ 1001 kind@ 1000 parent@ -> 1002 1000 tac-k-rfl 999 }T
T{ lf-author-begin 3 tac-steps store-limit! -> outcome-ok }T
T{ s" by-rfl by-rfl by-rfl end t" proof nfails -> 88 1 57 }T
T{ outcome -> outcome-full }T
T{ tac-limit tac-steps store-limit! 1 tac-args store-limit! -> outcome-ok outcome-ok }T
T{ s" n by-exact n by-exact end t" proof nfails -> 88 1 56 }T
T{ targ-limit tac-args store-limit! -> outcome-ok }T
\ The heap refuses: the steps' store shrunk to 16 records must grow for
\ the 17th; its first allocation then fails, the run stops full and
\ nothing is left allocated by the failure.
: rfls ( n -- ) 0 ?do s" by-rfl " text+ loop ;
s" " proof 2drop 20 rfls s" end t" text+
T{ text$ nfails drop drop -> 71 }T
T{ lf-author-begin 16 tac-steps store-limit! tac-limit tac-steps store-limit! -> outcome-ok outcome-ok }T
live-blocks @ constant blocks-before
T{ 1 heap-refusals ! text$ nfails drop drop outcome -> 88 outcome-full }T
T{ live-blocks @ blocks-before = heap-refusals @ -> true 0 }T
T{ text$ nfails drop drop -> 71 }T

\ ---- 6. State: after a failed run, the next gives the verdict it gives
\ alone, with the same record (twice, the same).
: main-text ( -- c-addr u )
  s" n by-induction-with | zero => by-rfl | succ k ih => by-rw[ ' Nat.add_succ ih ] by-end end t"
  proof ;
T{ main-text nfails -> 71 1 129 }T
lf-tactic-count constant steps-alone
5 step tac-to @ constant rw-to-alone
T{ s" n by-induction-with | zero => by-rfl end t" proof nfails drop drop -> 82 }T
T{ main-text nfails lf-tactic-count 5 step tac-to @ -> 71 1 129 steps-alone rw-to-alone }T
T{ main-text nfails lf-tactic-count 5 step tac-to @ -> 71 1 129 steps-alone rw-to-alone }T
T{ depth -> 0 }T
cr .( tactic-syntax.fs: all tests passed) cr
bye
