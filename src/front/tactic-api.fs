\ The tactic plug-in interface (docs/design/TACTIC_PLUGINS.md 3; slice
\ a2-ii): what a tactic file of src/front/tactics/ requires, and the word
\ by which it registers itself when it loads, as Lean's tactics do.
\   lf-tactic: ( shape "spelling" -- kind )  a new tactic word, spelt by-
\       and at least one more character (else the load aborts): the next
\       free kind (from 12; the S1/S2 kinds keep 1-11) and its row in the
\       runner (tactic-run.fs; until its run word is set it answers error
\       80, not supported yet), the spelling added to the printer's
\       reserved words (present/print-forth.fs) and to LF-WORDS
\       (author/words.fs: error 72 in the kernel form), its shape
\       (tactic-syntax.fs's tac-shape-plain, tac-shape-term) kept in the
\       row, its natural meaning tap-read, which finds the row by the
\       token's spelling and reads the shape. Usage:
\         tac-shape-plain lf-tactic: by-assumption constant tac-k-assumption
\         s" assumption" tac-k-assumption lf-tactic-lean!
\         ' run-word tac-k-assumption lf-tactic-action!
\ The rest of the interface is the words of the files below: the row
\ setters lf-tactic-action!, lf-tactic-lean!, lf-tactic-plan!,
\ lf-tactic-end! and lf-tac-eval (tactic-run.fs), lfa-code: for a
\ tactic's own error codes (author/errors.fs), the step record and
\ messages (tactic-basic.fs), liftMetaTactic and elabTermForApply
\ (tactic-core.fs), and the tactic library: meta-must.fs, app-builder.fs,
\ telescope.fs and the goal operations of meta-tactic/. A tactic file
\ writes no hook and sets rows only for its own kinds
\ (scripts/check-tactic-plugins.py); docs/development/ADDING_A_TACTIC.md
\ is the guide.
\ Untrusted: a tactic only builds a term for the kernel to check.
\ State: none of its own (the rows, the words and the reserved list it
\ adds to are set while the modules load and read-only afterwards).

require ../lib/lib.fs
require ../author/errors.fs
require ../author/words.fs
require ../author/groups.fs
require ../present/print-forth.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-basic.fs
require ./tactic-core.fs
require ./meta-must.fs
require ./app-builder.fs
require ./telescope.fs
require ./meta-tactic/goal.fs
require ./meta-tactic/apply.fs
require ./meta-tactic/assumption.fs
require ./meta-tactic/constructor.fs

\ The spelling is read three times: >in put back before each.
: tap-again ( in -- in ) dup >in ! ;
: tap-later ( kind -- kind ) ['] lf-tac-later over lf-tactic-action! ;
: tap-kind ( c-addr u -- kind )   \ the row, answering 80 until its run word is set
  lf-tactic-free dup >r lfr-spell r> tap-later ;
\ A tactic word is spelt by- and at least one more character.
: tap-by? ( c-addr u -- flag )
  dup 3 > if drop 3 s" by-" compare 0= else 2drop false then ;
: tap-row ( in c-addr u -- in kind )
  2dup tap-by? 0= abort" lf-tactic: a tactic word is spelt by-..."
  2dup lf-pf-reserved? abort" lf-tactic: a word reserved already"
  2dup lf-pf-reserve-more tap-kind ;
\ Every registered word's natural meaning: the row whose spelling is the
\ token run (the words are few and a row's spelling is unique, lf-tactic:).
: tap-spelled? ( c-addr u kind -- flag ) lf-tac-word compare 0= ;
: tap-row? ( c-addr u kind -- flag )
  dup lf-tactic-row? if tap-spelled? else drop 2drop false then ;
: tap-kind-of ( c-addr u -- kind )
  lf-tactic-kinds# 1+ tac-k-sorry 1+ ?do 2dup i tap-row? if 2drop i unloop exit then loop
  2drop lfa-e-tactic lfa-fail 0 ;
: tap-read ( -- ) lfa-token tap-kind-of dup lf-tactic-shape@ lft-read-as ;
: lf-tactic: ( shape "spelling" -- kind )
  >in @ parse-name tap-row rot over lf-tactic-shape! >r
  tap-again ['] lfa-w-tactic lfa-word >in ! ['] tap-read lfa-natural! r> ;
