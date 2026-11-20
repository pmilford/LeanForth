\ Prints the tactic record of a natural LeanForth text (format 1 of
\ src/front/tactic-syntax.fs) and the error its run ends with, for
\ tests/front/check_tactics.py, which compares the lines with
\ tests/front/tactics.golden, and for the unit tests. Test-only. Usage,
\ after src/load/checker.fs, src/load/front.fs and src/cli/check-lf.fs:
\   s" tests/front/01-zero-add-rw.lf" tactic-dump-file
\ The text runs against tests/front/tactic-slice.ndjson's constants (an
\ export of Nat.add_succ, Nat.zero_add and congrArg from Init).
\ One line per step: its index, kind and word's line:col; in N (its block,
\ - for none); text FROM-TO; a header's tag and =>; a block's inner
\ tactics; then its arguments, each a term or a name @ line:col. A term is
\ a numeral, a constant, vN (the binder in slot N), a hypothesis as
\ name#j (j: the argument that gave it its name), ( f a .. ) an
\ application, or [ binop% f a b ], [ binrel% f a b ] and
\ [ rightact% f a b ].

: dump-library ( -- )
  s" tests/front/tactic-slice.ndjson" true lfc-library-open ok? 0= abort" dump: no library" ;
dump-library
' type lf-print-unicode lf-print-setup
: .dec ( n -- ) 0 .r ;
: .pos ( pos -- ) dup 0< if drop ." -" exit then lfa-pos> swap .dec ." :" .dec ;
: .name-id ( id -- ) ?dup if lf-print-name drop else ." _" then ;
: .kind ( kind -- )
  case tac-k-by of ." by" endof tac-k-rfl of ." rfl" endof tac-k-exact of ." exact" endof
    tac-k-intro of ." intro" endof tac-k-induction of ." induction" endof
    tac-k-with of ." induction-with" endof tac-k-alt of ." alt" endof
    tac-k-case of ." case" endof tac-k-rw of ." rw" endof tac-k-rewrite of ." rewrite" endof
    ." ?" endcase ;

\ Terms.
defer .term ( node -- )
: .args ( app -- ) dup syn-b@ 0 ?do space dup i syn-arg .term loop drop ;
: .op ( node -- ) dup syn-a@ .name-id space dup syn-b@ .term space syn-c@ .term ;
: .node ( node -- )
  dup syn-kind@ case
    syn-k-num of syn-a@ .dec endof
    syn-k-var of ." v" syn-a@ .dec endof
    syn-k-const of syn-a@ lfa-decl-name .name-id endof
    syn-k-hyp of dup syn-a@ .name-id ." #" syn-b@ .dec endof
    syn-k-app of ." ( " dup syn-a@ .term .args ."  )" endof
    syn-k-binop of ." [ binop% " .op ."  ]" endof
    syn-k-binrel of ." [ binrel% " .op ."  ]" endof
    syn-k-rightact of ." [ rightact% " .op ."  ]" endof
    ." ?" endcase ;
' .node is .term

\ Steps.
: kind-block? ( kind -- flag ) dup tac-k-with tac-k-rewrite 1+ within swap tac-k-by = or ;
: names? ( kind -- flag ) dup tac-k-alt = over tac-k-case = or swap tac-k-intro = or ;
: .arg ( kind j -- ) lf-tactic-arg >r swap names? if .name-id else .term then ." @" r> .pos ;
: .step-args ( addr -- )
  dup tac-kind @ swap dup tac-first @ swap tac-count @ over + swap
  ?do space dup i .arg loop drop ;
: .parent ( addr -- ) ."  in " tac-parent @ dup 0< if drop ." -" else .dec then ;
: .text ( addr -- ) ."  text " dup tac-from @ .pos ." -" tac-to @ .pos ;
: .header ( addr -- )
  dup tac-arrow @ 0< if drop exit then
  ."  tag " dup tac-name @ .name-id ."  => " tac-arrow @ .pos ;
: .inner ( addr -- )
  dup tac-kind @ kind-block? if ."  inner " tac-inner @ .dec else drop then ;
: .step ( i -- )
  dup .dec space lf-tactic-step dup tac-kind @ .kind space dup tac-at @ .pos
  dup .parent dup .text dup .header dup .inner .step-args cr ;
: tactic-dump ( -- )
  ." tactic record " lf-tactic-format .dec ." : " lf-tactic-count .dec ."  steps" cr
  lf-tactic-count 0 ?do i .step loop ;
: .ending ( -- ) lf-author-code if lf-author-error. else ." ran: ok" then cr ;
: tactic-dump-file ( c-addr u -- ) lf-author-begin lf-author-file drop tactic-dump .ending ;
: tactic-dump-text ( c-addr u -- ) lf-author-begin lf-author-text drop tactic-dump .ending ;
