\ The tactic registry's dump (tactic plug-in design, slice a2-ii,
\ docs/design/TACTIC_PLUGINS.md 3.1 and 5): after src/load/front.fs, every
\ authoring error code with its outcome and message (the catalogue of
\ author/errors.fs and the codes tactic files add with lfa-code:), every
\ word of the printer's reserved list with whether LF-WORDS holds it, and
\ every tactic kind's row: its spelling, the plan step of a kind not
\ ported (0: it runs), Lean's name for the step log and whether a run
\ word is set. tests/front/check_registry.py compares the lines with
\ tests/front/tactic-registry.golden: a branch that moves tactics must
\ leave every line as it was, and a new tactic only adds its own lines.
\ Usage: gforth src/load/front.fs tests/front/tactic-registry.fs -e "registry-dump bye"
\ Test-only; prints, decides nothing.

decimal
: .dec ( n -- ) 0 .r ;
: .tab ( -- ) 9 emit ;

\ ---- The catalogue: code, outcome, message.
: .message ( message -- )
  dup lfa-message-code @ .dec .tab dup lfa-message-outcome @ .dec .tab
  lfa-message-text type cr ;
: dump-codes ( -- ) ['] .message lf-author-each-message ;

\ ---- The reserved words, each with whether LF-WORDS holds it.
: .in-words ( c-addr u -- ) lf-words search-wordlist if drop ."  word" else ."  -" then ;
: .reserved ( c-addr -- )
  ." reserved " dup count type count .in-words cr ;
: dump-reserved ( -- ) ['] .reserved lf-pf-each-reserved ;

\ ---- The rows: kind, spelling, plan, Lean's name, run word set.
: .row ( kind -- )
  ." kind " dup .dec space dup lf-tac-word type space dup lf-tactic-plan@ .dec
  space dup lf-tac-lean type space lf-tactic-run? if ." run" else ." -" then cr ;
: dump-rows ( -- ) lf-tactic-kinds# 1+ 1 ?do i lf-tactic-row? if i .row then loop ;

: registry-dump ( -- ) dump-codes dump-reserved dump-rows ;
