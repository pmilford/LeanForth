\ The tactic library's messages (docs/design/TACTIC_PLUGINS.md 2.5; plan
\ 9.4.8l-I), below the goal operations of meta-tactic/, so that the goal
\ layer needs no tactic file for its errors. Terms print as the goals
\ print them (notation on, the printer's flag put back however printing
\ ends), after Lean 4.35.0's MessageData helpers:
\   lf-tac-indented. ( term -- outcome )  indentExpr: the term
\       instantiated, on its own line, indented, to the message's sink
\   lf-tac-inline. ( term -- outcome )  inlineExpr: `term`
\   lf-tac-line. ( c-addr u term -- outcome )  a label, then the term
\       indented on the next line
\   lf-tac-goal-of. ( goal -- outcome )  a goal after a line break (Lean's
\       throwTacticEx with no message: "Tactic `t` failed\n\ngoal")
\   lf-tac-goal-below. ( goal -- outcome )  a goal after a blank line
\       (throwTacticEx with a message: its text, then the goal)
\   lf-tac-framed-with. ( goal x xt term -- outcome )  term indented,
\       what xt ( x -- outcome ) prints of x, then the goal after a blank
\       line; the first part that does not print ends the message, its
\       outcome kept
\   lf-tac-.name ( name -- )  a name between backquotes, m!"`{n}`"
\   lf-has-type-but-expected. ( e type expected -- outcome )
\       throwTypeMismatchError's text (Elab/Term/TermElabM.lean:1134) with
\       mkHasTypeButIsExpectedMsg (Meta/Check.lean:224): e indented, then
\       its type and the type expected; when both types' own types can be
\       inferred and are not defeq (lf-tac-defeq), each named "of sort"
\   lf-tac-inline ( x xt -- )  a detail xt ( x -- outcome ) printed on
\       the message's own line, unless an error is recorded already
\   lf-tac-failed ( xt code -- )  an error at the step running whose
\       detail xt ( 0 -- outcome ) prints
\   lf-tac-lean-error? ( code -- flag )  whether a THROW code is a Lean
\       error that try and observing? catch: an authoring error whose
\       outcome is invalid, or a library rejection; never unsupported, no
\       room, no fuel or a fault (Lean's try never catches a runtime
\       exception, CoreM.lean:806-810, and a gap of LeanForth's stays one)
\   lf-tac-forget-lean ( code -- )  a Lean error forgotten (the message
\       dropped), any other code thrown on
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../present/print-job.fs
require ../present/term-printer.fs
require ../author/errors.fs
require ./instantiate.fs
require ./goal-print.fs
require ./infer.fs
require ./tactic-run.fs
require ./meta-must.fs

\ ---- Terms and names.
: tmg-noted ( term -- outcome ) lf-print-sink true lf-print-to ;
: tmg-term. ( term -- outcome ) lf-instantiate-mvars ok-then? if tmg-noted then ;
: lf-tac-indented. ( term -- outcome ) s"   " lf-pp-emit tmg-term. ;
: lf-tac-line. ( c-addr u term -- outcome ) >r lf-pp-emit r> lf-tac-indented. ;
: lf-tac-inline. ( term -- outcome ) s" `" lf-pp-emit tmg-term. s" `" lf-pp-emit ;
: lf-tac-goal-of. ( goal -- outcome ) s\" \n" lf-pp-emit lf-goal-print ;
: lf-tac-goal-below. ( goal -- outcome ) s\" \n\n" lf-pp-emit lf-goal-print ;
: lf-tac-.name ( name -- ) s" `" lf-pp-emit lf-pp-name s" `" lf-pp-emit ;

\ ---- mkHasTypeButIsExpectedMsg. A step after another (outcome.fs's
\ ok-with, then nip): xt ( x -- outcome ) when the outcome so far is ok,
\ else x dropped and the outcome kept.
\ A term framed: indented, x as xt prints it, the goal.
: lf-tac-framed-with. ( goal x xt term -- outcome )
  lf-tac-indented. swap ok-with nip ['] lf-tac-goal-below. ok-with nip ;
: tmg-has. ( type -- outcome ) >r s\" \nhas type\n" r> lf-tac-line. ;
: tmg-but. ( expected -- outcome )
  >r s\" \nbut is expected to have type\n" r> lf-tac-line. ;
: tmg-of. ( sort -- outcome ) s\" \nof sort " lf-pp-emit lf-tac-inline. ;
: tmg-but-sort. ( expected -- outcome )
  s"  but is expected to have type" lf-pp-emit >r s\" \n" r> lf-tac-line. ;
: tmg-sort ( t -- sort true | false ) lf-infer ok? dup 0= if nip then ;
\ Both types' sorts, when both can be inferred and are not defeq.
: tmg-differ? ( s1 s2 -- s1 s2 flag ) 2dup lf-tac-defeq ok? if 0= else drop false then ;
: tmg-sorts ( type expected -- type expected s1 s2 true | type expected false )
  over tmg-sort 0= if false exit then
  over tmg-sort 0= if drop false exit then tmg-differ? dup if exit then nip nip ;
: tmg-plain. ( type expected -- outcome ) swap tmg-has. ['] tmg-but. ok-with nip ;
\ (printed in the order type, s1, expected, s2: the next to print on top)
: tmg-sorted. ( s2 expected s1 type -- outcome )
  tmg-has. ['] tmg-of. ok-with nip ['] tmg-but-sort. ok-with nip ['] tmg-of. ok-with nip ;
: tmg-order ( type expected s1 s2 -- s2 expected s1 type ) -rot 3 roll ;
: tmg-types. ( type expected -- outcome )
  tmg-sorts if tmg-order tmg-sorted. exit then tmg-plain. ;
: lf-has-type-but-expected. ( e type expected -- outcome )
  rot lf-tac-indented. dup ok? if drop tmg-types. else nip nip then ;

\ ---- Details and errors (tactic-run.fs's lf-tac-detail, lf-tac-stop).
: lf-tac-inline ( x xt -- ) lf-author-code if 2drop exit then lf-tac-detail lfa-inline ;
: lf-tac-failed ( xt code -- ) >r 0 swap lf-tac-detail r> lf-tac-stop ;

\ ---- Lean's errors, as try and observing? catch them.
: tmg-authored? ( -- flag ) lf-author-code lf-author-outcome outcome-invalid = ;
: tmg-rejected? ( code -- flag )
  dup lf-meta-thrown? if lf-meta-outcome outcome-rejected = else drop false then ;
: lf-tac-lean-error? ( code -- flag )
  dup lf-author-throw = if drop tmg-authored? else tmg-rejected? then ;
: lf-tac-forget-lean ( code -- )
  dup lf-tac-lean-error? 0= if throw then drop lf-tac-forget ;
base !   \ the BASE this file was loaded with
