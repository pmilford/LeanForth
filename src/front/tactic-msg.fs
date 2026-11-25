\ The tactic library's messages (docs/design/TACTIC_PLUGINS.md 2.5; plan
\ 9.4.8l-I), below the goal operations of meta-tactic/, so that the goal
\ layer needs no tactic file for its errors. Terms print as the goals
\ print them (notation on, the printer's flag put back however printing
\ ends; the current context's names as a goal there shows them, n✝ for
\ an inaccessible n, goal-print.fs's lf-with-names), after Lean 4.35.0's
\ MessageData helpers:
\   lf-tac-term. ( term -- outcome )  m!"{e}": the term instantiated, to
\       the message's sink, named as its goals print it
\   lf-tac-indented. ( term -- outcome )  indentExpr: the term
\       instantiated, on its own line, indented, to the message's sink
\   lf-tac-inline. ( term -- outcome )  inlineExpr: `term`
\   lf-tac-quoted. ( term -- outcome )  m!"'{e}'": 'term' (clear's)
\   lf-tac-quoted-after. ( term -- outcome )  a space, then 'term' (a name
\       in clear's and subst's first lines)
\   lf-tac-nothing. ( x -- outcome )  prints nothing (a framed term with no
\       part before its goal: subst's, rewrite's)
\   lf-tac-spaced. ( term xt -- outcome )  a space, `term`, then xt ( --
\       outcome ) when that printed (getFVarId's and rcases' first lines)
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
\   lf-tac-ex ( goal code -- )  throwTacticEx (Meta/Tactic/Util.lean:
\       43-49): the error code at the step running, its text Lean's
\       "Tactic `t` failed" with or without ": msg", then the goal after a
\       blank line (the goal layer's errors: assumption 381, constructor
\       382 and 383, apply 384, introN 94, left and right 385-388)
\   lf-tac-ex-quoted ( goal x code -- )  the same with 'x' after the
\       text (clear's 440, 442; subst's 479)
\   lf-tac-type-mismatch ( e type expected code -- )  an error at the
\       step running whose detail is lf-has-type-but-expected.'s (exact's
\       Type mismatch 96, setMotiveArg's 212)
\ (lf-tac-lean-error? and lf-tac-forget-lean, the gate of try and
\ observing?, are tactic-run.fs's since plan row TB2, blocks slice 1: its
\ loop takes errors back by them.)
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
\ Named in the current context as its goals print it (goal-print.fs's
\ lf-with-names: n✝ for an inaccessible n, plan 9.4.8l O).
: tmg-named ( term -- outcome ) ['] tmg-noted lf-mctx-view lf-with-names ;
: lf-tac-term. ( term -- outcome ) lf-instantiate-mvars ok-then? if tmg-named then ;
: lf-tac-indented. ( term -- outcome ) s"   " lf-pp-emit lf-tac-term. ;
: lf-tac-line. ( c-addr u term -- outcome ) >r lf-pp-emit r> lf-tac-indented. ;
: tmg-mark ( c-addr -- ) 1 lf-pp-emit ;   \ one character
: tmg-in ( term c-addr -- outcome ) dup tmg-mark swap lf-tac-term. swap tmg-mark ;
: lf-tac-inline. ( term -- outcome ) s" `" drop tmg-in ;
: lf-tac-quoted. ( term -- outcome ) s" '" drop tmg-in ;
: lf-tac-quoted-after. ( term -- outcome ) s"  " lf-pp-emit lf-tac-quoted. ;
: lf-tac-nothing. ( x -- outcome ) drop outcome-ok ;
: lf-tac-spaced. ( term xt -- outcome )
  >r s"  " lf-pp-emit lf-tac-inline. r> ok-and ;
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
\ Whether both types' sorts can be inferred and are not defeq.
: tmg-differ? ( s1 s2 -- flag ) lf-tac-defeq ok? if 0= else drop false then ;
: tmg-sorts? ( type expected -- type expected flag )
  over tmg-sort 0= if false exit then
  over tmg-sort 0= if drop false exit then tmg-differ? ;
: tmg-plain. ( type expected -- outcome ) swap tmg-has. ['] tmg-but. ok-with nip ;
\ Each type with its sort (inferred again: the message is the only user,
\ so the sorts tmg-sorts? compared are not carried across it, review
\ tactic-move L2).
: tmg-sort-of. ( type -- outcome ) lf-infer ok-then? if tmg-of. then ;
: tmg-and-sort ( type outcome -- outcome' ) ['] tmg-sort-of. ok-with nip ;
: tmg-but-sorted. ( expected -- outcome ) dup tmg-but-sort. tmg-and-sort ;
: tmg-sorted. ( type expected -- outcome )
  swap dup tmg-has. tmg-and-sort ['] tmg-but-sorted. ok-with nip ;
: tmg-types. ( type expected -- outcome )
  tmg-sorts? 0= if tmg-plain. exit then tmg-sorted. ;
: lf-has-type-but-expected. ( e type expected -- outcome )
  rot lf-tac-indented. dup ok? if drop tmg-types. else nip nip then ;

\ ---- Details and errors (tactic-run.fs's lf-tac-detail, lf-tac-stop).
: lf-tac-inline ( x xt -- ) lf-author-code if 2drop exit then lf-tac-detail lfa-inline ;
: lf-tac-failed ( xt code -- ) >r 0 swap lf-tac-detail r> lf-tac-stop ;
: lf-tac-ex ( goal code -- ) swap ['] lf-tac-goal-of. lf-tac-detail lf-tac-stop ;
: lf-tac-ex-quoted ( goal x code -- )
  swap ['] lf-tac-quoted-after. lf-tac-inline lf-tac-ex ;
: lf-tac-type-mismatch ( e type expected code -- )
  >r 3 ['] lf-has-type-but-expected. lf-tac-detail-n r> lf-tac-stop ;
\ A Lean error's detail (tactic-run.fs's lf-tac-lean-detail): its term
\ indented, then for synthInstance's (122) useDiagnosticMsg's hint
\ (CoreM.lean:67).
: tmg-diagnostics. ( -- outcome )
  s\" \n\nHint: Additional diagnostic information may be available " lf-pp-emit
  s" using the `set_option diagnostics true` command." lf-pp-emit outcome-ok ;
: tmg-lean-detail ( term code -- outcome )
  swap lf-tac-indented. swap lfa-e-synth-failed = if ['] tmg-diagnostics. ok-and then ;
' tmg-lean-detail is lf-tac-lean-detail
base !   \ the BASE this file was loaded with
