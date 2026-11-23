\ The new goals a term leaves (plan row TB2, tactic batch 3b; mechanism B,
\ holes), after Lean 4.35.0's Elab/Tactic/ElabTerm.lean:64-134 and
\ Elab/Tactic/Basic.lean:613-629, below the tactics' elaboration glue
\ (tactic-core.fs's lf-tac-elab-holes, lf-tac-tag-new and
\ closeMainGoalUsing):
\   lf-fresh-mvars ( e from -- mvars )  collectFreshMVars's list
\       (getMVarsNoDelayed, filterOldMVars, sortMVarIdsByIndex): the
\       metavariables numbered from `from` on (Lean's mvarCounter saved)
\       that e, instantiated, holds and that are neither assigned nor
\       delayed-assigned, oldest first, a run (lib/runs.fs). A
\       delayed-assigned metavariable in e, whose pending one Lean's
\       collectMVars enters, is not supported yet (99).
\   lf-natural-mvars ( mvars -- mvars' )  those of kind natural (the
\       filter withCollectingNewGoalsFrom applies without
\       allowNaturalHoles), in order, a new run.
\   lf-tac-log-unassigned ( mvars -- )  logUnassignedAndAbort
\       (ElabTerm.lean:64) over the error infos of holes
\       (Term/TermElabM.lean:901-956): nothing for none; when each one is
\       a hole (elab-app.fs's lf-elab-hole), the newest one's error, 461,
\       Lean's "don't know how to synthesize placeholder" with "context:"
\       and the hole's goal below (at the step's word; Lean's place is the
\       hole's); a hole that is an application's argument, whose message
\       Lean ends with the argument's name, is not supported yet (99); any
\       other metavariable is error 95 (an implicit argument's message,
\       not ported: exact's answer before batch 3b).
\   lf-tag-untagged ( goals suffix parent -- )  tagUntaggedGoals: the
\       goals' anonymous ones tagged parent when there is one, else
\       parent ++ suffix_1, suffix_2, .. in order (suffix a counted
\       string, Lean's one-part Name, with appendIndexAfter; the parts
\       joined by meta-tactic/goal.fs's lf-name-append-tag; refine's,
\       specialize's and tactics/and-intros.fs's). A suffix_idx longer
\       than 64 characters is a fault (invalid).
\ Errors are thrown as authoring errors at the step running
\ (tactic-run.fs's lf-tac-stop), Meta failures as outcomes (meta-must.fs).
\ Cost: lf-fresh-mvars walks e once for each metavariable made since
\ `from` (O(k*|e|), where Lean's getMVars walks it once and keeps what
\ it meets); a step makes a few, so this is fine at today's sizes
\ (review tb2-batch3b 10).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: tng-frames (lf-tag-untagged's frame per call open, meta-must.fs's
\ lf-with-record), in the checker context (ADR 0009); no other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bounds.fs
require ../lib/runs.fs
require ../lib/find.fs
require ../lib/decimal.fs
require ../author/errors.fs
require ./mvars.fs
require ./term-find.fs
require ./elab-app.fs
require ./tactic-run.fs
require ./tactic-msg.fs
require ./meta-must.fs
require ./meta-tactic/goal.fs

\ ---- collectFreshMVars: metavariable n kept when open and held by e.
: tng-sought? ( mvar leaf -- mvar flag ) over = ;
: tng-in? ( e mvar -- flag ) ['] tng-sought? lf-term-holds-with? lf-must ;
\ (e is instantiated and holds no delayed-assigned metavariable, which is
\ refused first: every metavariable it holds is open.)
: tng-holds? ( e n -- flag ) lf-mvar-at tng-in? ;
: tng-add ( e run n -- e run' )
  >r over r@ tng-holds? r> swap if lf-mvar-at lf-run+ else drop then ;
: tng-collect ( e from -- mvars ) 0 swap lf-mvar-count swap ?do i tng-add loop nip ;
: tng-undelayed ( e -- e )
  dup ['] lf-mvar-delayed? lf-term-holds? lf-must if lf-tac-unported then ;
: lf-fresh-mvars ( e from -- mvars )
  swap lf-instantiate! tng-undelayed swap tng-collect ;
: tng-natural? ( mvar -- flag ) lf-mvar-kind if mv-natural = else false then ;
: lf-natural-mvars ( mvars -- mvars' ) ['] tng-natural? run-filter lf-must ;

\ ---- logUnassignedAndAbort, the holes' error infos.
461 lfa-lean s" don't know how to synthesize placeholder"
  lfa-code: lfa-e-tac-placeholder
: tng-hole? ( mvar -- flag ) lf-elab-hole dup if nip nip then ;
: tng-other? ( run k -- run flag ) over swap run@ tng-hole? 0= ;
: tng-context. ( mvar -- outcome ) s" context:" lf-pp-emit lf-tac-goal-of. ;
: tng-placeholder ( mvar -- )
  dup lf-elab-hole drop nip if drop lf-tac-unported then
  ['] tng-context. lf-tac-detail lfa-e-tac-placeholder lf-tac-stop ;
: tng-others? ( mvars -- flag ) dup run-count ['] tng-other? find-index dup if nip then ;
: lf-tac-log-unassigned ( mvars -- )
  dup run-count 0= if drop exit then
  dup tng-others? if drop lfa-e-tac-unassigned lf-tac-fail then run-last tng-placeholder ;

\ ---- tagUntaggedGoals, a frame per call: the parent's tag, the suffix,
\ whether one goal is anonymous, how many were tagged so far, and the
\ text of suffix_idx.
64 constant tng-text#     \ room for suffix_idx, in characters
begin-structure /tng
  field: tng-parent
  field: tng-suffix
  field: tng-one
  field: tng-idx
  cell tng-text# chars + +field tng-text   \ a cell-counted text (lib/bounds.fs)
end-structure
/tng context-slab: tng-frames
: tng ( -- frame ) tng-frames slab-last ;
: tng-untagged? ( run k -- run flag ) over swap run@ lf-goal-tag 0= ;
: tng-anonymous# ( run -- n ) dup run-count ['] tng-untagged? count-index ;
\ suffix_idx (appendIndexAfter), written in the frame's text; one longer
\ than tng-text# characters is a fault (invalid).
: tng-put ( c-addr u -- ) tng tng-text tng-text# cell-counted+? flag>outcome lf-must ;
: tng-index-name ( suffix idx -- name )
  0 tng tng-text ! swap count tng-put s" _" tng-put u>decimal tng-put
  tng tng-text cell-count lfa-intern ;
: tng-next-tag ( -- tag )
  1 tng tng-idx +! tng tng-parent @ tng tng-one @ if exit then
  tng tng-suffix @ tng tng-idx @ tng-index-name lf-name-append-tag ;
: tng-tag ( goal -- outcome )
  dup lf-goal-tag if drop outcome-ok exit then tng-next-tag lf-mvar-tag! ;
: tng-run ( goals suffix parent -- )
  tng tng-parent ! tng tng-suffix ! dup tng-anonymous# 1 = tng tng-one !
  ['] tng-tag run-each lf-must ;
: lf-tag-untagged ( goals suffix parent -- ) tng-frames ['] tng-run lf-with-record ;
base !   \ the BASE this file was loaded with
