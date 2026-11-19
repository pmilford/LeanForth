\ t by-apply: Lean's apply t (slice a2-iii of docs/design/TACTIC_PLUGINS.md;
\ the owner approved the word on 2026-11-18), a port of Lean 4.35.0's
\ evalApply and evalApplyLikeTactic (src/lean/Lean/Elab/Tactic/
\ ElabTerm.lean:284-298): in the main goal's context, t elaborated as
\ elabTermForApply does (tactic-core.fs: an identifier with no argument
\ inserted, any other term with no expected type, postponing allowed),
\ MVarId.apply of the main goal and t (meta-tactic/apply.fs), the pending
\ problems synthesized with no postponing (the elaborator's
\ withSynthesize, as by-rw[ does), and the new goals in the main goal's
\ place (liftMetaTactic). Errors: 380 (no argument count fits: Lean's
\ "could not unify"), 125 (an instance not found), 384, 99 (not ported:
\ t a metavariable, or holding one, after elaboration).
\ Lean call list: withMainContext, getMainGoal, replaceMainGoal ->
\ lf-lift-meta-tactic (tactic-core.fs); elabTermForApply ->
\ lf-tac-elab-for-apply (tactic-core.fs); instantiateMVars ->
\ lf-instantiate!; MVarId.apply -> lf-goal-apply (meta-tactic/apply.fs);
\ synthesizeSyntheticMVarsNoPostponing -> lf-elab-with-synth with
\ lf-postpone-no (elab-pending.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the step record's fields after tb's (tap). Loads in decimal
\ whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../tactic-api.fs
require ../elab-pending.fs

tac-shape-term lf-tactic: by-apply constant tac-k-apply
s" apply" tac-k-apply lf-tactic-lean!

begin-structure /tap      \ the step's fields, after tb's
  /tb +field tap-tb
  field: tap-node         \ t, a syntax node
  field: tap-goals        \ the new goals, a run
end-structure
/tap lf-tac-work-cells cells >
[if] .( tactics/apply.fs: its fields are wider than a step record) cr abort [then]
: tap ( -- addr ) lf-tac-record ;

: tap-inner ( -- )
  tap tap-node @ lf-tac-elab-for-apply tb tb-goal @ swap lf-goal-apply tap tap-goals ! ;
: tap-node! ( i -- ) 0 lf-tac-arg tap tap-node ! ;
: tap-tac ( i goal -- goals )
  drop tap-node! ['] tap-inner lf-postpone-no lf-elab-with-synth lf-tac-must
  tap tap-goals @ ;
: tap-run ( i -- ) dup ['] tap-tac lf-lift-meta-tactic ;
' tap-run tac-k-apply lf-tactic-action!
base !   \ the BASE this file was loaded with
