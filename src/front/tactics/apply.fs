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
\ lf-instantiate!; MVarId.apply with term? `t` -> lf-goal-apply-named
\ (meta-tactic/apply.fs);
\ withSynthesize -> lf-tac-with-synth (tactic-core.fs).
\ lf-tac-apply-const ( goal c-addr u -- goals ): apply c of a macro (a
\ constant named in the source, funext.fs's and trivial.fs's), the same
\ evalApply on the constant c at new universe levels.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../tactic-api.fs

tac-shape-term lf-tactic: by-apply constant tac-k-apply
s" apply" tac-k-apply lf-tactic-lean!

: tap-inner ( goal node -- goals ) lf-tac-elab-for-apply lf-goal-apply-named ;
: tap-tac ( i goal -- goals ) swap 0 lf-tac-arg ['] tap-inner lf-tac-with-synth ;
: tap-run ( i -- ) dup ['] tap-tac lf-lift-meta-tactic ;
' tap-run tac-k-apply lf-tactic-action!

\ apply c written in a macro (funext's apply funext, trivial's apply
\ And.intro): evalApply of the constant c, resolved as an identifier
\ (meta-tactic/apply.fs's lf-goal-apply-const), under withSynthesize.
: lf-tac-apply-const ( goal c-addr u -- goals )
  ['] lf-goal-apply-const lf-tac-with-synth ;
base !   \ the BASE this file was loaded with
