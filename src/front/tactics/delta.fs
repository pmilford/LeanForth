\ ' f by-delta: Lean's delta f on the goal (plan row TB2, tactic batch 1),
\ a port of Lean 4.35.0's evalDelta and deltaTarget (src/lean/Lean/Elab/
\ Tactic/Delta.lean:25-38) for one constant: the main goal's type
\ instantiated (getMainTarget), every application of f in it delta
\ expanded (meta-tactic/delta.fs's lf-delta-expand); a result equal to
\ the target (Lean's ==) is error 448, "Tactic `delta` failed: did not
\ delta reduce [f]" with the goal; else MVarId.replaceTargetDefEq
\ (meta-tactic/goal.fs: @id T goal') and the new goal in the main goal's
\ place. Not supported yet (99): a term that is no constant (Lean's
\ realizeGlobalConstNoOverloadWithInfo resolves an identifier only),
\ several names (Lean's delta f g: a shape with several terms) and the
\ at h form (plan TB2 batch 3).
\ Lean call list: getMainGoal, getMainTarget, replaceMainGoal ->
\ lf-lift-meta-tactic1 (tactic-core.fs) and lf-instantiate!;
\ realizeGlobalConstNoOverloadWithInfo -> tdl-name; deltaExpand ->
\ lf-delta-expand; == -> lf-meta-eqv (term-eqv.fs); throwTacticEx ->
\ lf-tac-ex (tactic-msg.fs); replaceTargetDefEq ->
\ lf-goal-replace-target-defeq (meta-tactic/goal.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/delta.fs

448 outcome-invalid s" Tactic `delta` failed: did not delta reduce" lfa-code: lfa-e-delta
tac-shape-term lf-tactic: by-delta constant tac-k-delta
s" delta" tac-k-delta lf-tactic-lean!

: tdl-name ( node -- name )
  dup syn-kind@ syn-k-const <> if lfa-e-tac-form lf-tac-fail then syn-a@ lfa-decl-name ;
: tdl-names. ( name -- outcome )   \ the array of names as Lean prints it
  s"  [" lf-pp-emit lf-pp-name s" ]" lf-pp-emit outcome-ok ;
: tdl-same ( goal name new -- ) drop ['] tdl-names. lf-tac-inline lfa-e-delta lf-tac-ex ;
: tdl-expand ( goal name -- goal name t new )
  over lf-goal-type lf-instantiate! 2dup swap lf-delta-expand ;
: tdl-tac ( i goal -- goal' )
  swap 0 lf-tac-arg tdl-name tdl-expand tuck lf-meta-eqv lf-tac-must if tdl-same then
  nip lf-goal-replace-target-defeq ;
: tdl-run ( i -- ) dup ['] tdl-tac lf-lift-meta-tactic1 ;
' tdl-run tac-k-delta lf-tactic-action!
