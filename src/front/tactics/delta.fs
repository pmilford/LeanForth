\ ' f by-delta: Lean's delta f on the goal (plan row TB2, tactic batch 1),
\ a port of Lean 4.35.0's evalDelta and deltaTarget (src/lean/Lean/Elab/
\ Tactic/Delta.lean:25-38) for one constant: the main goal's type
\ instantiated (getMainTarget), every application of f in it delta
\ expanded (meta-tactic/delta.fs's lf-delta-expand); a result equal to
\ the target (Lean's ==) is error 448, "Tactic `delta` failed: did not
\ delta reduce [f]" with the goal; else MVarId.replaceTargetDefEq
\ (meta-tactic/goal.fs: @id T goal') and the new goal in the main goal's
\ place. With a trailing at[ ] (plan row TB2 batch 3a, withLocation:
\ tactic-core.fs's lf-with-location), each hypothesis named first
\ (deltaLocalDecl): its local's type expanded, and a result equal to it
\ is error 448 with " [f] at h"; a hypothesis that does change is not
\ supported yet (99: Lean's replaceLocalDeclDefEq gives the same free
\ variable another type in the new goal's context, and LeanForth keeps a
\ free variable's type with the variable, core/local-context.fs); then
\ the goal when |- is named. Not supported yet (99) either: a term that is
\ no constant (Lean's realizeGlobalConstNoOverloadWithInfo resolves an
\ identifier only), several names (Lean's delta f g: a shape with several
\ terms) and at[ * ].
\ Lean call list: getMainGoal, getMainTarget, replaceMainGoal ->
\ lf-lift-target1, lf-lift-local1 (tactic-core.fs) and lf-instantiate!;
\ realizeGlobalConstNoOverloadWithInfo -> tdl-name; deltaExpand ->
\ lf-delta-expand; == -> lf-meta-eqv (term-eqv.fs); throwTacticEx ->
\ lf-tac-ex (tactic-msg.fs); replaceTargetDefEq ->
\ lf-goal-replace-target-defeq (meta-tactic/goal.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/delta.fs

448 lfa-lean s" Tactic `delta` failed: did not delta reduce" lfa-code: lfa-e-delta
tac-shape-term-at lf-tactic: by-delta constant tac-k-delta
s" delta" tac-k-delta lf-tactic-lean!

: tdl-name ( node -- name )
  dup syn-kind@ syn-k-const <> if lf-tac-unported then syn-a@ lfa-decl-name ;
: tdl-array ( name -- )   \ the array of names as Lean prints it
  s"  [" lf-pp-emit lf-pp-name s" ]" lf-pp-emit ;
: tdl-names. ( name -- outcome ) tdl-array outcome-ok ;
: tdl-same ( goal name new -- ) drop ['] tdl-names. lf-tac-inline lfa-e-delta lf-tac-ex ;
: tdl-expand ( goal name -- goal name t new )
  over lf-goal-type lf-instantiate! 2dup swap lf-delta-expand ;
: tdl-tac ( i goal -- goal' )
  swap 0 lf-tac-arg tdl-name tdl-expand tuck lf-meta-eqv lf-tac-must if tdl-same then
  nip lf-goal-replace-target-defeq ;
: tdl-at-target ( i -- i ) ['] tdl-tac lf-lift-target1 ;
\ deltaLocalDecl: did not delta reduce [f] at h, else not supported yet.
: tdl-at. ( fvar -- outcome )
  lf-tac-step 0 lf-tac-arg tdl-name tdl-array s"  at " lf-pp-emit
  lf-fvar-user-name lf-pp-name outcome-ok ;
: tdl-unchanged? ( i fvar -- fvar flag )
  swap 0 lf-tac-arg tdl-name over lf-fvar-type tuck swap lf-delta-expand
  lf-meta-eqv lf-tac-must ;
: tdl-local ( i fvar goal -- goal' )
  -rot tdl-unchanged? if ['] tdl-at. lf-tac-inline lfa-e-delta lf-tac-ex then
  lf-tac-unported ;
: tdl-at-local ( i fvar -- i ) ['] tdl-local lf-lift-local1 ;
: tdl-run ( i -- ) ['] tdl-at-local ['] tdl-at-target lf-at-location ;
' tdl-run tac-k-delta lf-tactic-action!
