\ by-calc[ T1 e1 T2 e2 .. ]: Lean's calc T1 := e1 T2 := e2 .. (plan row
\ 9.4.8z12, small tactics 2), a port of Lean 4.35.0's evalCalc
\ (src/lean/Lean/Elab/Tactic/Calc.lean:18-50): closeMainGoalUsing with
\ checkNewUnassigned := false. The main goal's type instantiated is the
\ target; the steps are elaborated and chained (elab-calc.fs's
\ lf-elab-calc-steps) in runTermElab (no postponing after them:
\ tactic-core.fs's lf-tac-with-synth), in the elaborator's
\ configuration; then the chain is the value when its type is defeq the
\ target; else, when the target is a relation er x' y and the chain's x ~
\ b has x defeq x' and b's type defeq x''s, the chain is extended by a new
\ goal er b y (synthetic opaque, tagged the main goal's tag ++ calc.step)
\ through mkCalcTrans, kept when its type is defeq the target; anything
\ else, mkCalcTrans' own errors included (which Lean's try ... catch _
\ takes back), is Lean's ensureHasType with a coercion and then
\ throwCalcFailure, not ported: 131, not supported yet (a failure
\ mkCalcTrans throws, never met on well-typed steps, stops the step: no
\ acceptance either way). The new goals (withCollectingNewGoalsFrom with
\ the main goal's tag and the suffix calc): the chain's metavariables the
\ step made and left open, oldest first (a ?_ in a proof, the last
\ step's goal), a natural one Lean's placeholder error (461), each
\ anonymous one tagged (tagUntaggedGoals); the main goal is assigned the
\ chain and taken off, and the new goals go in front of the other goals
\ (pushGoals, Elab/Tactic/Basic.lean:471: mvarIds ++ goals).
\ The terms are the bracket's (tac-shape-list+: an empty one is 460), in
\ pairs, T then e; an odd count (Lean's first step written alone, a = _
\ := rfl) has no form: 99.
\ Lean call list: closeMainGoalUsing -> lf-close-main-goal-unchecked;
\ runTermElab -> lf-tac-with-synth; Term.elabCalcSteps ->
\ lf-elab-calc-steps; isDefEq -> lf-defeq!; getCalcRelation? ->
\ lf-calc-relation?; mkFreshExprSyntheticOpaqueMVar -> lf-goal-new;
\ Term.mkCalcTrans -> lf-calc-trans; try ... catch _ -> tcx-mismatch;
\ withCollectingNewGoalsFrom -> lf-tac-new-goals, lf-tac-tag-new;
\ popMainGoal, pushGoals -> lf-close-main-goal-unchecked (lf-goals-push).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../elab-calc.fs

tac-shape-list+ lf-tactic: by-calc[ constant tac-k-calc
s" calc" tac-k-calc lf-tactic-lean!

\ ---- The steps: the terms in pairs.
: tcx-steps ( i -- i n ) dup lf-tac-args# dup 1 and if lf-tac-unported then 2/ ;

\ ---- The target (the main goal's type instantiated) and tag, the step
\ record's (tactic-core.fs's tb: closeMainGoalUsing's type and tag).
: tcx-target ( -- target ) tb tb-want @ lf-instantiate! ;
: tcx-tag ( -- tag ) tb tb-goal @ lf-goal-tag ;
\ Not the target's type: 131 (a coercion, then throwCalcFailure).
: tcx-mismatch ( -- ) lfa-e-elab-coercion lf-tac-stop ;
\ The goal x' ~ y and the chain x ~ b: x defeq x', b's type x''s.
: tcx-fits? ( vtype target -- flag )
  2dup lf-calc-lhs swap lf-calc-lhs swap lf-defeq! 0= if 2drop false exit then
  lf-calc-lhs lf-infer! swap lf-calc-rhs lf-infer! swap lf-defeq! ;
\ The last step er b y, and its goal tagged tag ++ calc.step.
: tcx-last ( vtype target -- stype )
  tuck lf-calc-rel swap lf-calc-rhs lf-mk-app swap lf-calc-rhs lf-mk-app ;
: tcx-step-tag ( tag -- tag' ) s" calc.step" lfa-intern lf-name-append-tag ;
: tcx-goal ( stype -- stype goal )
  dup tcx-tag tcx-step-tag lf-mctx-view lf-goal-new lf-must ;
: tcx-tried ( val vtype goal stype -- val' vtype' )
  lf-calc-trans 0= if tcx-mismatch then ;
: tcx-extended ( val vtype stype goal -- val' )
  swap tcx-tried tcx-target lf-defeq! 0= if tcx-mismatch then ;
: tcx-extend ( val vtype -- val' )
  tcx-target lf-calc-rel? 0= if tcx-mismatch then
  dup tcx-target tcx-fits? 0= if tcx-mismatch then
  dup tcx-target tcx-last tcx-goal tcx-extended ;
\ The chain, when its type is the target, else extended.
: tcx-fit ( val vtype -- val' ) dup tcx-target lf-defeq! if drop exit then tcx-extend ;
: tcx-chain ( i -- val ) tcx-steps lf-elab-calc-steps tcx-fit ;
: tcx-elab ( i -- val ) ['] tcx-chain lf-elab-configured ;

\ ---- closeMainGoalUsing's body: the chain and its new goals, which
\ lf-close-main-goal-unchecked pushes in front of the others.
: tcx-goals ( val -- val goals ) dup false lf-tac-new-goals c" calc" lf-tac-tag-new ;
: tcx-calc ( i type tag -- val goals ) 2drop ['] tcx-elab lf-tac-with-synth tcx-goals ;
: tcx-run ( i -- ) dup ['] tcx-calc lf-close-main-goal-unchecked ;
' tcx-run tac-k-calc lf-tactic-action!
