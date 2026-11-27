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
\ through mkCalcTrans (a Lean error there caught, as Lean's try ... catch
\ _), kept when its type is defeq the target; anything else is Lean's
\ ensureHasType with a coercion and then throwCalcFailure, not ported:
\ 131, not supported yet. The new goals (withCollectingNewGoalsFrom with
\ the main goal's tag and the suffix calc): the chain's metavariables the
\ step made and left open, oldest first (a ?_ in a proof, the last
\ step's goal), a natural one Lean's placeholder error (461), each
\ anonymous one tagged (tagUntaggedGoals), pushed after the other goals
\ (pushGoals); then the main goal is assigned the chain and taken off.
\ The terms are the bracket's (tac-shape-list+: an empty one is 460), in
\ pairs, T then e; an odd count (Lean's first step written alone, a = _
\ := rfl) has no form: 99.
\ Lean call list: closeMainGoalUsing -> lf-close-main-goal-unchecked;
\ runTermElab -> lf-tac-with-synth; Term.elabCalcSteps ->
\ lf-elab-calc-steps; isDefEq -> lf-defeq!; getCalcRelation? ->
\ lf-calc-relation?; mkFreshExprSyntheticOpaqueMVar -> lf-goal-new;
\ Term.mkCalcTrans -> lf-calc-trans; try ... catch _ -> lf-meta-try;
\ withCollectingNewGoalsFrom -> lf-tac-new-goals, lf-tac-tag-new;
\ pushGoals -> lf-goals-append.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../elab-calc.fs

tac-shape-list+ lf-tactic: by-calc[ constant tac-k-calc
s" calc" tac-k-calc lf-tactic-lean!

\ ---- The steps: the terms in pairs.
: tcx-steps ( i -- i n ) dup lf-tac-args# dup 1 and if lf-tac-unported then 2/ ;

\ ---- Not the target's type: 131 (a coercion, then throwCalcFailure).
: tcx-mismatch ( -- ) lfa-e-elab-coercion lf-tac-stop ;
\ The goal x' ~ y and the chain x ~ b: x defeq x', b's type x''s.
: tcx-fits? ( vtype target -- flag )
  2dup lf-calc-lhs swap lf-calc-lhs swap lf-defeq! 0= if 2drop false exit then
  lf-calc-lhs lf-infer! swap lf-calc-rhs lf-infer! swap lf-defeq! ;
\ The last step er b y, and its goal tagged tag ++ calc.step.
: tcx-last ( vtype target -- stype )
  tuck lf-calc-rel swap lf-calc-rhs lf-mk-app swap lf-calc-rhs lf-mk-app ;
: tcx-step-tag ( tag -- tag' ) s" calc.step" lfa-intern lf-name-append-tag ;
: tcx-goal ( stype tag -- stype goal )
  over swap tcx-step-tag lf-mctx-view lf-goal-new lf-must ;
: tcx-tried ( val vtype goal stype -- val' vtype' ) lf-calc-trans if tcx-mismatch then ;
: tcx-extended ( val vtype target stype goal -- val' )
  rot >r swap ['] tcx-tried 4 2 lf-meta-try 0= if tcx-mismatch then
  r> lf-defeq! 0= if tcx-mismatch then ;
: tcx-extend ( val vtype target tag -- val' )
  over lf-calc-relation? 0= if tcx-mismatch then 2drop drop
  >r 2dup tcx-fits? 0= if tcx-mismatch then 2dup tcx-last r> tcx-goal tcx-extended ;
\ The chain, when its type is the target, else extended.
: tcx-fit ( val vtype target tag -- val' )
  2 pick 2 pick lf-defeq! if 2drop drop exit then tcx-extend ;
: tcx-chain ( i target tag -- val ) >r swap tcx-steps lf-elab-calc-steps rot r> tcx-fit ;
: tcx-elab ( i target tag -- val ) ['] tcx-chain lf-elab-configured ;

\ ---- closeMainGoalUsing's body: the chain, its new goals pushed.
: tcx-goals ( val -- val )
  dup false lf-tac-new-goals c" calc" lf-tac-tag-new lf-goals-append lf-tac-must ;
: tcx-calc ( i type tag -- val ) >r lf-instantiate! r> ['] tcx-elab lf-tac-with-synth tcx-goals ;
: tcx-run ( i -- ) dup ['] tcx-calc lf-close-main-goal-unchecked ;
' tcx-run tac-k-calc lf-tactic-action!
