\ h a $ by-specialize: Lean's specialize h a (plan row TB2, tactic batch
\ 1), a port of Lean 4.35.0's evalSpecialize (src/lean/Lean/Elab/Tactic/
\ ElabTerm.lean:235-245): in the main goal's context the term elaborated
\ with no expected type and its holes collected (elabTermWithHoles with
\ allowNaturalHoles, the suffix specialize: tactic-core.fs's
\ lf-tac-elab-holes and lf-tac-tag-new; since batch 3b a _ unification
\ leaves open, or a ?_, is a new goal), its head past its lambdas
\ (getLambdaBody, getAppFn) a free variable h, else error 447 with
\ Lean's text; then
\ MVarId.replace of the main goal, h, the term and its type head-beta
\ reduced (meta-tactic/assert.fs's lf-goal-replace: a new h, the old one
\ cleared when nothing depends on it); the new goals, then the new main
\ goal, in the main goal's place (mvarIds' ++ [result.mvarId]).
\ Lean call list: withMainContext, getMainGoal, replaceMainGoal ->
\ lf-lift-meta-tactic (tactic-core.fs); elabTermWithHoles ->
\ lf-tac-elab-holes, lf-tac-tag-new; getLambdaBody, getAppFn ->
\ lf-meta-lambda-body, lf-meta-app-head (meta-spine.fs);
\ inferType, headBeta -> lf-infer!, lf-meta-head-beta; MVarId.replace ->
\ lf-goal-replace (meta-tactic/assert.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/assert.fs

447 lfa-lean s" 'specialize' requires a term of the form `h x_1 .. x_n` "
  lfa-code: lfa-e-specialize
lfa-e-specialize lfa-message-of s" where `h` appears in the local context" lfa-more,
tac-shape-term lf-tactic: by-specialize constant tac-k-specialize
s" specialize" tac-k-specialize lf-tactic-lean!

: tsp-head ( e -- f ) lf-meta-lambda-body lf-meta-app-head ;
: tsp-fvar ( e -- e fvar )
  dup tsp-head dup lf-meta-fvar? 0= if lfa-e-specialize lf-tac-stop then ;
: tsp-type ( e -- type ) lf-infer! lf-meta-head-beta lf-must ;
: tsp-holes ( i -- e goals )
  0 lf-tac-arg -1 true lf-tac-elab-holes c" specialize" lf-tac-tag-new ;
: tsp-replaced ( goal e -- goal' ) tsp-fvar swap dup tsp-type lf-goal-replace ;
: tsp-tac ( i goal -- goals ) swap tsp-holes -rot tsp-replaced run-push lf-tac-must ;
: tsp-run ( i -- ) dup ['] tsp-tac lf-lift-meta-tactic ;
' tsp-run tac-k-specialize lf-tactic-action!
