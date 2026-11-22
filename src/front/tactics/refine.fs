\ t by-refine: Lean's refine t (plan row TB2, tactic batch 3b; mechanism
\ B, holes), a port of Lean 4.35.0's evalRefine and refineCore (src/lean/
\ Lean/Elab/Tactic/ElabTerm.lean:209-228): in the main goal's context the
\ term elaborated against the main goal's type with its new
\ metavariables collected (tactic-core.fs's lf-tac-elab-holes, natural
\ holes refused: a _ unification leaves open is Lean's "don't know how to
\ synthesize placeholder", 461) and tagged with the suffix refine
\ (lf-tac-tag-new), instantiated,
\ the main goal assigned it and the new goals, ?_ and ?: NAME among
\ them, in the order their metavariables were made, in its place. The
\ cases where the value is the main goal or holds it cannot arise: the
\ only way to name the main goal is a ?: NAME that finds a metavariable
\ already (findUserName?), which is not supported yet (139).
\ Lean call list: withMainContext, getMainGoal, replaceMainGoal ->
\ lf-lift-meta-tactic (tactic-core.fs); getMainTarget -> lf-goal-target
\ (meta-tactic/assert.fs); elabTermWithHoles -> lf-tac-elab-holes,
\ lf-tac-tag-new;
\ instantiateMVars -> lf-instantiate!; assign -> lf-mvar-assign.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/assert.fs

tac-shape-term lf-tactic: by-refine constant tac-k-refine
s" refine" tac-k-refine lf-tactic-lean!
: tre-holes ( i goal -- goal e goals )
  swap 0 lf-tac-arg over lf-goal-target drop false lf-tac-elab-holes ;
: tre-assign ( goal e -- ) lf-instantiate! lf-mvar-assign lf-must ;
: tre-tac ( i goal -- goals ) tre-holes c" refine" lf-tac-tag-new >r tre-assign r> ;
: tre-run ( i -- ) dup ['] tre-tac lf-lift-meta-tactic ;
' tre-run tac-k-refine lf-tactic-action!
