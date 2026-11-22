\ h by-revert: Lean's revert h, one hypothesis (plan row TB2, tactic
\ batch 1), a port of Lean 4.35.0's evalRevert (src/lean/Lean/Elab/
\ Tactic/BuiltinTactic.lean:410-415) for one term: in the main goal's
\ context getFVarId (tactic-core.fs's lf-tac-get-fvar: error 389 for a
\ term that is no free variable), then MVarId.revert of the main goal
\ (meta-tactic/revert.fs's lf-goal-revert: h and every later hypothesis
\ that depends on it become binders of the goal again), the new goal in
\ the main goal's place. by-revert[ h1 h2 ] (plan row TB2, tactic batch
\ 3b): Lean's revert h1 h2, the names getFVarIds resolves in the main
\ goal's context (tactic-core.fs's lf-tac-arg-fvars: 455 for a name no
\ local has), all reverted at once (Lean's order: the context's).
\ Lean call list: getFVarIds -> lf-tac-get-fvar; getMainGoal,
\ replaceMainGoal [mvarId] -> lf-lift-meta-tactic1 (tactic-core.fs);
\ MVarId.revert -> lf-goal-revert.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/revert.fs

tac-shape-term lf-tactic: by-revert constant tac-k-revert
s" revert" tac-k-revert lf-tactic-lean!
: trv-tac ( i goal -- goal' )
  swap 0 lf-tac-arg lf-tac-get-fvar 0 swap run-push lf-tac-must lf-goal-revert drop ;
: trv-run ( i -- ) dup ['] trv-tac lf-lift-meta-tactic1 ;
' trv-run tac-k-revert lf-tactic-action!
tac-shape-hyps lf-tactic: by-revert[ constant tac-k-revert-list
s" revert" tac-k-revert-list lf-tactic-lean!
: trv-list-tac ( i goal -- goal' ) swap lf-tac-arg-fvars lf-goal-revert drop ;
: trv-list ( i -- ) dup ['] trv-list-tac lf-lift-meta-tactic1 ;
' trv-list tac-k-revert-list lf-tactic-action!
