\ by-rewrite[ r1 .. rn ] and by-rw[ r1 .. rn ], Lean's rewrite and rw
\ (plan S2, design docs/design/S2_INTERFACE.md 5; moved onto the tactic
\ library by plan 9.4.8l-I, commit C3), after Lean 4.35.0's Elab/Tactic/
\ Rewrite.lean (evalRewriteSeq, withRWRulesSeq, rewriteTarget,
\ elabRewrite, finishElabRewrite) and Init/Tactics.lean's rw macro.
\ - by-rewrite[: each rule in order on the main goal, in its own step
\   record and the goal's context, inside Term.withSynthesize
\   (tactic-core.fs's lf-tac-with-synth): a rule naming a definition,
\   whose equation theorems Lean would use, is not supported yet (99,
\   FE8); the rule elaborated with no expected type, postponing allowed
\   (lf-tac-elab-term); the occurs check (220, the rule and the goal);
\   MVarId.rewrite of the target as stored (meta-tactic/rewrite.fs's
\   lf-goal-rewrite: errors 215-219, 99); then the new metavariables left
\   unassigned, or any other metavariable left in the proof (Lean's new
\   goals), not supported yet (99, slice LA); replaceTargetEq (meta-
\   tactic/goal.fs) and the new goal in the main goal's place.
\ - by-rw[: the same, then try (with_reducible rfl): by-rfl's row
\   (lf-tac-eval) at reducible transparency, a Lean error undone and
\   forgotten (lf-tac-try-lean), anything else thrown on.
\ Errors at the by-rw[ word with the rule's place second, as Lean gives
\ them at the rule: the refusals here and every error of
\ lf-goal-rewrite's own (a Meta failure is the runner's error, with no
\ second place, as an elaboration error is).
\ Lean call list: getArg -> lf-tac-arg, lf-tac-arg-at; Term.withSynthesize
\ -> lf-tac-with-synth; elabTerm stx none true -> lf-tac-elab-term;
\ occursCheck -> lf-mvar-occurs?; MVarId.rewrite -> lf-goal-rewrite;
\ replaceTargetEq -> lf-goal-replace-target-eq; replaceMainGoal ->
\ lf-replace-main; try (with_reducible rfl) -> lf-tac-try-lean,
\ lf-with-reducible, lf-tac-eval.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Its kinds are the runner's tac-k-rewrite and
\ tac-k-rw (fixed kinds, scripts/check-tactic-plugins.py's ownership
\ table).

require ../tactic-api.fs

\ ---- Errors at the rule k: its place second, unless one is set.
: trw-at ( k -- pos ) lf-tac-step swap lf-tac-arg-at ;
: trw-see ( k -- ) lfa-error lfa-err-see @ 0< if trw-at lfa-see! else drop then ;
: trw-stop ( k code -- ) swap trw-see lf-tac-stop ;
: trw-placed ( code k -- ) over lf-author-throw = if trw-see else drop then throw ;

\ ---- The rule: a definition's name refused; elaborated; occurs check.
: trw-node ( k -- node ) lf-tac-step swap lf-tac-arg ;
: trw-definition? ( node -- flag )
  dup syn-kind@ syn-k-const <> if drop false exit then
  syn-a@ lfa-decl-name lf-menv-find ok-then? if lf-menv-kind lf-kind-definition = else
    drop false then ;
: trw-elaborated ( k -- heq )
  dup trw-node trw-definition? if lfa-e-tac-form trw-stop then
  trw-node -1 true lf-tac-elab-term ;
: trw-occurs-free ( k heq -- k heq )
  tb tb-goal @ over lf-mvar-occurs? lf-tac-must 0= if exit then
  dup ['] lf-tac-indented. lf-tac-detail over lfa-e-tac-occurs trw-stop ;

\ ---- MVarId.rewrite of the target, its errors at the rule.
: trw-rewrite ( k heq -- new proof goals )
  swap >r >r tb tb-goal @ tb tb-want @ r> false ['] lf-goal-rewrite catch
  ?dup if >r 2drop 2drop r> r> trw-placed then r> drop ;
: trw-inner ( k -- k new proof goals )
  dup dup trw-elaborated trw-occurs-free trw-rewrite ;
\ finishElabRewrite: new goals, or another metavariable left in the
\ proof, not supported yet (99).
: trw-open? ( proof goals -- flag )
  ['] lf-meta-unassigned? run-filter lf-tac-must run-count 0<>
  swap lf-instantiate-mvars lf-tac-must lf-has-open-mvar? or ;
: trw-closed ( k new proof goals -- new proof )
  over swap trw-open? if 2drop lfa-e-tac-form trw-stop then rot drop ;
: trw-replaced ( new proof -- )
  tb tb-goal @ -rot lf-goal-replace-target-eq 0 swap run-push lf-tac-must lf-replace-main
  lf-tac-must ;
: trw-rule-run ( k i -- ) drop ['] trw-inner lf-tac-with-synth trw-closed trw-replaced ;
: trw-rule ( k i -- ) ['] trw-rule-run lf-tac-step-run ;
: trw-rules ( i -- ) dup lf-tac-args# 0 ?do i over trw-rule loop drop ;

\ ---- try (with_reducible rfl).
: trw-rfl ( -- ) lf-tac-step tac-k-rfl ['] lf-tac-eval lf-with-reducible ;
: trw-w-rw ( i -- ) trw-rules ['] trw-rfl lf-tac-try-lean drop ;
' trw-rules tac-k-rewrite lf-tactic-action!
' trw-w-rw tac-k-rw lf-tactic-action!
