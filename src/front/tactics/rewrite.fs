\ by-rewrite[ r1 .. rn ] and by-rw[ r1 .. rn ], Lean's rewrite and rw
\ (plan S2, design docs/design/S2_INTERFACE.md 5; moved onto the tactic
\ library by plan 9.4.8l-I, commit C3), after Lean 4.35.0's Elab/Tactic/
\ Rewrite.lean (evalRewriteSeq, withRWRulesSeq, rewriteTarget,
\ elabRewrite, finishElabRewrite) and Init/Tactics.lean's rw macro.
\ - by-rewrite[: each rule in order on the main goal (a rule followed by
\   <- right to left: Lean's ← h, withRWRulesSeq's symm), in its own step
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
\   With a trailing at: (plan row TB2 batch 3a), each rule runs at each
\   location in turn (withLocation, tactic-core.fs's lf-with-location):
\   a hypothesis named (getFVarId by its name, so one an earlier rule
\   replaced is found again) is rewritten as above with its local's type
\   as stored (rewriteLocalDeclCore), then replaceLocalDecl (meta-tactic/
\   assert.fs: the new hypothesis of the same name where its type allows,
\   the old one cleared unless something depends on it); then the goal
\   when |- is named. at: * is not supported yet (99).
\ - by-rw[: the same, then try (with_reducible rfl): by-rfl's row
\   (lf-tac-rfl-reducible) at reducible transparency, a Lean error undone and
\   forgotten (lf-tac-try-lean), anything else thrown on.
\ Errors at the by-rw[ word with the rule's place second, as Lean gives
\ them at the rule: the refusals here and every error of
\ lf-goal-rewrite's own (a Meta failure is the runner's error, with no
\ second place, as an elaboration error is).
\ Lean call list: getArg -> lf-tac-arg, lf-tac-arg-at; Term.withSynthesize
\ -> lf-tac-with-synth; elabTerm stx none true -> lf-tac-elab-term;
\ occursCheck -> lf-mvar-occurs?; the rule's symm flag ->
\ lf-tac-arg-symm?; MVarId.rewrite -> lf-goal-rewrite;
\ replaceTargetEq -> lf-goal-replace-target-eq; replaceMainGoal ->
\ lf-replace-main; try (with_reducible rfl) -> lf-tac-try-lean,
\ lf-tac-rfl-reducible; withLocation -> lf-with-location; getFVarId ->
\ lf-tac-loc-fvar; replaceLocalDecl -> lf-goal-replace-local-decl.
\ trw-local ( fvar k i -- fvar' ) is rewriteLocalDeclCore of rule k of
\ step i (tactics/rwa.fs's at h).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Its kinds are the runner's tac-k-rewrite and
\ tac-k-rw (fixed kinds, scripts/check-tactic-plugins.py's ownership
\ table).

require ../tactic-api.fs
require ../meta-tactic/assert.fs

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

\ ---- MVarId.rewrite of the target, right to left for a rule written
\ with <- (Lean's ←, symm), its errors at the rule.
: trw-symm? ( k -- flag ) lf-tac-step swap lf-tac-arg-symm? ;
: trw-call ( e heq k -- new proof goals code )
  trw-symm? >r >r tb tb-goal @ swap r> r> ['] lf-goal-rewrite catch ;
: trw-rewrite ( e k heq -- new proof goals )
  over >r swap trw-call ?dup if >r 2drop 2drop r> r> trw-placed then r> drop ;
\ Rule k rewriting e: the goal's type (rewriteTarget) or a hypothesis's
\ (rewriteLocalDeclCore: its local's type as stored).
: trw-inner ( e k -- k new proof goals )
  tuck dup trw-elaborated trw-occurs-free trw-rewrite ;
\ finishElabRewrite: new goals, or another metavariable left in the
\ proof, not supported yet (99).
: trw-open? ( proof goals -- flag )
  ['] lf-meta-unassigned? run-filter lf-tac-must run-count 0<>
  swap lf-instantiate-mvars lf-tac-must lf-has-open-mvar? or ;
: trw-closed ( k new proof goals -- new proof )
  over swap trw-open? if 2drop lfa-e-tac-form trw-stop then rot drop ;
: trw-main! ( goal' -- ) lf-goals1 lf-replace-main lf-tac-must ;
: trw-replaced ( new proof -- ) tb tb-goal @ -rot lf-goal-replace-target-eq trw-main! ;
: trw-target-run ( k i -- )
  drop tb tb-want @ swap ['] trw-inner lf-tac-with-synth trw-closed trw-replaced ;
\ rewriteLocalDeclCore: replaceLocalDecl outside withSynthesize, the new
\ goal in the main goal's place; the new hypothesis given (rwa's).
: trw-local-replaced ( fvar new proof -- fvar' )
  2>r tb tb-goal @ swap 2r> lf-goal-replace-local-decl swap trw-main! ;
: trw-local-inner ( fvar k -- fvar new proof )
  over lf-fvar-type swap ['] trw-inner lf-tac-with-synth trw-closed ;
: trw-local-run ( fvar k i -- fvar' ) drop trw-local-inner trw-local-replaced ;
: trw-local ( fvar k i -- fvar' ) ['] trw-local-run lf-tac-step-run ;
\ withLocation per rule (evalRewriteSeq): each hypothesis named, then the
\ goal (named, or no at:).
: trw-at-local ( k i fvar -- k i ) -rot 2dup 2>r trw-local drop 2r> ;
: trw-at-target ( k i -- k i ) 2dup ['] trw-target-run lf-tac-step-run ;
: trw-rule ( k i -- ) dup ['] trw-at-local ['] trw-at-target lf-with-location 2drop ;
: trw-rules ( i -- ) dup lf-tac-args# 0 ?do i over trw-rule loop drop ;

\ ---- try (with_reducible rfl).
: trw-w-rw ( i -- ) trw-rules ['] lf-tac-rfl-reducible lf-tac-try-lean drop ;
' trw-rules tac-k-rewrite lf-tactic-action!
' trw-w-rw tac-k-rw lf-tactic-action!
