\ by-rfl, Lean's rfl (plan FE1g-4, design docs/design/FE1G_TACTICS.md
\ 5.3; moved onto the tactic library by plan 9.4.8l-I; Iff, HEq and the
\ failure on other goals plan row TB2 batch 3a): Lean 4.35.0's
\ extensible macro rfl, its rules tried newest first, each from a saved
\ state, the error of the last tried (the first registered) reported
\ (Elab/Tactic/Basic.lean's expandEval; tactic-core.fs's lf-tac-macro-alts):
\ exact Iff.rfl (Init/Core.lean:1042), exact HEq.rfl (Init/
\ Tactics.lean:482), then eq_refl and apply_rfl (:480, :477: liftMetaTactic
\ of meta-tactic/goal.fs's lf-goal-refl, MVarId.refl and, on its failure,
\ MVarId.applyRfl, whose errors 97 and 457, and 93 where it is not
\ ported, are the ones shown). exact C is closeMainGoalUsing (tactic-
\ core.fs's lf-close-main-goal-using) of elabTermEnsuringType of the
\ identifier C against the goal's type: the constant at new level
\ metavariables applied to a natural metavariable per (implicit) binder,
\ elabAppArgs's (app-builder.fs's lf-const-meta-applied), its type made
\ defeq the goal's (lf-tac-ensure-type: Type mismatch, 96, a Lean error
\ that the next rule follows), no new metavariable left (95). So a goal
\ that is no reflexive relation fails with a Lean error, which try and
\ first undo: by-rw['s try (with_reducible rfl) and by-rwa['s rfl <|>
\ assumption go on as Lean's do. by-rw[ runs it under with_reducible.
\ Lean call list: macro rules -> lf-tac-macro-alts; exact -> lf-close-main-
\ goal-using, lf-const-meta-applied, lf-tac-ensure-type; eq_refl's
\ MVarId.refl, then apply_rfl's MVarId.applyRfl -> lf-goal-refl
\ (liftMetaTactic: lf-lift-meta-tactic).
\ A gap of the environment, not of Lean: Iff.rfl or HEq.rfl missing from
\ a slice of Init (real Init has both) is 38, marked Lean's error, so the
\ next rule runs as when that rule fails on the goal's type in Lean; it
\ can change only which rule closes the goal (review tb2-blocks1 7).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Its kind is the runner's tac-k-rfl (a fixed
\ kind, scripts/check-tactic-plugins.py's ownership table).

require ../tactic-api.fs

\ The identifier resolved: a constant the environment lacks (a slice of
\ Init) is the elaborator's unknown constant, 38, a Lean error.
: trf-decl ( c-addr u -- d )
  lfa-intern lf-menv-find dup outcome-invalid = if lfa-e-unknown-constant lf-tac-stop then
  lf-tac-must ;
: trf-exact ( type c-addr u -- e )
  trf-decl lf-const-meta-applied drop swap lf-tac-ensure-type ;
: trf-iff ( type tag -- e ) drop s" Iff.rfl" trf-exact ;
: trf-heq ( type tag -- e ) drop s" HEq.rfl" trf-exact ;
: trf-iff-rfl ( -- ) lf-tac-step ['] trf-iff lf-close-main-goal-using ;
: trf-heq-rfl ( -- ) lf-tac-step ['] trf-heq lf-close-main-goal-using ;
: trf-tac ( goal -- goals ) lf-goal-refl 0 ;
: trf-refl ( -- ) lf-tac-step ['] trf-tac lf-lift-meta-tactic ;
: trf-rules ( -- ) ['] trf-refl ['] trf-heq-rfl ['] trf-iff-rfl 3 lf-tac-macro-alts ;
: trf-run ( i -- ) drop trf-rules ;
' trf-run tac-k-rfl lf-tactic-action!
