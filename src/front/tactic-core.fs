\ The tactic library's Elab glue (docs/design/TACTIC_PLUGINS.md 2.5;
\ slices a2-ii and a2-iii), after Lean 4.35.0's Elab/Tactic/Basic.lean
\ and Elab/Tactic/ElabTerm.lean:
\   lf-lift-meta-tactic ( i*x i xt -- )  liftMetaTactic (Basic.lean:581):
\       step i runs in a new step record (tactic-basic.fs's
\       lf-tac-step-run: the main goal in tb, its context current), xt
\       ( i*x goal -- goals ) gets the main goal and its new goals (a run)
\       take the main goal's place (replaceMainGoal)
\   lf-tac-elab-for-apply ( node -- e )  elabTermForApply
\       (ElabTerm.lean:264) as evalApplyLikeTactic calls it (:284-292): an
\       identifier resolved with no argument inserted (elab-term.fs's
\       lf-elab-ident), any other term elaborated with no expected type,
\       postponing allowed (lf-tac-elab); the result instantiated; Lean
\       then synthesizes when it is a metavariable, which LeanForth does
\       not port (unsupported, error 99)
\ The tactics' messages and step record stay in tactic-basic.fs for now
\ (the design moves them here; plan row 9.4.8l).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../author/errors.fs
require ./syntax.fs
require ./goals.fs
require ./elab-term.fs
require ./tactic-run.fs
require ./tactic-basic.fs
require ./meta-must.fs

\ ---- liftMetaTactic.
: tcr-lifted ( i*x xt i -- ) drop tb tb-goal @ swap execute lf-replace-main lf-tac-must ;
: lf-lift-meta-tactic ( i*x i xt -- ) swap ['] tcr-lifted lf-tac-step-run ;

\ ---- elabTermForApply.
: tcr-ident ( node -- e ) lf-elab-ident lf-tac-must ;
: tcr-term ( node -- e ) -1 true lf-tac-elab lf-tac-must ;
: tcr-not-mvar ( e -- e ) dup lf-mvar? if lfa-e-tac-form lf-tac-fail then ;
: lf-tac-elab-for-apply ( node -- e )
  dup lf-elab-ident? if tcr-ident else tcr-term then lf-instantiate! tcr-not-mvar ;
base !   \ the BASE this file was loaded with
