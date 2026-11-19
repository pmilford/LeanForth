\ t by-induction, t by-induction-with and its | alternatives, Lean's
\ induction (plan S2, design docs/design/S2_INTERFACE.md 4; moved onto the
\ tactic library by plan 9.4.8l-I, commit C4), after Lean 4.35.0's
\ Elab/Tactic/Induction.lean (evalInduction 1005, evalInductionCore 977):
\ - The target, in the main goal's context (Lean's focus first): t
\   elaborated with no expected type (lf-tac-elab-term), a free variable
\   that is not a let (anything else Lean generalizes: 99, FE5);
\   hypotheses that depend on it (generalizeVars) are not supported yet
\   (99, FE5).
\ - The eliminator and its information (meta-tactic/elim.fs's
\   lf-elim-for and lf-elim-info: errors 205, 209, 99), mkElimApp with
\   the goal's tag (lf-elim-app), setMotiveArg (lf-elim-set-motive: 212),
\   the goal assigned the eliminator's application, off the list.
\ - evalAlts (tactic-alts.fs's lf-eval-alts): by-induction-with checks
\   its alternatives' names and opens its block, each | runs by
\   lf-alt-run and the block's end by lf-alts-missing (206-208, 213,
\   207); by-induction puts every alternative's goal, its fields named
\   inaccessibly and the target cleared, before the goals left.
\ Lean call list: elabTerm -> lf-tac-elab-term; getElimNameInfo ->
\ lf-elim-for, lf-elim-info; mkElimApp -> lf-elim-app; setMotiveArg ->
\ lf-elim-set-motive; MVarId.assign -> lf-mvar-assign; evalAlts ->
\ lf-eval-alts, lf-alt-run, lf-alts-missing.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Its kinds are the runner's tac-k-induction and
\ tac-k-with (fixed kinds, scripts/check-tactic-plugins.py's ownership
\ table).

require ../tactic-api.fs

\ ---- The target: a free variable that is not a let.
: tind-refused ( -- ) lfa-e-tac-form lf-tac-fail ;
: tind-target ( i -- fvar )
  0 lf-tac-arg -1 false lf-tac-elab-term dup lf-meta-fvar? 0= if tind-refused then
  dup lf-fvar-let? if tind-refused then ;
\ generalizeVars: a hypothesis whose type depends on the target.
: tind-depends? ( target local -- target flag )
  lf-local-fvar 2dup = if drop false exit then
  lf-fvar-type over lf-depends-on? lf-tac-must ;
: tind-dep-at? ( target k -- target flag ) tb tb-view @ swap lf-view-local tind-depends? ;
: tind-independent ( target -- target )
  tb tb-view @ lf-view-count ['] tind-dep-at? any? if tind-refused then ;

\ ---- The eliminator applied, the motive set, the goal assigned.
: tind-goal ( -- goal ) tb tb-goal @ ;
: tind-elim ( target -- info target ) dup true lf-elim-for lf-elim-info swap ;
: tind-motive ( target motive -- target ) over >r tind-goal swap r> lf-elim-set-motive ;
: tind-closed ( f alts -- alts )
  swap tind-goal swap lf-mvar-assign lf-tac-must lf-tac-pop-main ;
: tind-app ( info target -- info alts target )
  2dup tind-goal lf-goal-tag lf-elim-app -rot 2>r tind-motive 2r> tind-closed swap ;
: tind-run ( i -- ) dup tind-target tind-independent tind-elim tind-app lf-eval-alts ;

: tind-with ( i -- ) lf-tac-focus over ['] tind-run lf-tac-step-run lf-tac-block ;
: tind-plain ( i -- ) lf-tac-focus swap ['] tind-run lf-tac-step-run lf-tac-unfocus ;
' tind-with tac-k-with lf-tactic-action!
' lf-alt-run tac-k-with lf-tactic-alt!
' lf-alts-missing tac-k-with lf-tactic-end!
' tind-plain tac-k-induction lf-tactic-action!
