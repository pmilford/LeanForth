\ by-simp-only[ ' r1 .. ' rn ] at[ h1 .. hk |- ]: Lean's simp only [r1,
\ .., rn] at h1 .. hk ⊢ on the main goal (plan row FE9, simp slices
\ SL1a-1 and SL1a-2 of docs/design/TACTIC_SIMP.md), a port of Lean
\ 4.35.0's evalSimp with mkSimpContext's simp only
\ (src/lean/Lean/Elab/Tactic/Simp.lean: the set simpOnlyBuiltins, eq_self
\ and iff_self, 512, then each rule by elabSimpArgs, 336-370 and 268-300)
\ and simpLocation (761-778): the hypotheses named, resolved in the main
\ goal's context after the set (tactic-core.fs's lf-with-location; no
\ at[ ] is the target alone), or for at[ * ] (Location.wildcard, slice
\ SL1b) the target and every hypothesis of the main goal that is a
\ proposition nothing else depends on (meta-tactic/goal.fs's
\ lf-goal-nondep-prop-hyps), then simpGoal once (simp/goal.fs's
\ lf-goal-simp).
\ - A rule naming a constant whose type is a proposition is
\   mkSimpTheoremFromConst's theorem (simp/theorems.fs's lf-simp-add-decl);
\   one naming a hypothesis or a variable of proposition type h is
\   mkSimpTheoremFromExpr's of h, inverted when written with <- (Lean's
\   ←): simp/preprocess.fs's lf-simp-add-term, with Lean's errors 502 and
\   503 for <- on a rule to True or to False. A variable a that is no
\   proposition and no let is Lean's error 501 "Invalid argument:
\   Variable `a` is not a proposition or let-declaration". Not supported
\   yet (99): a constant with <- (Lean's auxiliary lemma, slice SL3d),
\   any other rule (a definition to unfold, a let variable, a simproc, a
\   term: SL3a), a theorem LeanForth's text declared (its rfl flag), and
\   every refusal of simp/preprocess.fs, simp/theorems.fs, simp/main.fs
\   and simp/goal.fs.
\ - The goal simplified (simp/goal.fs's lf-goal-simp, maxSteps 100000,
\   Simp.Config's defaults): closed (a hypothesis became False, or the
\   target True); else the new goal in the main goal's place, and Lean's
\   error 500 "`simp` made no progress" when the goal is the one it was
\   (failIfUnchanged: once, for all the locations together).
\ - config[ ] (SL5) is not supported yet; the reader does not take it.
\ Lean call list: getMainGoal, replaceMainGoal -> lf-lift-meta-tactic;
\ elabSimpArgs -> tso-rule; Term.resolveId? -> the rule's node (a
\ constant's declaration, else lf-tac-elab-for-apply: an identifier with
\ no argument inserted, so a ¬ hypothesis's type is not unfolded); isProp
\ -> lf-meta-is-prop; mkSimpTheoremFromExpr -> lf-simp-add-term; getFVarIds ->
\ lf-with-location; getNondepPropHyps -> lf-goal-nondep-prop-hyps; simpGoal ->
\ lf-goal-simp.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own; simp's set (simp/theorems.fs) is emptied after
\ each run.

require ../../lib/runs.fs
require ../tactic-api.fs
require ../simp/preprocess.fs
require ../simp/goal.fs

501 lfa-lean s" Invalid argument: Variable" lfa-code: lfa-e-simp-not-prop
tac-shape-rules lf-tactic: by-simp-only[ constant tac-k-simp-only
s" simp" tac-k-simp-only lf-tactic-lean!

\ ---- The set: simpOnlyBuiltins, then each rule in order.
: tso-prop? ( e -- flag ) lf-meta-is-prop lf-must ;
: tso-builtin ( c-addr u -- ) lfa-intern lf-menv-find lf-must true lf-simp-add-decl ;
: tso-decl ( symm? node -- )
  swap if lf-tac-unported then syn-a@ lfa-decl-name lf-menv-find lf-must
  dup lf-menv-type tso-prop? 0= if lf-tac-unported then true lf-simp-add-decl ;
\ A variable that is no proposition: a let (to unfold, slice SL3a), else
\ Lean's error naming it (Elab/Tactic/Simp.lean:292).
: tso-var-end. ( -- outcome )
  s"  is not a proposition or let-declaration" lf-pp-emit outcome-ok ;
: tso-var. ( e -- outcome ) ['] tso-var-end. lf-tac-spaced. ;
: tso-not-prop ( e -- )
  dup lf-fvar-let? if lf-tac-unported then
  ['] tso-var. lf-tac-inline lfa-e-simp-not-prop lf-tac-stop ;
\ A hypothesis's or a variable's node elaborates to its free variable.
: tso-hyp ( symm? node -- )
  lf-tac-elab-for-apply dup lf-infer! tso-prop? 0= if dup tso-not-prop then
  swap lf-simp-add-term ;
: tso-rule ( i k -- )
  2dup lf-tac-arg-symm? -rot lf-tac-arg dup syn-kind@ case
    syn-k-const of tso-decl endof
    syn-k-var of tso-hyp endof   syn-k-hyp of tso-hyp endof
    lf-tac-unported endcase ;
: tso-set ( i -- )
  lf-simp-set-new s" eq_self" tso-builtin s" iff_self" tso-builtin
  dup lf-tac-args# 0 ?do dup i tso-rule loop drop ;

\ ---- simpLocation: whether the target is a location, and the hypotheses
\ named, in order (getFVarIds in the main goal's context, after the set);
\ at[ * ] the target and getNondepPropHyps of the main goal.
: tso-loc-hyp ( target? fvars fvar -- target? fvars' ) run-push lf-tac-must ;
: tso-loc-goal ( target? fvars -- true fvars ) nip true swap ;
: tso-locs ( goal i -- goal target? fvars )
  dup lf-tac-loc-all? if drop true over lf-goal-nondep-prop-hyps exit then
  false swap 0 swap ['] tso-loc-hyp ['] tso-loc-goal lf-with-location ;

\ ---- simpGoal: closed, or the new goal (no progress is its error 500).
: tso-goals ( goal' | 0 -- goals ) ?dup if lf-goals1 else 0 then ;
: tso-inner ( i goal -- goals )
  swap dup tso-set tso-locs lf-simp-max-steps lf-goal-simp tso-goals ;
: tso-tac ( i goal -- goals ) ['] tso-inner lf-dt-scoped ;
: tso-lifted ( i -- ) dup ['] tso-tac lf-lift-meta-tactic ;
: tso-ported ( i -- ) ['] tso-lifted lf-tac-ported ;
: tso-run ( i -- ) ['] tso-ported catch lf-simp-set-new throw ;
' tso-run tac-k-simp-only lf-tactic-action!
