\ Simp's bracket items and locations (plan row FE9; simp group 4, pass 3,
\ the plan .claude/work/briefs/simp-group-4-architect.md section 3, moved
\ from tactics/simp-only.fs so that simp only [..] and simp [..] share
\ them): Lean 4.35.0's elabSimpArgs (src/lean/Lean/Elab/Tactic/Simp.lean:
\ 336-370 and 268-300) and simpLocation's locations (761-778).
\ - lf-simp-args ( i -- ): each rule of tactic step i, in order, added to
\   simp's set as it stands (simp/theorems.fs: simp only's builtins, or
\   the default set, where a rule's root is built first and the rule goes
\   in after its values, Lean's insertion into thmsArray[0], 434). A rule
\   naming a constant whose type is a proposition is
\   mkSimpTheoremFromConst's theorem (lf-simp-add-decl); one naming a
\   hypothesis or a variable of proposition type h is mkSimpTheoremFromExpr's
\   of h, inverted when written with <- (Lean's ←): simp/preprocess.fs's
\   lf-simp-add-term, with Lean's errors 502 and 503 for <- on a rule to
\   True or to False. A variable a that is no proposition and no let is
\   Lean's error 501 "Invalid argument: Variable `a` is not a proposition
\   or let-declaration". Not supported yet (99): a constant with <-
\   (Lean's auxiliary lemma, slice SL3d), any other rule (a definition to
\   unfold, a let variable, a simproc, a term: SL3a), a theorem
\   LeanForth's text declared (its rfl flag).
\ - lf-simp-locs ( goal i -- goal target? fvars ): whether the target is
\   a location, and the hypotheses named, in order, resolved in the main
\   goal's context after the set (tactic-core.fs's lf-with-location; no
\   at[ ] is the target alone); for at[ * ] (Location.wildcard) the target
\   and every hypothesis of the main goal that is a proposition nothing
\   else depends on (meta-tactic/goal.fs's lf-goal-nondep-prop-hyps).
\ Lean call list: elabSimpArgs -> lf-simp-args; Term.resolveId? -> the
\ rule's node (a constant's declaration, else lf-tac-elab-for-apply: an
\ identifier with no argument inserted, so a ¬ hypothesis's type is not
\ unfolded); isProp -> lf-meta-is-prop; mkSimpTheoremFromExpr ->
\ lf-simp-add-term; getFVarIds -> lf-with-location; getNondepPropHyps ->
\ lf-goal-nondep-prop-hyps.
\ Throws as the tactic words do. Untrusted: a rule only proposes
\ rewrites the kernel checks. State: none of its own.

require ../../lib/runs.fs
require ../tactic-api.fs
require ../meta-tactic/goal.fs
require ./theorems.fs
require ./preprocess.fs

501 lfa-lean s" Invalid argument: Variable" lfa-code: lfa-e-simp-not-prop

\ ---- The rules, each in order (elabSimpArgs).
: sar-decl ( symm? node -- )
  swap if lf-tac-unported then syn-a@ lfa-decl-name lf-menv-find lf-must
  dup lf-menv-type lf-is-prop! 0= if lf-tac-unported then true lf-simp-add-decl ;
\ A variable that is no proposition: a let (to unfold, slice SL3a), else
\ Lean's error naming it (Elab/Tactic/Simp.lean:292).
: sar-var-end. ( -- outcome )
  s"  is not a proposition or let-declaration" lf-pp-emit outcome-ok ;
: sar-var. ( e -- outcome ) ['] sar-var-end. lf-tac-spaced. ;
: sar-not-prop ( e -- )
  dup lf-fvar-let? if lf-tac-unported then
  ['] sar-var. lf-tac-inline lfa-e-simp-not-prop lf-tac-stop ;
\ A hypothesis's or a variable's node elaborates to its free variable.
: sar-hyp ( symm? node -- )
  lf-tac-elab-for-apply dup lf-infer! lf-is-prop! 0= if dup sar-not-prop then
  swap lf-simp-add-term ;
: sar-rule ( i k -- )
  2dup lf-tac-arg-symm? -rot lf-tac-arg dup syn-kind@ case
    syn-k-const of sar-decl endof
    syn-k-var of sar-hyp endof   syn-k-hyp of sar-hyp endof
    lf-tac-unported endcase ;
: lf-simp-args ( i -- ) dup lf-tac-args# 0 ?do dup i sar-rule loop drop ;

\ ---- simpLocation: whether the target is a location, and the hypotheses
\ named, in order (getFVarIds in the main goal's context, after the set);
\ at[ * ] the target and getNondepPropHyps of the main goal.
: sar-loc-hyp ( target? fvars fvar -- target? fvars' ) run-push lf-tac-must ;
: sar-loc-goal ( target? fvars -- true fvars ) nip true swap ;
: lf-simp-locs ( goal i -- goal target? fvars )
  dup lf-tac-loc-all? if drop true over lf-goal-nondep-prop-hyps exit then
  false swap 0 swap ['] sar-loc-hyp ['] sar-loc-goal lf-with-location ;
