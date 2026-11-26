\ e by-generalize: x and e by-generalize-eq: h x, each with at[ h .. ]:
\ Lean's generalize e = x and generalize h : e = x, with at h .. (plan
\ row TB2, small tactics 1), a port of Lean 4.35.0's evalGeneralize
\ (src/lean/Lean/Elab/Tactic/Generalize.lean:18-41) for one argument: in
\ the main goal's context e elaborated with no expected type (elabTerm,
\ no postponing), the location's names resolved (getFVarIds: tactic-
\ core.fs's lf-tac-loc-fvar, 455 for a name the context lacks; the goal
\ itself is always generalized, ⊢ or not, as Lean's targets case
\ ignores it), then MVarId.generalizeHyp (meta-tactic/generalize.fs's
\ lf-goal-generalize-hyp: the hypotheses holding e reverted, the goal's
\ e abstracted into x, with h : e = x for the equation form, and those
\ hypotheses introduced again) and the new goal in the main goal's
\ place. x and h become hypotheses later steps may name. Not supported
\ yet (99): a result that is not type correct (Lean's error), at[ * ]
\ (getLocalHyps), and _ for x or h (Lean's parser wants an identifier);
\ several arguments (generalize e1 = x, e2 = y) have no form.
\ Lean call list: withMainContext, getMainGoal, replaceMainGoal [g] ->
\ lf-lift-meta-tactic1 (tactic-core.fs); elabTerm stx none ->
\ lf-tac-elab-arg; expandOptLocation, getFVarIds -> lf-with-location's
\ walk of the names (lf-tac-loc-fvar; the wildcard 99); generalizeHyp ->
\ lf-goal-generalize-hyp under lf-tac-ported (a case not ported: 99).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/generalize.fs

1 1 tac-shape-term-names tac-shape-at
  lf-tactic: by-generalize: constant tac-k-generalize
s" generalize" tac-k-generalize lf-tactic-lean!
1 2 tac-shape-term-names tac-shape-at
  lf-tactic: by-generalize-eq: constant tac-k-generalize-eq
s" generalize" tac-k-generalize-eq lf-tactic-lean!

\ ---- Step i's names (each an identifier: _ not supported), its argument
\ k with e elaborated, the hypotheses of its at[ ] (getFVarIds, in the
\ order written: lf-with-location's walk; at[ * ] not supported).
: tgz-names ( i -- ) dup lf-tac-args# 1 ?do dup i lf-tac-name drop loop drop ;
: tgz-arg ( i k -- args ) over swap lf-tac-arg swap 0 lf-tac-elab-arg swap lf-run2 ;
\ The location's target (⊢) adds nothing: the goal is generalized anyway.
: tgz-target ( hyps -- hyps ) ;
: tgz-hyps ( i -- hyps ) 0 swap ['] lf-run+ ['] tgz-target lf-with-location ;

\ ---- generalize [h :] e = x at hyps, in Lean's order: the names (its
\ parser's), e (argument k: x's place), the names of at[ ], then
\ generalizeHyp with h (0: none, the plain form).
: tgz-gen ( goal args h hyps -- goal' ) ['] lf-goal-generalize-hyp lf-tac-ported nip ;
: tgz-with ( i goal k h -- goal' )
  2>r swap dup tgz-names dup 2r> >r tgz-arg r> rot tgz-hyps tgz-gen ;
: tgz-tac ( i goal -- goal' ) 1 0 tgz-with ;
: tgz-eq-tac ( i goal -- goal' ) over 1 lf-tac-arg 2 swap tgz-with ;
: tgz-run ( i -- ) dup ['] tgz-tac lf-lift-meta-tactic1 ;
: tgz-eq-run ( i -- ) dup ['] tgz-eq-tac lf-lift-meta-tactic1 ;
' tgz-run tac-k-generalize lf-tactic-action!
' tgz-eq-run tac-k-generalize-eq lf-tactic-action!
