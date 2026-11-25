\ by-simp-only[ ' r1 .. ' rn ]: Lean's simp only [r1, .., rn] on the
\ main goal's target (plan row FE9, simp slice SL1a-1 of
\ docs/design/TACTIC_SIMP.md), a port of Lean 4.35.0's evalSimp with
\ mkSimpContext's simp only (src/lean/Lean/Elab/Tactic/Simp.lean: the
\ set simpOnlyBuiltins, eq_self and iff_self, 512, then each rule by
\ elabSimpArgs, 336-370 and 268-300) and simpGoal on the target alone
\ (Meta/Tactic/Simp/Main.lean:874-911).
\ - A rule naming a constant whose type is a proposition is
\   mkSimpTheoremFromConst's theorem (simp/theorems.fs's lf-simp-add-decl);
\   one naming a hypothesis or a variable of proposition type is the
\   hypothesis's (lf-simp-add-hyp, origin .stx). Not supported yet (99):
\   a rule written with <- (Lean's ←, slice SL3d), any other rule (a
\   definition to unfold, a let variable, a simproc, a term: SL3a), a
\   theorem LeanForth's text declared (its rfl flag, SL1a-2), and every
\   refusal of simp/theorems.fs and simp/main.fs.
\ - The target simplified (simp/main.fs's lf-goal-simp-target, maxSteps
\   100000, Simp.Config's defaults): closed when it became True; else the
\   new goal in the main goal's place, and Lean's error 500 "`simp` made
\   no progress" when the goal is the one it was (failIfUnchanged).
\ - A trailing at[ ] is not supported yet (99, slice SL1a-2), nor is
\   config[ ] (SL5), which the reader does not take.
\ Lean call list: getMainGoal, replaceMainGoal -> lf-lift-meta-tactic;
\ elabSimpArgs -> tso-rule; Term.resolveId? -> the rule's node (a
\ constant's declaration, else lf-tac-elab-term); isProp ->
\ lf-meta-is-prop; simpGoal's target -> lf-goal-simp-target.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own; simp's set (simp/theorems.fs) is emptied after
\ each run.

require ../tactic-api.fs
require ../simp/main.fs

500 lfa-lean s" `simp` made no progress" lfa-code: lfa-e-simp-progress
tac-shape-rules lf-tactic: by-simp-only[ constant tac-k-simp-only
s" simp" tac-k-simp-only lf-tactic-lean!

\ ---- The set: simpOnlyBuiltins, then each rule in order.
: tso-prop? ( e -- flag ) lf-meta-is-prop lf-must ;
: tso-builtin ( c-addr u -- ) lfa-intern lf-menv-find lf-must true lf-simp-add-decl ;
: tso-decl ( node -- )
  syn-a@ lfa-decl-name lf-menv-find lf-must
  dup lf-menv-type tso-prop? 0= if lf-tac-unported then true lf-simp-add-decl ;
\ A hypothesis's or a variable's node elaborates to its free variable.
: tso-hyp ( node -- )
  -1 false lf-tac-elab-term dup lf-infer! tso-prop? 0= if lf-tac-unported then
  true lf-simp-add-hyp ;
: tso-rule ( i k -- )
  2dup lf-tac-arg-symm? if lf-tac-unported then lf-tac-arg dup syn-kind@ case
    syn-k-const of tso-decl endof
    syn-k-var of tso-hyp endof   syn-k-hyp of tso-hyp endof
    lf-tac-unported endcase ;
: tso-set ( i -- )
  lf-simp-set-new s" eq_self" tso-builtin s" iff_self" tso-builtin
  dup lf-tac-args# 0 ?do dup i tso-rule loop drop ;

\ ---- simpGoal on the target: closed, replaced, or no progress.
: tso-goals ( goal goal' -- goals )
  ?dup 0= if drop 0 exit then tuck = if lfa-e-simp-progress lf-tac-stop then lf-goals1 ;
: tso-inner ( i goal -- goals )
  swap tso-set dup lf-simp-max-steps lf-goal-simp-target tso-goals ;
: tso-tac ( i goal -- goals ) ['] tso-inner lf-dt-scoped ;
: tso-lifted ( i -- ) dup ['] tso-tac lf-lift-meta-tactic ;
: tso-ported ( i -- ) ['] tso-lifted lf-tac-ported ;
: tso-run ( i -- )
  dup lf-tac-located? if lf-tac-unported then ['] tso-ported catch lf-simp-set-new throw ;
' tso-run tac-k-simp-only lf-tactic-action!
