\ by-simp-only[ ' r1 .. ' rn ] at[ h1 .. hk |- ]: Lean's simp only [r1,
\ .., rn] at h1 .. hk ⊢ on the main goal (plan row FE9, simp slices
\ SL1a-1 and SL1a-2 of docs/design/TACTIC_SIMP.md), a port of Lean
\ 4.35.0's evalSimp with mkSimpContext's simp only
\ (src/lean/Lean/Elab/Tactic/Simp.lean: the set simpOnlyBuiltins, eq_self
\ and iff_self, 512, then each rule by elabSimpArgs, 336-370 and 268-300)
\ and simpLocation (761-778), then simpGoal once (simp/goal.fs's
\ lf-goal-simp).
\ - The rules and the locations are simp/args.fs's (lf-simp-args,
\   lf-simp-locs), which by-simp[ ] shares: a constant's theorem, a
\   hypothesis's (inverted with <-), Lean's errors 501, 502 and 503;
\   at[ h1 .. hk |- ] and at[ * ]. Not supported yet (99): a constant with
\   <-, any other rule, and every refusal of simp/args.fs,
\   simp/preprocess.fs, simp/theorems.fs, simp/main.fs and simp/goal.fs.
\ - The goal simplified (simp/goal.fs's lf-goal-simp, maxSteps 100000,
\   Simp.Config's defaults): closed (a hypothesis became False, or the
\   target True); else the new goal in the main goal's place, and Lean's
\   error 500 "`simp` made no progress" when the goal is the one it was
\   (failIfUnchanged: once, for all the locations together).
\ - config[ ] (SL5) is not supported yet; the reader does not take it.
\ Lean call list: getMainGoal, replaceMainGoal -> lf-lift-meta-tactic;
\ simpOnlyBuiltins -> tso-builtin; elabSimpArgs -> lf-simp-args;
\ simpLocation's locations -> lf-simp-locs; simpGoal -> lf-goal-simp.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own; simp's set (simp/theorems.fs) is emptied after
\ each run.

require ../tactic-api.fs
require ../simp/preprocess.fs
require ../simp/goal.fs
require ../simp/args.fs

tac-shape-rules lf-tactic: by-simp-only[ constant tac-k-simp-only
s" simp" tac-k-simp-only lf-tactic-lean!

\ ---- The set: simpOnlyBuiltins, then each rule in order.
: tso-builtin ( c-addr u -- ) lfa-intern lf-menv-find lf-must true lf-simp-add-decl ;
: tso-set ( i -- )
  lf-simp-set-new s" eq_self" tso-builtin s" iff_self" tso-builtin lf-simp-args ;

\ ---- simpGoal: closed, or the new goal (no progress is its error 500).
: tso-inner ( i goal -- goals )
  swap dup tso-set lf-simp-locs lf-goal-simp lf-goals0/1 ;
: tso-tac ( i goal -- goals ) ['] tso-inner lf-dt-scoped ;
: tso-lifted ( i -- ) dup ['] tso-tac lf-lift-meta-tactic ;
: tso-ported ( i -- ) ['] tso-lifted lf-tac-ported ;
: tso-run ( i -- ) ['] tso-ported catch lf-simp-set-new throw ;
' tso-run tac-k-simp-only lf-tactic-action!
