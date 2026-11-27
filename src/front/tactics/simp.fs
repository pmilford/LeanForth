\ by-simp, by-simp[ ' r1 .. ' rn ] and their at[ h1 .. hk |- ]: Lean's
\ plain simp, simp [r1, .., rn] and simp .. at h1 .. hk ⊢ on the main
\ goal (plan row FE9; simp group 4, passes 1 and 3; the plan
\ .claude/work/briefs/simp-group-4-architect.md section 1), a port of
\ Lean 4.35.0's evalSimp with mkSimpContext's default context
\ (src/lean/Lean/Elab/Tactic/Simp.lean:554-580: getSimpTheorems, the
\ congruence lemmas, getSimprocs; then elabSimpArgs) and simpLocation
\ (761-778), then simpGoal once (simp/goal.fs's lf-goal-simp, maxSteps
\ 100000, Simp.Config's defaults).
\ - The set is simp/default-set.fs's lf-simp-default: Lean's default
\   simp set from format 4.1's records; the bracket's rules are then
\   added to it (simp/args.fs's lf-simp-args, simp only's: each after its
\   root's values, Lean's order) and the locations read (lf-simp-locs).
\   Closed when the target becomes True (or a hypothesis False); else the
\   new goal in the main goal's place, and Lean's error 500 "`simp` made
\   no progress" when it is the one it was.
\ - The default simprocs (simp/simprocs.fs): reduceIte and reduceDIte,
\   Nat's literal arithmetic and predicates computed (pass 2); every other
\   one answers unsupported where Lean's may fire (its guard).
\ - Not supported yet (99): a simproc that is only guarded and may fire,
\   the discharger (a conditional lemma), a lemma the library lacks (or
\   cannot decode) reached in candidate order, a lemma whose recorded
\   keys are not its statement's (no_index), a definition the set
\   unfolds, data without the default set, a rule simp/args.fs refuses (a
\   constant with <-, a definition, a term, a simproc), and every refusal
\   of simp/main.fs, simp/congr.fs and simp/goal.fs.
\ Lean call list: getMainGoal, replaceMainGoal -> lf-lift-meta-tactic;
\ getSimpTheorems, Simp.getSimprocs -> lf-simp-default; elabSimpArgs ->
\ lf-simp-args; simpLocation's locations -> lf-simp-locs; simpGoal ->
\ lf-goal-simp.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own; simp's set (simp/theorems.fs) is emptied after
\ each run.

require ../tactic-api.fs
require ../simp/goal.fs
require ../simp/args.fs
require ../simp/default-set.fs

504 outcome-invalid
  s" elaboration data refused: two simp records of a root key with one rank, or a gap"
  lfa-code: lfa-e-simp-ranks
tac-shape-plain-at lf-tactic: by-simp constant tac-k-simp
s" simp" tac-k-simp lf-tactic-lean!

: tsm-inner ( i goal -- goals )
  swap dup lf-simp-default lf-simp-args lf-simp-locs lf-goal-simp lf-goals0/1 ;
: tsm-tac ( i goal -- goals ) ['] tsm-inner lf-dt-scoped ;
: tsm-lifted ( i -- ) dup ['] tsm-tac lf-lift-meta-tactic ;
: tsm-ported ( i -- ) ['] tsm-lifted lf-tac-ported ;
\ The data refused while the tactic ran: error 504 in place of its own
\ outcome (exit 4), the set made new first.
: tsm-refused ( code flag -- code ) if drop lfa-e-simp-ranks lf-tac-stop then ;
: tsm-run ( i -- )
  ['] tsm-ported catch lf-simp-data-refused? lf-simp-set-new tsm-refused throw ;
' tsm-run tac-k-simp lf-tactic-action!

tac-shape-rules lf-tactic: by-simp[ constant tac-k-simp-rules
s" simp" tac-k-simp-rules lf-tactic-lean!
' tsm-run tac-k-simp-rules lf-tactic-action!
