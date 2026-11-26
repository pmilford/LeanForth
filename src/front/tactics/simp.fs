\ by-simp: Lean's plain simp on the main goal's target (plan row FE9;
\ simp group 4, pass 1, the default set's first caller; the plan
\ .claude/work/briefs/simp-group-4-architect.md section 1), a port of
\ Lean 4.35.0's evalSimp with mkSimpContext's default context
\ (src/lean/Lean/Elab/Tactic/Simp.lean:554-580: getSimpTheorems, the
\ congruence lemmas, getSimprocs) and simpLocation with no location (the
\ target alone, 761-778), then simpGoal once (simp/goal.fs's
\ lf-goal-simp, maxSteps 100000, Simp.Config's defaults).
\ - The set is simp/default-set.fs's lf-simp-default: Lean's default
\   simp set from format 4.1's records. Closed when the target becomes
\   True; else the new goal in the main goal's place, and Lean's error
\   500 "`simp` made no progress" when it is the one it was.
\ - The default simprocs (simp/simprocs.fs): reduceIte and reduceDIte,
\   Nat's literal arithmetic and predicates computed (pass 2); every other
\   one answers unsupported where Lean's may fire (its guard).
\ - Not supported yet (99): a simproc that is only guarded and may fire,
\   the discharger (a conditional lemma), a lemma the
\   library lacks reached in candidate order, a lemma whose recorded keys
\   are not its statement's (no_index), a definition the set unfolds,
\   data without the default set, and every refusal of simp/main.fs,
\   simp/congr.fs and simp/goal.fs; brackets (by-simp[ ]) and at[ ] are
\   not read yet.
\ Lean call list: getMainGoal, replaceMainGoal -> lf-lift-meta-tactic;
\ getSimpTheorems, Simp.getSimprocs -> lf-simp-default; simpGoal ->
\ lf-goal-simp.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own; simp's set (simp/theorems.fs) is emptied after
\ each run.

require ../tactic-api.fs
require ../simp/goal.fs
require ../simp/default-set.fs

tac-shape-plain lf-tactic: by-simp constant tac-k-simp
s" simp" tac-k-simp lf-tactic-lean!

: tsm-inner ( i goal -- goals ) nip lf-simp-default true 0 lf-goal-simp lf-goals0/1 ;
: tsm-tac ( i goal -- goals ) ['] tsm-inner lf-dt-scoped ;
: tsm-lifted ( i -- ) dup ['] tsm-tac lf-lift-meta-tactic ;
: tsm-ported ( i -- ) ['] tsm-lifted lf-tac-ported ;
: tsm-run ( i -- ) ['] tsm-ported catch lf-simp-set-new throw ;
' tsm-run tac-k-simp lf-tactic-action!
