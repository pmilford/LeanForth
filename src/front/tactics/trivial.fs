\ by-trivial: Lean's trivial (plan row TB2, tactic batch 1), the
\ extensible macro of Lean 4.35.0's src/lean/Init/Tactics.lean:1200 with
\ its six rules (:1534-1539), tried as Lean's evalTactic tries a macro's
\ rules (Elab/Tactic/Basic.lean's expandEval: the newest first, each from
\ the saved state; the error of the last tried, the first registered,
\ reported): tactic-core.fs's lf-tac-macro-alts of
\   apply And.intro <;> trivial   focus on the main goal, apply And.intro
\                                 (meta-tactic/apply.fs), then trivial on
\                                 each of its goals in turn (all_goals: the
\                                 first failure fails the rule; Lean logs it
\                                 and fails at the end, the same outcome)
\   apply True.intro
\   decide                        by-decide's row (tactics/decide.fs)
\   contradiction                 by-contradiction's row
\   rfl                           by-rfl's row
\   assumption                    by-assumption's row: its error 381 is
\                                 trivial's when every rule fails
\ A rule that answers not supported yet (contradiction's 99 on a ≤
\ hypothesis, rfl's 93 on another relation, decide's 93) makes trivial
\ not supported, never accepted or refused where Lean might succeed. The
\ nested trivial of the first rule runs through this row
\ (lf-tac-eval): And nested deeper than ttr-most is not supported yet
\ (99), where Lean's limit is its recursion depth (maxRecDepth).
\ Lean call list: the macro's rules -> lf-tac-macro-alts; focus ->
\ lf-tac-focus, lf-tac-unfocus (tactic-run.fs); apply c ->
\ lf-lift-meta-tactic, lf-tac-with-synth (tactic-core.fs) and
\ lf-goal-apply-const (meta-tactic/apply.fs); all_goals -> ttr-all
\ (setGoals [g]: lf-tac-only; getUnsolvedGoals: lf-goals-unsolved); the
\ other rules -> lf-tac-row of their rows.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the record ttr (the nesting of trivial inside its own first
\ rule, put back however a nested run ends), in the checker context (ADR
\ 0009).

require ../tactic-api.fs
require ./assumption.fs
require ./contradiction.fs
require ./decide.fs
require ./rfl.fs

tac-shape-plain lf-tactic: by-trivial constant tac-k-trivial
s" trivial" tac-k-trivial lf-tactic-lean!

begin-structure /ttr
  field: ttr-depth        \ trivial runs open, one inside another
end-structure
/ttr context-record: ttr
32 constant ttr-most
: ttr-room ( -- ) ttr ttr-depth @ ttr-most < 0= if lf-tac-unported then ;
: ttr-deeper ( xt -- ) ttr-room 1 ttr ttr-depth +! catch -1 ttr ttr-depth +! throw ;

\ ---- apply c (evalApply: the apply under withSynthesize).
: ttr-apply-tac ( goal c-addr u -- goals ) ['] lf-goal-apply-const lf-tac-with-synth ;
: ttr-and-tac ( goal -- goals ) s" And.intro" ttr-apply-tac ;
: ttr-true-tac ( goal -- goals ) s" True.intro" ttr-apply-tac ;
: ttr-true ( -- ) lf-tac-step ['] ttr-true-tac lf-lift-meta-tactic ;

\ ---- apply And.intro <;> trivial: trivial on each goal apply leaves.
: ttr-nested ( -- ) tac-k-trivial lf-tac-row ;
: ttr-goal ( new goal -- new' outcome )
  dup lf-goal-assigned? if drop outcome-ok exit then
  lf-tac-only ttr-nested lf-goals-unsolved lf-tac-must run-cat ;
: ttr-all ( goals -- ) 0 swap ['] ttr-goal run-each lf-tac-must lf-goals! lf-tac-must ;
: ttr-and ( -- )
  lf-tac-focus lf-tac-step ['] ttr-and-tac lf-lift-meta-tactic lf-goals ttr-all
  lf-tac-unfocus ;

\ ---- The other rules: their rows on the step running.
: ttr-decide ( -- ) tac-k-decide lf-tac-row ;
: ttr-contradiction ( -- ) tac-k-contradiction lf-tac-row ;
: ttr-rfl ( -- ) tac-k-rfl lf-tac-row ;
\ The rules, the first registered deepest: Lean tries the newest first
\ (assumption: tactics/assumption.fs's tas-row).
: ttr-rules ( -- )
  ['] tas-row ['] ttr-rfl ['] ttr-contradiction ['] ttr-decide ['] ttr-true
  ['] ttr-and 6 lf-tac-macro-alts ;
: ttr-run ( i -- ) drop ['] ttr-rules ttr-deeper ;
' ttr-run tac-k-trivial lf-tactic-action!
