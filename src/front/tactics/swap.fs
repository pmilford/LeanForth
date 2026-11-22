\ by-swap: Batteries' swap (plan row TB2, tactic batch 1), the macro
\ pick_goal 2 (.tools/mathlib/mathlib4/.lake/packages/batteries/Batteries/
\ Tactic/PermuteGoals.lean:54), whose elab (:44-47) with elabGoalNum
\ (:31-37) moves the second goal of the goal list as it is (getGoals) to
\ the front: g1 g2 rest becomes g2 g1 rest. Fewer than two goals is error
\ 446, Lean's "goal index `2` is out of bounds" (throwError: no goals
\ printed).
\ Lean call list: getGoals -> lf-goals (goals.fs); List.splitAt ->
\ run-take and run-after (lib/runs.fs); setGoals -> lf-goals!.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

446 outcome-invalid s" goal index `2` is out of bounds" lfa-code: lfa-e-swap-bounds
tac-shape-plain lf-tactic: by-swap constant tac-k-swap
s" swap" tac-k-swap lf-tactic-lean!

: tsw-pair ( goals -- goals [g2 g1] )
  0 over 1 run@ run-push lf-tac-must over 0 run@ run-push lf-tac-must ;
: tsw-front ( goals -- goals' )   \ g2 :: g1 :: the rest
  tsw-pair swap 2 run-after lf-tac-must run-cat lf-tac-must ;
: tsw-run ( i -- )
  drop lf-goals dup run-count 2 < if lfa-e-swap-bounds lf-tac-stop then
  tsw-front lf-goals! lf-tac-must ;
' tsw-run tac-k-swap lf-tactic-action!
