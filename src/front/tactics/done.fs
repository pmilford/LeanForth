\ by-done: Lean's done (plan row TB2, small tactics 1), a port of Lean
\ 4.35.0's evalDone and done (src/lean/Lean/Elab/Tactic/
\ BuiltinTactic.lean:28, Basic.lean's done): no goal left unsolved, else
\ Lean's "unsolved goals" with them, error 89 at the step (Lean's
\ reportUnsolvedGoals, then throwAbortTactic), the runner's own check of
\ a block's end (tactic-run.fs's lf-tac-done).
\ Lean call list: getUnsolvedGoals, reportUnsolvedGoals -> lf-tac-done.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-plain lf-tactic: by-done constant tac-k-done
s" done" tac-k-done lf-tactic-lean!
: tdn-run ( i -- ) lf-tac-done ;
' tdn-run tac-k-done lf-tactic-action!
