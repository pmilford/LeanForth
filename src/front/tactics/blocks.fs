\ Tactic blocks (plan row TB2, piece F, slice 1; design docs/design/
\ TACTIC_BLOCKS.md; the owner's spellings, docs/project/OWNER_DECISIONS.md
\ "Blocks in proof text"), ports of Lean 4.35.0 (src/lean/):
\ - { tacs }  Lean's bullet · tacs and its { tacs } (Elab/Tactic/
\   BuiltinTactic.lean:167-185, evalTacticSeqBracketed and its copy
\   evalTacticCDot): closeUsingOrAdmit (Basic.lean:351-361) of
\   focusAndDone, the first unsolved goal alone (none: 90, before the
\   block opens, :354), the block's tactics, then no goal left (89), both
\   at its } (Lean's withRef stx[2] around it all), and the other goals
\   back. It closes itself
\   at }, may nest and may stand in an alternative's or a case's block;
\   the names given inside it go at }. { } is read, as Lean's parser
\   reads it, and fails as Lean's: 89, or 90 with no goal.
\ - by-focus tacs by-end  Lean's focus tacs (evalFocus :187; focus,
\   Basic.lean:332-338): the main goal alone (none: 90), the tactics,
\   then the goals they leave before the others; names given inside stay.
\ - by-all-goals tacs by-end  Lean's all_goals tacs (evalAllGoals,
\   BuiltinTactic.lean:229-253; slice 2): the tactics once on each goal
\   not assigned when reached, that goal alone, in order; the goals each
\   run leaves, in order, are the goals after it; names given inside stay.
\ - t1 <;> t2  Lean's macro focus (t1; all_goals t2) (Init/Tactics.lean:
\   451-456; slice 2): t1 on the main goal alone, t2 (one tactic or one
\   block) on each goal t1 leaves, as by-all-goals, then the other goals
\   after those left; a <;> b <;> c is (a <;> b) <;> c, as Lean's.
\ Lean call list: getUnsolvedGoals, setGoals -> tactic-run.fs's
\ lf-tac-focus (lf-tac-bracketed, lf-tac-focused); focusAndDone's done and
\ closeUsingOrAdmit -> the runner's mode lf-mode-done; focus's end ->
\ lf-mode-focus; evalAllGoals -> lf-mode-per-goal (getGoals, isAssigned:
\ goals.fs's lf-goals-next-open); <;>'s focus and all_goals ->
\ lf-mode-then with tac-then (tactic-syntax.fs's then-step). Where
\ closeUsingOrAdmit or all_goals logs an error, admits the goal and goes
\ on, LeanForth stops at that error (the same verdict).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

0 0 tac-block-cuts tac-block-self or tac-shape-block
  lf-tactic-sign: { constant tac-k-brace
s" braces" tac-k-brace lf-tactic-lean!
' lf-tac-bracketed tac-k-brace lf-tactic-action!
lf-mode-done tac-k-brace lf-tactic-mode!

0 0 0 tac-shape-block lf-tactic: by-focus constant tac-k-focus
s" focus" tac-k-focus lf-tactic-lean!
' lf-tac-focused tac-k-focus lf-tactic-action!
lf-mode-focus tac-k-focus lf-tactic-mode!

0 0 0 tac-shape-block lf-tactic: by-all-goals constant tac-k-all-goals
s" all_goals" tac-k-all-goals lf-tactic-lean!
' lf-tac-all tac-k-all-goals lf-tactic-action!
lf-mode-per-goal tac-k-all-goals lf-tactic-mode!

tac-shape-then lf-tactic-sign: <;> constant tac-k-then
s" and_then" tac-k-then lf-tactic-lean!
' lf-tac-all tac-k-then lf-tactic-action!
lf-mode-then tac-k-then lf-tactic-mode!

0 0 0 tac-shape-block lf-tactic: by-try constant tac-k-try
s" try" tac-k-try lf-tactic-lean!
' lf-tac-all tac-k-try lf-tactic-action!
lf-mode-try tac-k-try lf-tactic-mode!

0 0 tac-block-bars tac-block-bare or tac-shape-block lf-tactic: by-first
  constant tac-k-first
s" first" tac-k-first lf-tactic-lean!
' lf-tac-all tac-k-first lf-tactic-action!
lf-mode-first tac-k-first lf-tactic-mode!
' lf-tac-alternative tac-k-first lf-tactic-alt!

0 0 0 tac-shape-block lf-tactic: by-any-goals constant tac-k-any-goals
s" any_goals" tac-k-any-goals lf-tactic-lean!
' lf-tac-all tac-k-any-goals lf-tactic-action!
lf-mode-any tac-k-any-goals lf-tactic-mode!

0 0 0 tac-shape-block lf-tactic: by-repeat constant tac-k-repeat
s" repeat" tac-k-repeat lf-tactic-lean!
' lf-tac-all tac-k-repeat lf-tactic-action!
lf-mode-repeat tac-k-repeat lf-tactic-mode!
