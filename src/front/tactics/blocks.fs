\ Tactic blocks (plan row TB2, piece F, slice 1; design docs/design/
\ TACTIC_BLOCKS.md; the owner's spellings, docs/project/OWNER_DECISIONS.md
\ "Blocks in proof text"), ports of Lean 4.35.0 (src/lean/):
\ - { tacs }  Lean's bullet · tacs and its { tacs } (Elab/Tactic/
\   BuiltinTactic.lean:167-185, evalTacticSeqBracketed and its copy
\   evalTacticCDot): closeUsingOrAdmit (Basic.lean:351-361) of
\   focusAndDone, the first unsolved goal alone (none: 90, before the
\   block opens, :354), the block's tactics, then no goal left (89 at its
\   }, Lean's withRef stx[2]) and the other goals back. It closes itself
\   at }, may nest and may stand in an alternative's or a case's block;
\   the names given inside it go at }. { } is read, as Lean's parser
\   reads it, and fails as Lean's: 89, or 90 with no goal.
\ - by-focus tacs by-end  Lean's focus tacs (evalFocus :187; focus,
\   Basic.lean:332-338): the main goal alone (none: 90), the tactics,
\   then the goals they leave before the others; names given inside stay.
\ Lean call list: getUnsolvedGoals, setGoals -> tactic-run.fs's
\ lf-tac-focus (lf-tac-focused); focusAndDone's done and
\ closeUsingOrAdmit -> the runner's mode lf-mode-done; focus's end ->
\ lf-mode-focus. Where closeUsingOrAdmit logs an error, admits the goal
\ and goes on, LeanForth stops at that error (the same verdict).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

0 0 tac-block-cuts tac-block-self or tac-shape-block
  lf-tactic-sign: { constant tac-k-brace
s" braces" tac-k-brace lf-tactic-lean!
' lf-tac-focused tac-k-brace lf-tactic-action!
lf-mode-done tac-k-brace lf-tactic-mode!

0 0 0 tac-shape-block lf-tactic: by-focus constant tac-k-focus
s" focus" tac-k-focus lf-tactic-lean!
' lf-tac-focused tac-k-focus lf-tactic-action!
lf-mode-focus tac-k-focus lf-tactic-mode!
