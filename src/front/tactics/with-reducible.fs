\ by-with-reducible tacs by-end, by-with-reducible-and-instances tacs
\ by-end and by-with-unfolding-all tacs by-end: Lean's with_reducible,
\ with_reducible_and_instances and with_unfolding_all (plan row
\ 9.4.8z12, small tactics 2), ports of Lean 4.35.0's evalWithReducible,
\ evalWithReducibleAndInstances and evalWithUnfoldingAll (src/lean/Lean/
\ Elab/Tactic/ElabTerm.lean:328-338): withReducible, withReducibleAnd
\ Instances, withTransparency .all over evalTactic of the block's
\ tactics, which run in the block around it (no focus, no done, no save,
\ recover kept; names given inside it stay, as a tactic sequence's).
\ The block is a mode of the runner (tactic-run.fs's lf-block-mode)
\ whose open sets its frame's transparency (lf-tac-transparency!), at
\ which the runner runs every step inside it and every block's end
\ (lfr-advance-at), the one in force before put back however a step
\ ends, so that an error a handler below takes back (try, first,
\ any_goals, repeat) leaves no transparency behind; a block inside it
\ inherits it. The tactics' Meta and elaboration words read the
\ transparency in force (meta-must.fs's lf-tac-defeq, elab-decl.fs's
\ lf-elab-configured).
\ The recursion depth (tactic-run.fs's lf-tac-depth-most): measured on
\ pinned Lean (2026-11-26), with_reducible nested 167 times around rfl
\ passes and 168 times fails (maximum recursion depth), about 3.1
\ levels each; a block weighs 2 units of two levels (twr-weight), so
\ LeanForth supports 118 nested in a proof, where Lean accepts 167.
\ Lean call list: withReducible, withReducibleAndInstances,
\ withTransparency .all -> the modes' opens (twr-reducible, twr-instances,
\ twr-all); evalTactic of the sequence -> lf-tac-all (the block's steps
\ in the block around it).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (the transparency is the frame's).

require ../tactic-api.fs

\ ---- The modes: the frame's transparency set at its open.
: twr-reducible ( frame -- ) lf-tr-reducible swap lf-tac-transparency! ;
: twr-instances ( frame -- ) lf-tr-instances swap lf-tac-transparency! ;
: twr-all ( frame -- ) lf-tr-all swap lf-tac-transparency! ;
: twr-weight ( frame -- w ) drop 2 ;
: twr-mode ( open-xt -- mode )
  ['] drop 0 0 lf-block-mode ['] twr-weight over lf-mode-weight! ;
' twr-reducible twr-mode constant twr-mode-reducible
' twr-instances twr-mode constant twr-mode-instances
' twr-all twr-mode constant twr-mode-all

\ ---- The words: a block each, run in the block around it.
0 0 0 tac-shape-block lf-tactic: by-with-reducible constant tac-k-with-reducible
s" with_reducible" tac-k-with-reducible lf-tactic-lean!
twr-mode-reducible tac-k-with-reducible lf-tactic-mode!
' lf-tac-all tac-k-with-reducible lf-tactic-action!
0 0 0 tac-shape-block lf-tactic: by-with-reducible-and-instances
  constant tac-k-with-instances
s" with_reducible_and_instances" tac-k-with-instances lf-tactic-lean!
twr-mode-instances tac-k-with-instances lf-tactic-mode!
' lf-tac-all tac-k-with-instances lf-tactic-action!
0 0 0 tac-shape-block lf-tactic: by-with-unfolding-all constant tac-k-with-all
s" with_unfolding_all" tac-k-with-all lf-tactic-lean!
twr-mode-all tac-k-with-all lf-tactic-mode!
' lf-tac-all tac-k-with-all lf-tactic-action!
