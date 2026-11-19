\ by-intro: NAME, Lean's intro NAME (plan FE1g-4, design docs/design/
\ FE1G_TACTICS.md 5.1; moved onto the tactic library by plan 9.4.8l-I), a
\ port of Lean 4.35.0's evalIntro (src/lean/Lean/Elab/Tactic/
\ BuiltinTactic.lean) for one name: liftMetaTactic of MVarId.introN 1
\ (meta-tactic/goal.fs's lf-goal-intro-n), the binder's kind the node's,
\ which must be explicit. NAME is the hypothesis's name; _ gives the
\ binder's own, inaccessible. Not supported yet (99): the name rfl (Lean's
\ intro rfl substitutes, plan FE5). The goal's errors (94, 93, 99) are
\ lf-goal-intro-n's.
\ Lean call list: liftMetaTactic and introN 1 -> lf-tac-intro1
\ (tactic-core.fs); the pattern's name -> lf-tac-arg.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Its kind is the runner's tac-k-intro (a fixed
\ kind, scripts/check-tactic-plugins.py's ownership table).

require ../tactic-api.fs

: tin-rfl? ( name -- flag ) dup if s" rfl" lfa-intern = else drop false then ;
: tin-name ( i -- name ) 0 lf-tac-arg dup tin-rfl? if lfa-e-tac-form lf-tac-fail then ;
: tin-run ( i -- ) dup tin-name swap -1 swap lf-tac-intro1 ;
' tin-run tac-k-intro lf-tactic-action!
