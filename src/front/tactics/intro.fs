\ by-intro: NAME and by-intro[ NAMES ] (below), Lean's intro NAME and
\ intro a b c (plan FE1g-4, design docs/design/
\ FE1G_TACTICS.md 5.1; moved onto the tactic library by plan 9.4.8l-I), a
\ port of Lean 4.35.0's evalIntro (src/lean/Lean/Elab/Tactic/
\ BuiltinTactic.lean) for one name: liftMetaTactic of MVarId.introN 1
\ (meta-tactic/goal.fs's lf-goal-intro-n), the binder's kind the node's:
\ explicit, implicit or strict implicit, as Lean's intro (plan row TB1,
\ 2026-11-19; an instance binder needs a local instance, plan FE3, 99).
\ NAME is the hypothesis's name; _ gives the
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
: tin-name ( i k -- name ) lf-tac-arg dup tin-rfl? if lf-tac-unported then ;
\ introStep of step i's name k.
: tin-one ( i k -- i ) over swap tin-name over -1 swap lf-tac-intro1 ;
: tin-run ( i -- ) 0 tin-one drop ;
' tin-run tac-k-intro lf-tactic-action!

\ by-intro[ a b c ]: Lean's intro a b c (plan row TB2, tactic batch 3b;
\ evalIntro, BuiltinTactic.lean:322-341: evalArg of each name in turn,
\ introStep), by-intro:'s step for each name in order; an empty list is
\ Lean's bare intro, intro _ (an inaccessible hypothesis).
tac-shape-binders lf-tactic: by-intro[ constant tac-k-intro-list
s" intro" tac-k-intro-list lf-tactic-lean!
: tin-bare ( i -- ) 0 swap -1 swap lf-tac-intro1 ;
: tin-names ( i n -- ) 0 ?do i tin-one loop drop ;
: tin-list ( i -- ) dup lf-tac-args# ?dup if tin-names else tin-bare then ;
' tin-list tac-k-intro-list lf-tactic-action!
