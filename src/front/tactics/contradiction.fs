\ by-contradiction: Lean's contradiction (plan row TB2, tactic batch 1), a
\ port of Lean 4.35.0's evalContradiction (src/lean/Lean/Elab/Tactic/
\ BuiltinTactic.lean:315-317): liftMetaTactic of MVarId.contradiction
\ (meta-tactic/contradiction.fs's lf-goal-contradiction, with the rules it
\ ports and the ones it answers not supported yet, 99), which closes the
\ main goal; none closes it is error 449, "Tactic `contradiction` failed"
\ with the goal.
\ Lean call list: liftMetaTactic -> lf-lift-meta-tactic (tactic-core.fs);
\ MVarId.contradiction -> lf-goal-contradiction.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/contradiction.fs

tac-shape-plain lf-tactic: by-contradiction constant tac-k-contradiction
s" contradiction" tac-k-contradiction lf-tactic-lean!
: tcn-tac ( goal -- goals ) lf-goal-contradiction 0 ;
: tcn-run ( i -- ) ['] tcn-tac lf-lift-meta-tactic ;
' tcn-run tac-k-contradiction lf-tactic-action!
