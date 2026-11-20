\ by-rfl, Lean's rfl (plan FE1g-4, design docs/design/FE1G_TACTICS.md
\ 5.3; moved onto the tactic library by plan 9.4.8l-I): of the macro's
\ alternatives, exact Iff.rfl and exact HEq.rfl fail without a trace on
\ an Eq goal, eq_refl decides, and apply_rfl after its failure gives the
\ error: liftMetaTactic of meta-tactic/goal.fs's lf-goal-refl (MVarId.refl
\ and MVarId.applyRfl, src/lean/Lean/Meta/Tactic/Refl.lean and Rfl.lean
\ of Lean 4.35.0), whose errors (97, 93) it keeps. by-rw[ runs it after
\ the rewrite under with_reducible.
\ Lean call list: liftMetaTactic -> lf-lift-meta-tactic (tactic-core.fs);
\ eq_refl's MVarId.refl, then apply_rfl's MVarId.applyRfl -> lf-goal-refl.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Its kind is the runner's tac-k-rfl (a fixed
\ kind, scripts/check-tactic-plugins.py's ownership table).

require ../tactic-api.fs

: trf-tac ( goal -- goals ) lf-goal-refl 0 ;
: trf-run ( i -- ) ['] trf-tac lf-lift-meta-tactic ;
' trf-run tac-k-rfl lf-tactic-action!
