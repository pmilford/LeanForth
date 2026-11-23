\ by-assumption: Lean's assumption (slice a2-iii of docs/design/
\ TACTIC_PLUGINS.md; the owner approved the word on 2026-11-18), a port of
\ Lean 4.35.0's evalAssumption (src/lean/Lean/Elab/Tactic/
\ BuiltinTactic.lean:309): liftMetaTactic of MVarId.assumption under
\ withAssignableSyntheticOpaque (meta-tactic/assumption.fs): the newest
\ hypothesis whose type is definitionally equal to the main goal's closes
\ it; none is error 381 with the goal.
\ Lean call list: liftMetaTactic -> lf-lift-meta-tactic (tactic-core.fs);
\ withAssignableSyntheticOpaque and MVarId.assumption ->
\ lf-goal-assumption (meta-tactic/assumption.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-plain lf-tactic: by-assumption constant tac-k-assumption
s" assumption" tac-k-assumption lf-tactic-lean!

: tas-tac ( goal -- goals ) lf-goal-assumption 0 ;
: tas-run ( i -- ) ['] tas-tac lf-lift-meta-tactic ;
' tas-run tac-k-assumption lf-tactic-action!
\ assumption on the step running: an alternative of a tactic Lean writes
\ over it (trivial's last rule, lf-tac-macro-alts; rwa's closing,
\ lf-tac-first-of).
: tas-row ( -- ) tac-k-assumption lf-tac-row ;
