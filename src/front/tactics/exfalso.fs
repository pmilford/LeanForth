\ by-exfalso: Lean's exfalso (plan row TB1; the owner's gate "Tactics in
\ batches", 2026-11-19), a port of Lean 4.35.0's exfalso, the macro
\ refine False.elim ?_ (src/lean/Init/Tactics.lean:276): the main goal T
\ becomes False, the goal assigned @False.elim.{u} T ?g, ?g the new goal
\ with the main goal's tag and context. The term is that of
\ MVarId.exfalso (Meta/Tactic/Apply.lean:286-293; meta-tactic/goal.fs's
\ lf-goal-exfalso), which the macro's refine builds too: refine elaborates
\ False.elim ?_ against T (?u fixed by Sort ?u =?= the type of T, getLevel's
\ level) and its one new goal, untagged, takes the main goal's tag
\ (tagUntaggedGoals). The pinned comparison checks the term node for node.
\ No error of its own: refine fails only where False.elim is unknown
\ (Lean's "unknown identifier"; LeanForth's mkConst refuses it, a failed
\ step, never a closed goal).
\ Lean call list: liftMetaTactic1 -> lf-lift-meta-tactic1 (tactic-core.fs);
\ MVarId.exfalso -> lf-goal-exfalso (meta-tactic/goal.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-plain lf-tactic: by-exfalso constant tac-k-exfalso
s" exfalso" tac-k-exfalso lf-tactic-lean!
: tef-run ( i -- ) ['] lf-goal-exfalso lf-lift-meta-tactic1 ;
' tef-run tac-k-exfalso lf-tactic-action!
