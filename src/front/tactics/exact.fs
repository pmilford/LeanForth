\ t by-exact, Lean's exact t (plan FE1g-4, design docs/design/
\ FE1G_TACTICS.md 5.2; moved onto the tactic library by plan 9.4.8l-I), a
\ port of Lean 4.35.0's evalExact (src/lean/Lean/Elab/Tactic/
\ ElabTerm.lean): closeMainGoalUsing with t elaborated against the main
\ goal's type, no postponing (elabTermEnsuringType): its errors 96, 93,
\ 95, 98 and the Term layer's are those of lf-close-main-goal-using,
\ lf-tac-elab-ensuring (tactic-core.fs) and lf-goal-checked-assign
\ (meta-tactic/goal.fs).
\ Lean call list: closeMainGoalUsing -> lf-close-main-goal-using;
\ elabTermEnsuringType -> lf-tac-elab-ensuring; the term -> lf-tac-arg.
\ tex-exact ( i k -- ) is exact of step i's argument k, for a tactic Lean
\ writes over exact (by-exacts[, tactics/exacts.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own. Its kind is the runner's tac-k-exact (a fixed
\ kind, scripts/check-tactic-plugins.py's ownership table).

require ../tactic-api.fs

: tex-term ( node type tag -- e ) drop lf-tac-elab-ensuring ;
\ exact of step i's term k (by-exacts[ runs it for each of its terms).
: tex-exact ( i k -- ) over swap lf-tac-arg swap ['] tex-term lf-close-main-goal-using ;
: tex-run ( i -- ) 0 tex-exact ;
' tex-run tac-k-exact lf-tactic-action!
