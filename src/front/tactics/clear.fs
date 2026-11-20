\ h by-clear: Lean's clear h, one hypothesis (plan row TB1; the owner's
\ gate "Tactics in batches", 2026-11-19), a port of Lean 4.35.0's
\ evalClear (src/lean/Lean/Elab/Tactic/BuiltinTactic.lean:417-426) for one
\ term: in the main goal's context, getFVarId (tactic-core.fs's
\ lf-tac-get-fvar: the term must be a free variable, else error 389, "Unexpected
\ term ...; expected single reference to variable"), then MVarId.clear of
\ the main goal (meta-tactic/goal.fs's lf-goal-clear!: 440 unknown
\ variable, 441 another hypothesis depends on it, 442 the goal does), its
\ new goal in the main goal's place. Several hypotheses (Lean's clear h1 h2,
\ sorted by sortFVarIds and cleared newest first) need a shape with several
\ terms: not this word's.
\ Lean call list: getFVarIds/getFVarId -> lf-tac-get-fvar (tactic-core.fs);
\ withMainContext, getMainGoal, replaceMainGoal [mvarId] ->
\ lf-lift-meta-tactic1 (tactic-core.fs); MVarId.clear -> lf-goal-clear!
\ (meta-tactic/goal.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-term lf-tactic: by-clear constant tac-k-clear
s" clear" tac-k-clear lf-tactic-lean!
: tcl-tac ( i goal -- goal' ) swap 0 lf-tac-arg lf-tac-get-fvar lf-goal-clear! ;
: tcl-run ( i -- ) dup ['] tcl-tac lf-lift-meta-tactic1 ;
' tcl-run tac-k-clear lf-tactic-action!
