\ h by-clear: Lean's clear h, one hypothesis (plan row TB1; the owner's
\ gate "Tactics in batches", 2026-11-19), a port of Lean 4.35.0's
\ evalClear (src/lean/Lean/Elab/Tactic/BuiltinTactic.lean:417-426) for one
\ term: in the main goal's context, getFVarId (tactic-core.fs's
\ lf-tac-get-fvar: the term must be a free variable, else error 389, "Unexpected
\ term ...; expected single reference to variable"), then MVarId.clear of
\ the main goal (meta-tactic/goal.fs's lf-goal-clear!: 440 unknown
\ variable, 441 another hypothesis depends on it, 442 the goal does), its
\ new goal in the main goal's place. Several hypotheses: by-clear[ ]
\ below (plan row TB2, tactic batch 3b).
\ Lean call list: getFVarIds/getFVarId -> lf-tac-get-fvar (tactic-core.fs);
\ withMainContext, getMainGoal, replaceMainGoal [mvarId] ->
\ lf-lift-meta-tactic1 (tactic-core.fs); MVarId.clear -> lf-goal-clear!
\ (meta-tactic/goal.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: tcl-frames (by-clear['s frame per call open, meta-must.fs's
\ lf-with-record), in the checker context (ADR 0009); no other.

require ../tactic-api.fs

tac-shape-term lf-tactic: by-clear constant tac-k-clear
s" clear" tac-k-clear lf-tactic-lean!
: tcl-tac ( i goal -- goal' ) swap 0 lf-tac-arg lf-tac-get-fvar lf-goal-clear! ;
: tcl-run ( i -- ) dup ['] tcl-tac lf-lift-meta-tactic1 ;
' tcl-run tac-k-clear lf-tactic-action!

\ by-clear[ h1 h2 ]: Lean's clear h1 h2 (plan row TB2, tactic batch 3b;
\ evalClear, BuiltinTactic.lean:417-426): getFVarIds of the names in the
\ main goal's context (tactic-core.fs's lf-tac-arg-fvars: 455 for a name
\ no local has), sortFVarIds (their order in that context), then each
\ cleared from the main goal newest first (lf-goal-clear!: 440, 441,
\ 442), a name given twice cleared twice (440 the second time, as in
\ Lean). A frame per call holds the step and its free variables.
tac-shape-hyps lf-tactic: by-clear[ constant tac-k-clear-list
s" clear" tac-k-clear-list lf-tactic-lean!
begin-structure /tcl
  field: tcl-step
  field: tcl-fvars       \ the names' free variables, a run
end-structure
/tcl context-slab: tcl-frames
: tcl ( -- frame ) tcl-frames slab-last ;
: tcl-cleared ( fvar goal -- goal' ) swap lf-goal-clear! ;
: tcl-if ( fvar x -- fvar outcome )
  over = if dup tcl tcl-step @ ['] tcl-cleared lf-lift-meta-tactic1 then outcome-ok ;
\ The local fvar cleared as often as the names give it.
: tcl-clears ( fvar -- ) tcl tcl-fvars @ ['] tcl-if run-each lf-tac-must drop ;
: tcl-walk ( view -- )
  dup lf-view-count begin dup while 1- 2dup lf-view-fvar tcl-clears repeat 2drop ;
: tcl-sorted ( i -- )
  dup tcl tcl-step ! lf-tac-arg-fvars tcl tcl-fvars ! lf-tac-main lf-goal-view tcl-walk ;
: tcl-list ( i -- ) tcl-frames ['] tcl-sorted lf-with-record ;
' tcl-list tac-k-clear-list lf-tactic-action!
