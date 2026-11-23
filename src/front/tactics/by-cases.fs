\ p by-cases: h, Lean's by_cases h : p (plan row TB2, tactic batch 2b;
\ the owner's spelling, Lean's name kept beside by-case:), a port of
\ Lean 4.35.0's macro open Classical in refine if h : p then ?pos else
\ ?neg (src/lean/Init/ByCases.lean:25-28): in the main goal's context p
\ elaborated with no expected type and no postponing (the if-then-else
\ notation's let_mvar% ?m := p), closed (tactics/have.fs's thv-untyped:
\ 93 for a metavariable left open, 99 for a cleared hypothesis named),
\ and a Prop (Meta.isProp; else not supported yet, 99, where Lean
\ answers the application's type mismatch); its Decidable instance by
\ search, else Classical.propDecidable (open Classical's scoped instance:
\ meta-tactic/by-cases.fs's lf-decidable-instance; the axiom report then
\ lists propext, Classical.choice and Quot.sound); the main goal assigned
\ the dite (lf-goal-by-cases) and the goals pos (h : p) and neg (h : ¬p)
\ in its place, in that order (refine's new goals, tagged as the holes
\ name them). Not supported yet: _ for the name (99), and the form with
\ no name (Lean's by_cases p, whose h is inaccessible).
\ Lean call list: refine's withMainContext, replaceMainGoal ->
\ lf-lift-meta-tactic; elabTerm c none -> thv-untyped; isProp ->
\ lf-meta-is-prop (fun-info.fs); the instance -> lf-decidable-instance;
\ the dite and its holes -> lf-goal-by-cases.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/by-cases.fs
require ./have.fs

1 1 tac-shape-term-names lf-tactic: by-cases: constant tac-k-by-cases
s" by_cases" tac-k-by-cases lf-tactic-lean!

\ A proposition (else not supported yet, 99; by-contra-core's too).
: tbs-prop ( p -- p )
  dup lf-meta-is-prop lf-tac-must 0= if lf-tac-unported then ;
: tbs-args ( i goal -- goal name p inst )
  swap dup 1 thv-name swap thv-untyped tbs-prop dup lf-decidable-instance ;
: tbs-tac ( i goal -- goals ) tbs-args lf-goal-by-cases lf-goals2 ;
: tbs-run ( i -- ) dup ['] tbs-tac lf-lift-meta-tactic ;
' tbs-run tac-k-by-cases lf-tactic-action!
