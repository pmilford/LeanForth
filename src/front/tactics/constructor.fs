\ by-constructor: Lean's constructor (slice a2-iii of docs/design/
\ TACTIC_PLUGINS.md; the owner approved the word on 2026-11-18), a port of
\ Lean 4.35.0's evalConstructor and evalConstructorCore (src/lean/Lean/
\ Elab/Tactic/ElabTerm.lean:326-345): in the main goal's context,
\ MVarId.constructorCore with findAll (meta-tactic/constructor.fs: the
\ first constructor of the goal's inductive type that apply accepts), the
\ pending problems synthesized with no postponing, its goals in the main
\ goal's place. Errors 382 (not an inductive type), 383 (no constructor
\ applies). Lean's warning when several constructors apply is not printed
\ (LeanForth has no warnings; the choice and the term are Lean's).
\ Lean call list: withMainContext, getMainGoal, replaceMainGoal ->
\ lf-lift-meta-tactic (tactic-core.fs); constructorCore ->
\ lf-goal-constructor (meta-tactic/constructor.fs); logWarning -> not
\ ported; synthesizeSyntheticMVarsNoPostponing -> lf-tac-with-synth
\ (tactic-core.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-plain lf-tactic: by-constructor constant tac-k-constructor
s" constructor" tac-k-constructor lf-tactic-lean!

: tco-tac ( goal -- goals ) ['] lf-goal-constructor lf-tac-with-synth ;
: tco-run ( i -- ) ['] tco-tac lf-lift-meta-tactic ;
' tco-run tac-k-constructor lf-tactic-action!
