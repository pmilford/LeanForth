\ by-intros: Lean's intros with no names (plan row TB1; the owner's gate
\ "Tactics in batches", 2026-11-19), a port of Lean 4.35.0's evalIntros
\ (src/lean/Lean/Elab/Tactic/BuiltinTactic.lean:396-400): liftMetaTactic of
\ MVarId.intros (Meta/Tactic/Intro.lean:199-206; meta-tactic/goal.fs's
\ lf-goal-intros): every leading binder of the main goal's type,
\ instantiated, as it is (no definition unfolded: ¬ a = b has none), each
\ a hypothesis of its own binder's kind and name made inaccessible (a✝; a
\ when it has none); no binder leaves the goal as it is. No error of its
\ own: introN's (99 for a let, an instance binder or a binder of no known
\ kind; 93). The named form, intros x y _, needs a shape with names
\ (tactic-syntax.fs: its own branch), so a word before by-intros is refused
\ as a value left over (86).
\ Lean call list: liftMetaTactic -> lf-lift-meta-tactic1 (tactic-core.fs,
\ the one goal as a list); MVarId.intros -> lf-goal-intros
\ (meta-tactic/goal.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-plain lf-tactic: by-intros constant tac-k-intros
s" intros" tac-k-intros lf-tactic-lean!
: tis-run ( i -- ) ['] lf-goal-intros lf-lift-meta-tactic1 ;
' tis-run tac-k-intros lf-tactic-action!
