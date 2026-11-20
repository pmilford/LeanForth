\ by-right: Lean's right (plan row TB1; the owner's gate "Tactics in
\ batches", 2026-11-19), a port of Lean 4.35.0's evalRight (src/lean/Lean/
\ Elab/Tactic/BuiltinTactic.lean:663-664): liftMetaTactic of
\ MVarId.nthConstructor `right 1 (some 2) (meta-tactic/constructor.fs's
\ lf-goal-nth-constructor): the main goal's type, through whnf, must be an
\ inductive type with two constructors, and the second is applied
\ (Or.inr; Nat.le.step), its goals in the main goal's place. Errors 387
\ (not an inductive type), 388 (not two constructors), and apply's (380,
\ 384, 125). Unlike constructor, Lean synthesizes no pending problem here.
\ Lean call list: liftMetaTactic -> lf-lift-meta-tactic (tactic-core.fs);
\ MVarId.nthConstructor -> lf-goal-nth-constructor with the record tri-nth
\ (lf-nth-constructor:, meta-tactic/constructor.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (tri-nth is constant data).

require ../tactic-api.fs

387 outcome-invalid s" Tactic `right` failed: target is not an inductive datatype"
  lfa-code: lfa-e-right-target
388 outcome-invalid s" Tactic `right` failed: right tactic works for inductive types"
  lfa-code: lfa-e-right-count
lfa-e-right-count lfa-message-of s"  with exactly 2 constructors" lfa-more,
tac-shape-plain lf-tactic: by-right constant tac-k-right
s" right" tac-k-right lf-tactic-lean!

1 2 lfa-e-right-target lfa-e-right-count lf-nth-constructor: tri-nth
: tri-tac ( goal -- goals ) tri-nth lf-goal-nth-constructor ;
: tri-run ( i -- ) ['] tri-tac lf-lift-meta-tactic ;
' tri-run tac-k-right lf-tactic-action!
