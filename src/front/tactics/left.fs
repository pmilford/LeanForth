\ by-left: Lean's left (plan row TB1; the owner's gate "Tactics in
\ batches", 2026-11-19), a port of Lean 4.35.0's evalLeft (src/lean/Lean/
\ Elab/Tactic/BuiltinTactic.lean:660-661): liftMetaTactic of
\ MVarId.nthConstructor `left 0 (some 2) (meta-tactic/constructor.fs's
\ lf-goal-nth-constructor): the main goal's type, through whnf, must be an
\ inductive type with two constructors, and the first is applied (Or.inl;
\ Nat.le.refl), its goals in the main goal's place. Errors 385 (not an
\ inductive type), 386 (not two constructors), and apply's (380, 384,
\ 125). Unlike constructor, Lean synthesizes no pending problem here.
\ Lean call list: liftMetaTactic -> lf-lift-meta-tactic (tactic-core.fs);
\ MVarId.nthConstructor -> lf-goal-nth-constructor with the record tle-nth
\ (lf-nth-constructor:, meta-tactic/constructor.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (tle-nth is constant data).

require ../tactic-api.fs

385 outcome-invalid s" Tactic `left` failed: target is not an inductive datatype"
  lfa-code: lfa-e-left-target
386 outcome-invalid s" Tactic `left` failed: left tactic works for inductive types"
  lfa-code: lfa-e-left-count
lfa-e-left-count lfa-message-of s"  with exactly 2 constructors" lfa-more,
tac-shape-plain lf-tactic: by-left constant tac-k-left
s" left" tac-k-left lf-tactic-lean!

0 2 lfa-e-left-target lfa-e-left-count lf-nth-constructor: tle-nth
: tle-tac ( goal -- goals ) tle-nth lf-goal-nth-constructor ;
: tle-run ( i -- ) ['] tle-tac lf-lift-meta-tactic ;
' tle-run tac-k-left lf-tactic-action!
