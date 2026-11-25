\ by-contra: h, by-contra and by-contra-core: Batteries' by_contra h,
\ by_contra and by_contra_core (plan row TB2, tactic batch 2b), ports of
\ .tools/mathlib/mathlib4/.lake/packages/batteries/Batteries/Tactic/
\ Init.lean:43-61:
\ - by-contra-core: the macro first | guard_target = Not _; change _ →
\   False | refine @Decidable.byContradiction _ _ ?_ | refine
\   @Classical.byContradiction _ ?_, its alternatives in that order
\   (tactic-core.fs's lf-tac-first-of: a Lean error undone and the next
\   tried, the last one's error Lean's), each on the main goal in its
\   context:
\   guard_target = Not _ (Lean's reducible isDefEq, withoutModifyingState):
\     the target instantiated, through whnfR, Not p (else error 450, "The
\     main goal is", Lean's guard error); change _ → False: the target
\     through whnf, p → False (what isDefEq of ?a → False with it assigns
\     ?a, the arrow's binder name aside, which intro replaces), and
\     MVarId.replaceTargetDefEq (meta-tactic/goal.fs: @id T goal');
\   refine @Decidable.byContradiction _ _ ?_: the target, a Prop (else not
\     supported yet, 99, where Lean answers a type mismatch), its
\     Decidable instance by search (none: Lean's "failed to synthesize",
\     122), the goal assigned @Decidable.byContradiction p inst ?g, ?g a
\     new synthetic opaque goal of ¬p → False with the goal's tag;
\   refine @Classical.byContradiction _ ?_: the same with no instance
\     (the axiom report then lists propext, Classical.choice, Quot.sound).
\ - by-contra[ pat ]: Batteries' by_contra pat (Init.lean:57-60, the
\   macro by_contra_core; rintro (pat)): a sequence of rows (tactic-api.
\   fs's lf-tactic-seq:), by-contra-core's, then by-rintro['s on the same
\   step (rintro.fs: rcases.fs's lf-rintro), its pattern one element
\   (pattern-syntax.fs's tac-shape-contra: a | b is Lean's (a | b));
\ - by-contra: h: the same with the pattern h (Lean's by_contra h; h a
\   name, _ or rfl);
\ - by-contra: the same with the name this (Lean's default pattern).
\ Not supported yet: the : T form (Lean's by_contra h : T), slice E5.
\ Lean call list: first -> lf-tac-first-of; guard_target -> lf-whnf-r!,
\ lf-meta-app-of?; change -> lf-whnf!, lf-goal-replace-target-defeq;
\ refine -> lf-goal-target, lf-meta-is-prop, lf-synth-instance!,
\ lf-goal-fresh, lf-mvar-assign; liftMetaTactic1 -> lf-lift-meta-tactic1;
\ the macros -> lf-tactic-seq: of tac-k-rintro (tactics/rintro.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/by-cases.fs
require ./by-cases.fs
require ./rintro.fs

450 lfa-lean s" The main goal is" lfa-code: lfa-e-guard-target

tac-shape-plain lf-tactic: by-contra-core constant tac-k-by-contra-core
s" by_contra_core" tac-k-by-contra-core lf-tactic-lean!

\ ---- guard_target = Not _; change _ → False.
: tbc-not? ( t -- flag ) lf-whnf-r! 1 s" Not" lf-meta-app-of? ;
: tbc-guard ( t -- t ) dup tbc-not? 0= if lfa-e-guard-target lf-tac-stop then ;
: tbc-change-tac ( goal -- goal' )
  dup lf-goal-target drop tbc-guard lf-whnf! lf-goal-replace-target-defeq ;

\ ---- refine @C _ ?_: goal assigned e ?g, ?g of the domain of e's type.
: tbc-target ( goal -- goal p ) dup lf-goal-target drop tbs-prop ;
: tbc-hole ( goal e -- goal e g ) 2dup lf-infer! lf-term-first@ swap lf-goal-fresh ;
: tbc-refined ( goal e -- g ) tbc-hole tuck lf-mk-app rot swap lf-mvar-assign lf-must ;
: tbc-dec-term ( p -- e )
  s" Decidable.byContradiction" lf-mk-const0 over lf-mk-app swap lf-mk-decidable
  lf-synth-instance! lf-mk-app ;
: tbc-dec-tac ( goal -- g ) tbc-target tbc-dec-term tbc-refined ;
: tbc-cls-term ( p -- e ) s" Classical.byContradiction" lf-mk-const0 swap lf-mk-app ;
: tbc-cls-tac ( goal -- g ) tbc-target tbc-cls-term tbc-refined ;

\ ---- The alternatives, the first on top.
: tbc-change ( -- ) lf-tac-step ['] tbc-change-tac lf-lift-meta-tactic1 ;
: tbc-decidable ( -- ) lf-tac-step ['] tbc-dec-tac lf-lift-meta-tactic1 ;
: tbc-classical ( -- ) lf-tac-step ['] tbc-cls-tac lf-lift-meta-tactic1 ;
: tbc-run ( i -- )
  drop ['] tbc-classical ['] tbc-decidable ['] tbc-change 3 lf-tac-first-of ;
' tbc-run tac-k-by-contra-core lf-tactic-action!

\ ---- by_contra pat, by_contra h and by_contra: the core, then rintro.
tac-k-by-contra-core tac-k-rintro 2 tac-shape-contra-name
  lf-tactic-seq: by-contra: constant tac-k-by-contra
s" by_contra" tac-k-by-contra lf-tactic-lean!
tac-k-by-contra-core tac-k-rintro 2 tac-shape-contra-this
  lf-tactic-seq: by-contra constant tac-k-by-contra-this
s" by_contra" tac-k-by-contra-this lf-tactic-lean!
tac-k-by-contra-core tac-k-rintro 2 tac-shape-contra
  lf-tactic-seq: by-contra[ constant tac-k-by-contra-pat
s" by_contra" tac-k-by-contra-pat lf-tactic-lean!
