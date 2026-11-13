-- The Lean twins of the tactic runner's tests (plan FE1g-3a;
-- tests/front/tactic-run.fs, tests/front/05-unsolved.lf, 06-sorry.lf),
-- checked by tests/front/check_tactics.py --lean with pinned Lean 4.35.0.

-- 05-unsolved.lf: refused at `by`, "unsolved goals" and the goal below
-- (LeanForth: error 89 at by with the same lines).
theorem zero_add_open (n : Nat) : 0 + n = n := by

-- 06-sorry.lf: accepted with the warning "declaration uses `sorry`" (an
-- error under -DwarningAsError=true; the theorem is added all the same).
theorem zero_add_sorry (n : Nat) : 0 + n = n := by
  sorry

-- The statement the tests' stand-in gives 06-sorry.lf until plan FE1e.
theorem sorry_p (p : Prop) : p := by
  sorry

-- A second sorry: "No goals to be solved" at it (LeanForth: error 90).
theorem sorry_twice (p : Prop) : p := by
  sorry
  sorry

#print axioms zero_add_sorry
#print axioms sorry_p

-- The first tactics (plan FE1g-4; tests/front/tactic-basic.fs, 07-intro-exact.lf, 08-rfl.lf).
-- intro h; exact h: fun (p : Prop) (h : p) => h.
theorem self_imp (p : Prop) : p → p := by
  intro h
  exact h
-- rfl: fun (p : Prop) => @Eq.refl.{1} Prop p.
theorem refl_p (p : Prop) : p = p := by
  rfl
-- A second intro with nothing to introduce (LeanForth: error 94, the goal).
theorem intro_twice (p : Prop) : p → p := by
  intro
  intro
-- exact with a term of another type (LeanForth: error 96, the same lines),
-- the types of other sorts, then of the same sort.
theorem exact_sort (p : Prop) : p → p := by
  intro h
  exact p
theorem exact_wrong (p q : Prop) (h : q) : p := by
  exact h
-- rfl on two different sides (LeanForth: error 97, the same lines).
theorem refl_wrong (p q : Prop) : p = q := by
  rfl
-- Two binders, closed oldest first (review fe1g3 M1; tactic-basic.fs's
-- refl-x and imp-pq): fun (a : Type) (x : a) => @Eq.refl.{1} a x and
-- fun (p q : Prop) (h : p) => h.
theorem refl_x (a : Type) (x : a) : x = x := by
  rfl
set_option linter.unusedVariables false in
theorem imp_pq (p q : Prop) : p → p := by
  intro h
  exact h
-- rfl on sides that differ but are definitionally equal (two proofs of p):
-- Eq.refl of the left side (review fe1g3 L3; tactic-basic.fs's irrel).
theorem refl_irrel (p : Prop) (h1 h2 : p) : h1 = h2 := by
  rfl
-- intro head-beta reduces the binder's domain and the body, and whnfCore
-- finds the binder of a beta redex: the same goal after intro h, as
-- trace_state prints it (review fe1g3 L4; tactic-basic.fs's h-goal).
theorem intro_beta (p : Prop) : (fun x => x) p → (fun x => x) p := by
  intro h
  trace_state
  exact h
theorem intro_whnf (p : Prop) : (fun x => x) (p → p) := by
  intro h
  trace_state
  exact h
set_option pp.all true in
#print self_imp
set_option pp.all true in
#print refl_p
set_option pp.all true in
#print refl_x
set_option pp.all true in
#print imp_pq
set_option pp.all true in
#print refl_irrel
