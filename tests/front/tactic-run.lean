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
