/-
Goals as pinned Lean 4.35.0's trace_state prints them (plan FE1g-1), for
tests/front/check_goals.py: each `trace "=== NAME"` starts a block, which
the LeanForth twin tests/front/goals-print.fs prints from the same goal
state built by hand (src/front/goal-print.fs). Every block must print the
same, except the ones check_goals.py lists as gaps of the term printer
(plan 8.6). Run as
  lean -DwarningAsError=false tests/front/goals-print.lean
-/
set_option linter.unusedVariables false

-- The FE1 proof of 0 + n = n (FE1G_TACTICS.md §2.1): the goal at `by`,
-- the two cases of `induction n with`, the goal after `rewrite`.
theorem t1 (n : Nat) : 0 + n = n := by
  trace "=== t1.start"
  trace_state
  induction n with
  | zero => trace "=== t1.zero"; trace_state; rfl
  | succ k ih =>
    trace "=== t1.succ"
    trace_state
    rewrite [Nat.add_succ]
    trace "=== t1.rewritten"
    trace_state
    rw [ih]

-- Without `with`: two goals, the cases' hypotheses inaccessible (§2.2).
theorem t5 (n : Nat) : 0 + n = n := by
  induction n
  trace "=== t5.cases"
  trace_state
  case zero => rfl
  case succ k ih => exact congrArg Nat.succ ih

-- Groups, a let whose value shows, a have shown as a hypothesis.
theorem t8 (a b : Nat) (p q : Prop) (h : p) : True := by
  let x : Nat := a + b
  have y : Nat := a
  trace "=== t8"
  trace_state
  trivial

-- A shadowed name, a hypothesis generalized and introduced again.
theorem t9 (n : Nat) (n : Nat) (h : n = n) : True := by
  induction n
  trace "=== t9.cases"
  trace_state
  all_goals trivial

-- intro shadowing a hypothesis; intro without a name.
theorem c2 (n : Nat) : ∀ (m : Nat), m + n = m + n := by
  intro n
  trace "=== c2"
  trace_state
  rfl

theorem c4 : ∀ (x : Nat) (y : Nat), x = x := by
  intro x
  intro
  trace "=== c4"
  trace_state
  rfl

-- Tombstones with numbers: x✝¹, x✝²; shadowed and inaccessible.
theorem s1 : ∀ (x : Nat) (x : Nat) (x : Nat), True := by
  intro x x x
  trace "=== s1"
  trace_state
  trivial

theorem s2 : ∀ (x : Nat) (x : Nat) (x : Nat), True := by
  intro _ _ _
  trace "=== s2"
  trace_state
  trivial

-- Hypotheses of equal types share a line.
theorem d2 (a : Nat) (b : Nat) (c : Nat) (h : a = b) (h' : a = b) (q : b = c) :
    True := by
  trace "=== d2"
  trace_state
  trivial

-- A let value deeper than 254 (approxDepth 2 * 127 + 2) prints as ⋯.
theorem d127 : let y := 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1; y = y := by
  intro y
  trace "=== d127"
  trace_state
  rfl

-- No goals: an empty message; two tagged goals.
theorem e1 : True := by
  trivial
  trace "=== e1"
  trace_state

theorem e2 (p : Prop) (hp : p) : p ∧ p := by
  constructor
  trace "=== e2"
  trace_state
  all_goals exact hp

theorem e3 : ∀ (x : Nat), let y := x + 1; y = x + 1 := by
  intro x y
  trace "=== e3"
  trace_state
  rfl

-- Gaps of the term printer (plan 8.6): a Π that is a proposition (Lean
-- infers its type and prints ∀; the printer's quick test does not know
-- Eq's type), in the goal and in a hypothesis.
theorem g1 (n : Nat) : ∀ (m : Nat), m = m := by
  trace "=== g1"
  trace_state
  intro m
  rfl

theorem g3 (n : Nat) (h : ∀ (k : Nat), k = n) : True := by
  trace "=== g3"
  trace_state
  trivial
