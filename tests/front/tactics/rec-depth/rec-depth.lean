-- Pinned Lean 4.35.0 twins of the runner's bound on Lean's recursion depth (tests/front/tactics/
-- rec-depth/test.fs; src/front/tactic-run.fs's lf-tac-depth-most): the deepest nesting of each
-- block, in its one-line spelling, that pinned Lean accepts (measured 2026-11-26; one more level
-- of each is in rec-depth-wrong.lean, which Lean refuses with "maximum recursion depth has been
-- reached"). LeanForth answers not supported yet (99) before every one of these depths, its
-- weights being at least each level's cost here. check.py --lean checks both files.
-- Generated: iterate 126 skip is 2 * 126 + 3 levels; try (X), any_goals (X), all_goals (X),
-- first | (X), focus (X), { X }, (have z : a = b := by { X; exact h }), skip <;> try (X),
-- repeat ((X); fail), iterate 126 (try (...)), and with skip alone (have0, try0).
set_option linter.unusedVariables false
theorem rd_try_35 (a b : Nat) (h : a = b) : a = b := by
  try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (iterate 126 skip)))))))))))))))))))))))))))))))))))
  exact h

theorem rd_anyg_41 (a b : Nat) (h : a = b) : a = b := by
  any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (iterate 126 skip)))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_allg_41 (a b : Nat) (h : a = b) : a = b := by
  all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (iterate 126 skip)))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_first_41 (a b : Nat) (h : a = b) : a = b := by
  first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (iterate 126 skip)))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_focus_41 (a b : Nat) (h : a = b) : a = b := by
  focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (iterate 126 skip)))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_brace_200 (a b : Nat) (h : a = b) : a = b := by
  { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { (iterate 126 skip); exact h } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }

theorem rd_have_16 (a b : Nat) (h : a = b) : a = b := by
  (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (iterate 126 skip); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h })
  exact h

theorem rd_then_16 (a b : Nat) (h : a = b) : a = b := by
  skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (iterate 126 skip))))))))))))))))
  exact h

theorem rd_rep_27 (a b : Nat) (h : a = b) : a = b := by
  repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((iterate 126 skip); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)
  exact h

theorem rd_it_try_35 (a b : Nat) (h : a = b) : a = b := by
  iterate 126 (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (skip))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_have0_32 (a b : Nat) (h : a = b) : a = b := by
  (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { skip; exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h })
  exact h

theorem rd_try0_72 (a b : Nat) (h : a = b) : a = b := by
  try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (skip))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_it_251 (a b : Nat) (h : a = b) : a = b := by
  iterate 251 skip
  exact h

-- with_reducible (small tactics 2): 167 nested pass, 168 fail (rec-depth-wrong.lean).
theorem rd_wr (a : Nat) : a = a := by
  with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible with_reducible rfl
