-- Pinned Lean 4.35.0 refuses each theorem here with "maximum recursion depth has been reached"
-- (measured 2026-11-26): one level more of each block than rec-depth.lean's, the same spellings
-- (tests/front/tactics/rec-depth/test.fs has the table). LeanForth's twins of these depths are
-- not supported yet (99), never accepted. check.py --lean checks that each theorem fails so.
set_option linter.unusedVariables false
theorem rd_try_36 (a b : Nat) (h : a = b) : a = b := by
  try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (iterate 126 skip))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_anyg_42 (a b : Nat) (h : a = b) : a = b := by
  any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (any_goals (iterate 126 skip))))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_allg_42 (a b : Nat) (h : a = b) : a = b := by
  all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (all_goals (iterate 126 skip))))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_first_42 (a b : Nat) (h : a = b) : a = b := by
  first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (first | (iterate 126 skip))))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_focus_42 (a b : Nat) (h : a = b) : a = b := by
  focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (focus (iterate 126 skip))))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_brace_250 (a b : Nat) (h : a = b) : a = b := by
  { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { { (iterate 126 skip); exact h } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }

theorem rd_have_17 (a b : Nat) (h : a = b) : a = b := by
  (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (iterate 126 skip); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h })
  exact h

theorem rd_then_18 (a b : Nat) (h : a = b) : a = b := by
  skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (skip <;> try (iterate 126 skip))))))))))))))))))
  exact h

theorem rd_rep_28 (a b : Nat) (h : a = b) : a = b := by
  repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((repeat ((iterate 126 skip); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)); fail)
  exact h

theorem rd_it_try_36 (a b : Nat) (h : a = b) : a = b := by
  iterate 126 (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (skip)))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_have0_34 (a b : Nat) (h : a = b) : a = b := by
  (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { (have z : a = b := by { skip; exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h }); exact h })
  exact h

theorem rd_try0_74 (a b : Nat) (h : a = b) : a = b := by
  try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (try (skip))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact h

theorem rd_it_252 (a b : Nat) (h : a = b) : a = b := by
  iterate 252 skip
  exact h

