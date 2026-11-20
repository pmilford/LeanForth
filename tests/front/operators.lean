-- How pinned Lean 4.35.0 reads the statements of tests/front/check_front.py
-- (plan FE1a): each term after macro expansion, every nested macro expanded
-- (Lean.Elab.expandMacros), printed one per line. The natural reader must
-- build the same tree from the LeanForth spelling. Syntax only: nothing is
-- elaborated, so the variables need not exist.
import Lean

open Lean Elab Command in
elab "#expand " t:term : command => do
  let s ← liftMacroM (expandMacros t)
  logInfo m!"{s}"

#expand 0 + n = n
#expand 2 * 3 ≤ 7
#expand 0 + n + m = m * n
#expand Nat.succ n = n + 1
#expand n = 0 + (n + 0)
#expand congrArg Nat.succ n = n
#expand n - m < n
#expand n / 2 % 3 = n
#expand n > m
#expand n ≥ m
#expand n >= m
#expand n <= m
#expand n ≠ m
#expand 2 ^ 10 = n
#expand 2 ^ 3 ^ 2 = n
#expand 2 ^ 10 * 3 = n
#expand n = n ∧ m = m
#expand n = n /\ m = m
