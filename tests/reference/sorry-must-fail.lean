-- Negative fixture: a false theorem "proved" with `sorry`.
-- tests/reference/check.sh requires pinned Lean to reject this file when run
-- with -DwarningAsError=true, as every Lean invocation in the test scripts
-- is. If it were ever accepted, the Lean reference checks would fail open:
-- an unproved claim would count as checked.
-- scripts/check-lean-sources.py allowlists this one use of `sorry`.
theorem sorry_must_fail : (1 : Nat) = 2 := sorry
