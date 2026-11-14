-- The order of events of C17 (#check 0 + 0 = 0, FE1E_APPLICATIONS.md 6.1)
-- in pinned Lean, against which tests/front/s1-c17.trace and s1-c1.trace
-- (LeanForth's trace, tests/front/elab.fs) were reviewed: run
--   lean tests/front/s1-c17.lean
-- and read the elabAppArgs, resume and synthInstance lines.
set_option trace.Elab.resume true
set_option trace.Elab.postpone true
set_option trace.Elab.binrel true
set_option trace.Elab.binop true
set_option trace.Elab.app.args true
set_option trace.Elab.defaultInstance true
set_option trace.Meta.synthInstance true
#check 0 + 0 = 0
#check fun (n : Nat) => 0 + n = n
