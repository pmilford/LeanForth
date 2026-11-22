\ by-exacts[ e1 .. en ], Batteries' exacts [e1, ..., en] (plan row TB2,
\ tactic batch 2b), a port of its elaborator (.tools/mathlib/mathlib4/
\ .lake/packages/batteries/Batteries/Tactic/Init.lean:31-34): exact e1,
\ then exact e2, .., each on the main goal of the moment (evalTactic of
\ exact: tactics/exact.fs's tex-exact, its errors exact's), then done (no
\ goal left: else error 89, Lean's "unsolved goals", with the goals, at
\ the by-exacts[ word). The terms are the bracket's values (tactic-syntax.fs's
\ tac-shape-list: no <-).
\ Lean call list: evalTactic exact -> tex-exact; done -> lf-tac-done
\ (tactic-run.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ./exact.fs

tac-shape-list lf-tactic: by-exacts[ constant tac-k-exacts
s" exacts" tac-k-exacts lf-tactic-lean!

: tes-run ( i -- ) dup lf-tac-args# 0 ?do dup i tex-exact loop lf-tac-done ;
' tes-run tac-k-exacts lf-tactic-action!
