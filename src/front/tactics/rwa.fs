\ by-rwa[ r1 .. rn ], Lean's rwa [r1, ..., rn] (plan row TB2, tactic
\ batch 2b), a port of Lean 4.35.0's evalRwa (src/lean/Lean/Elab/Tactic/
\ Rwa.lean:70-77 over evalRwaCore :42-57; its own elaborator, not the
\ macro rw rs; assumption of earlier versions): focus on the main goal;
\ rewrite rs (by-rewrite['s row on this step: its rules, <- included,
\ and its errors at the rule); then with_reducible rfl, else assumption
\ (Lean's <|>: rfl tried from a saved state, its Lean error undone, then
\ assumption at the transparency in force, default: its error 381 is
\ rwa's; tactic-core.fs's lf-tac-first-of). Lean's inner focus and its
\ closing all_goals (first | with_reducible rfl | assumption | skip) act
\ on the rewrite's side goals, which LeanForth's rewrite refuses (99), so
\ they find none here; its linter's warning that rw alone closes the goal
\ ("`rw` already closes the goal") changes no term and is not printed.
\ The at h form is plan TB2 batch 3.
\ Lean call list: Tactic.focus -> lf-tac-focus, lf-tac-unfocus
\ (tactic-run.fs); evalTactic rewrite -> lf-tac-eval of tac-k-rewrite;
\ with_reducible rfl -> lf-tac-rfl-reducible; <|> -> lf-tac-first-of;
\ assumption -> tactics/assumption.fs's tas-row.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ./assumption.fs
require ./rewrite.fs
require ./rfl.fs

tac-shape-rules lf-tactic: by-rwa[ constant tac-k-rwa
s" rwa" tac-k-rwa lf-tactic-lean!

: trwa-close ( -- ) ['] tas-row ['] lf-tac-rfl-reducible 2 lf-tac-first-of ;
: trwa-core ( i -- ) tac-k-rewrite lf-tac-eval trwa-close ;
: trwa-run ( i -- ) lf-tac-focus swap trwa-core lf-tac-unfocus ;
' trwa-run tac-k-rwa lf-tactic-action!
