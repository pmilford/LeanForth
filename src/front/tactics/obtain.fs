\ e by-obtain[ pat ] and e by-rcases[ pat ]: Lean's obtain pat := e and
\ rcases e with pat (plan row TB2, piece E, slice E1; docs/design/
\ TACTIC_PATTERNS.md section 2; the owner's decision "Case patterns" of
\ 2026-11-22: both names, the value first), Lean 4.35.0's evalObtain
\ and evalRCases (Elab/Tactic/RCases.lean:520-552), each RCases.rcases
\ with one target on the main goal, its goals replacing it
\ (replaceMainGoal). The pattern is read by pattern-syntax.fs's
\ tac-shape-pattern (one element: Lean's rcasesPatMed for obtain, a
\ top-level group for rcases, which is the pattern itself); the walk is
\ rcases.fs's lf-rcases.
\ Lean call list: getMainGoal, replaceMainGoal -> lf-lift-meta-tactic;
\ RCases.rcases -> lf-rcases.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../pattern-syntax.fs
require ../rcases.fs

tac-shape-pattern lf-tactic: by-obtain[ constant tac-k-obtain
s" obtain" tac-k-obtain lf-tactic-lean!
tac-shape-pattern lf-tactic: by-rcases[ constant tac-k-rcases
s" rcases" tac-k-rcases lf-tactic-lean!
: tob-run ( i -- ) dup ['] lf-rcases lf-lift-meta-tactic ;
' tob-run tac-k-obtain lf-tactic-action!
' tob-run tac-k-rcases lf-tactic-action!
