\ by-rintro[ p1 p2 ... ]: Lean's rintro p1 p2 ... (plan row TB2, piece E,
\ slice E2a; docs/design/TACTIC_PATTERNS.md section 2; the owner's
\ decision "Case patterns" of 2026-11-22: by-rintro[ a | b c ] is Lean's
\ rintro (a | b) c), Lean 4.35.0's evalRIntro (Elab/Tactic/RCases.lean:
\ 553-558) with no type: RCases.rintro on the main goal in its context,
\ its goals replacing it. The patterns are read by pattern-syntax.fs's
\ tac-shape-rintro (one element or more, each one rintro pattern); the
\ walk is rcases.fs's lf-rintro (each pattern: intro, then rcases' walk
\ on the new hypothesis). Not supported yet: rintro's typed group (x y :
\ T) and its : T, which have no form until slice E5.
\ Lean call list: getMainGoal, replaceMainGoal -> lf-lift-meta-tactic;
\ RCases.rintro -> lf-rintro.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../pattern-syntax.fs
require ../rcases.fs

tac-shape-rintro lf-tactic: by-rintro[ constant tac-k-rintro
s" rintro" tac-k-rintro lf-tactic-lean!
: trt-run ( i -- ) dup ['] lf-rintro lf-lift-meta-tactic ;
' trt-run tac-k-rintro lf-tactic-action!
