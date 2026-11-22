\ by-symm, Lean's symm on the goal (plan row TB2, tactic batch 2b), a port
\ of Lean 4.35.0's evalSymm (src/lean/Lean/Elab/Tactic/Symm.lean:16-24)
\ without a location: liftMetaTactic1 of MVarId.applySymm (meta-tactic/
\ symm.fs's lf-goal-symm: Init's @[symm] lemmas of Eq, Iff, Ne, HEq, And
\ and Or; any other relation not supported yet, 99). The target is Lean's
\ Location.targets #[] true, so its "made no progress" case (a wildcard
\ location) cannot arise; the at h form is plan TB2 batch 3.
\ Lean call list: liftMetaTactic1 -> lf-lift-meta-tactic1; applySymm ->
\ lf-goal-symm.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/symm.fs

tac-shape-plain lf-tactic: by-symm constant tac-k-symm
s" symm" tac-k-symm lf-tactic-lean!

: tsy-run ( i -- ) ['] lf-goal-symm lf-lift-meta-tactic1 ;
' tsy-run tac-k-symm lf-tactic-action!
