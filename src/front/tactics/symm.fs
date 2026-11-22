\ by-symm, Lean's symm (plan row TB2, tactic batch 2b; at: batch 3a), a
\ port of Lean 4.35.0's evalSymm (src/lean/Lean/Elab/Tactic/Symm.lean:
\ 16-24): withLocation (tactic-core.fs's lf-with-location) of each
\ hypothesis named, liftMetaTactic1 of MVarId.applySymmAt h (meta-
\ tactic/symm.fs's lf-goal-symm-at: h replaced by its symmetric form,
\ under its name), then the goal, liftMetaTactic1 of MVarId.applySymm
\ (lf-goal-symm: Init's @[symm] lemmas of Eq, Iff, Ne, HEq, And and Or;
\ any other relation not supported yet, 99). Without at: the location is
\ Lean's Location.targets #[] true, the goal alone. Its "made no
\ progress" case belongs to the wildcard location, at: *, which is not
\ supported yet (99).
\ Lean call list: liftMetaTactic1 -> lf-lift-meta-tactic1; withLocation
\ -> lf-with-location; applySymmAt -> lf-goal-symm-at; applySymm ->
\ lf-goal-symm.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/symm.fs

tac-shape-plain-at lf-tactic: by-symm constant tac-k-symm
s" symm" tac-k-symm lf-tactic-lean!

: tsy-target ( i -- i ) dup ['] lf-goal-symm lf-lift-meta-tactic1 ;
: tsy-local ( fvar goal -- goal' ) swap lf-goal-symm-at ;
: tsy-at-local ( i fvar -- i ) over ['] tsy-local lf-lift-meta-tactic1 ;
: tsy-run ( i -- ) ['] tsy-at-local ['] tsy-target lf-at-location ;
' tsy-run tac-k-symm lf-tactic-action!
