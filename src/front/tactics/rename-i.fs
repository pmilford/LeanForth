\ by-rename-i[ a b ]: Lean's rename_i a b (plan row TB2, tactic batch 3b),
\ a port of Lean 4.35.0's evalRenameInaccessibles (src/lean/Lean/Elab/
\ Tactic/BuiltinTactic.lean:627-629): renameInaccessibles of the main
\ goal with the names (meta-tactic/rename.fs's
\ lf-goal-rename-inaccessibles: from the newest, each inaccessible or
\ shadowed hypothesis takes the last name not taken yet, _ keeping one as
\ it is; 211 when names are left), the new goal in the main goal's place.
\ The names, read up to ] (one at least, as Lean's
\ parser wants: 460), are hypotheses later steps may name.
\ Lean call list: getMainGoal, replaceMainGoal [g] -> lf-lift-meta-tactic1
\ (tactic-core.fs); the binder identifiers -> lf-tac-arg-names;
\ renameInaccessibles -> lf-goal-rename-inaccessibles.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/rename.fs

tac-shape-binders+ lf-tactic: by-rename-i[ constant tac-k-rename-i
s" rename_i" tac-k-rename-i lf-tactic-lean!
: trz-tac ( i goal -- goal' ) swap lf-tac-arg-names lf-goal-rename-inaccessibles ;
: trz-run ( i -- ) dup ['] trz-tac lf-lift-meta-tactic1 ;
' trz-run tac-k-rename-i lf-tactic-action!
