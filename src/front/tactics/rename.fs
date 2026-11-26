\ T by-rename: h: Lean's rename T => h (plan row TB2, small tactics 1), a
\ port of Lean 4.35.0's evalRename (src/lean/Lean/Elab/Tactic/
\ ElabTerm.lean:365-383): in the main goal's context, without modifying
\ the state (a save put back however the search ends), one metavariable
\ depth deeper and without recover, T elaborated with postponing
\ allowed, then the newest local that is no implementation detail and
\ whose type is defeq T (findDeclRevM?: meta-tactic/assumption.fs's
\ lf-local-index-with-type?, isDefEq type localDecl.type; T's holes may
\ be assigned there, the goal's metavariables not); none is error 482,
\ Lean's "Failed to find a hypothesis with type" and T. Then
\ MVarId.rename of the main goal (goals.fs's lf-goal-rename: a new goal
\ of the same type and tag whose context names that local h, the old
\ goal assigned it) in its place. h is a name (_ is not supported, 99:
\ Lean's parser wants an identifier there).
\ Lean call list: withMainContext, getMainGoal, replaceMainGoal [g] ->
\ lf-lift-meta-tactic1 (tactic-core.fs); withoutModifyingState ->
\ lf-tac-without-modifying (tactic-run.fs); h -> lf-tac-name
\ (tactic-core.fs); withNewMCtxDepth ->
\ lf-with-new-depth (meta-must.fs); withoutRecover -> lf-tac-no-recover;
\ elabTerm stx none true -> lf-tac-elab-term; findDeclRevM? with
\ isDefEq -> lf-local-index-with-type?; MVarId.rename -> lf-goal-rename.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/assumption.fs

1 1 tac-shape-term-names lf-tactic: by-rename: constant tac-k-rename
s" rename" tac-k-rename lf-tactic-lean!

482 lfa-lean s" Failed to find a hypothesis with type" lfa-code: lfa-e-rename

\ ---- The local T names (none: 482 with T indented).
: trn-none ( type -- ) ['] lf-tac-indented. lf-tac-detail lfa-e-rename lf-tac-stop ;
: trn-find ( node -- fvar )
  -1 true lf-tac-elab-term dup lf-local-index-with-type? if nip lf-mctx-fvar exit then
  trn-none ;
: trn-deep ( node -- fvar ) ['] trn-find lf-with-new-depth ;
: trn-quiet ( node -- fvar ) ['] trn-deep lf-tac-no-recover ;
\ withoutModifyingState: the state put back after, whatever the search did.
: trn-search ( node -- fvar ) ['] trn-quiet lf-tac-without-modifying ;

\ ---- MVarId.rename of the main goal.
: trn-tac ( i goal -- goal' )
  over 1 lf-tac-name >r swap 0 lf-tac-arg trn-search r> lf-goal-rename lf-must ;
: trn-run ( i -- ) dup ['] trn-tac lf-lift-meta-tactic1 ;
' trn-run tac-k-rename lf-tactic-action!
