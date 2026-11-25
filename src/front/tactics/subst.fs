\ h by-subst, by-subst[ h1 h2 ] and by-subst-vars: Lean's subst h, subst
\ h1 h2 and subst_vars (plan row TB2, piece E, slice E2a; docs/design/
\ TACTIC_PATTERNS.md section 2), ports of Lean 4.35.0's evalSubst and
\ evalSubstVars (src/lean/Lean/Elab/Tactic/BuiltinTactic.lean:500-520)
\ over meta-tactic/subst.fs:
\ - by-subst: in the main goal's context getFVarId of the term
\   (tactic-core.fs's lf-tac-get-fvar: 389 for a term that is no free
\   variable); a let variable (LocalDecl.isLet, which a have is not) Lean
\   unfolds (zeta-delta, :503-513), which is not supported yet (99,
\   revert.fs refuses lets; a have, a let with its value hidden, goes to
\   Meta.subst, whose revert refuses it: 99 too); else Meta.subst (lf-goal-subst: an equation
\   with a free variable on a side, an HEq made one, or a variable whose
\   equation it finds), its goal in the main goal's place;
\ - by-subst[ h1 h2 ]: forEachVar (:494-498), each name in turn resolved
\   in the main goal of that moment (lf-tac-name-fvar: 455 for a name no
\   local has, reported at by-subst['s word), then as by-subst;
\ - by-subst-vars: substVars on the main goal (lf-goal-subst-vars).
\ Lean call list: getFVarId -> lf-tac-get-fvar, lf-tac-name-fvar;
\ getMainGoal, replaceMainGoal [mvarId] -> lf-lift-meta-tactic1
\ (tactic-core.fs); Meta.subst -> lf-goal-subst; substVars ->
\ lf-goal-subst-vars.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/subst.fs

: tsb-not-let ( fvar -- fvar ) dup lf-fvar-let? if lf-tac-unported then ;
: tsb-fvar ( goal fvar -- goal' ) tsb-not-let lf-goal-subst ;
tac-shape-term lf-tactic: by-subst constant tac-k-subst
s" subst" tac-k-subst lf-tactic-lean!
: tsb-tac ( i goal -- goal' ) swap 0 lf-tac-arg lf-tac-get-fvar tsb-fvar ;
: tsb-run ( i -- ) dup ['] tsb-tac lf-lift-meta-tactic1 ;
' tsb-run tac-k-subst lf-tactic-action!

tac-shape-hyps lf-tactic: by-subst[ constant tac-k-subst-list
s" subst" tac-k-subst-list lf-tactic-lean!
: tsb-name-tac ( name goal -- goal' ) swap lf-tac-name-fvar tsb-fvar ;
: tsb-one ( i k -- i ) over swap lf-tac-arg over ['] tsb-name-tac lf-lift-meta-tactic1 ;
: tsb-list ( i -- ) dup lf-tac-args# 0 ?do i tsb-one loop drop ;
' tsb-list tac-k-subst-list lf-tactic-action!

tac-shape-plain lf-tactic: by-subst-vars constant tac-k-subst-vars
s" subst_vars" tac-k-subst-vars lf-tactic-lean!
: tsv-tac ( i goal -- goal' ) nip lf-goal-subst-vars ;
: tsv-run ( i -- ) dup ['] tsv-tac lf-lift-meta-tactic1 ;
' tsv-run tac-k-subst-vars lf-tactic-action!
