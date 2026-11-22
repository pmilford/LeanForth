\ h by-absurd: Batteries' absurd h (plan row TB2, tactic batch 1), the
\ macro of .tools/mathlib/mathlib4/.lake/packages/batteries/Batteries/
\ Tactic/Init.lean:67-73, first | refine @absurd _ _ ?_ h | refine
\ @absurd _ _ h ?_ (tactic-core.fs's lf-tac-first-of):
\ 1. h elaborated against ¬?a, ?a a new natural metavariable of type
\    Prop (elabTermEnsuringType: tactic-core.fs's lf-tac-elab-ensuring):
\    the main goal T assigned absurd.{u} p T ?g h (mkAbsurd, app-builder.fs:
\    u T's level, p ?a instantiated), ?g a new goal p with the main goal's
\    tag (refine's one new goal takes it);
\ 2. else h against ?a: absurd.{u} p T h ?g, the new goal ¬p, p h's type.
\ The second alternative's error is the one reported (Lean's first): a
\ type mismatch (96) when h is no proof. The term is refine's once
\ instantiated: the ?a and ?b of @absurd _ _ assigned by unification, as
\ the pinned comparison checks node for node.
\ Lean call list: first -> lf-tac-first-of (tactic-core.fs); refine's
\ elabTermEnsuringType -> lf-tac-elab-ensuring; mkFreshExprMVar ->
\ lf-mvar-new; mkAbsurd -> lf-mk-absurd; assign -> lf-mvar-assign;
\ replaceMainGoal -> lf-lift-meta-tactic1 (tactic-core.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-term lf-tactic: by-absurd constant tac-k-absurd
s" absurd" tac-k-absurd lf-tactic-lean!

: tab-prop ( -- mvar )   \ ?a : Prop
  0 lf-term-symbolic-sort lf-made! mv-natural lf-mvar-new lf-tac-must ;
\ The step's term; the main goal and its type (tactic-core.fs's tb); a new
\ goal in its place; the main goal assigned absurd.{u} p T hp hnp.
: tab-node ( -- node ) lf-tac-step 0 lf-tac-arg ;
: tab-new ( type -- goal' ) tb tb-goal @ lf-goal-fresh ;
: tab-close ( hp hnp -- )
  tb tb-want @ -rot lf-mk-absurd tb tb-goal @ swap lf-mvar-assign lf-tac-must ;
\ h against ¬?a: elaborated as elabTermForApply does (an identifier with
\ no argument inserted, tactic-core.fs's lf-tac-elab-for-apply), then its
\ type unified with ¬?a (ensureHasType): the elaborator takes no expected
\ pi (elab-term.fs's 133) and inserts no argument of a hypothesis ¬p
\ (136, a binder of Not's value); for a hypothesis, the term Lean's
\ elaboration against ¬?a gives.
: tab-against-not ( node t -- h ) swap lf-tac-elab-for-apply swap lf-tac-ensure-type ;
\ refine @absurd _ _ ?_ h: the new goal ?a; then refine @absurd _ _ h ?_:
\ the new goal ¬?a, ?a h's type.
: tab-neg-tac ( goal -- goal' )
  drop tab-prop dup lf-mk-not tab-node swap tab-against-not swap lf-instantiate! tab-new
  tuck swap tab-close ;
: tab-pos-tac ( goal -- goal' )
  drop tab-prop tab-node over lf-tac-elab-ensuring swap lf-instantiate! lf-mk-not tab-new
  tuck tab-close ;
: tab-neg ( -- ) lf-tac-step ['] tab-neg-tac lf-lift-meta-tactic1 ;
: tab-pos ( -- ) lf-tac-step ['] tab-pos-tac lf-lift-meta-tactic1 ;
: tab-run ( i -- ) drop ['] tab-pos ['] tab-neg 2 lf-tac-first-of ;
' tab-run tac-k-absurd lf-tactic-action!
