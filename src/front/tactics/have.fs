\ The have family (plan row TB2, tactic batch 2; the owner's spellings of
\ docs/project/OWNER_DECISIONS.md, "Tactics at speed"), ports of Lean
\ 4.35.0 (src/lean/) and of Mathlib's valueless have:
\ - T e by-have: h  Lean's have h : T := e, the macro refine_lift have h :
\   T := e; ?_ (Init/Tactics.lean:942, 882): in the main goal's context T
\   by Term.elabType under withSynthesize (postpone := .partial), e by
\   elabTermEnsuringType T (elabLetDeclAux, Elab/Binders.lean:745-800),
\   then the main goal assigned have h : T := e; ?_ (a nondependent let,
\   elabHaveDecl :942) and ?_ in its place (meta-tactic/assert.fs's
\   lf-goal-have: refine's one new goal, with the main goal's tag).
\ - e by-have  Lean's have := e: the same with no type (Lean's hole, which
\   e's type fills: e elaborated with no expected type, T its type) and
\   the name this, a hypothesis later steps may name (the reader gives it).
\ - T e by-let: x  Lean's let x : T := e (Init/Tactics.lean:980;
\   elabLetDecl, Binders.lean:939): as by-have: with a let whose value
\   later steps see (unfolded by whnf, shown as x : T := e).
\ - T e by-suffices: h  Lean's suffices h : T from e (Init/Tactics.lean:
\   951, refine_lift suffices h : T from e; ?_, which expandSuffices,
\   Elab/BuiltinNotation.lean:149-151, makes have h : T := ?_; e): T as
\   by-have:'s, ?_ a new goal of T with the main goal's tag (refine's one
\   new goal), e elaborated against the main goal's type in the context
\   with h, the main goal assigned have h : T := ?_; e and ?_ in its place.
\   e is read before the word, so it can name h only by a name that is a
\   variable or hypothesis already (resolved, as Lean's, to the newest
\   local of the name: the new h).
\ - T by-have-goal: h  Mathlib's have h : T (Mathlib/Tactic/Have.lean:
\   71-96, haveLetCore with keepTerm false): T by Term.elabType and
\   synthesizeSyntheticMVars (postpone := .no); p a new synthetic opaque
\   goal of T tagged h; MVarId.assert h T p, then intro1P (h's binder
\   name kept); the goals p, then the main one with h (replaceMainGoal
\   [goal1, goal2]).
\ - T by-have-by: h tacs by-end  Lean's have h : T := by tacs (plan row
\   TB2, blocks slice 1; the macro refine_lift have h : T := by tacs; ?_,
\   whose by block Term.runTactic runs, Elab/SyntheticMVars.lean:474-537):
\   T as by-have:'s; p a new goal of T in the main goal's context,
\   untagged (by's metavariable); the main goal assigned have h : T := p;
\   ?_ and ?_ in its place; then the block's tactics run on p alone, in a
\   fresh Tactic.run (recover true), and at by-end no goal may be left
\   (89 at by-have-by:, Lean's at by, always reported: final), the goals
\   after it the main one with h and the others. h is not in p's context
\   (a name h inside the block is the one the context has, as Lean's);
\   names given inside the block go at by-end, h stays.
\ Errors are the elaborator's (130 type expected, 96 type mismatch, with
\ Lean's text). Not supported yet: _ for the name (99; Lean's
\ inaccessible hypothesis), a type or term that leaves a metavariable
\ open (93: Lean's natural holes, which refine refuses, and Mathlib's
\ type holes; a written _ is plan TB2 batch 3), a type or value binders
\ (have h (x : A) : T := e) and patterns.
\ Lean call list: withMainContext, getMainGoal, replaceMainGoal ->
\ lf-lift-meta-tactic, lf-lift-meta-tactic1 (tactic-core.fs);
\ Term.elabType -> lf-tac-elab-type; elabTermEnsuringType ->
\ lf-tac-elab-ensuring; Tactic.elabTerm -> lf-tac-elab-term; inferType ->
\ lf-infer!; refine's new goals -> lf-open-mvar-free; withLetDecl and
\ mkLetFVars -> lf-goal-have, lf-goal-let, lf-goal-have-with
\ (meta-tactic/assert.fs); mkFreshExprSyntheticOpaqueMVar -> lf-goal-fresh,
\ lf-goal-new; MVarId.assert -> lf-goal-assert; intro1P -> lf-goal-intro-n.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (intro1P's name and free variable in the step
\ record's cells, tactic-core.fs's tb).

require ../tactic-api.fs
require ../meta-tactic/assert.fs

tac-shape-decl lf-tactic: by-have: constant tac-k-have
s" have" tac-k-have lf-tactic-lean!
1 tac-shape-term-this lf-tactic: by-have constant tac-k-have-this
s" have" tac-k-have-this lf-tactic-lean!
tac-shape-decl lf-tactic: by-let: constant tac-k-let
s" let" tac-k-let lf-tactic-lean!
tac-shape-decl lf-tactic: by-suffices: constant tac-k-suffices
s" suffices" tac-k-suffices lf-tactic-lean!
1 1 tac-shape-term-names lf-tactic: by-have-goal: constant tac-k-have-goal
s" have" tac-k-have-goal lf-tactic-lean!
1 1 tac-block-cuts tac-shape-block lf-tactic: by-have-by: constant tac-k-have-by
s" have" tac-k-have-by lf-tactic-lean!
lf-mode-nested tac-k-have-by lf-tactic-mode!

\ ---- The declaration: its name (_ not supported yet), type and value.
: thv-name ( i k -- name ) lf-tac-arg dup 0= if lf-tac-unported then ;
\ A term elaborated: no metavariable left open (93); a name the context
\ lacks (cleared) is refused as it is elaborated (elab-term.fs's et-var
\ and et-hyp, 76; Lean's unknown identifier).
\ Step i's name, its argument k, below i.
: thv-named ( i goal k -- goal name i ) rot tuck swap thv-name swap ;
: thv-type ( i -- T ) 0 lf-tac-arg lf-tac-elab-type lf-open-mvar-free ;
: thv-ensuring ( node T -- e ) lf-tac-elab-ensuring lf-open-mvar-free ;
: thv-value ( i T -- e ) swap 1 lf-tac-arg swap thv-ensuring ;
: thv-decl ( i goal -- goal name T e ) 2 thv-named dup thv-type tuck thv-value ;
: thv-have ( i goal -- goal' ) thv-decl lf-goal-have ;
: thv-run ( i -- ) dup ['] thv-have lf-lift-meta-tactic1 ;
' thv-run tac-k-have lf-tactic-action!

\ ---- have := e: no type; the name this.
: thv-untyped ( i -- e ) 0 lf-tac-elab-arg lf-open-mvar-free ;
: thv-this ( i goal -- goal' )
  1 thv-named thv-untyped dup lf-infer! swap lf-goal-have ;
: thv-this-run ( i -- ) dup ['] thv-this lf-lift-meta-tactic1 ;
' thv-this-run tac-k-have-this lf-tactic-action!

\ ---- let.
: tlt-let ( i goal -- goal' ) thv-decl lf-goal-let ;
: tlt-run ( i -- ) dup ['] tlt-let lf-lift-meta-tactic1 ;
' tlt-run tac-k-let lf-tactic-action!

\ ---- suffices: have h : T := ?_; e, ?_ (v) in the main goal's place.
: tsf-decl ( i goal -- goal name T v )
  over thv-type 2dup swap lf-goal-fresh 2>r 2 thv-named drop 2r> ;
: tsf-body ( goal -- e ) lf-goal-target drop lf-tac-step 1 lf-tac-arg swap thv-ensuring ;
: tsf-suffices ( i goal -- goal' )
  tsf-decl dup >r ['] tsf-body lf-goal-have-with drop r> ;
: tsf-run ( i -- ) dup ['] tsf-suffices lf-lift-meta-tactic1 ;
' tsf-run tac-k-suffices lf-tactic-action!

\ ---- Mathlib's have h : T: the goals p (tagged h) and the main one with h.
: thg-type ( i -- T )
  0 lf-tac-arg ['] lf-tac-elab-type lf-tac-with-synth lf-instantiate! lf-open-mvar-free ;
: thg-proof ( goal name T -- p ) swap rot lf-goal-view lf-goal-new lf-must ;
: thg-assert ( goal name T -- p goal' )
  2>r dup 2r@ thg-proof tuck 2r> rot lf-goal-assert ;
: thg-intro ( goal' name -- goal2 )
  tb tb-name ! tb tb-name 0 1 tb tb-x lf-goal-intro-n ;
: thg-tac ( i goal -- goals )
  1 thv-named over >r thg-type thg-assert r> thg-intro lf-goals2 ;
: thg-run ( i -- ) dup ['] thg-tac lf-lift-meta-tactic ;
' thg-run tac-k-have-goal lf-tactic-action!

\ ---- have h : T := by tacs: p, T's proof, a new goal in the main goal's
\ context, untagged (the metavariable of Lean's by); the main goal
\ assigned have h : T := p; ?_, ?_ in its place; then the block runs on
\ p alone, the goals after it outside (Term.runTactic: the runner's mode
\ lf-mode-nested).
\ (p in the main goal's context, tb's, with no tag; lf-goal-have takes p,
\ which the block needs after it.)
: thb-proof ( T -- T p ) dup 0 tb tb-view @ lf-goal-new lf-must ;
: thb-decl ( i goal -- goal name T p ) 1 thv-named thv-type thb-proof ;
: thb-tac ( i goal -- p goals ) thb-decl dup >r lf-goal-have r> swap lf-goals1 ;
: thb-run ( i -- )
  dup dup ['] thb-tac lf-lift-meta-tactic lf-goals swap lf-tac-only lf-tac-block ;
' thb-run tac-k-have-by lf-tactic-action!
