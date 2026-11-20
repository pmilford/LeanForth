\ Goal operations of the tactic library (docs/design/TACTIC_PLUGINS.md
\ 2.4; slices a2-ii and a2-iii): Lean 4.35.0's Meta/Tactic layer, the
\ MVarId functions a tactic calls on its goal. Each word throws on
\ failure (meta-must.fs), as Lean's do.
\ Public words (stack effect; the Lean function, file:line under
\ src/lean/Lean/Meta/Tactic/):
\   lf-goal-not-assigned ( goal -- goal )  MVarId.checkNotAssigned
\       (Util.lean:65); an assigned goal is thrown invalid: no tactic of
\       LeanForth's is handed one (lf-main-goal skips them), so it is a
\       fault, not Lean's message
\   lf-goal-replace-target-eq ( goal new h -- goal' )  MVarId.replaceTargetEq
\       (Replace.lean:21-32): a new synthetic opaque goal of type new with
\       goal's tag in goal's context; goal assigned
\       Eq.mpr.{u} target new (id (target = new) h) goal', target goal's
\       type as stored and u its level
\   lf-goal-head-beta-type ( goal -- goal' )  MVarId.headBetaType
\       (Util.lean:94): goal's type head-beta reduced; Lean sets the
\       declaration's type, LeanForth's metavariables keep theirs, so a
\       type that changes gives a new goal of the same kind, tag and
\       context, goal assigned it (the instantiated proof term is the same
\       node for node); an unchanged type gives goal itself
\   lf-goal-tag-append ( goal parent -- )  appendTag's use in
\       appendParentTag (Util.lean:29): goal's tag made parent ++ the tag
\       with its macro scopes erased (print-names.fs's lf-pp-unhygienic,
\       Lean's eraseMacroScopes), inside a hygienic parent's macro scopes
\       (Name.modifyBase): zero and a._@.M._hyg.3 give zero.a, x._@.M._hyg.1
\       and left give x.left._@.M._hyg.1; an anonymous tag gives parent
\   lf-name-append-tag ( parent tag -- tag' )  appendTag itself, on names:
\       the tag lf-goal-tag-append gives (an anonymous parent gives tag
\       with its macro scopes erased; mkElimApp's alternatives' tags)
\   lf-name-suffix-of? ( s n -- flag )  Name.isSuffixOf (Init/Meta/
\       Defs.lean): s's components the last ones of n (zero of succ.zero;
\       the anonymous name of any name)
\   lf-name-prefix-of? ( p n -- flag )  Name.isPrefixOf: p is n or one of
\       its prefixes (succ of succ.zero; su of su.x, not of succ: a
\       component compares whole)
\       (findTag?'s name tests, tactics/case.fs; general Name functions,
\       whose home is core/name-equal.fs once the [kernel] gate's next
\       batch takes them, plan 9.4.8l B)
\   lf-goal-intro-n ( goal names kinds n xs -- goal' )  MVarId.introN
\       (Intro.lean:15 introNImp, :102 mkAuxNameImp, n binders): goal's
\       type as stored, else instantiated, else through whnfCore, gives a
\       pi n times; each binder becomes a hypothesis, a new free variable
\       of its domain (head-beta reduced), stored in the caller's cell at
\       xs, its local pushed on the goal's context, named as the caller's
\       cell at names says (0, Lean's _: the binder's own name, a when it
\       has none, made inaccessible), of the kind at kinds (kinds 0: the
\       node's, which must be explicit); goal' is a new synthetic opaque
\       goal of the body (the variables put in, head-beta reduced) with
\       goal's tag, and goal is assigned fun xs => ?n xs (telescope.fs's
\       lf-mk-lambda-fvars). No pi is Lean's introN error 94 with the goal,
\       or 93 where whnf's delta might still make one (infer.fs's
\       lf-whnf-firm?); not supported yet (99): a let, a binder of no
\       known kind (kinds 0), an implicit or instance one (a local
\       instance is plan FE3). The current context is put back.
\   lf-goal-checked-assign ( goal e -- )  MVarId.checkedAssign
\       (ExprDefEq.lean:1341) as closeMainGoal calls it: a free variable
\       of e outside goal's context, or an assignment refused, is error 98
\       with e, Lean's occurs-check line and the goal; an unassigned
\       metavariable in e answers 93 (Lean's checkAssignment would
\       restrict it, not ported)
\   lf-goal-refl ( goal -- )  the rfl macro on an equation (Init/
\       Tactics.lean:477-482): eq_refl, MVarId.refl (Refl.lean:25) under
\       withAssignableSyntheticOpaque: goal's type through whnf at the
\       transparency in force, instantiated (getType'), must be Eq applied
\       to three arguments (any other goal: 93, exact Iff.rfl, exact
\       HEq.rfl and @[refl] lemmas are plan FE5); its sides instantiated
\       and definitionally equal close goal with @Eq.refl.{u} α lhs (Eq's
\       own level and type); else applyRfl (Rfl.lean:67-97): the type
\       instantiated through whnfR, a relation of two arguments or more
\       (else 93), its last two compared by approxDefEq
\       isDefEqGuarded (meta-must.fs's lf-defeq-approx!): unequal is error
\       97 with Lean's text (the sides, the goal); equal sides of Eq close
\       goal as above, of another relation 93 (@[refl] lemmas)
\ Errors are thrown as authoring errors at the step running
\ (tactic-run.fs's lf-tac-stop and lf-tac-fail), Meta failures as
\ outcomes (meta-must.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mti-frames and mrf-frames (introN's and refl's frames, one per
\ call open, meta-must.fs's lf-with-record, in the checker context, ADR
\ 0009); no other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../core/let-terms.fs
require ../../core/names.fs
require ../../core/name-equal.fs
require ../../present/print-names.fs
require ../../author/errors.fs
require ../../author/declarations.fs
require ../mvars.fs
require ../lctx-views.fs
require ../goals.fs
require ../instantiate.fs
require ../meta-config.fs
require ../whnf.fs
require ../infer.fs
require ../defeq.fs
require ../term-eqv.fs
require ../term-find.fs
require ../tactic-run.fs
require ../tactic-msg.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs

\ ---- checkNotAssigned.
: lf-goal-not-assigned ( goal -- goal )
  dup lf-goal-assigned? if outcome-invalid lf-must then ;

\ ---- replaceTargetEq: goal' new in goal's context with goal's tag, goal
\ assigned Eq.mpr.{u} target new (mkExpectedPropHint h (mkEq target new)) goal'.
: mtg-goal-new ( type goal -- goal' )
  dup lf-goal-tag swap lf-goal-view lf-goal-new lf-must ;
: mtg-fresh ( goal new -- goal goal' ) over lf-goal-not-assigned mtg-goal-new ;
: mtg-eq ( goal goal' -- eq ) lf-goal-type swap lf-goal-type swap lf-mk-eq ;
: mtg-hint ( goal goal' h -- goal goal' h' )
  >r 2dup mtg-eq r> swap lf-mk-expected-prop-hint ;
: mtg-mpr ( target -- f )   \ Eq.mpr.{u} target, u target's level
  s" Eq.mpr" lfa-intern over lf-level! 1 lf-mk-const-id swap lf-mk-app ;
: mtg-value ( goal goal' h' -- goal goal' value )
  >r 2dup lf-goal-type swap lf-goal-type mtg-mpr swap lf-mk-app r> lf-mk-app
  over lf-mk-app ;
: mtg-assign ( goal goal' value -- goal' ) rot swap lf-mvar-assign lf-must ;
: lf-goal-replace-target-eq ( goal new h -- goal' )
  >r mtg-fresh r> mtg-hint mtg-value mtg-assign ;

\ ---- headBetaType.
: mtg-tag-from ( goal' goal -- goal' ) lf-goal-tag over swap lf-mvar-tag! lf-must ;
: mtg-like ( type goal -- goal' )   \ a new metavariable as goal, of type
  tuck dup lf-goal-kind swap lf-goal-view lf-mvar-new-at lf-must swap mtg-tag-from ;
: lf-goal-head-beta-type ( goal -- goal' )
  dup lf-goal-type dup lf-meta-head-beta lf-must tuck = if drop exit then
  over mtg-like tuck lf-mvar-assign lf-must ;

\ ---- appendTag (Util.lean:29): parent.modifyBase (· ++ tag's macro
\ scopes erased); modifyBase (Init/Meta/Defs.lean:308) appends to the
\ part before a hygienic parent's macro scopes and puts them back after.
: mtg-graft ( name t base -- name' ) lf-name-graft 0= if outcome-full lf-must then ;
: mtg-plus ( tag base -- base' ) swap lf-pp-unhygienic dup lf-name-depth rot mtg-graft ;
: mtg-scopes ( parent -- parent n )   \ the macro scopes' parts
  dup lf-name-depth over lf-pp-unhygienic lf-name-depth - ;
: lf-name-append-tag ( parent tag -- tag' )
  over lf-pp-unhygienic mtg-plus >r mtg-scopes r> mtg-graft ;
: lf-goal-tag-append ( goal parent -- )
  over lf-goal-tag lf-name-append-tag lf-mvar-tag! lf-must ;

\ ---- Name.isSuffixOf and Name.isPrefixOf, component by component
\ (core/name-equal.fs's lf-name-part= and lf-name-same?).
: lf-name-suffix-of? ( s n -- flag )
  begin over while 2dup lf-name-part= 0= if 2drop false exit then lf-name-prefixes
  repeat 2drop true ;
: lf-name-prefix-of? ( p n -- flag )
  begin 2dup lf-name-same? 0= while dup 0= if 2drop false exit then lf-name-prefix@
  repeat 2drop true ;
\ An assignment that must be made (MVarId.assign).
: mtg-set ( e goal -- ) swap lf-mvar-assign lf-must ;

\ ---- introN (Intro.lean:15 introNImp, :102 mkAuxNameImp): a frame per
\ call (meta-must.fs's lf-with-record), in the goal's context.
begin-structure /mti
  field: mti-goal        \ the goal
  field: mti-type        \ the rest of its type
  field: mti-kinds       \ the caller's n kinds, or 0: the node's
  field: mti-names       \ the caller's n names (0: the binder's own)
  field: mti-xs          \ the caller's n cells for the free variables
  field: mti-n           \ and their count
  field: mti-i           \ binders introduced
end-structure
/mti context-slab: mti-frames
: mti ( -- frame ) mti-frames slab-last ;
: mti-fill ( goal names kinds n xs -- goal )
  mti mti-xs ! mti mti-n ! mti mti-kinds ! mti mti-names ! dup mti mti-goal ! ;
\ The binder: the type as it is, else instantiated, else put through
\ whnfCore; no pi is Lean's introN error (94), or 93 where whnf's delta
\ might still make one (infer.fs's lf-whnf-firm?).
: mti-binding? ( t -- flag ) dup lf-term-pi? swap lf-let? or ;
: mti-none ( t -- )
  lf-whnf-firm? lf-must 0= if outcome-unsupported lf-must then
  mti mti-goal @ ['] lf-tac-goal-of. lf-tac-detail lfa-e-tac-no-intro lf-tac-stop ;
: mti-reduced ( t -- pi ) lf-whnf-core lf-must dup lf-term-pi? if exit then dup mti-none ;
: mti-binder ( -- pi )
  mti mti-type @ dup mti-binding? if exit then lf-instantiate!
  dup mti-binding? if exit then mti-reduced ;
\ Not supported yet (99): a let; with no kinds given, a binder not known
\ explicit (the node's record, which a shared node may hide).
: mti-explicit? ( pi -- flag )
  lf-binder-of if nip lf-binder-default = else false then ;
: mti-plain? ( pi -- flag )
  dup lf-let? if drop false exit then
  mti mti-kinds @ if drop true else mti-explicit? then ;
\ The i-th of the caller's n cells at addr; the name given, else the
\ binder's own (a when it has none) made inaccessible; the kind given,
\ else explicit.
: mti-at ( addr -- addr' ) mti mti-i @ cells + ;
: mti-own ( pi -- name ) lf-binder-name ?dup 0= if s" a" lfa-intern then ;
: mti-named ( pi -- name flags )
  mti mti-names @ mti-at @ ?dup if nip 0 exit then mti-own lf-local-inaccessible ;
: mti-kind ( -- kind )
  mti mti-kinds @ ?dup if mti-at @ else lf-binder-default then ;
\ One binder: its free variable kept, its local pushed on the current view.
: mti-dom ( pi -- dom ) lf-term-first@ lf-meta-head-beta lf-must ;
: mti-local ( pi -- fvar )
  dup mti-dom swap mti-named mti-kind or lf-local-decl-new lf-mctx-view! ;
: mti-x! ( fvar -- ) mti mti-xs @ mti-at ! 1 mti mti-i +! ;
: mti-body ( pi fvar -- t )
  swap lf-term-second@ swap lf-meta-instantiate1 lf-must lf-meta-head-beta lf-must ;
: mti-step ( -- )
  mti-binder dup mti-plain? 0= if lfa-e-tac-form lf-tac-fail then
  dup mti-local dup mti-x! mti-body mti mti-type ! ;
\ The new goal of the body in the new context, the goal assigned
\ fun xs => ?n xs (mkLambdaFVars, telescope.fs).
: mti-new ( -- goal' )
  mti mti-type @ mti mti-goal @ lf-goal-tag lf-mctx-view lf-goal-new lf-must ;
: mti-close ( -- goal' )
  mti-new dup mti mti-xs @ mti mti-n @ lf-mk-lambda-fvars mti mti-goal @ mtg-set ;
: mti-start ( -- ) mti mti-goal @ lf-goal-not-assigned lf-goal-type mti mti-type ! ;
: mti-run ( -- goal' ) mti-start mti mti-n @ 0 ?do mti-step loop mti-close ;
: mti-framed ( goal names kinds n xs -- goal' ) mti-fill ['] mti-run lf-with-goal ;
: lf-goal-intro-n ( goal names kinds n xs -- goal' )
  mti-frames ['] mti-framed lf-with-record ;

\ ---- checkedAssign (ExprDefEq.lean:1341) as closeMainGoal calls it.
: mtg-outside? ( view leaf -- view flag )
  dup lf-term-tag@ lf-tag-fvar = if over swap lf-view-has? 0= else drop false then ;
: mtg-occurs. ( x -- outcome )
  drop s\" \nthis is often due to an occurs-check failure" lf-pp-emit outcome-ok ;
: mtg-assign. ( goal e -- outcome ) 0 swap ['] mtg-occurs. swap lf-tac-framed-with. ;
: mtg-unassignable ( goal e -- )
  2 ['] mtg-assign. lf-tac-detail-n lfa-e-tac-assign lf-tac-stop ;
: mtg-holes-free ( e -- e ) dup lf-has-open-mvar? if outcome-unsupported lf-must then ;
: mtg-in-scope ( goal e -- goal e )
  2dup swap lf-goal-view ['] mtg-outside? lf-term-holds-with? lf-must
  if 2dup mtg-unassignable then ;
: mtg-assigned ( goal e -- )
  2dup lf-mvar-assign dup outcome-invalid = if drop mtg-unassignable exit then
  lf-must 2drop ;
: lf-goal-checked-assign ( goal e -- ) mtg-holes-free mtg-in-scope mtg-assigned ;

\ ---- The rfl macro on an equation (Init/Tactics.lean:477-482): its
\ alternatives exact Iff.rfl and exact HEq.rfl fail on a goal whose type
\ is Eq after whnf (Iff, HEq and Eq: three inductive types, nothing
\ unfolds), so eq_refl decides (MVarId.refl, Refl.lean:25, under
\ withAssignableSyntheticOpaque, BuiltinTactic.lean:320), then on its
\ failure applyRfl (Rfl.lean:67-97), whose error is the one Lean shows.
\ A frame per call (lf-with-record).
begin-structure /mrf
  field: mrf-goal        \ the goal
  field: mrf-eq          \ its type: getType' (eq_refl), then whnfR (applyRfl)
  2 cells +field mrf-sides  \ that type's sides, instantiated: lhs rhs (2! and 2@)
end-structure
/mrf context-slab: mrf-frames
: mrf ( -- frame ) mrf-frames slab-last ;
\ getType' (Util.lean:80): whnf at the transparency in force, instantiated.
: mtg-eq-of ( goal -- t ) lf-goal-type lf-whnf! lf-instantiate! ;
: mtg-is-eq ( t -- t ) dup lf-eq? if 2drop drop exit then outcome-unsupported lf-must ;
: mtg-inst2 ( a b -- a' b' ) lf-instantiate! swap lf-instantiate! swap ;   \ b first
: mrf-eq! ( t -- ) dup mrf mrf-eq ! lf-eq? drop mtg-inst2 mrf mrf-sides 2! drop ;
\ eq_refl's isDefEq: at the transparency the step runs at (default;
\ reducible under by-rw[ 's with_reducible), the goals assignable.
: mrf-sides-defeq ( -- flag outcome ) mrf mrf-sides 2@ lf-defeq-mode lf-defeq-elab-at ;
: mrf-equal? ( -- flag ) ['] mrf-sides-defeq lf-with-assignable-opaque lf-must ;
\ applyRfl's relation (Rfl.lean:69-86): t, the type instantiated through
\ whnfR, applied to two arguments or more, its last two the sides (fewer:
\ Lean's "binary relation" error, not ported, 93; HEq, whose HEq.refl
\ path is not ported either, never comes here: its whnf is no Eq);
\ approxDefEq isDefEqGuarded of the sides.
: mrf-binary? ( t -- flag )
  dup lf-term-app? if lf-term-first@ lf-term-app? else drop false then ;
: mrf-rel ( t -- t ) dup mrf-binary? 0= if outcome-unsupported lf-must then ;
: mrf-rel-sides ( t -- lhs rhs ) dup lf-term-first@ lf-term-second@ swap lf-term-second@ ;
: mrf-whnf-r ( -- )
  mrf mrf-goal @ lf-goal-type lf-instantiate! lf-whnf-r! mrf-rel
  dup mrf mrf-eq ! mrf-rel-sides mrf mrf-sides 2! ;
: mrf-approx? ( -- flag ) mrf mrf-sides 2@ lf-defeq-approx! ;
: mrf-lhs ( -- lhs ) mrf mrf-sides 2@ drop ;
\ @Eq.refl.{u} α lhs, u and α those of the goal's Eq (mkConst Eq.refl us,
\ mkApp2).
: mtg-refl-const ( t -- f )
  lf-meta-head s" Eq.refl" lfa-intern swap lf-const-levels lf-mk-const-id ;
: mtg-alpha ( t -- α ) lf-eq? drop 2drop ;
: mrf-term ( -- e )
  mrf mrf-eq @ dup mtg-refl-const swap mtg-alpha lf-mk-app mrf-lhs lf-mk-app ;
: mrf-closed ( -- ) mrf-term mrf mrf-goal @ mtg-set ;
\ applyRfl's message: the two sides, then the goal (addPPExplicitToExposeDiff
\ not ported).
: mtg-rhs. ( rhs -- outcome )
  s\" \nis not definitionally equal to the right-hand side\n" lf-pp-emit
  lf-tac-indented. ;
: mrf-rfl. ( x -- outcome )
  drop mrf mrf-goal @ mrf mrf-sides 2@ swap ['] mtg-rhs. swap lf-tac-framed-with. ;
: mrf-unequal ( -- ) 0 ['] mrf-rfl. lf-tac-detail lfa-e-tac-rfl lf-tac-stop ;
\ Equal sides of Eq close the goal; of another relation, Lean's @[refl]
\ lemmas would (plan FE5): 93.
: mrf-eq-closed ( -- ) mrf mrf-eq @ mtg-is-eq drop mrf-closed ;
: mrf-apply-rfl ( -- ) mrf-whnf-r mrf-approx? 0= if mrf-unequal then mrf-eq-closed ;
: mrf-run ( -- )
  mrf mrf-goal @ mtg-eq-of mtg-is-eq mrf-eq!
  mrf-equal? if mrf-closed else mrf-apply-rfl then ;
: mrf-framed ( goal -- ) mrf mrf-goal ! mrf-run ;
: lf-goal-refl ( goal -- ) lf-goal-not-assigned mrf-frames ['] mrf-framed lf-with-record ;
base !   \ the BASE this file was loaded with
