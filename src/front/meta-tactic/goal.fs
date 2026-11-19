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
\       (findTag?'s name tests, tactic-case.fs; general Name functions,
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
\   lf-goal-refl ( goal -- )  MVarId.refl (Refl.lean:25) as applyRfl's Eq
\       path reaches it (Rfl.lean:67-97): goal's type, instantiated and
\       put through whnfCore, must be Eq applied to three arguments (any
\       other goal: 93, Lean's @[refl] lemmas are plan FE5); its sides,
\       instantiated, definitionally equal at the transparency in force
\       (the elaborator's flags) close goal with @Eq.refl.{u} α lhs (Eq's
\       own level and type); unequal is error 97 with Lean's text (the
\       sides, the goal), or 93 with a metavariable left in a side
\       (apply_rfl's approximations might still unify them)
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
\ ---- introN (Intro.lean:15 introNImp, :102 mkAuxNameImp): a frame per
\ call (meta-must.fs's lf-with-record), in the goal's context.
begin-structure /mti
  field: mti-goal        \ the goal
  field: mti-type        \ the rest of its type
  field: mti-names       \ the caller's n names (0: the binder's own)
  field: mti-kinds       \ the caller's n kinds, or 0: the node's
  field: mti-xs          \ the caller's n cells for the free variables
  field: mti-n
  field: mti-i           \ binders introduced
end-structure
/mti context-slab: mti-frames
: mti ( -- frame ) mti-frames slab-last ;
: mti-fill ( goal names kinds n xs frame -- )
  tuck mti-xs ! tuck mti-n ! tuck mti-kinds ! tuck mti-names ! mti-goal ! ;
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
  mti-new dup mti mti-xs @ mti mti-n @ lf-mk-lambda-fvars
  mti mti-goal @ swap lf-mvar-assign lf-must ;
: mti-start ( -- ) mti mti-goal @ lf-goal-not-assigned lf-goal-type mti mti-type ! ;
: mti-run ( -- goal' ) mti-start mti mti-n @ 0 ?do mti-step loop mti-close ;
: mti-framed ( goal names kinds n xs frame -- goal' )
  mti-fill mti mti-goal @ ['] mti-run lf-with-goal ;
: lf-goal-intro-n ( goal names kinds n xs -- goal' )
  mti-frames ['] mti-framed lf-with-record ;

\ ---- checkedAssign (ExprDefEq.lean:1341) as closeMainGoal calls it.
: mtg-open? ( t -- flag ) ['] lf-mvar-open? lf-term-holds? lf-must ;
: mtg-seen? ( view fvar -- view flag ) over swap lf-view-find dup if nip then ;
: mtg-outside? ( view leaf -- view flag )
  dup lf-term-tag@ lf-tag-fvar = if mtg-seen? 0= else drop false then ;
: mtg-occurs. ( x -- outcome )
  drop s\" \nthis is often due to an occurs-check failure" lf-pp-emit outcome-ok ;
: mtg-assign. ( goal e -- outcome ) 0 swap ['] mtg-occurs. swap lf-tac-framed-with. ;
: mtg-unassignable ( goal e -- )
  2 ['] mtg-assign. lf-tac-detail-n lfa-e-tac-assign lf-tac-stop ;
: mtg-holes-free ( e -- e ) dup mtg-open? if outcome-unsupported lf-must then ;
: mtg-in-scope ( goal e -- goal e )
  2dup swap lf-goal-view ['] mtg-outside? lf-term-holds-with? lf-must
  if 2dup mtg-unassignable then ;
: mtg-assigned ( goal e -- )
  2dup lf-mvar-assign dup outcome-invalid = if drop mtg-unassignable exit then
  lf-must 2drop ;
: lf-goal-checked-assign ( goal e -- ) mtg-holes-free mtg-in-scope mtg-assigned ;

\ ---- MVarId.refl (Refl.lean:25) by applyRfl's Eq path (Rfl.lean:67-97):
\ a frame per call (lf-with-record).
begin-structure /mrf
  field: mrf-goal        \ the goal
  field: mrf-eq          \ its type, instantiated, through whnfCore
  field: mrf-lhs         \ its sides, instantiated
  field: mrf-rhs
end-structure
/mrf context-slab: mrf-frames
: mrf ( -- frame ) mrf-frames slab-last ;
: mtg-eq-of ( goal -- t ) lf-goal-type lf-instantiate! lf-whnf-core lf-must ;
: mtg-is-eq ( t -- t ) dup lf-eq? if 2drop drop exit then outcome-unsupported lf-must ;
: mtg-inst2 ( a b -- a' b' ) lf-instantiate! swap lf-instantiate! swap ;   \ b first
: mrf-sides ( -- ) mrf mrf-eq @ lf-eq? drop mtg-inst2 mrf mrf-rhs ! mrf mrf-lhs ! drop ;
\ isDefEq at the transparency the step runs at (default; reducible under
\ by-rw[ 's with_reducible).
: mtg-defeq ( t s -- flag )
  ['] lf-meta-defeq lf-defeq-elab lf-defeq-mode lf-meta-with outcome-sane lf-must ;
: mrf-equal? ( -- flag ) mrf mrf-lhs @ mrf mrf-rhs @ mtg-defeq ;
\ @Eq.refl.{u} α lhs, u and α those of the goal's Eq (mkConst Eq.refl us,
\ mkApp2).
: mtg-refl-const ( t -- f )
  lf-meta-head s" Eq.refl" lfa-intern swap lf-const-levels lf-mk-const-id ;
: mtg-alpha ( t -- α ) lf-eq? drop 2drop ;
: mrf-term ( -- e )
  mrf mrf-eq @ dup mtg-refl-const swap mtg-alpha lf-mk-app mrf mrf-lhs @ lf-mk-app ;
: mrf-closed ( -- ) mrf mrf-goal @ mrf-term lf-mvar-assign lf-must ;
\ applyRfl's message: the two sides, then the goal; a metavariable left in
\ a side answers 93 instead.
: mtg-rhs. ( rhs -- outcome )
  s\" \nis not definitionally equal to the right-hand side\n" lf-pp-emit
  lf-tac-indented. ;
: mrf-rfl. ( x -- outcome )
  drop mrf mrf-goal @ mrf mrf-rhs @ ['] mtg-rhs. mrf mrf-lhs @ lf-tac-framed-with. ;
: mrf-open? ( -- flag ) mrf mrf-lhs @ mtg-open? mrf mrf-rhs @ mtg-open? or ;
: mrf-unequal ( -- )
  mrf-open? if outcome-unsupported lf-must then
  0 ['] mrf-rfl. lf-tac-detail lfa-e-tac-rfl lf-tac-stop ;
: mrf-run ( -- )
  mrf mrf-goal @ mtg-eq-of mtg-is-eq mrf mrf-eq ! mrf-sides
  mrf-equal? if mrf-closed else mrf-unequal then ;
: mrf-framed ( goal frame -- ) mrf-goal ! mrf-run ;
: lf-goal-refl ( goal -- ) lf-goal-not-assigned mrf-frames ['] mrf-framed lf-with-record ;
base !   \ the BASE this file was loaded with
