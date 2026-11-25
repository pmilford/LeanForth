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
\   lf-goal-within ( i*x goal xt -- j*x )  mvarId.withContext do
\       mvarId.checkNotAssigned ...: xt ( i*x goal -- j*x ) in goal's
\       context once goal is checked not assigned (Meta induction's and
\       cases')
\   lf-goal-replace-target-eq ( goal new h -- goal' )  MVarId.replaceTargetEq
\       (Replace.lean:21-32): a new synthetic opaque goal of type new with
\       goal's tag in goal's context; goal assigned
\       Eq.mpr.{u} target new (id (target = new) h) goal', target goal's
\       type as stored and u its level
\   lf-goal-exfalso ( goal -- goal' )  MVarId.exfalso (Apply.lean:286-293),
\       the term of Lean's exfalso macro (refine False.elim ?_, Init/
\       Tactics.lean:276: refine's one new goal takes the main goal's tag,
\       and Sort ?u =?= inferType target gives getLevel's level): in goal's
\       context (the caller's; checkNotAssigned first), goal' a new
\       synthetic opaque goal of type False with goal's tag; goal assigned
\       @False.elim.{u} target goal', target goal's type instantiated, u
\       its level (getLevel)
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
\       has none, made inaccessible; names 0: none given, Lean's [], each
\       so), of the kind at kinds (kinds 0: the node's, Lean's c,
\       explicit, implicit or strict implicit: plan row TB1, by-intro and
\       by-intros as Lean's intro and intros); goal' is a new synthetic
\       opaque goal of the body (the variables put in, head-beta reduced)
\       with goal's tag, and goal is assigned fun xs => ?n xs
\       (telescope.fs's lf-mk-lambda-fvars). No pi is Lean's introN error
\       94 with the goal, or 93 where whnf's delta might still make one
\       (infer.fs's lf-whnf-firm?); not supported yet (99): a let
\       (mkLambdaFVars has no let case), and with kinds 0 a binder of no
\       known kind or an instance one (a local instance is plan FE3). The
\       current context is put back.
\   lf-goal-intro-names ( goal names n -- goal' xs )  introN n with the
\       names of the run names (Lean's givenNames, useNamesForExplicitOnly
\       false: a name for every binder in turn; 0, Lean's _, and every
\       binder past the run's end the binder's own name, inaccessible)
\       and the nodes' kinds: lf-goal-intro-n, xs the new free variables
\       as a run; n 0 gives goal itself and 0 (Lean asks nothing then)
\   lf-goal-intro-kept ( goal kept n -- goal' xs )  introNP n (Intro.lean
\       :139, preserveBinderNames) of binders revert.fs's
\       lf-goal-revert-kept made: each takes its name, kind and
\       inaccessible flag back from the first n locals of the run kept (an
\       anonymous one a fresh inaccessible a, Intro.lean:116), so a name
\       Lean hides stays hidden (TACTIC_PATTERNS.md section 3, review 2);
\       an instance binder is not supported yet (99, plan FE3); xs a run;
\       n 0 gives goal itself and 0; kept shorter than n is thrown invalid
\   lf-binder-domain ( pi -- dom )  a binder's domain head-beta reduced
\       (introN's and Meta induction's d.headBeta)
\   lf-intros-size ( type -- n )  getIntrosSize (Intro.lean:190): the
\       leading pis and lets of type as it is (no delta, no
\       instantiation; LeanForth's terms carry no mdata)
\   lf-goal-intros ( goal -- goal' )  MVarId.intros (Intro.lean:199-206):
\       n, lf-intros-size of goal's type instantiated; 0 gives goal itself
\       (unassigned), else introN n with no names and the nodes' kinds, the
\       n free variables in cells of mti-cells (meta-must.fs's
\       lf-with-cells)
\   lf-goal-clear! ( goal fvar -- goal' )  MVarId.clear (Clear.lean:20-41),
\       the throwing face of goals.fs's lf-goal-clear: in goal's context
\       (checkNotAssigned first), fvar must be a local of it (else error
\       440, "Tactic `clear` failed: unknown variable 'x'"), no other
\       local's declaration may depend on it (the oldest that does: 441,
\       "variable 'h' depends on 'x'"), nor the goal's type (442, "target
\       depends on 'x'"), each with the goal after a blank line; goal' a
\       new goal of the same type and tag in the context without fvar,
\       goal assigned it
\   lf-view-scoped? ( e view -- flag )  whether every free variable of e
\       is a local of the context view (checkAssignment's fvar test;
\       have's terms, tactics/have.fs)
\   lf-goal-checked-assign ( goal e -- )  MVarId.checkedAssign
\       (ExprDefEq.lean:1341) as closeMainGoal calls it: a free variable
\       of e outside goal's context, or an assignment refused, is error 98
\       with e, Lean's occurs-check line and the goal; an unassigned
\       metavariable in e answers 93 (Lean's checkAssignment would
\       restrict it, not ported)
\   lf-goal-refl ( goal -- )  the rfl macro's last two rules (Init/
\       Tactics.lean:477-480; tactics/rfl.fs tries exact Iff.rfl and
\       exact HEq.rfl first): eq_refl, MVarId.refl (Refl.lean:25) under
\       withAssignableSyntheticOpaque: goal's type through whnf at the
\       transparency in force, instantiated (getType'), Eq applied to
\       three arguments (any other goal: applyRfl at once); its sides
\       instantiated and definitionally equal close goal with
\       @Eq.refl.{u} α lhs (Eq's own level and type); else applyRfl
\       (Rfl.lean:67-97): the type instantiated through whnfR, a relation
\       of two arguments or more (else error 457, "Tactic `rfl` failed:
\       Expected the goal to be a binary relation", its hint and the goal;
\       HEq of four 93, its HEq.refl path not ported), its last two
\       compared by approxDefEq isDefEqGuarded (meta-must.fs's
\       lf-defeq-approx!): unequal is error 97 with Lean's text (the
\       sides, the goal); equal sides of Eq close goal as above, of
\       another relation 93 (its @[refl] lemmas, Init's Iff.refl and the
\       Perm lemmas, are not in the elaboration data)
\   lf-goal-fresh ( type goal -- goal' )  mkFreshExprSyntheticOpaqueMVar
\       type (getTag goal) in goal's context: a new synthetic opaque goal
\       of type with goal's tag (the goal words' new goals)
\   lf-local-detail-at? ( k -- flag )  LocalDecl.isImplementationDetail of
\       local k of the current context
\   lf-goal-replace-target-defeq ( goal new -- goal' )
\       MVarId.replaceTargetDefEq (Replace.lean:44-61): goal itself when
\       new equals its type, as stored or both instantiated; else goal' a
\       new synthetic opaque goal of type new with goal's tag in goal's
\       context, goal assigned @id.{u} target goal' (mkExpectedTypeHint,
\       app-builder.fs: target instantiated, u its level); show's,
\       change's and delta's (plan row TB2)
\ Errors are thrown as authoring errors at the step running
\ (tactic-run.fs's lf-tac-stop and lf-tac-fail), Meta failures as
\ outcomes (meta-must.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mti-frames and mrf-frames (introN's and refl's frames, one per
\ call open, meta-must.fs's lf-with-record), mti-cells (intros' free
\ variables, n cells a call, meta-must.fs's lf-with-cells) and mtk-frames
\ (intro-names' and intro-kept's frames, one per call open), in the
\ checker context (ADR 0009); no other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/find.fs
require ../../lib/runs.fs
require ../../lib/bounds.fs
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
require ../meta-spine.fs
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
: lf-goal-within ( i*x goal xt -- j*x ) swap lf-goal-not-assigned tuck swap lf-with-goal ;

\ ---- replaceTargetEq: goal' new in goal's context with goal's tag, goal
\ assigned Eq.mpr.{u} target new (mkExpectedPropHint h (mkEq target new)) goal'.
\ mkFreshExprSyntheticOpaqueMVar type tag in goal's context, the goal
\ words' new goal (here and meta-tactic/assert.fs's).
: lf-goal-fresh ( type goal -- goal' )
  dup lf-goal-tag swap lf-goal-view lf-goal-new lf-must ;
: mtg-fresh ( goal new -- goal goal' ) over lf-goal-not-assigned lf-goal-fresh ;
\ Whether local k of the current context is an implementation detail
\ (isImplementationDetail: revert's and contradiction's test).
: lf-local-detail-at? ( k -- flag ) lf-mctx-view swap lf-view-local lf-local-detail? ;
: mtg-eq ( goal goal' -- eq ) lf-goal-type swap lf-goal-type swap lf-mk-eq ;
: mtg-hint ( goal goal' h -- goal goal' h' )
  >r 2dup mtg-eq r> swap lf-mk-expected-prop-hint ;
\ The constant c-addr u at target's level, applied to target: C.{u} target.
: mtg-at-level ( target c-addr u -- f )
  lfa-intern over lf-level! 1 lf-mk-const-id swap lf-mk-app ;
: mtg-mpr ( target -- f ) s" Eq.mpr" mtg-at-level ;
: mtg-value ( goal goal' h' -- goal goal' value )
  >r 2dup lf-goal-type swap lf-goal-type mtg-mpr swap lf-mk-app r> lf-mk-app
  over lf-mk-app ;
: mtg-assign ( goal goal' value -- goal' ) rot swap lf-mvar-assign lf-must ;
: lf-goal-replace-target-eq ( goal new h -- goal' )
  >r mtg-fresh r> mtg-hint mtg-value mtg-assign ;

\ ---- MVarId.exfalso (Apply.lean:286-293): goal' of type False in goal's
\ context with goal's tag; goal assigned False.elim.{u} target goal'.
: mtg-elim ( goal -- goal f )
  dup lf-goal-type lf-instantiate! s" False.elim" mtg-at-level ;
: mtg-false ( goal f -- goal goal' f )
  over s" False" lf-mk-const0 swap lf-goal-fresh swap ;
: lf-goal-exfalso ( goal -- goal' )
  lf-goal-not-assigned mtg-elim mtg-false over lf-mk-app mtg-assign ;

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
  field: mti-k           \ the binder's kind (the caller's, else the node's)
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
  mti mti-goal @ lfa-e-tac-no-intro lf-tac-ex ;
: mti-reduced ( t -- pi ) lf-whnf-core lf-must dup lf-term-pi? if exit then dup mti-none ;
: mti-binder ( -- pi )
  mti mti-type @ dup mti-binding? if exit then lf-instantiate!
  dup mti-binding? if exit then mti-reduced ;
\ The i-th of the caller's n cells at addr (none given: addr 0, the cell 0).
: mti-at ( addr -- addr' ) mti mti-i @ cells + ;
: mti-given ( addr -- x ) ?dup if mti-at @ else 0 then ;
\ Not supported yet (99): a let (telescope.fs's mkLambdaFVars has no let
\ case); with no kinds given, a binder whose kind is not known (the
\ node's record, which a shared node may hide) or is instance implicit
\ (a local instance, plan FE3). Else the binder's kind is the caller's,
\ or the node's (Lean's c of introNImp's forallE case): explicit,
\ implicit or strict implicit, kept in the frame.
: mti-unlet ( pi -- pi ) dup lf-let? if lf-tac-unported then ;
: mti-introduced ( kind -- kind ) dup lf-binder-instance < 0= if lf-tac-unported then ;
: mti-node-kind ( pi -- kind ) lf-binder-of 0= if lf-tac-unported then nip
  mti-introduced ;
: mti-kind ( pi -- kind ) mti mti-kinds @ ?dup if nip mti-at @ else mti-node-kind then ;
: mti-kind! ( pi -- pi ) dup mti-kind mti mti-k ! ;
\ The name given, else the binder's own (a when it has none) made
\ inaccessible (names 0: none given, Lean's []).
: mti-own ( pi -- name ) lf-binder-name ?dup 0= if s" a" lfa-intern then ;
: mti-named ( pi -- name flags )
  mti mti-names @ mti-given ?dup if nip 0 exit then mti-own lf-local-inaccessible ;
\ One binder: its free variable kept, its local pushed on the current view.
: lf-binder-domain ( pi -- dom ) lf-term-first@ lf-meta-head-beta lf-must ;
: mti-local ( pi -- fvar )
  dup lf-binder-domain swap mti-named mti mti-k @ or lf-local-decl-new lf-mctx-view! ;
: mti-x! ( fvar -- ) mti mti-xs @ mti-at ! 1 mti mti-i +! ;
: mti-body ( pi fvar -- t )
  swap lf-term-second@ swap lf-meta-instantiate1 lf-must lf-meta-head-beta lf-must ;
: mti-step ( -- )
  mti-binder mti-unlet mti-kind! dup mti-local dup mti-x! mti-body mti mti-type ! ;
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

\ ---- getIntrosSize (Intro.lean:190) and MVarId.intros (:199): every
\ leading pi and let of the type instantiated, as they are (no delta;
\ LeanForth's terms carry no mdata), introduced at once with no names, in
\ n cells of mti-cells (lf-with-cells, meta-must.fs).
: lf-intros-size ( type -- n )
  0 swap begin lf-tag-pi lf-meta-under while swap 1+ swap repeat drop ;
1 cells context-slab: mti-cells
: mti-intros ( goal n xs -- goal' ) 0 0 2swap lf-goal-intro-n ;
: lf-goal-intros ( goal -- goal' )
  dup lf-goal-type lf-instantiate! lf-intros-size ?dup 0= if exit then
  dup mti-cells ['] mti-intros lf-with-cells ;

\ ---- introN with a run of names, introNP with revert's kept locals: a
\ binder at a time (introN of 1, its new goal the next one's: the same
\ term once instantiated), a frame per call (lf-with-record) holding the
\ binder's name, its kind (intro-kept's: the kind and the inaccessible
\ flag, which mti-local ORs into the local's flags) and its variable.
begin-structure /mtk
  field: mtk-name        \ the binder's name (introN's one cell)
  field: mtk-kind        \ its kind and flag (intro-kept's one cell)
  field: mtk-x           \ its free variable
  field: mtk-xs          \ the free variables so far, a run
end-structure
/mtk context-slab: mtk-frames
: mtk ( -- frame ) mtk-frames slab-last ;
: mtk-kinds ( kinds? -- addr|0 ) if mtk mtk-kind else 0 then ;
: mtk-one ( goal kinds? -- goal' )
  mtk mtk-name swap mtk-kinds 1 mtk mtk-x lf-goal-intro-n
  mtk mtk-xs @ mtk mtk-x @ lf-run+ mtk mtk-xs ! ;
\ introN's names: name i of the run, 0 past its end.
: mtn-step ( goal names i -- goal' names )
  over swap run@0 mtk mtk-name ! swap false mtk-one swap ;
: mtn-run ( goal names n -- goal' xs ) 0 ?do i mtn-step loop drop mtk mtk-xs @ ;
\ n 0 gives goal itself and the empty run; else xt in a frame of its own.
: mtk-framed ( goal src n xt -- goal' xs )
  over 0= if 2drop drop 0 exit then mtk-frames swap lf-with-record ;
: lf-goal-intro-names ( goal names n -- goal' xs ) ['] mtn-run mtk-framed ;
\ introNP's: each kept local's name, and its kind with its inaccessible flag.
: mtk-flags ( local -- flags )
  dup lf-local-binder mti-introduced swap lf-local-inaccessible? lf-local-inaccessible
  and or ;
: mtk-local ( local -- ) dup lf-local-name mtk mtk-name ! mtk-flags mtk mtk-kind ! ;
: mtk-step ( goal kept i -- goal' kept ) over swap run@ mtk-local swap true mtk-one swap ;
: mtk-run ( goal kept n -- goal' xs )
  2dup swap run-count > if outcome-invalid lf-must then
  0 ?do i mtk-step loop drop mtk mtk-xs @ ;
: lf-goal-intro-kept ( goal kept n -- goal' xs ) ['] mtk-run mtk-framed ;

\ ---- MVarId.clear (Clear.lean:20-41): its three refusals, each
\ throwTacticEx `clear` with Lean's text and the goal, then goals.fs's
\ lf-goal-clear (which checks again and makes the goal).
440 lfa-lean s" Tactic `clear` failed: unknown variable"
  lfa-code: lfa-e-clear-unknown
441 lfa-lean s" Tactic `clear` failed: variable" lfa-code: lfa-e-clear-depends
442 lfa-lean s" Tactic `clear` failed: target depends on"
  lfa-code: lfa-e-clear-target
: mcl-depends. ( fvar -- outcome ) s"  depends on" lf-pp-emit lf-tac-quoted-after. ;
: mcl-known ( goal fvar -- goal fvar )
  over lf-goal-view over lf-view-has? 0= if lfa-e-clear-unknown lf-tac-ex-quoted then ;
\ localDeclDependsOn of local k, fvar's own passed over (lctx.forM: the
\ oldest first).
: mcl-dep? ( fvar k -- fvar flag )
  lf-mctx-fvar 2dup = if drop false exit then
  over lf-local-depends-on? lf-must ;
: mcl-dependent ( goal fvar k -- )
  lf-mctx-fvar ['] lf-tac-quoted-after. lf-tac-inline
  ['] mcl-depends. lf-tac-inline lfa-e-clear-depends lf-tac-ex ;
: mcl-locals ( goal fvar -- goal fvar )
  dup lf-mctx-view lf-view-count ['] mcl-dep? find-index if mcl-dependent then ;
: mcl-target ( goal fvar -- goal fvar )
  over lf-goal-type over lf-depends-on? lf-must
  if lfa-e-clear-target lf-tac-ex-quoted then ;
: mcl-run ( goal fvar -- goal' ) mcl-known mcl-locals mcl-target lf-goal-clear lf-must ;
: lf-goal-clear! ( goal fvar -- goal' )
  over lf-goal-not-assigned drop over ['] mcl-run lf-with-goal ;

\ ---- checkedAssign (ExprDefEq.lean:1341) as closeMainGoal calls it.
: mtg-outside? ( view leaf -- view flag )
  dup lf-term-tag@ lf-tag-fvar = if over swap lf-view-has? 0= else drop false then ;
: mtg-occurs. ( x -- outcome )
  drop s\" \nthis is often due to an occurs-check failure" lf-pp-emit outcome-ok ;
: mtg-assign. ( goal e -- outcome ) 0 swap ['] mtg-occurs. swap lf-tac-framed-with. ;
: mtg-unassignable ( goal e -- )
  2 ['] mtg-assign. lf-tac-detail-n lfa-e-tac-assign lf-tac-stop ;
: lf-view-scoped? ( e view -- flag ) ['] mtg-outside? lf-term-holds-with? lf-must 0= ;
: mtg-in-scope ( goal e -- goal e )
  2dup swap lf-goal-view lf-view-scoped? 0= if 2dup mtg-unassignable then ;
: mtg-assigned ( goal e -- )
  2dup lf-mvar-assign dup outcome-invalid = if drop mtg-unassignable exit then
  lf-must 2drop ;
: lf-goal-checked-assign ( goal e -- ) lf-open-mvar-free mtg-in-scope mtg-assigned ;

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
\ Lean's error 457 with its hint and the goal, rfl's own on a goal that
\ is no relation; HEq of four, whose HEq.refl path is not ported, 93);
\ approxDefEq isDefEqGuarded of the sides.
457 lfa-lean s" Tactic `rfl` failed: Expected the goal to be a binary relation"
  lfa-code: lfa-e-rfl-binary
: mrf-hint. ( goal -- outcome )
  s\" \nHint: Reflexivity tactics can only be used on goals of the form " lf-pp-emit
  s\" `x ~ x` or `R x x`\n" lf-pp-emit lf-tac-goal-of. ;
: mrf-binary ( t -- t )
  dup lf-meta-app2? if exit then
  mrf mrf-goal @ ['] mrf-hint. lf-tac-detail lfa-e-rfl-binary lf-tac-stop ;
: mrf-rel ( t -- t )
  mrf-binary dup 4 s" HEq" lf-meta-app-of? if outcome-unsupported lf-must then ;
: mrf-whnf-r ( -- )
  mrf mrf-goal @ lf-goal-type lf-instantiate! lf-whnf-r! mrf-rel
  dup mrf mrf-eq ! lf-meta-args2 mrf mrf-sides 2! ;
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
\ eq_refl on a goal that is no Eq (Lean's "equality expected", never the
\ error shown) gives way to apply_rfl at once.
: mtg-eq-app? ( t -- flag ) lf-eq? dup if nip nip nip then ;
: mrf-eq-of? ( -- flag )
  mrf mrf-goal @ mtg-eq-of dup mtg-eq-app? if mrf-eq! true else drop false then ;
: mrf-run ( -- )
  mrf-eq-of? 0= if mrf-apply-rfl exit then
  mrf-equal? if mrf-closed else mrf-apply-rfl then ;
: mrf-framed ( goal -- ) mrf mrf-goal ! mrf-run ;
: lf-goal-refl ( goal -- ) lf-goal-not-assigned mrf-frames ['] mrf-framed lf-with-record ;

\ ---- replaceTargetDefEq (Replace.lean:44-61): goal itself when new is
\ its type as stored, or both instantiated are, compared node for node
\ (Expr.equal; term-eqv.fs's lf-meta-eqv, Lean's ==, differs only on
\ binder names, which LeanForth's terms keep apart and no text writes);
\ else goal' of type new with goal's tag in its context, and goal
\ assigned @id.{u} target goal' (mkExpectedTypeHint of the target
\ instantiated). LeanForth keeps a goal's type as made, so the type
\ Lean caches on the second test stays as it was (the same term once
\ instantiated).
: mtg-same? ( a b -- flag ) lf-meta-eqv lf-must ;
: mtg-unchanged? ( goal new -- goal new flag ) over lf-goal-type over mtg-same? ;
: mtg-inst-same? ( goal new -- goal new' flag )
  lf-instantiate! over lf-goal-type lf-instantiate! over mtg-same? ;
: mtg-hinted ( goal new -- goal' )
  over lf-goal-fresh over lf-goal-type lf-instantiate! over swap lf-mk-expected-type-hint
  mtg-assign ;
: lf-goal-replace-target-defeq ( goal new -- goal' )
  over lf-goal-not-assigned drop mtg-unchanged? if drop exit then
  mtg-inst-same? if drop exit then mtg-hinted ;
base !   \ the BASE this file was loaded with
