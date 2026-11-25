\ Meta induction of the tactic library (plan row TB2, piece E, slice E1;
\ docs/design/TACTIC_PATTERNS.md section 1): Lean 4.35.0's
\ Meta/RecursorInfo.lean (mkRecursorInfoCore :186-226) and
\ Meta/Tactic/Induction.lean (MVarId.induction :203, mkRecursorAppPrefix
\ :166, finalize :57-122), the split under Meta cases (meta-tactic/
\ cases.fs) and through it obtain and rcases (rcases.fs). Each word throws
\ on failure (meta-must.fs), as Lean's do.
\ Public words:
\   lf-recursor-info ( d -- info )  mkRecursorInfo of declaration d, read
\       from d's type, never the inductive's record (so Nat.casesAuxOn, a
\       plain definition, has one): past its pis a bound variable, the
\       motive (the binders before it are the parameters), applied to the
\       indices and the major premise, its last argument (RecursorInfo
\       .lean:105-110: dependent elimination); the major's type a
\       constant I applied to the parameters first, in order (Lean's
\       paramsPos found by position); each level parameter of d the
\       motive's sort's or one of I's levels (getUnivLevelPos). info is a
\       run (lib/runs.fs): d, the binders, the parameters, the major's
\       position, the indices, I's name, then per level parameter of d -1
\       (the motive's) or the index of I's level
\   lf-rinfo-decl lf-rinfo-args lf-rinfo-params lf-rinfo-major
\       lf-rinfo-indices lf-rinfo-type ( info -- x ) those cells;
\       lf-rinfo-minors ( info -- n ) the minor premises (the binders but
\       the parameters, the motive, the indices and the major);
\       lf-rinfo-levels# ( info -- n ), lf-rinfo-level ( info k -- pos )
\   The subgoal record (InductionSubgoal, CasesSubgoal), lf-subgoal-cells
\       cells a subgoal: lf-subgoals# ( subgoals -- n ) their count;
\       lf-subgoal@ ( subgoals i k -- x ) cell k of subgoal i; its fields
\       lf-subgoal-goal, lf-subgoal-fields (a run of free variables),
\       lf-subgoal-subst (fvar-subst.fs) and lf-subgoal-ctor (its
\       constructor's name, cases.fs's) ( subgoals i -- x )
\   lf-target-arity ( t -- n )  getTargetArity (Induction.lean:19): t's
\       leading pis, through head-beta redexes
\   lf-goal-induction ( goal major d names -- subgoals )  MVarId.induction
\       of goal on the free variable major with recursor d, in goal's
\       context (checkNotAssigned first): the major's type through whnf
\       headed by I; the major and its dependents reverted, the major
\       introduced again with its name and flag (revert.fs's
\       lf-goal-revert-kept, goal.fs's lf-goal-intro-kept); the recursor
\       at its levels (the motive's the goal's type's level, normalized),
\       applied to the major type's parameters and to the motive fun x :
\       T => the goal's type over the major (mkRecursorAppPrefix); then
\       each binder in turn (finalize): the major, or a minor premise: a
\       new goal of its domain head-beta reduced, tagged the goal's tag
\       when d has one minor premise, else tag.NAME (NAME the binder's,
\       goal.fs's lf-name-append-tag; Induction.lean:84), the major
\       try-cleared from it, its fields introduced (the binders past the
\       goal's own arity) with names from names' run k for minor k
\       (lf-goal-intro-names: rcases' AltVarNames, explicit), then the
\       other reverted locals with their names and flags (introNP); goal
\       assigned the recursor applied. names: a run of runs of name IDs
\       (a missing run, or name 0, gives the binder's own, inaccessible).
\       subgoals: a subgoal record per minor premise, in order: its
\       goal, its fields, its substitution (the major and each other
\       reverted local to its new free variable) and constructor 0
\       (cases.fs puts the constructor there)
\ Not supported yet (thrown unsupported, 99 at a tactic): indices (an
\ indexed family, slice E4); a recursor whose parameters are not the
\ major type's first arguments in order, or have an instance among them,
\ or whose motive's sort is neither Prop nor a level parameter (Lean's
\ "invalid user defined recursor" errors); the recursor's "ill-formed"
\ and "unexpected major premise type" cases and its eliminating only
\ into Prop on a goal of another sort ("can only eliminate into Prop"),
\ which no recursor Meta cases picks reaches. An instance-implicit minor
\ premise with no names (synthInstance, Induction.lean:89) is taken as
\ an explicit one: no casesOn and no Nat.casesAuxOn has one.
\ Lean call list: getConstInfo, forallTelescopeReducing -> lf-menv-type,
\ lf-meta-forall-body#; whnfUntil -> lf-whnf!; revert -> lf-goal-revert-kept;
\ introNP, intro1P -> lf-goal-intro-kept; getLevel, normalizeLevel ->
\ lf-level!, lf-meta-level-normalize; mkConst -> lf-mk-const-id;
\ mkLambda, abstractM -> lf-term-lam, lf-meta-abstract; inferType ->
\ lf-infer!; whnfForall -> lf-meta-whnf-forall; mkFreshExprSyntheticOpaqueMVar
\ -> lf-goal-new; tryClear -> lf-goal-try-clear; introN ->
\ lf-goal-intro-names; FVarSubst.insert -> lf-fsubst-insert; assign ->
\ lf-mvar-assign.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mri-frames and mid-frames (recursor info's and induction's
\ frames, one per call open, meta-must.fs's lf-with-record), in the
\ checker context (ADR 0009); no other. Loads in decimal whatever BASE
\ is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/bounds.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../core/levels.fs
require ../../present/binder-table.fs
require ../../author/declarations.fs
require ../mvars.fs
require ../goals.fs
require ../instantiate.fs
require ../meta-env.fs
require ../meta-spine.fs
require ../term-eqv.fs
require ../whnf.fs
require ../infer.fs
require ../level-normalize.fs
require ../tactic-run.fs
require ../meta-must.fs
require ../app-builder.fs
require ../fvar-subst.fs
require ./goal.fs
require ./revert.fs
require ./assert.fs
require ./elim.fs


\ ---- RecursorInfo: its six head cells, then a cell per level parameter.
6 constant mri-head#
: lf-rinfo-decl ( info -- d ) 0 run@ ;
: lf-rinfo-args ( info -- n ) 1 run@ ;
: lf-rinfo-params ( info -- n ) 2 run@ ;
: lf-rinfo-major ( info -- k ) 3 run@ ;
: lf-rinfo-indices ( info -- n ) 4 run@ ;
: lf-rinfo-type ( info -- name ) 5 run@ ;
: lf-rinfo-minors ( info -- n )
  dup lf-rinfo-args over lf-rinfo-params - swap lf-rinfo-indices - 2 - ;
: lf-rinfo-levels# ( info -- n ) run-count mri-head# - ;
: lf-rinfo-level ( info k -- pos ) mri-head# + run@ ;

\ mkRecursorInfoCore: a frame per call, d, its binders and conclusion.
begin-structure /mri
  field: mri-concl       \ the conclusion: the motive applied
  field: mri-out         \ the information so far, a run (d, its binders first)
end-structure
/mri context-slab: mri-frames
: mri ( -- frame ) mri-frames slab-last ;
: mri+ ( x -- ) mri mri-out lf-run+! ;
: mri-info ( -- info ) mri mri-out @ ;
\ Binder k's pi of d's type; a bound variable's binder seen from depth n.
: mri-d ( -- d ) mri-info lf-rinfo-decl ;
: mri-n ( -- n ) mri-info lf-rinfo-args ;
: mri-pi ( k -- pi ) mri-d lf-menv-type swap 0 ?do lf-term-second@ loop ;
: mri-at ( n bvar -- k )
  dup lf-term-bvar? 0= if outcome-unsupported lf-must then lf-bvar-binder ;
: mri-args# ( -- m ) mri mri-concl @ lf-meta-args# ;
: mri-motive ( -- k ) mri-n mri mri-concl @ lf-meta-head mri-at ;
: mri-major ( -- k ) mri-args# 0= if outcome-unsupported lf-must then
  mri-n mri mri-concl @ lf-term-second@ mri-at ;
\ The major's type, I applied: I's constant, and parameter k its argument k.
: mri-itype ( -- t ) mri-info lf-rinfo-major mri-pi lf-term-first@ ;
: mri-iconst ( -- const )
  mri-itype lf-meta-head dup lf-term-const? 0= if outcome-unsupported lf-must then ;
: mri-param ( k -- ) mri-info lf-rinfo-major over mri-itype swap lf-meta-app-arg mri-at
  <> if outcome-unsupported lf-must then ;
: mri-params# ( -- n ) mri-info lf-rinfo-params ;
: mri-params ( -- )
  mri-params# mri-itype lf-meta-args# > if outcome-unsupported lf-must then
  mri-params# 0 ?do i mri-param loop ;
\ getUnivLevelPos: the motive's sort's level (getMotiveLevel: Prop, -1
\ here, or a parameter), else one of I's levels, the parameter's.
: mri-motive-sort ( -- sort )
  mri-params# mri-pi lf-term-first@ lf-meta-forall-body# drop ;
: mri-sort ( -- level|-1 )
  mri-motive-sort dup lf-prop? if drop -1 exit then
  dup lf-tag-symbolic-sort lf-term-tag? 0= if outcome-unsupported lf-must then
  lf-term-first@ ;
: mri-param-level? ( level name -- flag )
  over lf-level-tag@ lf-level-tag-param <> if 2drop false exit then
  swap lf-level-first@ = ;
: mri-motive-level? ( name -- flag )
  mri-sort dup 0< if 2drop false else swap mri-param-level? then ;
: mri-ilevel? ( const name k -- const name flag ) >r over r> lf-const-level@
  over mri-param-level? ;
: mri-ilevel ( name -- k ) mri-iconst swap over lf-const-levels#
  ['] mri-ilevel? find-index 0= if outcome-unsupported lf-must then nip ;
: mri-univ ( name -- pos ) dup mri-motive-level? if drop -1 else mri-ilevel then ;
: mri-levels ( -- ) mri-d lf-menv-params 0 ?do i over cell-at@ mri-univ mri+ loop drop ;
: mri-start ( d -- ) lf-decl-telescope mri mri-concl ! mri mri-out ! ;
: mri-run ( d -- info )
  mri-start mri-motive mri+ mri-major mri+ mri-args# 1- mri+ mri-iconst lf-const-name mri+
  mri-params mri-levels mri-info ;
: lf-recursor-info ( d -- info ) mri-frames ['] mri-run lf-with-record ;

\ ---- getTargetArity: pis counted; at a head-beta redex, its function's
\ body counted on (its reduct's count whenever the argument puts no pi at
\ the head, as never for a motive fun x => T applied to a constructor;
\ a redex under the pis has the fields' bound variables in its argument,
\ which instantiate1 would have to lift: not ported, so not reduced).
: mid-redex? ( t -- flag ) dup lf-meta-app? if lf-meta-app-head lf-term-lam? else drop
  false then ;
: mid-arity-step ( n t -- n' t' flag )
  dup lf-term-pi? if lf-term-second@ swap 1+ swap true exit then
  dup mid-redex? if lf-meta-app-head lf-term-second@ true else false then ;
: lf-target-arity ( t -- n ) 0 swap begin mid-arity-step 0= until drop ;

\ ---- MVarId.induction: a frame per call (lf-with-record).
begin-structure /mid
  field: mid-d           \ the recursor's declaration
  field: mid-info        \ and its information
  field: mid-names       \ the alternatives' names, a run of runs
  field: mid-kept        \ the reverted locals, the major first
  field: mid-goal        \ the goal reverted, its major introduced again
  field: mid-major       \ the major premise given, then introduced again
  field: mid-rec         \ the recursor applied so far
  field: mid-rtype       \ and its type
  field: mid-pos         \ the binder reached
  field: mid-minor       \ the minor premises passed
  field: mid-arity       \ the goal's type's arity (initialArity)
  field: mid-done        \ true once the major is applied (consumedMajor)
  field: mid-out         \ the subgoals so far, a run
end-structure
/mid context-slab: mid-frames
: mid ( -- frame ) mid-frames slab-last ;
: mid-info@ ( -- info ) mid mid-info @ ;
: mid-goal@ ( -- goal ) mid mid-goal @ ;
: mid-out+ ( x -- ) mid mid-out lf-run+! ;

\ ---- The subgoal record: a goal, its fields, substitution, constructor.
4 constant lf-subgoal-cells
: lf-subgoals# ( subgoals -- n ) run-count lf-subgoal-cells / ;
: lf-subgoal@ ( subgoals i k -- x ) swap lf-subgoal-cells * + run@ ;
: lf-subgoal-goal ( subgoals i -- goal ) 0 lf-subgoal@ ;
: lf-subgoal-fields ( subgoals i -- fields ) 1 lf-subgoal@ ;
: lf-subgoal-subst ( subgoals i -- fs ) 2 lf-subgoal@ ;
: lf-subgoal-ctor ( subgoals i -- name ) 3 lf-subgoal@ ;
\ The major's type through whnf (whnfUntil I: no type of a free variable
\ is reduced further once headed by an inductive type), headed by I.
: mid-itype ( fvar -- t ) lf-infer! lf-whnf! ;
: mid-typed ( major -- major )
  dup mid-itype lf-meta-head-name 0= if outcome-unsupported lf-must then
  mid-info@ lf-rinfo-type lf-name-same? 0= if outcome-unsupported lf-must then ;
: mid-checked ( major -- major )
  mid-info@ lf-rinfo-indices if outcome-unsupported lf-must then mid-typed ;
\ Revert the major and its dependents, introduce the major again.
: mid-revert ( goal major -- goal2 )
  lf-run1 lf-goal-revert-kept dup mid mid-kept ! 1 lf-goal-intro-kept 0 run@
  mid mid-major ! dup mid mid-goal ! ;

\ ---- mkRecursorAppPrefix, in goal2's context.
: mid-level ( -- u ) mid-goal@ lf-goal-type lf-level! lf-meta-level-normalize lf-must ;
: mid-ilevel ( k -- u ) mid mid-major @ mid-itype lf-meta-head swap lf-const-level@ ;
: mid-ulevel ( pos -- u ) dup 0< if drop mid-level else mid-ilevel then ;
: mid-motive-at? ( info k -- info flag ) over swap lf-rinfo-level 0< ;
: mid-prop-only ( -- )
  mid-info@ dup lf-rinfo-levels# ['] mid-motive-at? any? nip if exit then
  mid-level lf-level-tag@ lf-level-tag-zero <> if outcome-unsupported lf-must then ;
: mid-levels ( -- u1 .. un n )
  mid-info@ lf-rinfo-levels# dup 0 ?do mid-info@ i lf-rinfo-level mid-ulevel swap loop ;
: mid-const ( -- e ) mid-info@ lf-rinfo-decl lf-menv-name mid-levels lf-mk-const-id ;
: mid-motive ( -- lam )
  mid mid-major @ lf-infer! mid-goal@ lf-goal-type lf-instantiate! mid mid-major 1
  lf-meta-abstract lf-must lf-term-lam lf-made! dup s" x" lfa-intern lf-binder-default
  lf-pres-binder! lf-must ;
\ The recursor applied, its type instantiated binder by binder (whnfForall,
\ instantiate1: Lean's inferType of the application would also
\ beta-reduce the motive's applications in the minor premises' types,
\ whose arguments under the fields' pis hold bound variables that
\ instantiate1 does not lift; the fields' goals are head-beta reduced as
\ introN makes them, so goals and term are Lean's).
: mid-pi ( -- pi ) mid mid-rtype @ lf-meta-whnf-forall lf-must dup mid mid-rtype ! ;
: mid-apply ( x -- )
  mid mid-rec @ over lf-mk-app mid mid-rec ! mid mid-rtype @ lf-term-second@ swap
  lf-meta-instantiate1 lf-must mid mid-rtype ! 1 mid mid-pos +! ;
: mid-app ( x -- ) mid-pi lf-term-pi? 0= if outcome-unsupported lf-must then mid-apply ;
: mid-param ( type k -- type ) over swap lf-meta-app-arg mid-app ;
: mid-params ( -- )
  mid mid-major @ mid-itype mid-info@ lf-rinfo-params 0 ?do i mid-param loop drop ;
: mid-prefix ( -- )
  mid-prop-only mid-const dup mid mid-rec ! lf-infer! mid mid-rtype ! mid-params
  mid-motive mid-app ;

\ ---- finalize: each binder after the motive, the major or a minor premise.
: mid-more? ( -- flag ) mid-pi lf-term-pi? mid mid-pos @ mid-info@ lf-rinfo-args < and ;
: mid-major! ( -- ) mid mid-major @ mid-apply true mid mid-done ! ;
\ A minor premise's goal: its domain, the tag Induction.lean:84 gives.
: mid-tag ( pi -- tag )
  mid-goal@ lf-goal-tag mid-info@ lf-rinfo-minors 1 = if nip exit then
  swap lf-binder-name lf-name-append-tag ;
: mid-mvar ( pi -- mvar ) dup lf-binder-domain swap mid-tag mid-goal@ lf-goal-view
  lf-goal-new lf-must ;
: mid-fields# ( mvar -- n )
  lf-goal-type lf-target-arity mid mid-arity @ -
  dup 0< if outcome-unsupported lf-must then ;
: mid-names@ ( -- names ) mid mid-names @ mid mid-minor @ run@0 ;
: mid-extras ( -- kept n ) mid mid-kept @ 1 run-after lf-must dup run-count ;
\ The major try-cleared, the fields introduced, then the other reverted.
: mid-subgoal ( mvar -- goal fields extras )
  dup mid-fields# >r mid mid-major @ lf-goal-try-clear mid-names@ r> lf-goal-intro-names
  >r mid-extras lf-goal-intro-kept r> swap ;
\ The substitution: the major's, then each other reverted local's.
: mid-base ( -- fs ) 0 mid mid-kept @ 0 run@ lf-local-fvar mid mid-major
  @ lf-fsubst-insert ;
: mid-old ( k -- fvar ) mid mid-kept @ swap 1+ run@ lf-local-fvar ;
: mid-extra+ ( fs extras k -- fs' extras ) 2dup run@ swap mid-old swap rot >r
  lf-fsubst-insert r> ;
: mid-subst ( extras -- fs ) mid-base swap dup run-count 0 ?do i mid-extra+ loop drop ;
: mid-minor! ( -- )
  mid mid-rtype @ mid-mvar dup mid-apply mid-subgoal mid-subst >r swap mid-out+ mid-out+
  r> mid-out+ 0 mid-out+ 1 mid mid-minor +! ;
: mid-step ( -- )
  mid mid-pos @ mid-info@ lf-rinfo-major = if mid-major! else mid-minor! then ;
: mid-start ( -- )
  mid-goal@ lf-goal-type lf-target-arity mid mid-arity ! mid-info@ lf-rinfo-params 1+
  mid mid-pos ! ;
: mid-end ( -- subgoals )
  mid mid-done @ 0= if outcome-unsupported lf-must then
  mid-goal@ mid mid-rec @ lf-mvar-assign lf-must mid mid-out @ ;
: mid-rest ( -- subgoals )
  mid-prefix mid-start begin mid-more? while mid-step repeat mid-end ;
\ In goal's context, once it is checked not assigned.
: mid-body ( goal -- subgoals )
  mid mid-d @ lf-recursor-info mid mid-info ! mid mid-major @ mid-checked mid-revert
  ['] mid-rest lf-with-goal ;
: mid-framed ( goal major d names -- subgoals )
  mid mid-names ! mid mid-d ! mid mid-major ! ['] mid-body lf-goal-within ;
: lf-goal-induction ( goal major d names -- subgoals )
  mid-frames ['] mid-framed lf-with-record ;
base !   \ the BASE this file was loaded with
