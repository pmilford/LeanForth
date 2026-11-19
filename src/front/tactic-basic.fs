\ The first tactics (plan FE1g-4; design docs/design/FE1G_TACTICS.md
\ 5.1-5.3), each the action of its kind's row of the runner
\ (tactic-run.fs), after Lean 4.35.0's Elab/Tactic/BuiltinTactic.lean
\ (evalIntro), Meta/Tactic/Intro.lean (introNImp, mkAuxNameImp),
\ MetavarContext.lean (elimMVar), Elab/Tactic/ElabTerm.lean (evalExact,
\ closeMainGoalUsing, elabTermEnsuringType), Meta/Tactic/Refl.lean
\ (MVarId.refl) and Meta/Tactic/Rfl.lean (applyRfl's message).
\ - by-intro: NAME, Lean's intro NAME: the main goal's type as stored,
\   else instantiated, else put through whnfCore (front/whnf.fs), must
\   be a pi. Its binder becomes a hypothesis, a new free variable of the
\   domain (head-beta reduced) whose local, named NAME or for _ the
\   binder's own name (a when it has none) made inaccessible, explicit,
\   is pushed on the goal's context; a new synthetic
\   opaque goal of the body (the variable put in, head-beta reduced),
\   with the old goal's tag, takes the old goal's place, which is
\   assigned fun x => ?n x, ?n a new synthetic opaque metavariable of
\   type (x : domain) -> body in the old context, delayed-assigned [x] :=
\   the new goal (Lean's mkLambdaFVars through elimMVar: telescope.fs's
\   lf-mk-lambda-fvars in the new goal's context). No pi: error 94
\   with the goal (Lean's introN error); where whnf's delta might still
\   make one (a definition at the head, front/infer.fs lf-whnf-firm?):
\   93. Not supported yet (99): a let to introduce, the name rfl (Lean's
\   intro rfl substitutes, plan FE5), and a binder whose kind is not
\   known explicit: the presentation side table holds a node's binder
\   kind, which a shared node may hide (review fe1c-3 R1), and an
\   instance binder would make the hypothesis a local instance (Lean's
\   isClass?, plan FE3). A hypothesis of a class type whose binder is
\   explicit is not made a local instance either (plan FE3).
\ - t by-exact, Lean's exact t: in the main goal's context (its view
\   current), t elaborated against the goal's type (lf-tac-elab, Lean's
\   Tactic.elabTerm, front/elab-decl.fs, with no postponing), its type inferred
\   (infer.fs) and compared with the goal's by isDefEq (defeq.fs, the
\   elaborator's configuration, default transparency): false is error 96
\   with Lean's text (tactic-msg.fs's lf-has-type-but-expected.). Lean
\   compares with
\   synthetic opaque metavariables assignable; this does not, so either
\   type holding an unassigned one answers 93 first. A metavariable the
\   step made and left unassigned is error 95 (Lean's "don't know how to
\   synthesize"); then the goal is assigned the term, which must hold no
\   unassigned metavariable (Lean's checkAssignment would restrict it:
\   93) and no free variable outside the goal's context (Lean's
\   checkedAssign fails: error 98, as the occurs check), and leaves the
\   list.
\ - by-rfl, Lean's rfl: its macro's alternatives exact Iff.rfl and exact
\   HEq.rfl fail without a trace on a goal whose type, instantiated and
\   put through whnfCore, is Eq applied to three arguments (another
\   inductive type, nothing unfolds), and eq_refl decides: the sides
\   instantiated, isDefEq at default transparency; true assigns
\   @Eq.refl.{u} α lhs (Eq's own level and type), false is apply_rfl's
\   error 97 with Lean's text (the sides and the goal). Any other goal,
\   and false with a metavariable left in a side (apply_rfl's
\   approximations might still unify them), answer 93.
\ Error texts print terms as the goals print them; Lean's
\ addPPExplicitToExposeDiff (explicit arguments where the two would
\ print alike) and its line breaks past width 120 are not ported (plan
\ 8.6).
\ Words for S2's tactics (tactic-induction.fs): lf-tac-intro-as ( given
\ kind i -- ) the main goal's first binder introduced as given (0: its
\ own name, inaccessible) with the kind given (introN for an
\ alternative's fields); lf-tac-binder ( pi -- name kind ).
\ The step record, the messages and the Elab glue are tactic-core.fs's
\ and tactic-msg.fs's; terms are built by the tactic library
\ (app-builder.fs, telescope.fs), whose failures the runner makes
\ authoring errors (tactic-run.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (the step record's fields, tactic-core.fs's tb).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/let-terms.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs
require ../present/print-job.fs
require ../author/errors.fs
require ../author/declarations.fs
require ./term-find.fs
require ./mvars.fs
require ./lctx-views.fs
require ./goals.fs
require ./instantiate.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./whnf.fs
require ./infer.fs
require ./defeq.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-msg.fs
require ./tactic-core.fs
require ./meta-must.fs
require ./app-builder.fs
require ./telescope.fs

: lfb-failed ( xt code -- ) lf-tac-failed ;

\ ---- Leaves (front/term-find.fs's lf-term-holds-with?).
\ The tests: a metavariable not assigned (mvars.fs's lf-mvar-open?), one
\ also synthetic opaque, one also new (numbered from the count from); a
\ free variable outside the context view.
: lfb-opaque? ( leaf -- flag )
  dup lf-mvar-open? if lf-mvar-kind drop mv-opaque = else drop false then ;
: lfb-new? ( from leaf -- from flag )
  dup lf-mvar-open? if lf-term-first@ over < 0= else drop false then ;
: lfb-seen? ( view fvar -- view flag ) over swap lf-view-find dup if nip then ;
: lfb-outside? ( view leaf -- view flag )
  dup lf-term-tag@ lf-tag-fvar = if lfb-seen? 0= else drop false then ;
: lfb-holds? ( term xt -- flag ) lf-term-holds? lf-tac-must ;
: lfb-holds-with? ( term x xt -- flag ) lf-term-holds-with? lf-tac-must ;

\ A pi's binder name and kind: the presentation table's, else its input
\ record's, else the anonymous name, explicit.
: lf-tac-binder ( pi -- name kind )
  dup lf-pres-binder@ if 2>r drop 2r> exit then
  lf-term-input-binder@ 0= if 0 lf-binder-default then ;
: lfb-blank-goal. ( x -- outcome ) drop tb tb-goal @ lf-tac-goal-of. ;

\ ---- by-intro: NAME.
: lfb-binding? ( t -- flag ) dup lf-term-pi? swap lf-let? or ;
: lfb-no-binder ( t -- )
  lf-whnf-firm? lf-tac-must if ['] lfb-blank-goal. lfa-e-tac-no-intro lfb-failed then
  lfa-e-tac-meta lf-tac-fail ;
: lfb-reduced ( t -- t' )
  lf-whnf-core lf-tac-must dup lf-term-pi? if exit then dup lfb-no-binder ;
: lfb-binder ( t -- t' )
  dup lfb-binding? if exit then lf-instantiate-mvars lf-tac-must
  dup lfb-binding? if exit then lfb-reduced ;
\ Not supported yet: a let, the name rfl, a binder not known explicit.
: lfb-explicit? ( pi -- flag )
  lf-pres-binder@ if nip lf-binder-default = else false then ;
: lfb-plain? ( pi -- flag ) dup lf-let? if drop false else lfb-explicit? then ;
: lfb-rfl? ( name -- flag ) dup if s" rfl" lfa-intern = else drop false then ;
: lfb-later? ( pi given -- flag ) lfb-rfl? swap lfb-plain? 0= or ;
\ The name given, or for _ the binder's own (a when it has none),
\ inaccessible; the binder known explicit.
: lfb-own ( pi -- name ) lf-tac-binder drop ?dup 0= if s" a" lfa-intern then ;
: lfb-named ( pi given -- name flags )
  ?dup if nip 0 exit then lfb-own lf-local-inaccessible ;
: lfb-plain ( given -- given )
  tb tb-pi @ over lfb-later? if lfa-e-tac-form lf-tac-fail then ;
\ The hypothesis: its domain, name, free variable and local.
: lfb-dom ( -- ) tb tb-pi @ lf-term-first@ lf-meta-head-beta lf-tac-must tb tb-dom ! ;
: lfb-name! ( given -- ) tb tb-pi @ swap lfb-named tb tb-flags ! tb tb-name ! ;
: lfb-hyp ( -- view )
  tb tb-dom @ tb tb-name @ tb tb-flags @ lf-local-decl-new swap tb tb-x ! ;
: lfb-body ( -- body )
  tb tb-pi @ lf-term-second@ tb tb-x @ lf-meta-instantiate1 lf-tac-must
  lf-meta-head-beta lf-tac-must ;
: lfb-new ( body view -- )
  >r tb tb-goal @ lf-goal-tag r> lf-goal-new lf-tac-must tb tb-new ! ;
\ fun x => ?n x: mkLambdaFVars [x] of the new goal in its context.
: lfb-closed ( -- value ) tb tb-new @ tb tb-x 1 lf-mk-lambda-fvars ;
: lfb-value ( -- value ) tb tb-new @ ['] lfb-closed lf-with-goal ;
: lfb-assigned ( value -- ) tb tb-goal @ swap lf-mvar-assign lf-tac-must ;
: lfb-replaced ( -- ) 0 tb tb-new @ run-push lf-tac-must lf-replace-main lf-tac-must ;
: lfb-introduced ( -- )
  lfb-hyp lfb-body swap lfb-new lfb-value lfb-assigned lfb-replaced ;
: lfb-intro ( i -- )
  0 lf-tac-arg tb tb-want @ lfb-binder tb tb-pi !
  lfb-plain lfb-dom lfb-name! lfb-introduced ;
: lfb-w-intro ( i -- ) ['] lfb-intro lf-tac-step-run ;
\ For an alternative's fields (tactic-induction.fs, Lean's introN): the
\ main goal's first binder introduced as given (0: its own name,
\ inaccessible), of the kind the eliminator's declared type gives, never
\ read from the goal's node (S2_INTERFACE 4).
: lfb-kind! ( kind -- ) tb tb-flags @ or tb tb-flags ! ;
: lfb-intro-as ( given kind i -- )
  drop tb tb-want @ lfb-binder tb tb-pi ! swap lfb-name! lfb-kind! lfb-dom
    lfb-introduced ;
: lf-tac-intro-as ( given kind i -- ) ['] lfb-intro-as lf-tac-step-run ;

\ ---- t by-exact.
: lfb-opaque-free ( t -- ) ['] lfb-opaque? lfb-holds? if lfa-e-tac-meta lf-tac-fail then ;
: lfb-elaborated ( i -- )
  0 lf-tac-arg tb tb-want @ false lf-tac-elab lf-tac-must tb tb-term ! ;
: lfb-typed ( -- ) tb tb-term @ lf-infer lf-tac-must tb tb-type ! ;
: lfb-guarded ( -- ) tb tb-type @ lfb-opaque-free tb tb-want @ lfb-opaque-free ;
\ Lean's throwTypeMismatchError: the term, its type, the type expected.
: lfb-mismatch. ( x -- outcome )
  drop tb tb-term @ tb tb-type @ tb tb-want @ lf-has-type-but-expected. ;
: lfb-matched ( -- )
  tb tb-type @ tb tb-want @ lf-tac-defeq lf-tac-must
  0= if ['] lfb-mismatch. lfa-e-tac-mismatch lfb-failed then ;
: lfb-value-now ( -- e ) tb tb-term @ lf-instantiate-mvars lf-tac-must ;
: lfb-fresh-free ( e -- e )
  dup tb tb-from @ ['] lfb-new? lfb-holds-with? if lfa-e-tac-unassigned lf-tac-fail then ;
: lfb-holes-free ( e -- e )
  dup ['] lf-mvar-open? lfb-holds? if lfa-e-tac-meta lf-tac-fail then ;
\ Lean's checkedAssign: the occurs check, the free variables in scope.
: lfb-occurs. ( -- outcome )
  s\" \nthis is often due to an occurs-check failure" lf-pp-emit outcome-ok ;
: lfb-term-framed. ( xt -- outcome ) tb tb-term @ swap lf-tac-framed. ;
: lfb-assign. ( x -- outcome ) drop ['] lfb-occurs. lfb-term-framed. ;
: lfb-unassignable ( -- ) ['] lfb-assign. lfa-e-tac-assign lfb-failed ;
: lfb-in-scope ( e -- e )
  dup tb tb-view @ ['] lfb-outside? lfb-holds-with? if lfb-unassignable then ;
: lfb-close ( e -- )
  tb tb-goal @ swap lf-mvar-assign dup outcome-invalid = if drop lfb-unassignable then
  lf-tac-must ;
: lfb-exact ( i -- )
  lfb-elaborated lfb-typed lfb-guarded lfb-matched lfb-value-now lfb-fresh-free
  lfb-holes-free lfb-in-scope lfb-close lf-tac-pop-main ;
: lfb-w-exact ( i -- ) ['] lfb-exact lf-tac-step-run ;

\ ---- by-rfl.
: lfb-target ( -- t )
  tb tb-want @ lf-instantiate-mvars lf-tac-must lf-whnf-core lf-tac-must ;
: lfb-inst ( t -- t' ) lf-instantiate-mvars lf-tac-must ;
: lfb-sides ( t -- ) lf-eq? drop lfb-inst tb tb-type ! lfb-inst tb tb-term ! drop ;
\ applyRfl's message: the two sides, then the goal.
: lfb-rhs. ( -- outcome )
  s\" \nis not definitionally equal to the right-hand side\n" tb tb-type @ lf-tac-line. ;
: lfb-rfl. ( x -- outcome ) drop ['] lfb-rhs. lfb-term-framed. ;
: lfb-sides-hold? ( -- flag )
  tb tb-term @ ['] lf-mvar-open? lfb-holds? tb tb-type @ ['] lf-mvar-open? lfb-holds? or ;
: lfb-unequal ( -- )
  lfb-sides-hold? if lfa-e-tac-meta lf-tac-fail then
  ['] lfb-rfl. lfa-e-tac-rfl lfb-failed ;
\ @Eq.refl.{u} α lhs, u and α those of the goal's Eq (Refl.lean:25:
\ mkConst Eq.refl us, mkApp2).
: lfb-refl-const ( eq -- f )
  lf-meta-head s" Eq.refl" lfa-intern swap lf-const-levels lf-mk-const-id ;
: lfb-alpha ( t -- α ) lf-eq? drop 2drop ;
: lfb-refl ( t -- term ) dup lfb-refl-const swap lfb-alpha tb tb-term @ 2 lf-mk-app-n ;
\ isDefEq at the transparency the step runs at (default; reducible under
\ by-rw[ 's with_reducible).
: lfb-defeq ( t s -- flag outcome )
  ['] lf-meta-defeq lf-defeq-elab lf-defeq-mode lf-meta-with outcome-sane ;
: lfb-decided ( t -- )
  tb tb-term @ tb tb-type @ lfb-defeq lf-tac-must
  if lfb-refl tb tb-goal @ swap lf-mvar-assign lf-tac-must else drop lfb-unequal then ;
: lfb-eq? ( t -- flag ) lf-eq? dup if >r 2drop drop r> then ;
: lfb-rfl ( i -- )
  drop lfb-target dup lfb-eq? 0= if drop lfa-e-tac-meta lf-tac-fail then
  dup lfb-sides lfb-decided lf-tac-pop-main ;
: lfb-w-rfl ( i -- ) ['] lfb-rfl lf-tac-step-run ;

' lfb-w-intro tac-k-intro lf-tactic-action!
' lfb-w-exact tac-k-exact lf-tactic-action!
' lfb-w-rfl tac-k-rfl lf-tactic-action!
base !   \ the BASE this file was loaded with
