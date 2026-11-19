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
\   with Lean's text (the term and both types). Lean compares with
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
\ Words: lf-tac-elab ( node expected postpone? -- term outcome ), a
\ deferred word front/elab-decl.fs sets (Lean's Tactic.elabTerm:
\ Term.elabTerm against expected, a negative one for none, the synthetic
\ metavariables synthesized, postponing when postpone? is true, Lean's
\ mayPostpone, the result instantiated; exact passes false); error 71
\ without front/elab-decl.fs;
\ lf-tac-defeq ( t s -- flag outcome ), the tactics' isDefEq;
\ lf-tac-indented. ( term -- outcome ), a term of a message, instantiated
\ and indented on its own line (Lean's indentExpr), to the message's sink;
\ For S2's tactics (tactic-rewrite.fs, tactic-induction.fs):
\ lf-tac-step-run ( i*x i xt -- j*x ) xt in a new step record, the main
\ goal's fields in tb and its context current; lf-tac-rfl-reducible
\ ( i -- ) rfl at reducible transparency (by-rfl decides at the
\ transparency it runs at); lf-tac-intro-as ( given kind i -- ) the main
\ goal's first binder introduced as given (0: its own name, inaccessible)
\ with the kind given (introN for an alternative's fields); lf-tac-only
\ ( goal -- ) setGoals [goal] (an alternative's or a case's); lf-tac-args#
\ ( i -- n ) how many arguments step i has (names, rules); and the
\ message and term helpers lf-tac-line., lf-tac-goal., lf-tac-failed,
\ lf-tac-inline, lf-tac-inline., lf-tac-eq?, lf-tac-hole?,
\ lf-tac-binder ( pi -- name kind ).
\ Terms are built by the tactic library (app-builder.fs, telescope.fs),
\ whose failures the runner makes authoring errors (tactic-run.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: tb, the running step record's fields (tactic-run.fs's
\ lf-tac-record, review fe1g3 M2: the step's goal, terms and context, the
\ metavariable count when the step began) in the checker context (ADR
\ 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/let-terms.fs
require ../core/constant-references.fs
require ../core/mvar-leaves.fs
require ../present/binder-table.fs
require ../present/term-printer.fs
require ../present/print-job.fs
require ../author/errors.fs
require ../author/declarations.fs
require ./term-find.fs
require ./mvars.fs
require ./lctx-views.fs
require ./goals.fs
require ./goal-print.fs
require ./instantiate.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./term-eqv.fs
require ./whnf.fs
require ./infer.fs
require ./defeq.fs
require ./defeq-delta.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./meta-must.fs
require ./app-builder.fs
require ./telescope.fs

begin-structure /tb
  field: tb-goal        \ the goal the step works on
  field: tb-view        \ its context
  field: tb-term        \ exact's term, or rfl's left side
  field: tb-type        \ its type, or rfl's right side
  field: tb-want        \ the goal's type
  field: tb-sort        \ a type mismatch message: the term's type's type
  field: tb-want-sort   \ and the goal's type's type
  field: tb-from        \ the metavariable count when the step began
  field: tb-pi          \ intro's binder
  field: tb-dom         \ its domain, head-beta reduced
  field: tb-x           \ its free variable
  field: tb-name        \ the hypothesis's name
  field: tb-flags       \ and its local's flags
  field: tb-new         \ the goal in its place
end-structure
/tb lf-tac-work-cells cells >
[if] .( tactic-basic.fs: tb is wider than a step record) cr abort [then]
\ The step's fields: in the running step record (tactic-run.fs's
\ lf-tac-record, review fe1g3 M2), else the last one's.
: tb ( -- addr ) lf-tac-record ;

\ ---- Hooks.
defer lf-tac-elab ( node expected postpone? -- term outcome )
: lfb-unelaborated ( node expected postpone? -- term outcome )
  2drop drop lfa-e-elaborate lf-tac-fail -1 outcome-unsupported ;
' lfb-unelaborated is lf-tac-elab
\ isDefEq in the elaborator's configuration at default transparency
\ (lf-meta-with: defeq's own configuration and mode put back however it
\ ends), an internal code such as the stuck signal made invalid
\ (outcome-sane).
: lf-tac-defeq ( t s -- flag outcome )
  ['] lf-meta-defeq lf-defeq-elab lf-tr-default lf-meta-with outcome-sane ;

\ ---- Leaves (front/term-find.fs's lf-term-holds?).
\ The tests: a metavariable not assigned (a delayed one counts as
\ assigned, as Lean's isAssigned and isDelayedAssigned together), one
\ also synthetic opaque, one also new; a free variable outside the
\ step's context.
: lfb-open? ( mvar -- flag )
  dup lf-mvar-delayed if 2drop 2drop false exit then lf-goal-assigned? 0= ;
: lfb-hole? ( leaf -- flag ) dup lf-mvar? if lfb-open? else drop false then ;
: lfb-opaque? ( leaf -- flag )
  dup lfb-hole? if lf-mvar-kind drop mv-opaque = else drop false then ;
: lfb-new? ( leaf -- flag )
  dup lfb-hole? if lf-term-first@ tb tb-from @ < 0= else drop false then ;
: lfb-seen? ( fvar -- flag ) tb tb-view @ swap lf-view-find dup if nip then ;
: lfb-outside? ( leaf -- flag )
  dup lf-term-tag@ lf-tag-fvar = if lfb-seen? 0= else drop false then ;
: lfb-holds? ( term xt -- flag ) lf-term-holds? lf-tac-must ;
: lf-tac-hole? ( leaf -- flag ) lfb-hole? ;

\ ---- The step's goal and context (Lean's withMainContext, meta-must.fs's
\ lf-with-goal); the row's action leaves the current context as it found
\ it, also when it fails.
: lfb-start ( goal -- goal )
  dup tb tb-goal ! dup lf-mvar-type drop tb tb-want ! dup lf-mvar-view drop tb tb-view !
  lf-mvar-count tb tb-from ! ;
\ A step's action xt ( i*x i -- j*x ) runs in a new step record.
: lfb-run ( i*x xt i -- j*x ) swap lf-tac-main lfb-start swap lf-with-goal ;
: lfb-step ( i*x i xt -- j*x ) swap ['] lfb-run lf-tac-in-record ;
\ For the other tactics: the same, the step's goal and context in tb.
: lf-tac-step-run ( i*x i xt -- j*x ) lfb-step ;
: lfb-popped ( -- ) 0 lf-replace-main lf-tac-must ;
\ setGoals [goal]: the goal list that goal alone (an alternative's or a
\ case's).
: lf-tac-only ( goal -- ) 0 swap run-push lf-tac-must lf-goals! lf-tac-must ;
\ A pi's binder name and kind: the presentation table's, else its input
\ record's, else the anonymous name, explicit.
: lf-tac-binder ( pi -- name kind )
  dup lf-pres-binder@ if 2>r drop 2r> exit then
  lf-term-input-binder@ 0= if 0 lf-binder-default then ;
: lfb-arg ( i -- x ) lf-tactic-step tac-first @ lf-tactic-arg drop ;
: lf-tac-args# ( i -- n ) lf-tactic-step tac-count @ ;   \ step i's arguments

\ ---- Messages: terms printed as goals print them (notation on, the
\ printer's flag put back however printing ends), indented as Lean's
\ indentExpr; a tactic error's goal after a blank line.
\ A term of a message, in Lean's notation, to the message's sink.
: lfb-noted ( term -- outcome ) lf-print-sink true lf-print-to ;
: lfb-term. ( term -- outcome ) lf-instantiate-mvars ok-then? if lfb-noted then ;
: lf-tac-indented. ( term -- outcome ) s"   " lf-pp-emit lfb-term. ;
: lfb-line. ( c-addr u term -- outcome ) >r lf-pp-emit r> lf-tac-indented. ;
: lfb-the-goal. ( -- outcome ) s\" \n\n" lf-pp-emit tb tb-goal @ lf-goal-print ;
\ A goal after a line break: as the whole detail, the goal after the
\ message's line and a blank one (Lean's throwTacticEx with no message:
\ "Tactic `t` failed\n\ngoal"); it needs no step record.
: lf-tac-goal-of. ( goal -- outcome ) s\" \n" lf-pp-emit lf-goal-print ;
: lfb-blank-goal. ( x -- outcome ) drop tb tb-goal @ lf-tac-goal-of. ;
: lfb-failed ( xt code -- ) >r 0 swap lf-tac-detail r> lf-tac-stop ;
\ For the other tactics' messages (tactic-rewrite.fs, tactic-induction.fs):
\ a label and a term on the next line, the goal after a blank line, an
\ error whose detail xt ( x -- outcome ) prints, at the step running.
: lf-tac-line. ( c-addr u term -- outcome ) lfb-line. ;
: lf-tac-goal. ( -- outcome ) lfb-the-goal. ;
: lf-tac-failed ( xt code -- ) lfb-failed ;
\ A detail xt ( x -- outcome ) prints that ends the message's own line.
: lf-tac-inline ( x xt -- ) lf-author-code if 2drop exit then lf-tac-detail lfa-inline ;

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
: lfb-local ( fvar -- local ) tb tb-name @ tb tb-flags @ lf-local-new lf-tac-must ;
: lfb-hyp ( -- local ) tb tb-dom @ lf-lctx-local lf-tac-must dup tb tb-x ! lfb-local ;
: lfb-view ( local -- view ) tb tb-view @ swap lf-view-push lf-tac-must ;
: lfb-body ( -- body )
  tb tb-pi @ lf-term-second@ tb tb-x @ lf-meta-instantiate1 lf-tac-must
  lf-meta-head-beta lf-tac-must ;
: lfb-new ( body view -- )
  >r tb tb-goal @ lf-mvar-tag drop r> lf-goal-new lf-tac-must tb tb-new ! ;
\ fun x => ?n x: mkLambdaFVars [x] of the new goal in its context.
: lfb-closed ( -- value ) tb tb-new @ tb tb-x 1 lf-mk-lambda-fvars ;
: lfb-value ( -- value ) tb tb-new @ ['] lfb-closed lf-with-goal ;
: lfb-assigned ( value -- ) tb tb-goal @ swap lf-mvar-assign lf-tac-must ;
: lfb-replaced ( -- ) 0 tb tb-new @ run-push lf-tac-must lf-replace-main lf-tac-must ;
: lfb-introduced ( -- )
  lfb-hyp lfb-view lfb-body swap lfb-new lfb-value lfb-assigned lfb-replaced ;
: lfb-intro ( i -- )
  lfb-arg tb tb-want @ lfb-binder tb tb-pi ! lfb-plain lfb-dom lfb-name! lfb-introduced ;
: lfb-w-intro ( i -- ) ['] lfb-intro lfb-step ;
\ For an alternative's fields (tactic-induction.fs, Lean's introN): the
\ main goal's first binder introduced as given (0: its own name,
\ inaccessible), of the kind the eliminator's declared type gives, never
\ read from the goal's node (S2_INTERFACE 4).
: lfb-kind! ( kind -- ) tb tb-flags @ or tb tb-flags ! ;
: lfb-intro-as ( given kind i -- )
  drop tb tb-want @ lfb-binder tb tb-pi ! swap lfb-name! lfb-kind! lfb-dom
    lfb-introduced ;
: lf-tac-intro-as ( given kind i -- ) ['] lfb-intro-as lfb-step ;

\ ---- t by-exact.
: lfb-opaque-free ( t -- ) ['] lfb-opaque? lfb-holds? if lfa-e-tac-meta lf-tac-fail then ;
: lfb-elaborated ( i -- )
  lfb-arg tb tb-want @ false lf-tac-elab lf-tac-must tb tb-term ! ;
: lfb-typed ( -- ) tb tb-term @ lf-infer lf-tac-must tb tb-type ! ;
: lfb-guarded ( -- ) tb tb-type @ lfb-opaque-free tb tb-want @ lfb-opaque-free ;
\ Lean's throwTypeMismatchError: the term, its type, the type expected.
\ (mkHasTypeButIsExpectedMsg: when the two types' own types are not
\ defeq, both are named, "of sort"; when either cannot be inferred, not.)
: lfb-sort ( t -- sort true | false ) lf-infer ok? dup 0= if nip then ;
: lfb-sorts ( -- flag )
  tb tb-type @ lfb-sort 0= if false exit then tb tb-sort !
  tb tb-want @ lfb-sort 0= if false exit then tb tb-want-sort ! true ;
: lfb-sorted? ( -- flag )
  lfb-sorts 0= if false exit then
  tb tb-sort @ tb tb-want-sort @ lf-tac-defeq ok? if 0= else drop false then ;
: lfb-inline. ( term -- outcome ) s" `" lf-pp-emit lfb-term. s" `" lf-pp-emit ;
: lf-tac-inline. ( term -- outcome ) lfb-inline. ;   \ `term`, as Lean's inlineExpr
: lfb-has. ( -- outcome ) s\" \nhas type\n" tb tb-type @ lfb-line. ;
: lfb-but. ( -- outcome ) s\" \nbut is expected to have type\n" tb tb-want @ lfb-line. ;
: lfb-of. ( -- outcome ) s\" \nof sort " lf-pp-emit tb tb-sort @ lfb-inline. ;
: lfb-but-sort. ( -- outcome )
  s"  but is expected to have type" lf-pp-emit s\" \n" tb tb-want @ lfb-line. ;
: lfb-of-want. ( -- outcome ) s\" \nof sort " lf-pp-emit tb tb-want-sort @ lfb-inline. ;
: lfb-plain. ( -- outcome ) lfb-has. ['] lfb-but. ok-and ;
: lfb-sorted. ( -- outcome )
  lfb-has. ['] lfb-of. ok-and ['] lfb-but-sort. ok-and ['] lfb-of-want. ok-and ;
: lfb-types. ( -- outcome ) lfb-sorted? if lfb-sorted. else lfb-plain. then ;
: lfb-mismatch. ( x -- outcome )
  drop tb tb-term @ lf-tac-indented. ['] lfb-types. ok-and ;
: lfb-matched ( -- )
  tb tb-type @ tb tb-want @ lf-tac-defeq lf-tac-must
  0= if ['] lfb-mismatch. lfa-e-tac-mismatch lfb-failed then ;
: lfb-value-now ( -- e ) tb tb-term @ lf-instantiate-mvars lf-tac-must ;
: lfb-fresh-free ( e -- e )
  dup ['] lfb-new? lfb-holds? if lfa-e-tac-unassigned lf-tac-fail then ;
: lfb-holes-free ( e -- e )
  dup ['] lfb-hole? lfb-holds? if lfa-e-tac-meta lf-tac-fail then ;
\ Lean's checkedAssign: the occurs check, the free variables in scope.
: lfb-occurs. ( -- outcome )
  s\" \nthis is often due to an occurs-check failure" lf-pp-emit outcome-ok ;
: lfb-assign. ( x -- outcome )
  drop tb tb-term @ lf-tac-indented. ['] lfb-occurs. ok-and ['] lfb-the-goal. ok-and ;
: lfb-unassignable ( -- ) ['] lfb-assign. lfa-e-tac-assign lfb-failed ;
: lfb-in-scope ( e -- e ) dup ['] lfb-outside? lfb-holds? if lfb-unassignable then ;
: lfb-close ( e -- )
  tb tb-goal @ swap lf-mvar-assign dup outcome-invalid = if drop lfb-unassignable then
  lf-tac-must ;
: lfb-exact ( i -- )
  lfb-elaborated lfb-typed lfb-guarded lfb-matched lfb-value-now lfb-fresh-free
  lfb-holes-free lfb-in-scope lfb-close lfb-popped ;
: lfb-w-exact ( i -- ) ['] lfb-exact lfb-step ;

\ ---- by-rfl.
\ Eq applied to three arguments.
: lfb-eq? ( t -- flag ) 3 s" Eq" lf-meta-app-of? ;
: lf-tac-eq? ( t -- flag ) lfb-eq? ;
: lfb-target ( -- t )
  tb tb-want @ lf-instantiate-mvars lf-tac-must lf-whnf-core lf-tac-must ;
: lfb-inst ( t -- t' ) lf-instantiate-mvars lf-tac-must ;
: lfb-sides ( t -- ) lf-eq? drop lfb-inst tb tb-type ! lfb-inst tb tb-term ! drop ;
\ applyRfl's message: the two sides, then the goal.
: lfb-rhs. ( -- outcome )
  s\" \nis not definitionally equal to the right-hand side\n" tb tb-type @ lfb-line. ;
: lfb-rfl. ( x -- outcome )
  drop tb tb-term @ lf-tac-indented. ['] lfb-rhs. ok-and ['] lfb-the-goal. ok-and ;
: lfb-sides-hold? ( -- flag )
  tb tb-term @ ['] lfb-hole? lfb-holds? tb tb-type @ ['] lfb-hole? lfb-holds? or ;
: lfb-unequal ( -- )
  lfb-sides-hold? if lfa-e-tac-meta lf-tac-fail then
  ['] lfb-rfl. lfa-e-tac-rfl lfb-failed ;
\ @Eq.refl.{u} α lhs, u and α those of the goal's Eq (Refl.lean:25:
\ mkConst Eq.refl us, mkApp2).
: lfb-level ( t -- level ) lf-meta-head-args drop lf-const-slot lf-cref-pairs drop
  0 lf-cref-pair@ drop ;
: lfb-alpha ( t -- α ) lf-eq? drop 2drop ;
: lfb-refl ( t -- term )
  dup lfb-level >r s" Eq.refl" r> lf-mk-const1 swap lfb-alpha tb tb-term @ 2 lf-mk-app-n ;
\ isDefEq at the transparency the step runs at (default; reducible under
\ by-rw[ 's with_reducible).
: lfb-defeq ( t s -- flag outcome )
  ['] lf-meta-defeq lf-defeq-elab lf-defeq-mode lf-meta-with outcome-sane ;
: lfb-decided ( t -- )
  tb tb-term @ tb tb-type @ lfb-defeq lf-tac-must
  if lfb-refl tb tb-goal @ swap lf-mvar-assign lf-tac-must else drop lfb-unequal then ;
: lfb-rfl ( i -- )
  drop lfb-target dup lfb-eq? 0= if drop lfa-e-tac-meta lf-tac-fail then
  dup lfb-sides lfb-decided lfb-popped ;
: lfb-w-rfl ( i -- ) ['] lfb-rfl lfb-step ;
\ with_reducible rfl (by-rw[ 's closing step, Init/Tactics.lean's rw).
: lf-tac-rfl-reducible ( i -- ) ['] lfb-w-rfl lf-tr-reducible lf-meta-at ;

' lfb-w-intro tac-k-intro lf-tactic-action!
' lfb-w-exact tac-k-exact lf-tactic-action!
' lfb-w-rfl tac-k-rfl lf-tactic-action!
base !   \ the BASE this file was loaded with
