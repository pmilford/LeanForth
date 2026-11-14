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
\   the new goal (Lean's mkLambdaFVars through elimMVar). No pi: error 94
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
\ Term.elabTerm against expected, 0 or -1 for none, the synthetic
\ metavariables synthesized, postponing when postpone? is true, Lean's
\ mayPostpone, the result instantiated; exact passes false); until then
\ error 71;
\ lf-tac-defeq ( t s -- flag outcome ), the tactics' isDefEq;
\ lf-tac-holds? ( term xt -- flag outcome ), whether a term holds a leaf
\ xt ( leaf -- flag ) accepts (heap stacks of dag-walk.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the record tb (the step's goal, terms and context, the leaf test
\ and walk, the metavariable count when the step began) in the checker
\ context (ADR 0009). Loads in decimal whatever BASE is, then restores it.

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
require ./dag-walk.fs
require ./mvars.fs
require ./lctx-views.fs
require ./goals.fs
require ./goal-print.fs
require ./instantiate.fs
require ./meta-env.fs
require ./whnf.fs
require ./infer.fs
require ./defeq.fs
require ./tactic-syntax.fs
require ./tactic-run.fs

100000 constant lfb-print-fuel     \ printer fuel for each term of a message
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
  field: tb-test        \ the leaf test of lf-tac-holds? ( leaf -- flag )
  /dw +field tb-walk    \ and its walk
end-structure
/tb context-record: tb

\ ---- Hooks.
defer lf-tac-elab ( node expected postpone? -- term outcome )
: lfb-unelaborated ( node expected postpone? -- term outcome )
  2drop drop lfa-e-elaborate lf-tac-fail -1 outcome-unsupported ;
' lfb-unelaborated is lf-tac-elab
\ isDefEq in the elaborator's configuration at default transparency;
\ defeq's own configuration and mode put back however it ends, and an
\ internal code such as the stuck signal made invalid (outcome-sane).
: lfb-elab-defeq ( t s -- flag outcome )
  lf-defeq-elab lf-defeq-flags! lf-tr-default lf-defeq-mode! lf-meta-defeq ;
: lfb-defeq-set! ( flags mode -- ) lf-defeq-mode! lf-defeq-flags! ;
: lf-tac-defeq ( t s -- flag outcome )
  lf-defeq-flags lf-defeq-mode 2>r ['] lfb-elab-defeq catch 2r> lfb-defeq-set! throw
  outcome-sane ;

\ ---- Leaves: a bottom-up walk (dag-walk.fs) whose image is 1 where a
\ leaf passes the test.
: lfb-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: lfb-pending ( node walk -- child true | false )
  over lf-term-binary? 0= if 2drop false exit then
  over lf-term-first@ over lfb-undone if nip nip true exit then
  swap lf-term-second@ swap lfb-undone ;
: lfb-images ( node walk -- i1 i2 )
  over lf-term-first@ over dw-image >r swap lf-term-second@ swap dw-image r> swap ;
: lfb-leaf ( leaf -- 0|1 ) tb tb-test @ execute 1 and ;
: lfb-build ( node walk -- 0|1 )
  over lf-term-binary? if lfb-images or else drop lfb-leaf then ;
: lfb-walk ( -- walk )
  tb tb-walk ['] lfb-build over dw-build ! ['] lfb-pending over dw-pending !
  lf-term-base lf-term-count @ + over dw-size ! ;
: lf-tac-holds? ( term xt -- flag outcome ) tb tb-test ! lfb-walk dw-run swap 0<> swap ;
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
: lfb-holds? ( term xt -- flag ) lf-tac-holds? lf-tac-must ;

\ ---- The step's goal and context (Lean's withMainContext); the row's
\ action leaves the current context as it found it, also when it fails.
: lfb-start ( goal -- )
  dup tb tb-goal ! dup lf-mvar-type drop tb tb-want ! lf-mvar-view drop
  dup tb tb-view ! lf-mctx-view! lf-mvar-count tb tb-from ! ;
: lfb-step ( i xt -- )
  lf-mctx-view >r lf-tac-main lfb-start catch r> lf-mctx-view! throw ;
: lfb-popped ( -- ) 0 lf-replace-main lf-tac-must ;
: lfb-made ( flag -- ) 0= if outcome-full lf-tac-must then ;
: lfb-arg ( i -- x ) lf-tactic-step tac-first @ lf-tactic-arg drop ;

\ ---- Messages: terms printed as goals print them (notation on, the
\ printer's flag put back however printing ends), indented as Lean's
\ indentExpr; a tactic error's goal after a blank line.
: lfb-noting ( term -- outcome ) true lf-print-notation! lfb-print-fuel lf-print-term ;
: lfb-noted ( term -- outcome )
  lf-print-notation? >r ['] lfb-noting catch r> lf-print-notation! throw ;
: lfb-term. ( term -- outcome ) lf-instantiate-mvars ok-then? if lfb-noted then ;
: lfb-indented. ( term -- outcome ) s"   " lf-pp-emit lfb-term. ;
: lfb-line. ( c-addr u term -- outcome ) >r lf-pp-emit r> lfb-indented. ;
: lfb-the-goal. ( -- outcome ) s\" \n\n" lf-pp-emit tb tb-goal @ lf-goal-print ;
: lfb-blank-goal. ( x -- outcome ) drop s\" \n" lf-pp-emit tb tb-goal @ lf-goal-print ;
: lfb-failed ( xt code -- ) >r 0 swap lf-tac-detail r> lf-tac-stop ;

\ ---- by-intro: NAME.
: lfb-binding? ( t -- flag ) dup lf-term-pi? swap lf-let? or ;
: lfb-no-binder ( t -- )
  lf-whnf-firm? if ['] lfb-blank-goal. lfa-e-tac-no-intro lfb-failed then
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
: lfb-own ( pi -- name ) lf-pres-binder@ 2drop ?dup 0= if s" a" lfa-intern then ;
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
\ Binders over the hypothesis, named as its local (Lean's mkForallFVars
\ and mkLambdaFVars of one variable).
: lfb-binder-kind ( -- kind ) tb tb-flags @ lf-local-binder-mask and ;
: lfb-name-on ( t -- t )
  dup tb tb-name @ lfb-binder-kind lf-pres-binder! lf-tac-must ;
: lfb-abstract ( e -- e' ) tb tb-x 1 lf-meta-abstract lf-tac-must ;
: lfb-over ( body xt -- t )
  >r lfb-abstract tb tb-dom @ swap r> execute lfb-made lfb-name-on ;
\ ?n : (x : domain) -> body in the old context, delayed [x] := the new goal.
: lfb-aux-type ( -- type ) tb tb-new @ lf-mvar-type drop ['] lf-term-pi lfb-over ;
: lfb-aux ( -- mvar ) lfb-aux-type mv-opaque tb tb-view @ lf-mvar-new-at lf-tac-must ;
: lfb-delayed ( mvar -- )
  tb tb-x @ lf-delay-fvar lf-tac-must tb tb-new @ 1 lf-mvar-delay lf-tac-must ;
: lfb-value ( mvar -- value ) tb tb-x @ lf-term-app lfb-made ['] lf-term-lam lfb-over ;
: lfb-assigned ( value -- ) tb tb-goal @ swap lf-mvar-assign lf-tac-must ;
: lfb-replaced ( -- ) 0 tb tb-new @ run-push lf-tac-must lf-replace-main lf-tac-must ;
: lfb-introduced ( -- )
  lfb-hyp lfb-view lfb-body swap lfb-new lfb-aux dup lfb-delayed lfb-value lfb-assigned
  lfb-replaced ;
: lfb-intro ( i -- )
  lfb-arg tb tb-want @ lfb-binder tb tb-pi ! lfb-plain lfb-dom lfb-name! lfb-introduced ;
: lfb-w-intro ( i -- ) ['] lfb-intro lfb-step ;

\ ---- t by-exact.
: lfb-opaque-free ( t -- ) ['] lfb-opaque? lfb-holds? if lfa-e-tac-meta lf-tac-fail then ;
: lfb-elaborated ( i -- ) lfb-arg tb tb-want @ false lf-tac-elab lf-tac-must tb tb-term ! ;
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
: lfb-mismatch. ( x -- outcome ) drop tb tb-term @ lfb-indented. ['] lfb-types. ok-and ;
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
  drop tb tb-term @ lfb-indented. ['] lfb-occurs. ok-and ['] lfb-the-goal. ok-and ;
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
: lfb-spine ( t -- head n )
  0 swap begin dup lf-term-app? while lf-term-first@ swap 1+ swap repeat swap ;
: lfb-const-name ( c -- name ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: lfb-eq-head? ( head -- flag )
  dup lf-term-const? 0= if drop false exit then
  lfb-const-name s" Eq" lfa-intern = ;
: lfb-eq? ( t -- flag ) lfb-spine 3 = swap lfb-eq-head? and ;
: lfb-target ( -- t )
  tb tb-want @ lf-instantiate-mvars lf-tac-must lf-whnf-core lf-tac-must ;
: lfb-side ( t -- t' ) lf-term-second@ lf-instantiate-mvars lf-tac-must ;
: lfb-sides ( t -- ) dup lfb-side tb tb-type ! lf-term-first@ lfb-side tb tb-term ! ;
\ applyRfl's message: the two sides, then the goal.
: lfb-rhs. ( -- outcome )
  s\" \nis not definitionally equal to the right-hand side\n" tb tb-type @ lfb-line. ;
: lfb-rfl. ( x -- outcome )
  drop tb tb-term @ lfb-indented. ['] lfb-rhs. ok-and ['] lfb-the-goal. ok-and ;
: lfb-sides-hold? ( -- flag )
  tb tb-term @ ['] lfb-hole? lfb-holds? tb tb-type @ ['] lfb-hole? lfb-holds? or ;
: lfb-unequal ( -- )
  lfb-sides-hold? if lfa-e-tac-meta lf-tac-fail then
  ['] lfb-rfl. lfa-e-tac-rfl lfb-failed ;
\ @Eq.refl.{u} α lhs, u and α those of the goal's Eq.
: lfb-level ( t -- level ) lfb-spine drop lf-term-first@ lf-cref-slot lf-cref-pairs drop
  0 lf-cref-pair@ drop ;
: lfb-alpha ( t -- α ) lf-term-first@ lf-term-first@ lf-term-second@ ;
: lfb-refl ( t -- term )
  dup lfb-level s" Eq.refl" lf-tac-const1 swap lfb-alpha lf-tac-app
  tb tb-term @ lf-tac-app ;
: lfb-decided ( t -- )
  tb tb-term @ tb tb-type @ lf-tac-defeq lf-tac-must
  if lfb-refl tb tb-goal @ swap lf-mvar-assign lf-tac-must else drop lfb-unequal then ;
: lfb-rfl ( i -- )
  drop lfb-target dup lfb-eq? 0= if drop lfa-e-tac-meta lf-tac-fail then
  dup lfb-sides lfb-decided lfb-popped ;
: lfb-w-rfl ( i -- ) ['] lfb-rfl lfb-step ;

' lfb-w-intro tac-k-intro lf-tactic-action!
' lfb-w-exact tac-k-exact lf-tactic-action!
' lfb-w-rfl tac-k-rfl lf-tactic-action!
base !   \ the BASE this file was loaded with
