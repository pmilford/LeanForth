\ Eliminators of the tactic library (docs/design/TACTIC_PLUGINS.md 2.4;
\ plan 9.4.8l-I, commit C4): Lean 4.35.0's Meta/Tactic/ElimInfo.lean
\ (getElimExprInfo :57, getCustomEliminator? :276) and Elab/Tactic/
\ Induction.lean (getInductiveValFromMajor :770, mkElimApp :165,
\ setMotiveArg :249), the goal operations under induction (tactics/
\ induction.fs; cases later). Each failure throws (meta-must.fs), as
\ Lean's do.
\   lf-elim-for ( target induction? -- d )  the eliminator of the target
\       (a free variable; Lean's major premise): the elaboration data's
\       induction eliminator (induction? true; else its cases eliminator)
\       for the head constant of the target's type, instantiated and
\       head-beta reduced (getCustomEliminator?: Nat.recAux for Nat); else
\       the type put through whnf must be an inductive type (error 205,
\       Lean's text with its hints for a proposition or a type universe,
\       then the main goal), neither mutual nor nested (209, Lean's text
\       and its hint), and its recursor C.rec (C.casesOn for induction?
\       false) is the eliminator
\   lf-elim-info ( d -- info )  getElimExprInfo, read from d's declared
\       type: past its pis, the motive applied to one target, both bound
\       variables (an eliminator with index targets: 99); the alternatives
\       are the other explicit binders (their kinds from the declaration's
\       data, lf-menv-kind@: unknown 99), each named as its binder, with as
\       many fields as its domain has pis. info is a run (lib/runs.fs, a
\       value that never changes): d, the binders, the motive's and the
\       target's positions, then name, position and fields per alternative
\   lf-elim-decl ( info -- d ), lf-elim-alts# ( info -- n ),
\   lf-elim-alt-name lf-elim-alt-pos lf-elim-alt-fields ( info k -- x )
\       alternative k's name, binder position and number of fields (ElimAltInfo)
\   lf-elim-alt-kinds ( info k -- addr n )  the kinds of alternative k's
\       fields, from the eliminator's declared type (meta-env.fs's
\       lf-menv-kinds-in: valid until its next call)
\   lf-elim-alt-find ( info name -- k true | false )  the alternative of
\       that name (Lean's alts.findFinIdx?)
\   lf-elim-app ( info target tag -- f alts motive )  mkElimApp in the
\       current context: the eliminator at new level metavariables,
\       applied binder by binder (whnf where no pi is left: 93 when none
\       comes), the motive a new synthetic opaque metavariable; the target,
\       its type defeq the binder's (99 otherwise); an alternative a new
\       goal of the binder's type named tag.NAME (goal.fs's
\       lf-name-append-tag, Lean's appendTag); an implicit binder a natural
\       metavariable (an instance binder: 99); alts the alternatives'
\       goals in order, a run
\   lf-elim-set-motive ( goal motive target -- )  setMotiveArg: fun x =>
\       goal's type with the target abstracted (telescope.fs's
\       lf-mk-lambda-fvars: x named and of the kind of the target's local),
\       its type defeq the motive's (else error 212 with the motive), the
\       motive assigned
\ Errors are thrown as authoring errors at the step running
\ (tactic-run.fs's lf-tac-stop and lf-tac-fail), Meta failures as
\ outcomes (meta-must.fs). Not ported: generalizeVars and index targets
\ (99, plan FE5), mkHasTypeButIsExpectedMsg in 212's text (plan 9.4.8l-I's
\ fidelity commit).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mea-frames and mes-frames (mkElimApp's and setMotiveArg's
\ frames, one per call open, meta-must.fs's lf-with-record, in the
\ checker context, ADR 0009); no other. Loads in decimal whatever BASE
\ is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../core/input.fs
require ../../core/local-context.fs
require ../../present/binder-table.fs
require ../../author/errors.fs
require ../../author/declarations.fs
require ../mvars.fs
require ../goals.fs
require ../instantiate.fs
require ../meta-env.fs
require ../meta-spine.fs
require ../term-eqv.fs
require ../elab-data.fs
require ../whnf.fs
require ../infer.fs
require ../tactic-run.fs
require ../tactic-msg.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ./goal.fs

\ ---- The information: a run of d, the binders, the motive's and the
\ target's positions, then name, position and fields per alternative.
: mel+ ( run x -- run' ) run-push lf-must ;
: lf-elim-decl ( info -- d ) 0 run@ ;
: mel-binders ( info -- n ) 1 run@ ;
: lf-elim-alts# ( info -- n ) run-count 4 - 3 / ;
: mel-alt@ ( info k field -- x ) swap 3 * + 4 + run@ ;
: lf-elim-alt-name ( info k -- name ) 0 mel-alt@ ;
: lf-elim-alt-pos ( info k -- pos ) 1 mel-alt@ ;
: lf-elim-alt-fields ( info k -- n ) 2 mel-alt@ ;
: lf-elim-alt-kinds ( info k -- addr n )
  over lf-elim-decl -rot lf-elim-alt-pos lf-menv-kinds-in ;
: lf-elim-alt-find ( info name -- k true | false )
  over lf-elim-alts# 0 ?do over i lf-elim-alt-name over = if 2drop i true unloop exit then
  loop 2drop false ;

\ ---- getCustomEliminator?: the data's eliminator for the head constant.
: mel-custom ( name induction? -- d true | false )
  swap lf-menv-data-decl 0= if drop false exit then
  swap if elab-induction else elab-cases then elab-eliminator-for 0= if false exit then
  elab-eliminator@ nip lf-menv-of-data lf-must true ;
: mel-custom? ( target induction? -- d true | false )
  swap lf-infer! lf-instantiate! lf-meta-head-beta lf-must lf-meta-head-name
  if swap mel-custom else drop false then ;

\ ---- getInductiveValFromMajor: not an inductive type (205): Lean's text
\ with its hints (majorType.isProp and .isType: Sort 0; a Sort of a succ
\ level), then the main goal.
: mel-succ-sort? ( t -- flag )
  dup lf-tag-symbolic-sort lf-term-tag? 0= if lf-sort? exit then
  lf-term-first@ lf-level-tag@ lf-level-tag-succ = ;
: mel-prop-hint. ( -- )
  s\" \n\nConsider using the 'by_cases' tactic, which does true/false " lf-pp-emit
  s" reasoning for propositions." lf-pp-emit ;
: mel-type-hint. ( -- )
  s\" \n\nType universes are not inductive types, and type-constructor-based " lf-pp-emit
  s" reasoning is not possible. This is a strong limitation. " lf-pp-emit
  s" According to Lean's underlying theory, the only provable " lf-pp-emit
  s" distinguishing feature of types is their cardinalities." lf-pp-emit ;
: mel-sort-hint. ( t -- )
  dup lf-prop? if drop mel-prop-hint. exit then mel-succ-sort? if mel-type-hint. then ;
: mel-explanation. ( -- )
  s\" \n\nExplanation: the `induction` tactic is for constructor-based " lf-pp-emit
  s" reasoning as well as for applying custom induction principles with a " lf-pp-emit
  s" 'using' clause or a registered '@[induction_eliminator]' theorem. " lf-pp-emit ;
: mel-unregistered. ( -- )
  s" The above type neither is an inductive type " lf-pp-emit
  s" nor has a registered theorem." lf-pp-emit ;
: mel-explain. ( t -- outcome )
  mel-explanation. mel-unregistered. mel-sort-hint. outcome-ok ;
: mel-goal. ( -- outcome ) lf-main-goal ok-then? if lf-tac-goal-below. then ;
: mel-major. ( t -- outcome )
  dup lf-tac-indented. dup ok? if drop mel-explain. ['] mel-goal. ok-and else nip then ;
: mel-not-inductive ( t -- )
  ['] mel-major. lf-tac-detail lfa-e-tac-not-inductive lf-tac-stop ;
: mel-inductive ( t -- d true | false )
  lf-meta-head-name 0= if false exit then
  lf-menv-find dup outcome-invalid = if 2drop false exit then
  lf-must dup lf-menv-kind lf-kind-inductive = dup 0= if nip then ;
\ Mutual or nested (209): Lean's text and its hint.
: mel-kind. ( t c-addr u -- outcome )
  s"  `" lf-pp-emit rot lf-meta-head-args drop lf-const-name lf-pp-name
  s" ` because it is " lf-pp-emit lf-pp-emit outcome-ok ;
: mel-mutual. ( t -- outcome ) s" mutually inductive" mel-kind. ;
: mel-nested. ( t -- outcome ) s" a nested inductive type" mel-kind. ;
: mel-hint. ( x -- outcome )
  drop s\" \nHint: Consider using the `cases` tactic instead" lf-pp-emit outcome-ok ;
: mel-unsupported ( t xt -- )
  lf-tac-inline 0 ['] mel-hint. lf-tac-detail lfa-e-tac-mutual lf-tac-stop ;
: mel-simple ( t d -- t d )
  dup lf-menv-data ?dup 0= if lfa-e-tac-meta lf-tac-fail then
  dup lf-ity-all@ nip 1 <> if drop over ['] mel-mutual. mel-unsupported then
  lf-ity-nested lf-more-field if over ['] mel-nested. mel-unsupported then ;
: mel-rec ( d induction? -- d' )
  >r lf-menv-name r> if s" rec" else s" casesOn" then lfa-intern-part lf-menv-find
  lf-must ;
: mel-recursor ( target induction? -- d )
  swap lf-infer! lf-whnf! dup mel-inductive 0= if mel-not-inductive then mel-simple nip
  swap mel-rec ;
: lf-elim-for ( target induction? -- d )
  2dup mel-custom? if nip nip exit then mel-recursor ;

\ ---- getElimExprInfo, from d's declared type.
: mel-shape? ( concl -- flag )   \ a bound variable applied to one
  dup lf-meta-head-args 1 = swap lf-term-bvar? and swap lf-term-second@ lf-term-bvar?
  and ;
: mel-at ( info bvar -- info k ) lf-term-first@ over mel-binders swap - 1- ;
: mel-ends ( info concl -- info' )
  dup mel-shape? 0= if lfa-e-tac-form lf-tac-fail then
  tuck lf-term-first@ mel-at mel+ swap lf-term-second@ mel-at mel+ ;
: mel-special? ( info k -- flag ) over 2 run@ over = >r swap 3 run@ = r> or ;
: mel-kind ( info k -- kind )
  swap lf-elim-decl swap lf-menv-kind@ 0= if lfa-e-tac-form lf-tac-fail then ;
: mel-alt? ( info k -- flag )   \ explicit, neither the motive nor the target
  2dup mel-special? if 2drop false exit then mel-kind lf-binder-default = ;
: mel-alt+ ( info pi k -- info' )
  >r tuck lf-binder-name mel+ r> mel+ swap lf-term-first@ lf-meta-forall-body# nip mel+ ;
: mel-binder ( info pi k -- info' )
  >r over r@ mel-alt? r> swap if mel-alt+ else 2drop then ;
: mel-alts ( info -- info' )
  dup lf-elim-decl lf-menv-type over mel-binders 0 ?do
    tuck i mel-binder swap lf-term-second@ loop drop ;
: mel-head ( d -- info concl )   \ d and how many binders, and the conclusion
  0 over mel+ swap lf-menv-type lf-meta-forall-body# rot swap mel+ swap ;
: lf-elim-info ( d -- info ) mel-head mel-ends mel-alts ;

\ ---- mkElimApp: a frame per call (lf-with-record), in the current context.
begin-structure /mea
  field: mea-info        \ the eliminator's information
  field: mea-target      \ the target
  field: mea-tag         \ the goal's tag, the alternatives' tags' parent
  field: mea-f           \ the eliminator applied so far
  field: mea-ftype       \ and its type
  field: mea-alts        \ the alternatives' goals so far, a run
  field: mea-motive      \ the motive's metavariable
end-structure
/mea context-slab: mea-frames
: mea ( -- frame ) mea-frames slab-last ;
: mea-info@ ( -- info ) mea mea-info @ ;
: mea-motive-arg ( pi -- arg )
  lf-term-first@ mv-opaque lf-mvar-new lf-must dup mea mea-motive ! ;
: mea-target-arg ( pi -- arg )
  lf-term-first@ mea mea-target @ lf-infer! lf-tac-defeq lf-must 0= if
    lfa-e-tac-form lf-tac-fail then mea mea-target @ ;
: mea-implicit ( pi k -- arg )
  mea-info@ swap mel-kind lf-binder-instance = if lfa-e-tac-form lf-tac-fail then
  lf-term-first@ mv-natural lf-mvar-new lf-must ;
\ The next alternative (one per explicit binder, in order) is at k.
: mea-next ( -- k ) mea mea-alts @ run-count ;
: mea-alt? ( k -- flag )
  mea-next dup mea-info@ lf-elim-alts# < if mea-info@ swap lf-elim-alt-pos = exit then
  2drop false ;
: mea-alt-tag ( -- tag )
  mea mea-tag @ mea-info@ mea-next lf-elim-alt-name lf-name-append-tag ;
: mea-alt ( pi -- arg )
  lf-term-first@ mea-alt-tag lf-mctx-view lf-goal-new lf-must
  mea mea-alts @ over mel+ mea mea-alts ! ;
: mea-arg ( pi k -- arg )
  dup mea-info@ 2 run@ = if drop mea-motive-arg exit then
  dup mea-info@ 3 run@ = if drop mea-target-arg exit then
  dup mea-alt? if drop mea-alt else mea-implicit then ;
: mea-pi ( -- pi )
  mea mea-ftype @ lf-meta-whnf-forall lf-must dup lf-term-pi? 0= if
    lfa-e-tac-meta lf-tac-fail then ;
: mea-applied ( pi arg -- )
  dup mea mea-f @ swap lf-mk-app mea mea-f ! lf-meta-open lf-must mea mea-ftype ! ;
: mea-start ( -- )
  mea-info@ lf-elim-decl lf-meta-const-fresh lf-must dup mea mea-f ! lf-infer!
  mea mea-ftype ! ;
: mea-run ( -- f alts motive )
  mea-start mea-info@ mel-binders 0 ?do mea-pi dup i mea-arg mea-applied loop
  mea mea-f @ mea mea-alts @ mea mea-motive @ ;
: mea-framed ( info target tag -- f alts motive )
  mea mea-tag ! mea mea-target ! mea mea-info ! mea-run ;
: lf-elim-app ( info target tag -- f alts motive )
  mea-frames ['] mea-framed lf-with-record ;

\ ---- setMotiveArg: fun x => the goal's type over the target (Lean's
\ mkLambdaFVars targets type: the target outside the current context is
\ invalid), a frame per call holding the target as mkLambdaFVars' xs.
begin-structure /mes
  field: mes-target      \ the target (the xs of one)
end-structure
/mes context-slab: mes-frames
: mes ( -- frame ) mes-frames slab-last ;
: mes-lam ( goal -- lam ) lf-goal-type mes mes-target 1 lf-mk-lambda-fvars ;
: mes-fits ( motive lam -- motive lam )
  over lf-goal-type over lf-infer! swap lf-tac-defeq lf-must 0= if
    dup ['] lf-tac-indented. lf-tac-detail lfa-e-tac-elim-motive lf-tac-stop then ;
: mes-framed ( goal motive target -- )
  mes mes-target ! swap mes-lam mes-fits lf-mvar-assign lf-must ;
: lf-elim-set-motive ( goal motive target -- ) mes-frames ['] mes-framed lf-with-record ;
base !   \ the BASE this file was loaded with
