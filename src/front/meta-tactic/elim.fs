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
\       Lean's text, its explanation naming the tactic, induction or
\       cases as the flag says, with its hints for a proposition or a type
\       universe, then the main goal), under induction neither mutual nor
\       nested (209, Lean's text and its hint; cases takes both, as
\       getElimNameInfo's `induction &&` tests say), and its recursor
\       C.rec (C.casesOn for induction? false) is the eliminator. 205's
\       header, author/errors.fs's catalogue text, is induction's
\       ("Tactic `induction` failed") whatever the flag, until cases is
\       ported (plan 9.4.8l, item W)
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
\       its type defeq the motive's (else error 212 with the motive, its
\       type and the motive's, Lean's text), the motive assigned
\ Errors are thrown as authoring errors at the step running
\ (tactic-run.fs's lf-tac-stop and lf-tac-fail), Meta failures as
\ outcomes (meta-must.fs). Not ported: generalizeVars and index targets
\ (99, plan FE5).
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

\ ---- The information: a run of mel-head# cells, d, the binders, the
\ motive's and the target's positions, then mel-alt-cells per alternative,
\ its name, position and fields (review tactic-move-c4 M2: the layout
\ named here, read only through these words).
4 constant mel-head#        \ d, binders, the motive's and the target's positions
3 constant mel-alt-cells    \ an alternative's name, position and fields
: lf-elim-decl ( info -- d ) 0 run@ ;
: mel-binders ( info -- n ) 1 run@ ;
: mel-motive-at ( info -- k ) 2 run@ ;
: mel-target-at ( info -- k ) 3 run@ ;
: lf-elim-alts# ( info -- n ) run-count mel-head# - mel-alt-cells / ;
: mel-alt@ ( info k field -- x ) swap mel-alt-cells * + mel-head# + run@ ;
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
\ level), then the main goal. The explanation names the tactic (Lean's
\ tacticName, Induction.lean:776): induction, or cases for induction?
\ false.
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
: mel-tactic ( induction? -- c-addr u ) if s" induction" else s" cases" then ;
: mel-tactic. ( c-addr u -- c-addr u ) 2dup lf-pp-emit ;
: mel-custom. ( c-addr u -- )
  s" for applying custom " lf-pp-emit mel-tactic. s"  principles with a " lf-pp-emit
  s" 'using' clause or a registered '@[" lf-pp-emit lf-pp-emit
  s" _eliminator]' theorem. " lf-pp-emit ;
: mel-explanation. ( induction? -- )
  mel-tactic s\" \n\nExplanation: the `" lf-pp-emit mel-tactic.
  s" ` tactic is for constructor-based reasoning as well as " lf-pp-emit mel-custom. ;
: mel-unregistered. ( -- )
  s" The above type neither is an inductive type " lf-pp-emit
  s" nor has a registered theorem." lf-pp-emit ;
: mel-explain. ( t induction? -- outcome )
  mel-explanation. mel-unregistered. mel-sort-hint. outcome-ok ;
: mel-goal. ( -- outcome ) lf-main-goal ok-then? if lf-tac-goal-below. then ;
: mel-major. ( t induction? -- outcome )
  over lf-tac-indented. dup ok? 0= if nip nip exit then
  drop mel-explain. ['] mel-goal. ok-and ;
: mel-not-inductive ( t induction? -- )
  2 ['] mel-major. lf-tac-detail-n lfa-e-tac-not-inductive lf-tac-stop ;
: mel-inductive ( t -- d true | false ) lf-meta-head lf-match-const-induct ;
\ Mutual or nested (209): Lean's text and its hint, under induction only
\ (Induction.lean:833-836: cases takes C.casesOn of any inductive type).
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
: mel-checked ( t d induction? -- t d ) if mel-simple then ;
\ The inductive type of the target's type, its refusals checked (205
\ throws with the flag's tactic named).
: mel-inductive-of ( target induction? -- d )
  swap lf-infer! lf-whnf! dup mel-inductive 0= if swap mel-not-inductive then
  rot mel-checked nip ;
: mel-recursor ( target induction? -- d ) tuck mel-inductive-of swap mel-rec ;
: lf-elim-for ( target induction? -- d )
  2dup mel-custom? if nip nip exit then mel-recursor ;

\ ---- getElimExprInfo, from d's declared type.
: mel-shape? ( concl -- flag )   \ a bound variable applied to one
  dup lf-meta-head-args 1 = swap lf-term-bvar? and swap lf-term-second@ lf-term-bvar?
  and ;
: mel-at ( info bvar -- info k ) lf-term-first@ over mel-binders swap - 1- ;
: mel-ends ( info concl -- info' )
  dup mel-shape? 0= if lfa-e-tac-form lf-tac-fail then
  tuck lf-term-first@ mel-at lf-run+ swap lf-term-second@ mel-at lf-run+ ;
: mel-special? ( info k -- flag )   \ the motive's binder or the target's
  2dup swap mel-motive-at = >r swap mel-target-at = r> or ;
: mel-kind ( info k -- kind )
  swap lf-elim-decl swap lf-menv-kind@ 0= if lfa-e-tac-form lf-tac-fail then ;
: mel-alt? ( info k -- flag )   \ explicit, neither the motive nor the target
  2dup mel-special? if 2drop false exit then mel-kind lf-binder-default = ;
: mel-alt+ ( info pi k -- info' )
  >r tuck lf-binder-name lf-run+ r> lf-run+ swap lf-term-first@ lf-meta-forall-body# nip
  lf-run+ ;
: mel-binder ( info pi k -- info' )
  >r over r@ mel-alt? r> swap if mel-alt+ else 2drop then ;
: mel-alts ( info -- info' )
  dup lf-elim-decl lf-menv-type over mel-binders 0 ?do
    tuck i mel-binder swap lf-term-second@ loop drop ;
: mel-head ( d -- info concl )   \ d and how many binders, and the conclusion
  0 over lf-run+ swap lf-menv-type lf-meta-forall-body# rot swap lf-run+ swap ;
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
  mea mea-alts @ over lf-run+ mea mea-alts ! ;
: mea-arg ( pi k -- arg )
  dup mea-info@ mel-motive-at = if drop mea-motive-arg exit then
  dup mea-info@ mel-target-at = if drop mea-target-arg exit then
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
\ The motive's inferred type against the motive metavariable's: unequal
\ is error 212 with the motive and Lean's mkHasTypeButIsExpectedMsg
\ (Induction.lean:271-273; tactic-msg.fs's lf-tac-type-mismatch).
: mes-types ( motive lam -- motive lam inferred expected )
  over lf-goal-type over lf-infer! swap ;
: mes-fits ( motive lam -- motive lam )
  mes-types 2dup lf-tac-defeq lf-must if 2drop exit then
  2>r dup 2r> lfa-e-tac-elim-motive lf-tac-type-mismatch ;
: mes-framed ( goal motive target -- )
  mes mes-target ! swap mes-lam mes-fits lf-mvar-assign lf-must ;
: lf-elim-set-motive ( goal motive target -- ) mes-frames ['] mes-framed lf-with-record ;
base !   \ the BASE this file was loaded with
