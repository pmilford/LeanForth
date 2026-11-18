\ Applications (plan S1, FE1e6; design docs/design/FE1E_APPLICATIONS.md
\ 2.2), after Lean 4.35.0's Elab/App.lean: elabAppArgs, a state machine
\ over the function's binders (fTypeIsForall, addImplicitArg,
\ processExplicitArg, processInstImplicitArg, elabAndAddNewArg,
\ propagateExpectedType with getResultingType?, finalize,
\ synthesizeAppInstMVars, trySynthesizeAppInstMVars,
\ synthesizePendingAndNormalizeFunType,
\ isNextOutParamOfLocalInstanceAndResult), with no named arguments, no @
\ and no .. (plan FE2), and TermElabM's ensureHasType. A binder's kind is
\ read from the head constant's declared type (lf-menv-kinds, S1 4), never
\ from a term node: a binder that only whnf or an argument shows, or a
\ binder of a head that is no constant, answers 136 (plan S5).
\ - An activation, lf-elab-app-new ( f expected -- outcome ) (expected -1:
\   none), holds f, the rest of its type (Lean's fType, loose bound
\   variables for the arguments so far, fArgs), the instance
\   metavariables not filled yet, propagateExpected (off for a head
\   tagged elab_without_expected_type) and resultTypeOutParam?; its
\   arguments are a syntax application's (lf-elab-app-syntax! ( app -- ))
\   or terms already elaborated (lf-elab-app-term+ ( term -- outcome ),
\   Lean's Arg.expr); lf-elab-app-plain ( -- ) turns resultIsOutParamSupport
\   off (binop% and binrel%; it is off too in an environment without
\   Lean.Internal.coeM, as in Lean).
\ - lf-elab-app-call ( a b frames cont -- ... frames next ) visits the
\   newest activation (a b ignored) and gives ( term outcome ). A syntax
\   argument is elaborated against its binder's domain by the deferred
\   visit lf-elab-term-call ( node expected frames cont -- ... ) that
\   elab-term.fs sets, an elaborated one taken as it is; either must then
\   have that type (ensureArgType).
\ - lf-elab-ensure ( e expected -- e outcome ), ensureHasType: isDefEq of
\   e's type and the expected type (-1: none, ok); false is a coercion
\   Lean would insert, not ported: 131 (plan FE4).
\ - Not ported, unsupported: postponing at a function whose type's whnfR has
\   a metavariable at its head (isMVarApp, 132), an optParam or autoParam
\   binder or eta argument (134), a recursor, casesOn, recOn, brecOn or
\   elab_as_elim head (135), a function that is no pi even after synthesis
\   (a coercion to a function, 131). getResultingType? and hasOptAutoParams
\   put whnf only on a rest with no loose bound variable (Lean's
\   forallTelescopeReducing would enter the binders first).
\ - The frames (lib/frame.fs, no host recursion): ea-frames, shared with
\   elab-term.fs; lf-elab-frames ( -- frames ); lf-elab-visit ( a b xt --
\   result outcome ) runs one visit, xt ( a b frames cont -- ... ) its
\   call, to its end as a pass (on a record already busy, from the
\   cells in use: a step may run a nested pass).
\ Outcomes: ok; invalid (Lean's errors, recorded, or broken input);
\ unsupported; exhausted (the Meta budget: each visit spends one step);
\ full. Untrusted: only the kernel's check of a finished term decides.
\ State: the frames ea-frames and the slabs ea-acts (activations),
\ ea-args (their arguments), ea-insts (their instance metavariables),
\ ea-xargs (their elaborated arguments), a range of each per open
\ activation, ea-spine and ea-rev, in the checker context (ADR 0009).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/input.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../present/binder-table.fs
require ../author/errors.fs
require ../author/declarations.fs
require ./syntax.fs
require ./mvars.fs
require ./meta-env.fs
require ./meta-spine.fs
require ./term-eqv.fs
require ./lib-decode.fs
require ./elab-data.fs
require ./beta-inst.fs
require ./instantiate.fs
require ./whnf.fs
require ./infer.fs
require ./fun-info.fs
require ./elab-pending.fs

begin-structure /ea
  field: ea-f          \ the application so far
  field: ea-ftype      \ the rest of its type (a pi while ea-dom is its domain)
  field: ea-dom        \ the current binder's domain, instantiated
  field: ea-fargs      \ its arguments: the first in ea-args
  field: ea-inst0      \ instance metavariables not filled: the first in ea-insts
  field: ea-expected   \ the expected type, or -1
  field: ea-propagate  \ propagateExpected
  field: ea-outparam   \ resultTypeOutParam?, or -1
  field: ea-support    \ resultIsOutParamSupport
  field: ea-head       \ the head constant's declaration, or -1
  field: ea-stx        \ the syntax application, or -1
  field: ea-next       \ its next argument
  field: ea-xs         \ elaborated arguments: the first in ea-xargs
  field: ea-xi         \ the next of them
  field: ea-rt         \ getResultingType?: the rest walked
  field: ea-rk         \ its binder's index
  field: ea-rn         \ the arguments not yet matched
  field: ea-rres       \ its answer, or -1 (none)
end-structure
/ea context-slab: ea-acts
1 cells context-slab: ea-args
1 cells context-slab: ea-insts
1 cells context-slab: ea-xargs
1 cells context-slab: ea-spine
1 cells context-slab: ea-rev
: ea-visit-none ( x frames -- x frames 0 ) 0 ;
' ea-visit-none context-frames: ea-frames
: lf-elab-frames ( -- frames ) ea-frames ;
: lf-elab-visit ( a b xt -- result outcome )
  >r ea-frames lf-elab-frames-ready r> frame-through drop ;
\ For a new declaration: no activation open, the frames idle.
: lf-elab-app-reset ( -- )
  ea-acts slab-clear ea-args slab-clear ea-insts slab-clear ea-xargs slab-clear
  ea-frames frame-reset ;
defer lf-elab-term-call ( node expected frames cont -- ... frames next )

\ ---- Activations.
: ea ( -- addr ) ea-acts slab-last ;
: ea-fill ( f expected addr -- )
  dup /ea erase tuck ea-expected ! tuck ea-f ! -1 over ea-outparam !
  true over ea-support ! -1 over ea-head ! -1 over ea-stx !
  ea-args slab-count over ea-fargs !
  ea-insts slab-count over ea-inst0 ! ea-xargs slab-count swap ea-xs ! ;
: lf-elab-app-new ( f expected -- outcome )
  1 ea-acts slab-claim ok-then? 0= if nip nip exit then
  ea-acts slab-at ea-fill outcome-ok ;
: lf-elab-app-syntax! ( app -- ) ea ea-stx ! ;
: lf-elab-app-term+ ( term -- outcome ) ea-xargs slab-push ;
: lf-elab-app-plain ( -- ) false ea ea-support ! ;
: ea-end ( term outcome frames -- term outcome frames 0 )
  ea ea-fargs @ ea-args slab-cut ea ea-inst0 @ ea-insts slab-cut
  ea ea-xs @ ea-xargs slab-cut ea-acts slab-drop 0 ;
: ea-fail ( outcome frames -- -1 outcome frames 0 ) >r no-result r> ea-end ;
: ea-error ( code frames -- -1 outcome frames 0 ) >r lf-elab-fail r> ea-fail ;
: ea-result ( outcome frames -- term outcome frames 0 )
  >r dup ok? if ea ea-f @ swap else no-result then r> ea-end ;

\ ---- The arguments left: a syntax application's, or elaborated terms.
: ea-syntax? ( -- flag ) ea ea-stx @ 0< 0= ;
: ea-xn ( -- n ) ea-xargs slab-count ea ea-xs @ - ;
: ea-left ( -- n )
  ea-syntax? if ea ea-stx @ syn-b@ ea ea-next @ - else ea-xn ea ea-xi @ - then ;
: ea-left? ( -- flag ) ea-left 0> ;
: ea-take-syntax ( -- node ) ea ea-stx @ ea ea-next @ syn-arg 1 ea ea-next +! ;
: ea-take-term ( -- term ) ea ea-xi @ ea ea-xs @ + ea-xargs slab-at @ 1 ea ea-xi +! ;

\ ---- The arguments so far (getFType), binders' kinds by index.
: ea-paramidx ( -- k ) ea-args slab-count ea ea-fargs @ - ;
: ea-fargs-at ( -- addr n ) ea ea-fargs @ ea-args slab-at ea-paramidx ;
\ instantiateBetaRevRange: the last argument for #0 (beta-inst.fs takes
\ #k from cell k: the arguments reversed into ea-rev first).
: ea-rev+ ( k -- outcome )
  ea-paramidx 1- swap - ea ea-fargs @ + ea-args slab-at @ ea-rev slab-push ;
: ea-reversed ( -- addr n outcome )
  ea-rev slab-clear ea-paramidx ['] ea-rev+ ok-each
  0 ea-rev slab-at ea-rev slab-count rot ;
: ea-inst-args ( e -- e' outcome )
  ea-reversed ok-then2? if lf-meta-instantiate-rev-beta else nip no-result then
  lf-elab-meta ;
: ea-kind-of ( k -- kind true | false )
  ea ea-head @ dup 0< if 2drop false exit then swap lf-menv-kind@ ;
: ea-kind ( -- kind true | false ) ea-paramidx ea-kind-of ;
: ea-closed? ( t -- flag outcome )
  lf-meta-loose lf-elab-meta ok-then? if 0= outcome-ok then ;

\ ---- Format 2 facts of the head: the run mode's library declarations.
: ea-data? ( -- flag ) lf-libdec-stage dup if elab-read-against? then ;
: ea-tagged? ( d tag -- flag outcome )
  lf-libdec-stage 0= if 2drop false outcome-unsupported exit then
  over lf-libdec-count u< 0= if 2drop false outcome-ok exit then
  ea-data? if elab-tagged? outcome-ok else 2drop false outcome-unsupported then ;
\ shouldElabAsElim's tags, the k-th: elab_as_elim, casesOn, recOn, brecOn.
: ea-elim-tag ( k -- tag )
  case 0 of elab-tag-as-elim endof 1 of elab-tag-cases-on endof
    2 of elab-tag-rec-on endof elab-tag-brec-on swap endcase ;
: ea-elim-tag? ( d k -- d flag outcome ) ea-elim-tag over swap ea-tagged? ;
: ea-elim-tags? ( d -- flag outcome ) 4 ['] ea-elim-tag? ok-any? rot drop ;
\ shouldElabAsElim: a recursor, or casesOn, recOn, brecOn or elab_as_elim.
: ea-elim? ( d -- flag outcome )
  dup lf-menv-kind lf-kind-recursor = if drop true outcome-ok else ea-elim-tags? then ;
: ea-coe-m? ( -- flag ) s" Lean.Internal.coeM" lfa-intern lf-menv-find nip ok? ;
\ A class constant's out-parameter positions, when the data has them.
: ea-class-outs ( c -- addr n true | false )
  lf-meta-const-decl ok? 0= if drop false exit then
  dup lf-libdec-count u< ea-data? and 0= if drop false exit then
  elab-class-of 0= if false exit then elab-class-out-params true ;

\ ---- elabAppArgs's start: f's type instantiated, the head's facts.
: ea-head! ( -- )
  ea ea-f @ dup lf-term-const? 0= if drop exit then
  lf-meta-const-decl drop ea ea-head ! ;
: ea-type ( -- outcome )
  ea ea-f @ lf-infer lf-elab-meta ok-then? 0= if exit then
  lf-instantiate-mvars lf-elab-meta ok-then? if ea ea-ftype ! outcome-ok then ;
\ tryPostponeIfMVar (TermElabM.lean:1379): with arguments left, whnfR of
\ f's type headed by a metavariable (isMVarApp).
: ea-mvar-app? ( t -- flag ) lf-meta-head dup lf-mvar? swap lf-meta-unassigned? and ;
: ea-postpone? ( -- flag outcome )
  ea-left? 0= if false outcome-ok exit then
  ea ea-ftype @ lf-meta-whnf-r lf-elab-meta ok-then? if ea-mvar-app? outcome-ok
  else false swap then ;
: ea-facts ( -- outcome )
  ea ea-head @ dup 0< if drop outcome-ok exit then
  dup ea-elim? ok-then? 0= if nip exit then if drop lfa-e-elab-elim lf-elab-fail exit then
  elab-tag-no-expected ea-tagged? ok-then? if 0= ea ea-propagate ! outcome-ok then ;
: ea-support! ( -- ) ea ea-support @ if ea-coe-m? ea ea-support ! then ;
: ea-app. ( -- ) s" app " lf-elab-note ea ea-f @ lf-elab-term. lf-elab-nl ;
: ea-started ( -- outcome )
  ea-app. true ea ea-propagate ! ea-head! ea-type dup ok? 0= if exit then drop
  ea-postpone? ok-then? 0= if exit then if lfa-e-elab-postpone lf-elab-fail exit then
  ea-facts dup ok? if ea-support! then ;

\ ---- addNewArg.
: ea-arg. ( arg -- arg )
  s"  arg " lf-elab-note ea-paramidx lf-elab-n. s" : " lf-elab-note dup lf-elab-term.
  lf-elab-nl ;
: ea-add ( arg -- outcome )
  ea-arg. ea ea-f @ over lf-meta-app ok-then? 0= if nip exit then ea ea-f !
  ea-args slab-push dup ok? if ea ea-ftype @ lf-term-second@ ea ea-ftype ! then ;

\ ---- fTypeIsForall: a pi, its domain instantiated, with its outParam,
\ semiOutParam, optParam and autoParam annotations consumed (Lean's
\ getArgExpectedType, App.lean:273: the metavariables and the argument's
\ expected type have the plain type); else whnfForall of the type
\ instantiated (getFType), kept. getParamType's raw domain is the pi's.
: ea-domain ( -- outcome )
  ea ea-ftype @ lf-term-first@ ea-inst-args ok-then?
  if lf-meta-consume-annotations ea ea-dom ! outcome-ok then ;
: ea-param-type ( -- t ) ea ea-ftype @ lf-term-first@ ;
: ea-whnf ( -- outcome )
  ea ea-ftype @ ea-inst-args ok-then? 0= if exit then
  lf-meta-whnf-forall lf-elab-meta ok-then? if ea ea-ftype ! outcome-ok then ;
: ea-pi? ( -- flag outcome )
  ea ea-ftype @ lf-term-pi? if ea-domain true swap exit then false outcome-ok ;
: ea-forall? ( -- flag outcome )
  ea ea-ftype @ lf-term-pi? if ea-pi? exit then
  ea-whnf dup ok? if drop ea-pi? else false swap then ;

\ ---- ensureHasType.
: ea-coerced ( e flag -- e outcome )
  if outcome-ok else lfa-e-elab-coercion lf-elab-fail then ;
: ea-against ( e expected -- e outcome )
  over lf-infer lf-elab-meta ok-then? 0= if nip exit then
  swap lf-elab-defeq lf-elab-meta ok-then? if ea-coerced then ;
: lf-elab-ensure ( e expected -- e outcome )
  dup 0< if drop outcome-ok else ea-against then ;

\ ---- The instance metavariables (Lean's instMVars).
: ea-insts# ( -- n ) ea-insts slab-count ea ea-inst0 @ - ;
: ea-inst ( k -- mvar ) ea ea-inst0 @ + ea-insts slab-at @ ;
: ea-inst-drop ( k -- ) ea ea-inst0 @ + ea-insts slab-remove ;
\ synthesizeAppInstMVars: each by synthesizeInstMVarCore, those not
\ filled made pending; then none is left.
: ea-pend ( k -- outcome )
  ea-inst dup lf-elab-synth-core ok-then? 0= if nip exit then
  if drop outcome-ok else lf-elab-pend then ;
: ea-synthesize ( -- outcome )
  ea-insts# ['] ea-pend ok-each dup ok? if ea ea-inst0 @ ea-insts slab-cut then ;
\ trySynthesizeAppInstMVars (App.lean:355): those whose type,
\ instantiated, is no metavariable (Lean's isMVar of the type itself,
\ not of its head), by synthesizeInstMVarCore under Lean's try (a Lean
\ error keeps it); the filled ones taken out.
: ea-mvar-typed? ( mvar -- flag outcome )
  lf-mvar-type-instantiated lf-elab-meta ok-then? if lf-mvar? outcome-ok
  else false swap then ;
: ea-try-one ( k -- filled? outcome )
  dup ea-inst ea-mvar-typed? ok-then? 0= if nip false swap exit then
  if drop false outcome-ok exit then ea-inst lf-elab-synth-core
  dup lf-elab-catch if 2drop false outcome-ok then ;
: ea-try-at ( k -- k' outcome )
  dup ea-try-one ok-then? 0= if exit then if dup ea-inst-drop else 1+ then outcome-ok ;
: ea-try-synthesize ( -- outcome )
  0 begin dup ea-insts# < while ea-try-at dup ok? 0= if nip exit then drop repeat
  drop outcome-ok ;

\ ---- isNextOutParamOfLocalInstanceAndResult (App.lean:681): the rest
\ after the current binder ends in that binder (isResultType), and an
\ instance binder of the rest, of a class with out-parameters, has the
\ binder (bound variable j at the depth j of that binder) at an
\ out-parameter position.
: ea-result? ( type -- flag )
  0 begin over lf-term-pi? while 1+ swap lf-term-second@ swap repeat lf-term-bvar-is? ;
: ea-pos-hit? ( j p -- j flag )
  dup ea-spine slab-count < 0= if drop false exit then
  ea-spine lf-meta-arg over lf-term-bvar-is? ;
: ea-outs-hit? ( j addr n -- j flag )
  0 ?do dup i cells + @ rot swap ea-pos-hit? if nip true unloop exit then swap loop
  drop false ;
: ea-dom-hit? ( dom j -- flag outcome )
  swap ea-spine lf-meta-spine lf-elab-meta ok-then? 0= if nip false swap exit then
  dup lf-term-const? 0= if 2drop false outcome-ok exit then
  ea-class-outs 0= if drop false outcome-ok exit then ea-outs-hit? nip outcome-ok ;
: ea-binder-out? ( type j -- flag outcome )
  dup ea-paramidx + 1+ ea-kind-of 0= if 2drop false lfa-e-elab-binder lf-elab-fail exit
  then lf-binder-instance <> if 2drop false outcome-ok exit then
  swap lf-term-first@ swap ea-dom-hit? ;
: ea-out-walk ( type -- flag outcome )
  0 begin over lf-term-pi? while
    2dup ea-binder-out? lf-elab-settled? if 2swap 2drop exit then 2drop
    1+ swap lf-term-second@ swap repeat 2drop false outcome-ok ;
: ea-next-out? ( -- flag outcome )
  ea ea-support @ ea ea-outparam @ 0< and 0= if false outcome-ok exit then
  ea ea-ftype @ lf-term-second@ dup ea-result? if ea-out-walk exit then
  drop false outcome-ok ;

\ ---- The binders' kinds: implicit (addImplicitArg), instance
\ (processInstImplicitArg).
: ea-mvar. ( mvar c-addr u -- mvar )
  lf-elab-note s"  ?" lf-elab-note dup lf-term-first@ lf-elab-n. lf-elab-nl ;
: ea-out! ( mvar out? -- mvar )
  if dup ea ea-outparam ! false ea ea-propagate ! then ;
: ea-implicit ( -- outcome )
  ea-next-out? ok-then? 0= if exit then
  ea ea-dom @ mv-natural lf-mvar-new lf-elab-meta ok-then? 0= if nip exit then
  swap ea-out! s"  implicit" ea-mvar. ea-add ;
: ea-instance ( -- outcome )
  ea ea-dom @ mv-synthetic lf-mvar-new lf-elab-meta ok-then? 0= if exit then
  s"  instance" ea-mvar. dup ea-insts slab-push dup ok? 0= if nip exit then drop ea-add ;

\ ---- optParam, autoParam (Lean's getOptParamDefault?, getAutoParamTactic?,
\ hasOptAutoParams).
\ One step: a pi's domain an optParam or autoParam (found), else its
\ body (more); no pi: whnf where nothing is loose (more when a pi comes).
: ea-opt-pi ( pi -- t' found? more? outcome )
  dup lf-term-first@ lf-meta-opt-auto? if true false outcome-ok exit then
  lf-term-second@ false true outcome-ok ;
: ea-opt-whnf ( t -- t' found? more? outcome )
  lf-meta-whnf-forall lf-elab-meta ok-then? 0= if -1 false false rot exit then
  false over lf-term-pi? outcome-ok ;
: ea-opt-step ( t -- t' found? more? outcome )
  dup lf-term-pi? if ea-opt-pi exit then
  dup ea-closed? ok-then? 0= if false false rot exit then
  if ea-opt-whnf else false false outcome-ok then ;
: ea-opt-walk ( type -- flag outcome )
  begin ea-opt-step dup ok? 0= if >r 2drop drop false r> exit then drop while drop repeat
  nip outcome-ok ;

\ ---- getResultingType? (App.lean:449), from the current binder: the
\ type the application would have, or none (-1); the walk in ea-rt,
\ ea-rk (binder index) and ea-rn (arguments not matched).
: ea-r-stop ( res -- false outcome ) ea ea-rres ! false outcome-ok ;
: ea-r-none ( -- false outcome ) -1 ea-r-stop ;
: ea-r-some ( -- false outcome )
  ea ea-rt @ dup ea-closed? ok-then? 0= if nip false swap exit then
  if ea-r-stop else drop ea-r-none then ;
: ea-r-go ( t' -- true outcome )
  lf-term-second@ ea ea-rt ! 1 ea ea-rk +! true outcome-ok ;
: ea-r-last ( t' -- false outcome )
  dup ea-closed? ok-then? 0= if nip false swap exit then
  0= if drop ea-r-none exit then ea-opt-walk ok-then? 0= if false swap exit then
  if ea-r-none else ea-r-some then ;
: ea-r-pi ( t' kind -- more? outcome )
  dup lf-binder-strict = ea ea-rn @ 0= and if 2drop ea-r-some exit then
  lf-binder-default <> if ea-r-go exit then
  ea ea-rn @ if -1 ea ea-rn +! ea-r-go exit then
  dup lf-term-first@ lf-meta-opt-auto? if ea-r-go else ea-r-last then ;
: ea-r-reduced ( -- t' outcome )
  ea ea-rt @ dup lf-term-pi? if outcome-ok exit then
  dup ea-closed? ok-then? 0= if nip no-result exit then
  if lf-meta-whnf-forall lf-elab-meta else outcome-ok then ;
: ea-r-step ( -- more? outcome )
  ea-r-reduced ok-then? 0= if false swap exit then
  dup lf-term-pi? 0= if drop ea ea-rn @ if ea-r-none else ea-r-some then exit then
  ea ea-rk @ ea-kind-of if ea-r-pi else drop false lfa-e-elab-binder lf-elab-fail then ;
: ea-r-start ( -- outcome )
  ea ea-ftype @ ea-inst-args ok-then? 0= if exit then lf-instantiate-mvars lf-elab-meta
  ok-then? 0= if exit then dup ea ea-ftype ! ea ea-rt !
  ea-paramidx ea ea-rk ! ea-left ea ea-rn ! outcome-ok ;
: ea-resulting ( -- type outcome )
  ea-r-start dup ok? 0= if no-result exit then drop
  begin ea-r-step dup ok? 0= if nip no-result exit then drop 0= until
  ea ea-rres @ outcome-ok ;

\ ---- propagateExpectedType (App.lean:563), before a syntax argument.
\ Lean's expectedType.isProp after instantiateMVars (App.lean:593): Sort 0
\ exactly; an expected Prop is never propagated (review N2 of 2026-11-18).
: ea-prop? ( t -- flag outcome )
  lf-instantiate-mvars lf-elab-meta ok-then? if lf-prop? outcome-ok else false swap then ;
: ea-prop-off ( -- outcome ) false ea ea-propagate ! outcome-ok ;
: ea-prop-try ( expected type -- outcome )
  ea-try-synthesize dup ok? 0= if nip nip exit then drop
  lf-elab-defeq lf-elab-meta ok-then? if if ea-prop-off else outcome-ok then then ;
: ea-prop-with ( expected -- outcome )
  dup ea-prop? ok-then? 0= if nip exit then if drop ea-prop-off exit then
  ea-resulting ok-then? 0= if nip exit then
  dup 0< if 2drop outcome-ok else ea-prop-try then ;
: ea-propagate-arg ( -- outcome )
  ea ea-propagate @ ea ea-expected @ 0< 0= and 0= if outcome-ok exit then
  ea ea-expected @ lf-instantiate-mvars lf-elab-meta ok-then? if ea-prop-with then ;

\ ---- finalize (App.lean:610).
: ea-final. ( -- ) s"  finalize" lf-elab-note lf-elab-nl ;
: ea-out-done ( etype -- outcome )
  ea-synthesize dup ok? 0= if nip exit then drop
  ea ea-outparam @ tuck = swap lf-meta-unassigned? and
  if lf-elab-synthesize-default else outcome-ok then ;
: ea-expected-done ( etype -- outcome )
  ea-try-synthesize dup ok? 0= if nip exit then drop
  ea ea-expected @ swap lf-elab-defeq lf-elab-meta nip
  dup ok? if drop ea-synthesize then ;
: ea-finalized ( etype -- outcome )
  ea ea-outparam @ 0< 0= if ea-out-done exit then
  ea ea-expected @ 0< if drop ea-synthesize else ea-expected-done then ;
: ea-finalize ( frames -- term outcome frames 0 )
  >r ea-final. ea ea-f @ lf-infer lf-elab-meta ok-then? if ea-finalized then
  r> ea-result ;

\ ---- The loop (main, App.lean:926), one binder a step.
defer ea-main ( frames -- ... frames next )
: ea-step-done ( outcome frames -- frames next | -1 outcome frames 0 )
  over ok? if nip ['] ea-main else ea-fail then ;
: ea-added ( e outcome frames -- ... frames next )
  >r ok-then? if ea ea-dom @ lf-elab-ensure ok-then? if ea-add then then r> ea-step-done ;
: ea-no-arg ( frames -- ... frames next )
  ea-param-type lf-meta-opt-auto? if lfa-e-elab-opt-param swap ea-error exit then
  >r ea ea-ftype @ ea-inst-args ok-then? if ea-opt-walk else false swap then
  ok-then? 0= if r> ea-fail exit then
  if lfa-e-elab-opt-param r> ea-error else r> ea-finalize then ;
: ea-explicit ( frames -- ... frames next )
  ea-left? 0= if ea-no-arg exit then
  ea-syntax? 0= if ea-take-term outcome-ok rot ea-added exit then
  >r ea-propagate-arg dup ok? 0= if r> ea-fail exit then drop
  ea-take-syntax ea ea-dom @ r> ['] ea-added lf-elab-term-call ;
: ea-implicit-step ( frames -- ... frames next ) >r ea-implicit r> ea-step-done ;
: ea-instance-step ( frames -- ... frames next ) >r ea-instance r> ea-step-done ;
: ea-strict ( frames -- ... frames next )
  ea-left? if ea-implicit-step else ea-finalize then ;
: ea-binder ( frames -- ... frames next )
  ea-kind 0= if lfa-e-elab-binder swap ea-error exit then
  case lf-binder-default of ea-explicit endof lf-binder-instance of ea-instance-step endof
    lf-binder-strict of ea-strict endof >r ea-implicit-step r> endcase ;
\ synthesizePendingAndNormalizeFunType: no pi with arguments left.
: ea-synth-yes ( -- outcome ) lf-postpone-yes lf-elab-synthesize ;
: ea-normalized ( -- flag outcome )
  ea-try-synthesize ['] ea-synth-yes ok-and dup ok? 0= if false swap exit then
  drop ea-forall? ;
: ea-normalize ( frames -- ... frames next )
  >r ea-normalized ok-then? 0= if r> ea-fail exit then
  if r> ea-binder else lfa-e-elab-coercion r> ea-error then ;
:noname ( frames -- ... frames next )
  >r ea-forall? ok-then? 0= if r> ea-fail exit then
  if r> ea-binder exit then ea-left? if r> ea-normalize else r> ea-finalize then ;
is ea-main
: ea-visit ( a b frames -- ... frames next )
  >r 2drop ea-started dup ok? if drop r> ea-main else r> ea-fail then ;
: lf-elab-app-call ( a b frames cont -- ... frames next ) ['] ea-visit lf-elab-open ;

base !   \ the BASE this file was loaded with
