\ Term unification of the front end (plan FE1c; ADR 0021 D6): a port of
\ Lean 4.35.0's Meta isDefEq (Lean/Meta/ExprDefEq.lean, isExprDefEqAuxImpl
\ under checkpointDefEq, Lean/Meta/Basic.lean), in Lean's order, over the
\ term store, with no use of src/kernel/.
\ lf-meta-defeq ( t s -- flag outcome ) is Lean's isDefEq t s:
\ - isDefEqQuick: unused lets dropped; literals by value (Nat literals
\   as unsigned cells, string literals by their text); Sorts by
\   level unification (level-defeq.fs); lambdas and pis equal node for
\   node (term-eqv.fs), else binder by binder: each pair of domains
\   opened with one new free variable of the first, then the domains
\   compared in order, then the bodies; free variables: the same one, a
\   let variable undef, else proof irrelevance; any other pair equal
\   node for node or by eta (fun x => f x and f), else, with a
\   metavariable at a head: an assigned head instantiated, a delayed
\   one expanded, the same metavariable's arguments compared, an
\   assignable one assigned (processAssignment, below), two that are
\   not assignable proof-irrelevant or not equal;
\ - proof irrelevance (isProofQuick, prop-quick.fs; isProp, fun-info.fs):
\   two proofs of equal propositions are equal;
\ - whnfCore of both sides (whnf.fs) and again when either changes;
\   both instantiated;
\ - eta (fun x => t against s whose type is a pi), Nat offsets
\   (isDefEqOffset, nat-offset.fs: Nat.succ ?a against Nat.succ (k + 1)
\   assigns ?a := k + 1), two constants by name and universe levels, two
\   applications by their heads and arguments (isDefEqApp and
\   isDefEqArgs: explicit arguments first, implicit ones after, proofs
\   left to proof irrelevance, under getFunInfoNArgs, fun-info.fs), then
\   Lean's late cases (a structure with no fields: isDefEqUnitLike)
\   and the stuck metavariables of isDefEqOnFailure.
\ - processAssignment: ?m a1 .. an =?= v with a1 .. an distinct free
\   variables out of ?m's scope is ?m := fun a1 .. an => v
\   (checkAssignment, mkLambdaFVars with eta, assign-check.fs), the
\   types compared first (checkTypesAndAssign); otherwise first-order
\   approximation under foApprox (?m a1 .. an =?= f b: an =?= b and
\   ?m a1 .. an-1 =?= f, under a checkpoint) and, with no arguments, the
\   constant assignment; processAssignment' retries with whnf's value.
\ Each checkpointDefEq of Lean is a mark of mvars.fs, rolled back when
\ its answer is false and on any failure, kept when true; each
\ withNewMCtxDepth a depth scope, rolled back at its end.
\ Configuration (meta-config.fs, Lean's Meta.Config read as getConfig):
\ lf-defeq-flags! (foApprox, ctxApprox, quasiPatternApprox, constApprox,
\ isDefEqStuckEx, ...), lf-defeq-mode! (the transparency); implicit
\ arguments and metavariable types are compared at implicit transparency
\ or above, as Lean's withImplicitConfig. Each comparison spends one step
\ of meta-config.fs's budget too.
\ The stuck signal (meta-config.fs, lf-meta-stuck), under isDefEqStuckEx:
\ raised where both heads are metavariables neither side may assign and
\ proof irrelevance cannot decide (ExprDefEq.lean:2118), where
\ isDefEqOnFailure meets a stuck metavariable of an outer depth that
\ synthPending leaves (2182), and by level unification
\ (level-defeq.fs); every mark rolls back on it and it passes on as the
\ answer's outcome. Caught only as Lean does: isDefEqAppFallback (2393)
\ catches isDefEqOnFailure's, tries the late cases and raises it again
\ unless one answers true (isDefEqOnFailure changes nothing here, so
\ Lean's restore is the identity); lf-meta-defeq-guarded ( t s -- flag
\ outcome ), Lean's isDefEqGuarded, answers false for it alone.
\ Never a guess, answered unsupported (plan FE1c, FE1d2, FE1e): an
\ unfoldable definition at either head (lazy delta reduction, FE1d2's
\ facts), a projection node (isDefEqProj), a ground Nat operation
\ (isDefEqNat's reduceNat?), structure eta for a structure-like type,
\ isDefEqOnFailure's comparison again after synthPending fills a stuck
\ metavariable (unstuckMVar), an instance-typed metavariable's types
\ that differ at instances transparency where its type is a pi or its
\ value's spine holds a let (checkTypesAndAssign's instance-typed
\ branch, ported otherwise: S1 appendix D), isDefEqProjInst at instances
\ or implicit transparency, a
\ string literal against String.ofList (isDefEqStringLit), the steps of
\ the files above that answer unsupported, quasi-pattern assignments
\ (isTypeCorrect), constApprox,
\ and processAssignment's retry after a level comparison that may have
\ left assignments Lean keeps and this rolled back. Caches are not
\ kept: they change no answer.
\ Unification hints (isDefEqOnFailure's tryUnificationHints): the hint
\ table is not read (an export does not carry it). A failure with a
\ definition at the head of either side answers unsupported, never
\ false: that covers Init's only hint, Not p =?= p -> False
\ (Init/Hints.lean), whose key is Not, a definition. A library with a
\ hint keyed at a constructor, an inductive type or a variable is not
\ covered: such an environment needs the hint table first (plan FE1c).
\ Machine: each Lean call is an activation with registers (t, s, x, y
\ and a mark) and an entry step; a call pushes the caller's registers
\ and its continuation on the heap stack de-frames; a return pops them
\ and runs the continuation with the answer (an LBool); arrays an
\ activation keeps (binders, arguments) wait on the heap stack de-cells.
\ No host recursion (plan task 6.2.0). Fuel: each comparison spends one;
\ lf-defeq-fuel! sets a call's limit (0: lf-defeq-default-fuel).
\ Outcomes: ok with the flag; lf-meta-stuck and unsupported as above;
\ exhausted (the call's fuel or the budget spent); full; invalid for
\ terms that are not live, for a broken step and for a mark or depth
\ scope that cannot be closed. On any failure every assignment made is
\ rolled back, every new depth left; after every call the local context
\ and its view are as on entry (binders' free variables dropped).
\ Untrusted front-end code: only the kernel's check of a finished term
\ decides anything.
\ State: the record df and the slabs de-frames, de-cells and de-saved,
\ in the checker context (ADR 0009); one unification at a time per
\ context, but for the synthesis hooks (synth.fs), which unify while
\ this machine is set aside on de-saved.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/mvar-leaves.fs
require ../core/let-terms.fs
require ../core/literals.fs
require ../core/projections.fs
require ../core/input.fs
require ../present/binder-table.fs
require ./mvars.fs
require ./instantiate.fs
require ./meta-spine.fs
require ./meta-config.fs
require ./meta-env.fs
require ./whnf.fs
require ./infer.fs
require ./level-defeq.fs
require ./term-eqv.fs
require ./prop-quick.fs
require ./assign-check.fs
require ./nat-offset.fs
require ./fun-info.fs

1000000 constant lf-defeq-default-fuel

begin-structure /df
  field: df-k        \ the continuation the next call returns to: with the
  field: df-t        \ registers t, s, x, y, the mark and the mode, the
  field: df-s        \ cells a frame keeps (de-regs)
  field: df-x
  field: df-y
  field: df-m        \ the activation's open mark, or 0
  field: df-mode     \ the transparency
  field: df-next     \ de-run, de-ret, de-done or de-stall
  field: df-entry    \ the step that starts the activation
  field: df-result   \ the answer being returned
  field: df-limit    \ fuel per call (a unit-test setting); 0: the default
  field: df-fuel
  field: df-outcome  \ ok, or the failure that ended the call
  field: df-taint    \ a false level comparison may have left assignments
  field: df-view0    \ the local context on entry
  field: df-mark0    \ and the term mark (lf-lctx-drop's) on entry
end-structure
/df context-record: df
7 cells constant de-regs
begin-structure /de-frame       \ a call's saved activation
  de-regs +field fr-regs        \ the registers df-k .. df-mode
  field: fr-scope               \ the callee's depth scope, or 0
end-structure
/de-frame context-slab: de-frames
1 cells context-slab: de-cells
: lf-defeq-fuel! ( n -- ) df df-limit ! ;

\ ---- Registers.
: de-t ( -- t ) df df-t @ ;   : de-s ( -- s ) df df-s @ ;
: de-x ( -- x ) df df-x @ ;   : de-y ( -- y ) df df-y @ ;   : de-m ( -- m ) df df-m @ ;
: de-t! ( t -- ) df df-t ! ;   : de-s! ( s -- ) df df-s ! ;
: de-y+ ( -- ) 1 df df-y +! ;
: de-flag? ( bit -- flag ) lf-meta-flag? ;

\ ---- The machine.
0 constant de-run  1 constant de-ret  2 constant de-done  3 constant de-stall
: de-next! ( state -- ) df df-next ! ;
: de-aborted? ( -- flag ) df df-next @ de-done = ;
: de-abort ( outcome -- ) de-aborted? if drop exit then df df-outcome ! de-done de-next! ;
: de-must ( x outcome -- x flag ) dup ok? if drop true else de-abort false then ;
: de-made ( x true | false -- x flag ) dup 0= if outcome-full de-abort -1 swap then ;
: de-return ( r -- ) de-aborted? if drop exit then df df-result ! de-ret de-next! ;
: de-pass ( r -- ) de-return ;
: de-then ( k -- ) df df-k ! ;
: de-frame ( -- addr ) de-frames dup slab-count 1- swap slab-at ;
: de-save ( -- outcome )
  1 de-frames slab-claim ok-then? 0= if exit then
  de-frames slab-at df df-k over fr-regs de-regs move 0 swap fr-scope ! outcome-ok ;
: de-regs! ( t s entry -- )
  df df-entry ! de-s! de-t! 0 df df-x ! 0 df df-y ! de-run de-next! ;
: de-invoke ( t s entry -- )
  de-aborted? if drop 2drop exit then
  de-save dup ok? 0= if de-abort drop 2drop exit then drop 0 df df-m ! de-regs! ;
: de-fuel? ( -- flag ) df df-fuel @ dup 0> if 1- df df-fuel ! true else drop false then ;
: de-spend? ( -- flag )
  de-fuel? dup if drop lf-meta-spend? then dup 0= if outcome-exhausted de-abort then ;
: de-goto ( t s entry -- ) de-aborted? de-spend? 0= or if drop 2drop exit then de-regs! ;
defer de-solve-x ( -- )   \ isExprDefEqAux
defer de-top-x ( -- )     \ isDefEq: isExprDefEqAux under a checkpoint
: de-solve ( t s k -- ) de-then ['] de-solve-x de-invoke ;
\ The callee of the last call runs at implicit transparency or above,
\ or one depth deeper (withNewMCtxDepth: a depth scope, its handle in the
\ frame's fr-scope, closed when the callee returns or the call fails).
: de-rank ( mode -- n )
  case lf-tr-none of 0 endof  lf-tr-reducible of 1 endof  lf-tr-instances of 2 endof
    lf-tr-implicit of 3 endof  lf-tr-default of 4 endof  5 swap endcase ;
: de-bump ( -- )
  df df-mode @ de-rank lf-tr-implicit de-rank < if lf-tr-implicit df df-mode ! then ;
: de-deeper ( -- )
  de-aborted? if exit then
  false lf-mctx-depth{ de-must if de-frame fr-scope ! else drop then ;
: de-pop ( -- k scope )
  de-frame dup fr-regs df df-k de-regs move fr-scope @ df df-k @ swap
  -1 de-frames slab-commit ;
: de-shallow ( scope -- flag )
  ?dup 0= if true exit then }lf-mctx-depth dup ok? if drop true else de-abort false then ;
: de-resume ( -- ) de-pop de-shallow if df df-result @ swap execute else drop then ;
: de-ret-step ( -- ) de-frames slab-count 0= if de-done de-next! else de-resume then ;
: de-step ( -- )
  df df-next @ de-stall de-next! de-run = if df df-entry @ execute else de-ret-step then
  df df-next @ de-stall = if outcome-invalid de-abort then ;
: de-loop ( -- ) begin df df-next @ de-done <> while de-step repeat ;
\ Marks: checkpointDefEq keeps the assignments when the answer is true.
: de-mark? ( -- flag )
  lf-mctx-mark dup ok? if drop df df-m ! true else nip de-abort false then ;
: de-close ( r -- r )
  de-m 0 df df-m ! over lf-lb-true = if lf-mctx-commit else lf-mctx-rollback then
  dup ok? if drop else de-abort then ;
: de-close-k ( r -- ) de-close de-return ;
\ A mark that cannot be rolled back leaves the context broken: invalid.
: de-broken ( outcome -- ) ok? 0= if outcome-invalid df df-outcome ! then ;
: de-roll ( -- ) de-m ?dup if lf-mctx-rollback de-broken 0 df df-m ! then ;
: de-unframe ( -- ) de-pop nip ?dup if }lf-mctx-depth de-broken then de-roll ;
: de-unwind ( -- ) de-roll begin de-frames slab-count 0> while de-unframe repeat ;

\ ---- Cells: arrays of an activation, from de-x on.
: de-cell ( i -- addr ) de-cells slab-at ;
: de-push ( x -- flag )
  de-cells lf-meta-push dup ok? if drop true else de-abort false then ;
: de-truncate ( n -- ) de-cells slab-cut ;
\ An answer, with the activation's cells (from de-x on) given back.
: de-cells-return ( r -- ) de-x de-truncate de-return ;
: de-claim ( n -- i flag )
  de-cells slab-claim dup ok? if drop true else de-abort false then ;
: de-fill ( t i n -- )
  begin dup 0> while 1- >r over lf-term-second@
  over r@ + de-cell ! swap lf-term-first@ swap r> repeat drop 2drop ;
: de-push-args ( t n -- flag )
  dup de-claim 0= if drop 2drop false exit then swap de-fill true ;

\ ---- Shapes and small steps.
: de-const? ( t -- flag ) lf-tag-constant lf-meta-tag? ;
: de-lam? ( t -- flag ) lf-tag-lam lf-meta-tag? ;
: de-pi? ( t -- flag ) lf-tag-pi lf-meta-tag? ;
: de-const-name ( const -- name ) lf-term-first@ lf-cref-slot lf-cref-name@ drop ;
: de-decl ( const -- d true | false ) lf-meta-const-decl ;
: de-kind? ( head kind -- flag )
  over de-const? if swap de-decl if lf-menv-kind = else drop false then
  else 2drop false then ;
: de-head-defn? ( t -- flag )
  lf-meta-head dup de-const? if de-decl if lf-menv-kind lf-kind-definition =
  else true then
  else drop false then ;
: de-eqv-of ( a b -- flag ) lf-meta-eqv dup ok? if drop else de-abort drop false then ;
: de-eqv? ( -- flag ) de-t de-s de-eqv-of ;
: de-inst ( t -- t' ) lf-instantiate-mvars de-must drop ;
: de-whnf ( t -- t' flag ) lf-whnf-core de-must ;
\ inferType; a literal's type is Nat (infer.fs has no literal case).
: de-infer ( t -- type flag )
  dup lf-term-tag@ lf-tag-lit = if drop lf-meta-nat de-must exit then lf-infer de-must ;
: de-free-mvar? ( t -- flag )
  dup lf-mvar? 0= if drop false exit then
  dup lf-mvar-assignable? swap lf-meta-unassigned? and ;
\ whnfD: a pi, or what whnf would leave (abort when whnf would do more).
: de-whnf-d ( type -- type' flag )
  dup de-pi? if true exit then de-whnf 0= if false exit then dup de-pi? if true exit then
  dup lf-meta-whnf-final? if true else outcome-unsupported de-abort false then ;

\ ---- Level lists (isListLevelDefEqAux): pairwise, Lean's way with no
\ checkpoint of its own; a false pair that held an assignable level
\ metavariable may have left assignments in Lean (de-taint).
\ A side that holds, or might hold, an assignable level metavariable.
: de-may-assign? ( level -- flag ) lf-level-assignable-mvar? ok? 0= or ;
: de-level-taint ( l r -- )
  de-may-assign? swap de-may-assign? or if true df df-taint ! then ;
: de-level-defeq? ( l r -- flag )
  2dup lf-meta-level-defeq dup ok? 0= if de-abort drop 2drop false exit then drop
  dup if nip nip exit then drop de-level-taint false ;
: de-level@ ( const i -- level ) swap lf-term-first@ lf-cref-slot lf-cref-pairs drop swap
  lf-cref-pair@ drop ;
: de-levels# ( const -- n ) lf-term-first@ lf-cref-slot lf-cref-pairs nip ;
: de-level-pair ( c1 c2 i -- flag ) tuck de-level@ >r de-level@ r> de-level-defeq? ;
\ isListLevelDefEqAux: pair by pair while both lists last; false when one
\ ends first.
: de-levels-min ( c1 c2 -- n ) de-levels# swap de-levels# min ;
: de-levels= ( c1 c2 -- flag ) de-levels# swap de-levels# = ;
: de-levels ( c1 c2 -- lbool )
  2dup de-levels-min 0 ?do 2dup i de-level-pair 0=
  if 2drop unloop lf-lb-false exit then loop de-levels= lf-lb ;
: de-same-const? ( h1 h2 -- flag )
  over de-const? over de-const? and if de-const-name swap de-const-name lf-name-same?
  else 2drop false then ;

\ ---- isDefEqProofIrrel.
: de-pi-types ( -- )
  de-t de-infer 0= if drop exit then de-s de-infer 0=
  if 2drop exit then ['] de-pass de-solve ;
: de-pi-check ( -- )
  de-t de-infer 0= if drop exit then dup lf-meta-is-prop de-must 0= if 2drop exit then
  if de-s de-infer 0= if 2drop exit then ['] de-pass de-solve
  else drop lf-lb-undef de-return then ;
: de-pirrel ( -- )
  de-t lf-meta-proof-quick de-must 0= if drop exit then
  case lf-lb-false of lf-lb-undef de-return endof  lf-lb-true of de-pi-types endof
    lf-lb-undef of de-pi-check endof endcase ;

\ ---- isDefEqEta (a := t, b := s): fun x => .. against b whose type is a
\ pi is compared with fun x : d => b x.
: de-eta-expand ( pi -- )
  lf-term-first@ 0 lf-term-bvar de-made 0= if 2drop exit then
  de-s swap lf-term-app de-made 0= if 2drop exit then
  lf-term-lam de-made 0= if drop exit then de-t swap ['] de-pass de-solve ;
: de-eta ( -- )
  de-t de-lam? de-s de-lam? 0= and 0= if lf-lb-undef de-return exit then
  de-s de-infer 0= if drop exit then de-whnf-d 0= if drop exit then
  dup de-pi? if de-eta-expand else drop lf-lb-undef de-return then ;

\ ---- isDefEqBinding: pairs of binders of one kind opened with new free
\ variables, each pushed on the current local context (Lean's withLCtx'
\ over mkLocalDecl), then the domains compared, then the bodies; at the
\ end the context comes back and the new entries go (lf-lctx-drop). Cells
\ from de-x: the context and the term mark on entry, then per pair the
\ variable and the second domain.
: de-same-binder? ( -- flag )
  de-t lf-term-tag@ dup de-s lf-term-tag@ = swap lf-term-binder-tag? and ;
: de-open-body ( body fvar -- body' flag ) lf-meta-instantiate1 de-must ;
: de-bind-push ( fvar -- fvar flag )
  dup de-push if de-s lf-term-first@ de-push else false then ;
: de-bind-bodies ( fvar -- flag )
  de-t lf-term-second@ over de-open-body 0= if 2drop false exit then de-t!
  de-s lf-term-second@ swap de-open-body 0= if drop false exit then de-s! true ;
: de-bind-local ( fvar -- fvar flag )
  dup 0 0 lf-local-new de-must 0= if drop false exit then
  lf-mctx-view swap lf-view-push de-must if lf-mctx-view! true else drop false then ;
: de-bind-fvar ( -- fvar flag ) de-t lf-term-first@ lf-lctx-local de-must ;
: de-bind-one ( -- flag )
  de-bind-fvar 0= if drop false exit then de-bind-local 0= if drop false exit then
  de-bind-push if de-bind-bodies else drop false then ;
: de-pair-at ( -- addr ) de-x de-y 2* + 2 + de-cell ;
: de-bind-n ( -- n ) de-cells slab-count de-x - 2 - 2/ ;
: de-restore ( view mark -- ) lf-lctx-drop lf-mctx-view! ;
: de-bind-done ( r -- )
  de-x de-cell 2@ de-restore de-cells-return ;
defer de-bind-dom ( -- )
: de-bind-dom-k ( r -- )
  lf-lb-true = if de-y+ de-bind-dom else lf-lb-false de-bind-done then ;
:noname ( -- )
  de-y de-bind-n < 0= if de-t de-s ['] de-bind-done de-solve exit then
  de-pair-at dup @ lf-fvar-type swap cell+ @ ['] de-bind-dom-k de-solve ;
is de-bind-dom
: de-term-mark ( -- mark ) lf-term-base lf-term-count @ + ;
: de-bind-save ( -- flag )
  de-cells slab-count df df-x ! de-term-mark de-push 0= if false exit then
  lf-mctx-view de-push ;
: de-binding ( -- )
  de-bind-save 0= if exit then
  begin de-same-binder? while de-bind-one 0= if exit then repeat de-bind-dom ;

\ ---- isDefEqOnFailure: a stuck metavariable (getStuckMVar?, whnf.fs)
\ that synthPending would not touch (synthetic opaque, or a type that is
\ no class), and unification hints: Init's one hint (Not p =?= p ->
\ False) can match only a definition at the head. Anything else
\ answers unsupported; this never answers true. Under isDefEqStuckEx a
\ stuck metavariable made at an outer depth is Lean's stuck signal: the
\ flag stuck? (raised by the caller), the rest skipped as Lean's throw
\ skips it.
: de-stuck-mvar ( t -- mvar true | false )
  lf-whnf-stuck dup ok? 0= if nip de-abort false exit then drop ;
: de-opaque? ( mvar -- flag ) lf-mvar-kind if mv-opaque = else true then ;
\ The synthesis hooks (S1 appendix D): Lean's synthPending
\ (SynthInstance.lean:1037) and synthInstance (ExprDefEq.lean:626),
\ answering unsupported until front/synth.fs, loaded, sets them.
: de-synth-later ( mvar -- flag outcome ) drop false outcome-unsupported ;
defer lf-meta-synth-pending ( mvar -- flag outcome )
' de-synth-later is lf-meta-synth-pending
: de-synth-none ( type -- inst flag outcome ) drop -1 false outcome-unsupported ;
defer lf-meta-synth ( type -- inst flag outcome )
' de-synth-none is lf-meta-synth
\ A hook runs a synthesis, which unifies: this machine (its record and
\ both stacks) is set aside on de-saved meanwhile, each stack's cells from
\ the last and its count after, and brought back after, however the hook
\ ends (Lean's nested isDefEq leaves its caller's state); no room to set
\ it aside answers full, nothing kept.
1 cells context-slab: de-saved
: de-out1 ( p k y -- p' outcome ) 2drop dup @ de-saved slab-push swap cell - swap ;
: de-out ( addr n -- outcome ) tuck 1- cells + swap 0 ['] de-out1 ok-fold nip ;
: de-in ( addr n -- ) cells over + swap ?do de-saved slab-pop i ! cell +loop ;
: de-cells# ( slab -- n ) dup slab-count swap slab-unit cell / * ;
: de-out-slab ( slab -- outcome )
  dup slab-base over de-cells# de-out ok-then? if slab-count de-saved slab-push then ;
: de-in-slab ( slab -- )
  de-saved slab-pop over slab-clear over slab-commit dup slab-base swap de-cells# de-in ;
: de-out-df ( -- outcome ) df /df cell / de-out ;
: de-out-frames ( -- outcome ) de-frames de-out-slab ;
: de-out-cells ( -- outcome ) de-cells de-out-slab ;
: de-aside ( -- outcome )
  de-saved slab-count de-out-df ['] de-out-frames ok-and ['] de-out-cells ok-and
  dup ok? if nip exit then swap de-saved slab-cut ;
: de-back ( -- ) de-cells de-in-slab de-frames de-in-slab df /df cell / de-in ;
: de-nested ( mvar xt -- flag outcome )
  de-aside dup ok? 0= if nip nip false swap exit then drop catch de-back throw ;
: de-pending ( mvar -- flag outcome ) ['] lf-meta-synth-pending de-nested ;
: de-class? ( mvar -- flag ) lf-mvar-type drop lf-meta-class-none? 0= ;
\ synthPending: true when it filled the metavariable, a failure aborts.
\ isDefEqArgs' postponed instance arguments discard the answer (Lean's
\ trySynthPending; the comparison that follows reads the filled one);
\ isDefEqOnFailure would compare again (unstuckMVar): not ported.
: de-synth-try ( mvar -- flag )
  dup de-opaque? if drop false exit then dup de-class? 0= if drop false exit then
  de-pending ok-then? 0= if de-abort false then ;
: de-synth-pending ( mvar -- ) de-synth-try if outcome-unsupported de-abort then ;
: de-try-synth ( t -- ) de-stuck-mvar if de-synth-try drop then ;
: de-older? ( mvar -- flag ) lf-mvar-depth if lf-mctx-depth < else false then ;
: de-unstuck ( t -- stuck? )
  de-stuck-mvar 0= if false exit then dup de-synth-pending
  lf-defeq-stuck de-flag? if de-older? else drop false then ;
: de-hints ( t -- )
  dup lf-mvar? if drop exit then de-head-defn? if outcome-unsupported de-abort then ;
: de-stuck-either ( -- stuck? )
  de-t de-unstuck ?dup if exit then de-aborted? if false exit then de-s de-unstuck ;
: de-on-failure ( -- stuck? )
  de-stuck-either dup de-aborted? or if exit then de-t de-hints de-s de-hints ;

\ ---- isDefEqArgs (t and s applications with one head, the parameter
\ facts from t's). Cells from de-x: n, m, the n arguments of t, the n of
\ s, (kind, prop) for m parameters, then the postponed parameters.
: de-a-n ( -- n ) de-x de-cell @ ;
: de-a-m ( -- m ) de-x 1+ de-cell @ ;
: de-a1 ( i -- t ) de-x 2 + + de-cell @ ;
: de-a2 ( i -- t ) de-x 2 + de-a-n + + de-cell @ ;
: de-pair ( i -- a1 a2 ) dup de-a1 swap de-a2 ;
: de-info ( i -- kind prop ) 2* de-x 2 + de-a-n 2* + + dup de-cell @ swap 1+ de-cell @ ;
: de-post0 ( -- i ) de-x 2 + de-a-n 2* + de-a-m 2* + ;
: de-post# ( -- k ) de-cells slab-count de-post0 - ;
: de-infos ( -- flag )
  de-a-m 0 ?do i lf-meta-param swap de-push 0= if drop unloop false exit then
    de-push 0= if unloop false exit then loop true ;
\ m, the parameters getFunInfoNArgs finds for t's head and n arguments.
: de-args-info ( n -- flag )
  de-t lf-meta-head swap lf-meta-fun-info de-must if de-push else drop false then ;
: de-args-arrays ( -- flag )
  de-t de-a-n de-push-args if de-s de-a-n de-push-args else false then ;
: de-args-layout ( -- flag )
  de-t lf-meta-args# dup de-push 0= if drop false exit then
  de-args-info 0= if false exit then de-args-arrays if de-infos else false then ;
\ isAbstractedUnassignedMVar (lambdas and functions passed) and
\ isEtaUnassignedMVar: an assignable metavariable still free.
: de-abs-step ( e -- e' flag )
  dup de-lam? if lf-term-second@ true exit then
  dup lf-meta-app? if lf-term-first@ true else false then ;
: de-abs-mvar? ( e -- flag ) begin de-abs-step 0= until de-free-mvar? ;
: de-eta-mvar? ( e -- flag )
  lf-meta-eta-expanded dup ok? 0= if de-abort 2drop false exit then drop
  if de-free-mvar? else drop false then ;
\ The first pass's code for argument i: 0 skip (a proof left to proof
\ irrelevance), 1 compare, 2 compare at implicit transparency, 3 later.
: de-a-skip? ( i -- flag )
  dup de-info nip swap dup de-a1 de-abs-mvar? swap de-a2 de-abs-mvar? or 0= and ;
: de-a-explicit? ( i -- flag ) de-info drop lf-binder-default = ;
: de-a-eta? ( i -- flag ) dup de-a1 de-eta-mvar? swap de-a2 de-eta-mvar? or ;
: de-first-code ( i -- code )
  dup de-a-explicit? if de-a-skip? if 0 else 1 then exit then
  dup de-a-eta? if drop 2 exit then de-a-skip? if 0 else 3 then ;
defer de-args-first ( -- )
defer de-args-rest ( -- )
defer de-args-post ( -- )
: de-args-first-k ( r -- )
  lf-lb-true = if de-y+ de-args-first else lf-lb-false de-cells-return then ;
: de-args-rest-k ( r -- )
  lf-lb-true = if de-y+ de-args-rest else lf-lb-false de-cells-return then ;
: de-args-post-k ( r -- )
  lf-lb-true = if de-y+ de-args-post else lf-lb-false de-cells-return then ;
: de-first-go ( code -- stop? )
  case 0 of false endof  1 of de-y de-pair ['] de-args-first-k de-solve true endof
    2 of de-y de-pair ['] de-args-first-k de-solve de-bump true endof
    3 of de-y de-push 0= endof endcase ;
:noname ( -- )
  begin de-y de-a-m < while de-y de-first-code de-first-go if exit then de-y+ repeat
  de-a-m df df-y ! de-args-rest ; is de-args-first
:noname ( -- )
  de-y de-a-n < 0= if 0 df df-y ! de-args-post exit then
  de-y de-pair ['] de-args-rest-k de-solve ; is de-args-rest
: de-post@ ( j -- i ) de-post0 + de-cell @ ;
:noname ( -- )
  de-y de-post# < 0= if lf-lb-true de-cells-return exit then
  de-y de-post@ dup de-info drop lf-binder-instance = if
  dup de-pair de-try-synth de-try-synth then
  de-pair ['] de-args-post-k de-solve de-bump ; is de-args-post
: de-args ( -- )
  de-t lf-meta-args# de-s lf-meta-args# <> if lf-lb-false de-return exit then
  de-cells slab-count df df-x ! de-args-layout if 0 df df-y ! de-args-first then ;

\ ---- isDefEqApp, under a checkpoint: one constant at both heads, the
\ arguments then the universe levels; else the heads, then the arguments.
: de-app-c ( r -- )
  lf-lb-true = if de-t lf-meta-head de-s lf-meta-head de-levels
  else lf-lb-false then de-close-k ;
: de-app-f ( r -- )
  lf-lb-true = 0= if lf-lb-false de-close-k exit then
  ['] de-close-k de-then de-t de-s ['] de-args de-invoke ;
: de-app ( -- )
  de-mark? 0= if exit then de-t lf-meta-head de-s lf-meta-head 2dup de-same-const?
  if 2drop ['] de-app-c de-then de-t de-s ['] de-args de-invoke
  else ['] de-app-f de-solve then ;

\ ---- checkTypesAndAssign (t := ?m, s := v): the types compared at
\ implicit transparency or above, then ?m := v.
\ mvars.fs refuses an assignment Lean would make (the metavariable was
\ assigned meanwhile, which checkAssignment's checks rule out):
\ unsupported; a full store stays full.
: de-assign-failed ( outcome -- )
  dup outcome-invalid = if drop outcome-unsupported then de-abort ;
: de-assign-now ( -- )
  de-t de-s lf-mvar-assign dup ok? if drop lf-lb-true de-return else de-assign-failed
  then ;
: de-ct-k ( r -- ) lf-lb-true = if de-assign-now else lf-lb-false de-return then ;
\ An instance-typed metavariable (Lean's branch under the option
\ backward.isDefEq.respectTransparency.instanceSearchTypes, default true,
\ ExprDefEq.lean:640-660; synthesis's subgoals are instance-typed,
\ SynthInstance.lean:358): v instantiated; when its spine's metavariables
\ are admissible (spineMVarsAdmissible: instance-typed, read-only or
\ synthetic opaque) the types are compared at exactly instances
\ transparency and ?m := v on true (checkTypesForInstanceTypedMVar-
\ Assignment); otherwise, or when they differ and ?m's type is no pi,
\ synthInstanceTypedMVarAndUnify: under a checkpoint, synthPending (the
\ hook, the machine set aside), then v against ?m's instance. Not ported,
\ unsupported: types that differ where ?m's type is a pi (Lean compares
\ them at implicit transparency and the bodies under its binders), and a
\ let on v's spine.
: de-read-only? ( mvar -- flag )
  dup lf-mvar-depth drop lf-mctx-depth <> if drop true exit then
  lf-mvar-kind drop mv-opaque = lf-defeq-opaque de-flag? 0= and ;
: de-adm-mvar ( mvar -- e lbool )   \ a delayed one's pending one, or the verdict
  dup lf-mvar-delayed if 2drop nip lf-lb-undef exit then
  dup lf-mvar-inst? swap de-read-only? or lf-lb 0 swap ;
: de-adm-node ( e tag -- e' lbool )
  case lf-tag-app of lf-term-first@ lf-lb-undef endof
    lf-tag-lam of lf-term-second@ lf-lb-undef endof
    lf-tag-projection of lf-proj-struct lf-lb-undef endof
    lf-tag-mvar of de-adm-mvar endof  lf-lb-true swap endcase ;
: de-adm-step ( e -- e' lbool )
  dup lf-meta-mvar-free? if lf-lb-true exit then
  dup lf-let? if outcome-unsupported de-abort lf-lb-false exit then
  dup lf-term-tag@ de-adm-node ;
: de-admissible? ( v -- flag )
  begin de-adm-step dup lf-lb-undef = while drop repeat nip lf-lb-true = ;
: de-synth-k ( flag outcome -- )
  de-must 0= if drop exit then 0= if lf-lb-false de-close-k exit then
  de-s de-t de-inst ['] de-close-k de-solve ;
: de-inst-synth ( -- ) de-mark? if de-t de-pending de-synth-k then ;
: de-inst-k ( r -- )
  lf-lb-true = if de-assign-now exit then
  de-t lf-mvar-type drop de-pi? if outcome-unsupported de-abort else de-inst-synth then ;
: de-inst-types ( -- )
  de-t lf-mvar-type 0= if outcome-invalid de-abort exit then
  de-s de-infer 0= if 2drop exit then ['] de-inst-k de-solve lf-tr-instances df df-mode
  ! ;
: de-check-inst ( -- )
  de-s de-inst de-aborted? if drop exit then de-s!
  de-s de-admissible? de-aborted? if drop exit then if de-inst-types else de-inst-synth
  then ;
: de-check-types ( -- )
  de-t lf-mvar? 0= if lf-lb-false de-return exit then
  de-t lf-mvar-inst? if de-check-inst exit then
  de-t lf-mvar-type 0= if outcome-invalid de-abort exit then
  de-s de-infer 0= if 2drop exit then ['] de-ct-k de-solve de-bump ;

\ ---- processAssignment (t := ?m a1 .. an, s := v). Cells from de-x: n,
\ then the arguments, simplified in place (simpAssignmentArg); de-y the
\ next one.
: de-pa-n ( -- n ) de-x de-cell @ ;
: de-pa-arg ( i -- addr ) de-x 1+ + de-cell ;
: de-pa-args ( -- addr n ) 0 de-pa-arg de-pa-n ;
: de-mvar ( -- mvar ) de-t lf-meta-head ;
: de-scope ( fvar -- flag ) de-mvar swap lf-mvar-sees? ;
: de-let-fvar? ( t -- flag ) dup lf-meta-fvar? if lf-fvar-let? else drop false then ;
: de-simp ( arg -- arg' flag )
  dup lf-meta-head lf-meta-mvar-free? 0= if de-inst de-aborted? if false exit then then
  begin dup de-let-fvar? while lf-fvar-value repeat true ;
: de-pa-simp ( i -- flag )
  de-pa-arg dup @ de-simp 0= if 2drop false exit then swap ! true ;
: de-pa-dup? ( a i -- flag ) false swap 0 ?do over i de-pa-arg @ = or loop nip ;
: de-pa-pattern? ( i -- flag )
  dup de-pa-arg @ dup lf-meta-fvar? 0= if 2drop false exit then
  tuck swap de-pa-dup? if drop false exit then de-scope 0= lf-defeq-quasi de-flag? or ;
: de-pa-locals? ( -- flag ) false de-pa-n 0 ?do i de-pa-arg @ de-scope or loop ;
: de-pa-check ( v -- v' flag )
  de-mvar de-pa-args lf-meta-pattern! lf-meta-check-assignment de-must
  0= if drop false then ;
: de-pa-types ( v -- )
  de-mvar swap ['] de-cells-return de-then ['] de-check-types de-invoke ;
\ Quasi-patterns need Lean's isTypeCorrect: not ported.
: de-pa-abstract ( v -- )
  >r de-pa-args r> lf-meta-mk-lambda de-must 0= if drop exit then
  de-pa-locals? if drop outcome-unsupported de-abort exit then de-pa-types ;
\ constApprox's default case with no arguments: ?m := v once more
\ checked; with arguments only under constApprox (not ported).
: de-assign-const ( -- )
  de-s de-pa-check de-aborted? if 2drop exit then if de-pa-types
  else drop lf-lb-false de-cells-return then ;
: de-const-approx ( -- )
  de-pa-n 0= if de-assign-const exit then
  lf-defeq-const de-flag? if outcome-unsupported de-abort
  else lf-lb-false de-cells-return then ;
\ First-order approximation (foApprox), v head-beta reduced in de-y:
\ ?m a1 .. an =?= f b is an =?= b and ?m a1 .. an-1 =?= f under a
\ checkpoint; else Lean unfolds v (not ported) or goes on.
: de-fo-lhs ( -- t )
  de-mvar de-pa-n 0 ?do i de-pa-arg @ lf-term-app de-made 0= if unloop exit then loop ;
: de-fo-aux-1 ( r -- )
  lf-lb-true = 0= if lf-lb-false de-close-k exit then
  de-t lf-term-first@ de-s lf-term-first@ ['] de-close-k de-solve ;
: de-fo-aux ( -- )
  de-mark? if de-t lf-term-second@ de-s lf-term-second@ ['] de-fo-aux-1 de-solve then ;
\ With no arguments first-order approximation never succeeds, so Lean's
\ unfolding of v cannot change the answer: only with arguments is it
\ needed (not ported).
: de-fo-fail ( -- )
  de-pa-n 0> de-y de-head-defn? and
  if outcome-unsupported de-abort else de-const-approx then ;
: de-fo-k ( r -- ) lf-lb-true = if lf-lb-true de-cells-return else de-fo-fail then ;
: de-fo ( -- )
  lf-defeq-fo de-flag? 0= if de-const-approx exit then
  de-s lf-meta-head-beta de-must 0= if drop exit then df df-y !
  de-pa-n 0> de-y lf-meta-app? and 0= if de-fo-fail exit then
  ['] de-fo-k de-then de-fo-lhs de-y ['] de-fo-aux de-invoke ;
: de-pa-final ( -- )
  de-s de-inst de-aborted? if drop exit then dup lf-meta-head de-mvar =
  if drop de-fo exit then
  de-pa-check de-aborted? if 2drop exit then if de-pa-abstract else drop de-fo then ;
: de-pa-loop ( -- )
  begin de-y de-pa-n < while de-y de-pa-simp 0= if exit then
    de-y de-pa-pattern? 0= if de-fo exit then de-y+ repeat de-pa-final ;
: de-assign ( -- )
  de-cells slab-count df df-x ! de-t lf-meta-args# dup de-push 0= if drop exit then
  de-t swap de-push-args if 0 df df-y ! de-pa-loop then ;
\ processAssignment': on false, again with whnf's value of v.
: de-pa2-retry ( v' -- )
  dup de-s de-eqv-of if drop lf-lb-false de-return exit then
  dup de-t de-eqv-of if drop lf-lb-true de-return exit then
  df df-taint @ if drop outcome-unsupported de-abort exit then
  de-t swap ['] de-pass de-then ['] de-assign de-invoke ;
: de-pa2-k ( r -- )
  dup lf-lb-true = if de-return exit then drop de-s de-whnf 0= if drop exit then
  dup lf-meta-whnf-final? if de-pa2-retry else drop outcome-unsupported de-abort then ;
: de-assign2 ( -- ) ['] de-pa2-k de-then de-t de-s ['] de-assign de-invoke ;

\ ---- isDefEqMVarSelf and isDefEqQuickMVarMVar.
: de-ms-k ( r -- )
  lf-lb-true = if lf-lb-true de-return exit then
  de-mvar lf-mvar-assignable? 0= if lf-lb-false de-return exit then
  lf-defeq-const de-flag? if outcome-unsupported de-abort
  else lf-lb-false de-return then ;
: de-mvar-self ( -- )
  de-t lf-meta-args# de-s lf-meta-args# <> if lf-lb-false de-return exit then
  ['] de-ms-k de-then de-t de-s ['] de-args de-invoke ;
: de-ckpt-assign ( -- )
  de-mark? if ['] de-close-k de-then de-t de-s ['] de-assign de-invoke then ;
: de-mm-st ( r -- )
  dup lf-lb-true = if de-return exit then drop ['] de-pass de-then de-t
  de-s ['] de-assign de-invoke ;
: de-mm-ts ( r -- )
  dup lf-lb-true = if de-return exit then drop ['] de-pass de-then de-s
  de-t ['] de-assign de-invoke ;
: de-mvar-mvar ( -- )
  de-s lf-mvar? de-t lf-mvar? 0= and
  if ['] de-mm-st de-then de-s de-t else ['] de-mm-ts de-then de-t de-s then
  ['] de-ckpt-assign de-invoke ;

\ ---- isDefEqOffset (Lean's s := t, t := s): the pair to compare in x
\ and y (code 1), or the answer in y, x -1 (code 2), each only for Nat
\ terms (ifNatExpr: t's type against Nat one depth deeper); code 0
\ undef.
: de-off-pair ( a b -- code ) df df-y ! df df-x ! 1 ;
: de-off-const ( lbool -- code ) df df-y ! -1 df df-x ! 2 ;
: de-mk-off ( e k -- e' ) lf-meta-mk-offset de-must drop ;
: de-lit ( n -- t ) lf-meta-nat-lit de-must drop ;
\ Offsets and values are unsigned cells (nat-offset.fs): compared with u>.
: de-off-both ( a k1 b k2 -- code )
  rot 2dup = if 2drop de-off-pair exit then
  2dup u> if - de-mk-off else swap - rot swap de-mk-off swap then de-off-pair ;
: de-off-value ( a k1 v2 -- code )
  2dup u> if 2drop drop lf-lb-false de-off-const else swap - de-lit de-off-pair then ;
: de-value-off ( v1 b k2 -- code )
  rot 2dup u> if 2drop drop lf-lb-false de-off-const
  else swap - de-lit swap de-off-pair then ;
: de-off-a ( a k1 -- code )
  de-s lf-meta-offset de-must 0= if 2drop 2drop drop 0 exit then
  if de-off-both exit then 2drop
  de-s lf-meta-eval-nat de-must 0= if 2drop 2drop 0 exit then
  if de-off-value else 2drop drop 0 then ;
: de-off-v ( v1 -- code )
  de-s lf-meta-offset de-must 0= if 2drop 2drop 0 exit then
  if de-value-off exit then 2drop
  de-s lf-meta-eval-nat de-must 0= if 2drop drop 0 exit then
  if = lf-lb de-off-const else 2drop 0 then ;
: de-off-code ( -- code )
  de-t lf-meta-offset de-must 0= if 2drop drop 0 exit then
  if de-off-a exit then 2drop
  de-t lf-meta-eval-nat de-must 0= if 2drop 0 exit then
  if de-off-v else drop 0 then ;
: de-off-k ( r -- )
  lf-lb-true = 0= if lf-lb-undef de-return exit then
  de-x 0< if de-y de-return else de-x de-y ['] de-pass de-solve then ;
: de-offset ( -- )
  de-off-code 0= if lf-lb-undef de-return exit then
  de-t de-infer 0= if drop exit then lf-meta-nat de-must 0= if 2drop exit then
  ['] de-off-k de-solve de-deeper ;

\ ---- isDefEqLateSpecialCases: isDefEqProjInst (unsupported where it
\ might unfold), isDefEqStringLit (a string literal against
\ String.ofList cs: not ported), isDefEqUnitLike.
: de-mode-inst? ( -- flag ) df df-mode @ dup lf-tr-instances = swap lf-tr-implicit = or ;
: de-str? ( t -- flag ) lf-term-tag@ lf-tag-str = ;
: de-of-list? ( t -- flag ) lf-meta-head s" String.ofList" lf-meta-const-named? ;
: de-str-list? ( a b -- flag ) de-of-list? swap de-str? and ;
: de-string-lit? ( -- flag ) de-t de-s de-str-list? de-s de-t de-str-list? or ;
: de-nonrec? ( data -- flag )
  dup lf-ity-indices lf-more-field 0= over lf-ity-ctors@ nip 1 = and
  swap lf-ity-flags lf-more-field lf-ity-rec-bit and 0= and ;
: de-data ( d -- data ) lf-menv-data ;
\ The inductive data of a name's declaration; none (no such declaration,
\ a library one not decoded for want of room) ends the comparison with
\ that outcome.
: de-named-data ( name -- data true | false )
  lf-menv-find de-must if de-data true else drop false then ;
: de-ctor-fields ( name -- n|-1 )
  de-named-data if lf-ict-fields lf-more-field else -1 then ;
: de-unit-data? ( data -- flag )
  dup de-nonrec? if lf-ity-ctors@ drop @ de-ctor-fields 0= else drop false then ;
: de-unit-type? ( type -- flag )
  lf-meta-head dup lf-kind-inductive de-kind? if de-decl drop de-data de-unit-data?
  else drop false then ;
: de-late-u ( r -- ) lf-lb-true = if lf-lb-true else lf-lb-undef then de-return ;
: de-late-type ( -- type flag )
  de-t de-infer 0= if false exit then de-whnf 0= if false exit then
  dup lf-meta-whnf-final? if true else outcome-unsupported de-abort false then ;
: de-proj-inst? ( -- flag ) de-mode-inst? de-t de-head-defn? de-s de-head-defn? or and ;
: de-late-unit ( type -- ) de-s de-infer 0= if 2drop exit then ['] de-late-u de-solve ;
: de-late ( -- )
  de-proj-inst? de-string-lit? or if outcome-unsupported de-abort exit then
  de-late-type 0= if drop exit then
  dup de-unit-type? if de-late-unit else drop lf-lb-undef de-return then ;

\ ---- Delta candidates, isDefEqNat, isDefEqEtaStruct.
: de-delta? ( t -- flag )
  lf-meta-head dup de-const? 0= if drop false exit then
  de-const-name df df-mode @ lf-menv-unfoldable de-must if nip else 2drop true then ;
: de-nat-name? ( const -- flag ) de-const-name lf-name-prefix@ s" Nat" rot lf-meta-name? ;
: de-nat-op? ( t -- flag )
  dup lf-meta-args# 1 3 within 0= if drop false exit then
  lf-meta-head dup de-const? if de-nat-name? else drop false then ;
: de-nat-unported? ( -- flag )
  de-t lf-meta-fvar-free? de-s lf-meta-fvar-free? and
  if de-t de-nat-op? de-s de-nat-op? or
  else false then ;
: de-ctor? ( t -- flag ) lf-meta-head lf-kind-constructor de-kind? ;
: de-ctor-arity ( ctor -- n )
  de-decl drop de-data
  dup lf-ict-params lf-more-field swap lf-ict-fields lf-more-field + ;
: de-ctor-induct ( ctor -- data true | false )
  de-decl drop de-data lf-ict-induct lf-more-field de-named-data ;
: de-induct-nonrec? ( ctor -- flag ) de-ctor-induct if de-nonrec? else false then ;
: de-ctor-fields-of ( ctor -- n ) de-decl drop de-data lf-ict-fields lf-more-field ;
\ isDefEqEtaStruct a b with b a constructor application of a non-recursive
\ structure and a none: code 1 when it has no fields (Lean then compares
\ the two types under a checkpoint), else 0 (false); with fields Lean
\ compares projections (unsupported, as projections are, plan FE1c).
: de-eta-struct ( a b -- code )
  dup de-ctor? 0= if 2drop 0 exit then over de-ctor? if 2drop 0 exit then
  dup lf-meta-head de-ctor-arity over lf-meta-args# <> if 2drop 0 exit then
  nip lf-meta-head dup de-induct-nonrec? 0= if drop 0 exit then
  de-ctor-fields-of 0= if 1 else outcome-unsupported de-abort 0 then ;

\ ---- isDefEqQuick.
defer de-quick-x ( -- )
: de-let-step ( e -- e' flag outcome )
  dup lf-let? 0= if false outcome-ok exit then
  dup lf-let-body lf-meta-loose ok-then? 0= if false swap exit then
  if false else lf-let-body true then outcome-ok ;
: de-consume ( e -- e' flag )
  begin de-let-step de-must 0= if drop false exit then 0= until true ;
: de-quick-lit ( -- ) de-t de-s lf-lit-same? lf-lb de-return ;
: de-quick-str ( -- ) de-t de-s lf-str-same? lf-lb de-return ;
: de-quick-sort ( -- )
  de-t lf-term-first@ de-s lf-term-first@ de-level-defeq? lf-lb de-return ;
: de-quick-binder ( -- )
  de-eqv? if lf-lb-true de-return exit then ['] de-pass de-then de-t
  de-s ['] de-binding de-invoke ;
: de-live? ( -- flag ) de-t lf-fvar-live? de-s lf-fvar-live? and ;
: de-quick-fvar ( -- )
  de-live? 0= if outcome-invalid de-abort exit then  de-t de-s =
  if lf-lb-true de-return exit then
  de-t lf-fvar-let? de-s lf-fvar-let? or if lf-lb-undef de-return exit then
  ['] de-pass de-then de-t de-s ['] de-pirrel de-invoke ;
: de-assigned? ( head -- flag )
  dup lf-mvar? if lf-meta-unassigned? 0= else drop false then ;
: de-delayed? ( head -- flag ) dup lf-mvar? if lf-meta-delayed? else drop false then ;
\ expandDelayedAssigned?: a delayed head, when instantiating changes t.
: de-expand ( t -- t' flag )
  dup lf-meta-head de-delayed? 0= if false exit then
  dup de-inst 2dup de-eqv-of if drop false else nip true then ;
: de-same-mvar? ( -- flag ) de-t lf-meta-head dup lf-mvar? swap de-s lf-meta-head = and ;
: de-assignable? ( t -- flag )
  lf-meta-head dup lf-mvar? if lf-mvar-assignable? else drop false then ;
: de-both-fixed-k ( r -- )
  dup lf-lb-undef <> if de-return exit then drop
  lf-defeq-stuck de-flag? if lf-meta-stuck de-abort else lf-lb-false de-return then ;
: de-assignables ( -- )
  de-t de-assignable? de-s de-assignable? 2dup and if 2drop de-mvar-mvar exit then
  2dup or 0= if 2drop ['] de-both-fixed-k de-then de-t
  de-s ['] de-pirrel de-invoke exit then
  drop if de-t de-s else de-s de-t then ['] de-pass de-then ['] de-assign2 de-invoke ;
: de-requick ( t s -- true ) ['] de-quick-x de-goto true ;
\ An assigned head instantiated or a delayed one expanded, and
\ isDefEqQuick again.
: de-heads-again? ( -- flag )
  de-t lf-meta-head de-assigned? if de-t de-inst de-s de-requick exit then
  de-s lf-meta-head de-assigned? if de-t de-s de-inst de-requick exit then
  de-t de-expand if de-s de-requick exit then drop
  de-s de-expand if de-t swap de-requick else drop false then ;
: de-quick-heads ( -- )
  de-heads-again? if exit then de-same-mvar? 0= if de-assignables exit then
  ['] de-pass de-then de-t de-s ['] de-mvar-self de-invoke ;
: de-eta1 ( a b -- flag )
  swap lf-meta-eta-expanded dup ok? 0= if de-abort 2drop drop false exit then drop
  if de-eqv-of else 2drop false then ;
: de-quick-other ( -- )
  de-eqv? if lf-lb-true de-return exit then
  de-t de-s de-eta1 de-s de-t de-eta1 or if lf-lb-true de-return exit then
  de-t lf-meta-head lf-mvar? de-s lf-meta-head lf-mvar? or
  if de-quick-heads else lf-lb-undef de-return then ;
: de-quick-same ( tag -- )
  case lf-tag-lit of de-quick-lit endof  lf-tag-str of de-quick-str endof
    lf-tag-symbolic-sort of de-quick-sort endof
    lf-tag-lam of de-quick-binder endof  lf-tag-pi of de-quick-binder endof
    lf-tag-fvar of de-quick-fvar endof  >r de-quick-other r> endcase ;
: de-quick ( -- )
  de-t de-consume 0= if drop exit then de-t!  de-s de-consume 0= if drop exit then de-s!
  de-t lf-term-tag@ de-s lf-term-tag@ over = if de-quick-same
  else drop de-quick-other then ;
' de-quick is de-quick-x

\ ---- isExprDefEqExpensive and isExprDefEqAuxImpl.
: de-consts ( -- )
  de-t de-const-name de-s de-const-name lf-name-same? 0=
  if lf-lb-false de-return exit then
  de-t de-s de-levels de-return ;
\ isDefEqAppFallback: the late cases after isDefEqOnFailure; its stuck
\ signal caught, raised again unless the late cases answer true.
: de-fb-late ( r -- ) lf-lb-true = lf-lb de-return ;
: de-fb-stuck ( r -- )
  lf-lb-true = if lf-lb-true de-return else lf-meta-stuck de-abort then ;
: de-exp-app ( r -- )
  dup lf-lb-true = if de-return exit then drop de-on-failure
  if ['] de-fb-stuck else ['] de-fb-late then de-then de-t de-s ['] de-late de-invoke ;
: de-exp-late ( r -- )
  dup lf-lb-undef <> if de-return exit then drop
  de-on-failure if lf-meta-stuck de-abort else lf-lb-false de-return then ;
: de-exp-shape ( -- )
  de-t de-const? de-s de-const? and if de-consts exit then
  de-t lf-meta-app? de-s lf-meta-app? and
  if ['] de-exp-app de-then de-t de-s ['] de-app de-invoke exit then
  ['] de-exp-late de-then de-t de-s ['] de-late de-invoke ;
\ Structure eta both ways (each a checkpointed isDefEq of the types).
: de-es-types ( a b -- )
  de-infer 0= if 2drop exit then swap de-infer 0= if 2drop drop exit then
  swap ['] de-top-x de-invoke ;
: de-es-k2 ( r -- ) lf-lb-true = if lf-lb-true de-return else de-exp-shape then ;
: de-exp-es2 ( -- )
  de-s de-t de-eta-struct if ['] de-es-k2 de-then de-s de-t de-es-types
  else de-exp-shape then ;
: de-es-k1 ( r -- ) lf-lb-true = if lf-lb-true de-return else de-exp-es2 then ;
: de-exp-delta ( -- )
  de-t de-delta? de-s de-delta? or if outcome-unsupported de-abort exit then
  de-t de-s de-eta-struct if ['] de-es-k1 de-then de-t de-s de-es-types
  else de-exp-es2 then ;
: de-exp-o ( r -- ) dup lf-lb-undef = if drop de-exp-delta else de-return then ;
: de-exp-nat ( -- )
  de-nat-unported? if outcome-unsupported de-abort exit then
  ['] de-exp-o de-then de-t de-s ['] de-offset de-invoke ;
: de-changed? ( t' s' -- t' s' flag ) over de-t de-eqv-of 0= over de-s de-eqv-of 0= or ;
\ whnfCore of both sides: when either changes, isExprDefEqAux again;
\ else the step xt.
: de-rewhnf ( xt -- )
  de-t de-whnf 0= if 2drop exit then de-s de-whnf 0= if 2drop drop exit then
  de-changed? if rot drop ['] de-solve-x de-goto else 2drop execute then ;
: de-exp-proj ( -- )
  de-t lf-proj? de-s lf-proj? or if outcome-unsupported de-abort
  else ['] de-exp-nat de-rewhnf then ;
: de-exp-e2 ( r -- ) dup lf-lb-undef = if drop de-exp-proj else de-return then ;
: de-exp-e1 ( r -- )
  dup lf-lb-undef <> if de-return exit then drop
  ['] de-exp-e2 de-then de-s de-t ['] de-eta de-invoke ;
: de-expensive ( -- ) ['] de-exp-e1 de-then de-t de-s ['] de-eta de-invoke ;
: de-solve-inst ( -- )
  de-t de-inst de-t! de-s de-inst de-s! de-aborted? 0= if de-expensive then ;
: de-solve-p ( r -- )
  dup lf-lb-undef = if drop ['] de-solve-inst de-rewhnf else de-return then ;
: de-solve-q ( r -- )
  dup lf-lb-undef <> if de-return exit then drop
  ['] de-solve-p de-then de-t de-s ['] de-pirrel de-invoke ;
: de-solve-entry ( -- )
  de-spend? if ['] de-solve-q de-then de-t de-s ['] de-quick de-invoke then ;
' de-solve-entry is de-solve-x

\ ---- isDefEq: checkpointDefEq of isExprDefEqAux.
: de-top ( -- ) de-mark? if de-t de-s ['] de-close-k de-solve then ;
' de-top is de-top-x
: de-config ( -- )
  lf-defeq-mode df df-mode ! outcome-ok df df-outcome ! false df df-taint !
  df df-limit @ ?dup 0= if lf-defeq-default-fuel then df df-fuel !
  lf-lb-undef df df-result !  lf-defeq-ctx de-flag? lf-meta-ctx-approx! ;
: de-start ( t s -- )
  de-frames slab-clear de-cells slab-clear 0 df df-m ! ['] de-top de-regs! de-config
  lf-mctx-view df df-view0 ! de-term-mark df df-mark0 ! ;
\ The local context as on entry, the entries made since dropped.
: de-leave ( -- ) df df-view0 @ df df-mark0 @ de-restore ;
: de-answer ( -- flag outcome )
  df df-result @ dup lf-lb-undef =
  if drop false outcome-invalid exit then lf-lb-true = outcome-ok ;
: de-finish ( -- flag outcome )
  df df-outcome @ ok? if de-answer else de-unwind false df df-outcome @ then de-leave ;
: lf-meta-defeq ( t s -- flag outcome )
  2dup lf-term-pair-valid? 0= if 2drop false outcome-invalid exit then
  de-start ['] de-loop catch ?dup if de-unwind de-leave throw then de-finish ;
\ isDefEqGuarded (Basic.lean:2546): the stuck signal answers false; every
\ other failure passes on.
: lf-meta-defeq-guarded ( t s -- flag outcome )
  lf-meta-defeq dup lf-meta-stuck = if 2drop false outcome-ok then ;

base !   \ the BASE this file was loaded with
